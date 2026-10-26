import V185TrunkScan23Chunk0162

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_964707 : List Nat := [1, 1, 1, 5, 1, 1, 2, 1, 5, 5]
def baseStart_964707 : Nat := 118140960795 + 964707 * 2 ^ 59
def prefixEnd_964707 : Nat := 4983230072969 + 3 ^ 40 * 964707 * 2
def baseEnd_964707 : Nat := 165119460585687437708633

theorem tailTrace_964707 : CollatzResearch.WordTrace tailWord_964707 prefixEnd_964707 165119460585687437708633 := by
  unfold tailWord_964707
  simp only [CollatzResearch.WordTrace]
  refine ⟨35185754916038772683588375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23457169944025848455725583 35185754916038772683588375)
  ·
    refine ⟨52778632374058159025382563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35185754916038772683588375 52778632374058159025382563)
    ·
      refine ⟨79167948561087238538073845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52778632374058159025382563 79167948561087238538073845)
      ·
        refine ⟨7421995177601928612944423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 79167948561087238538073845 7421995177601928612944423)
        ·
          refine ⟨11132992766402892919416635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7421995177601928612944423 11132992766402892919416635)
          ·
            refine ⟨16699489149604339379124953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11132992766402892919416635 16699489149604339379124953)
            ·
              refine ⟨12524616862203254534343715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16699489149604339379124953 12524616862203254534343715)
              ·
                refine ⟨18786925293304881801515573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12524616862203254534343715 18786925293304881801515573)
                ·
                  refine ⟨1761274246247332668892085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18786925293304881801515573 1761274246247332668892085)
                  ·
                    refine ⟨165119460585687437708633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1761274246247332668892085 165119460585687437708633)
                    ·
                      rfl

theorem cell23_964707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 5, 5].length) (baseStart_964707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_964707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_964707 prefixEnd_964707 := by exact prefixLift 964707
  have htrace : WordTrace (prefixWord ++ tailWord_964707) baseStart_964707 baseEnd_964707 := by
    simpa [prefixWord, tailWord_964707, baseEnd_964707] using wordTrace_append hprefix tailTrace_964707
  have hstable : (prefixWord ++ tailWord_964707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964707).length < 2 ^ (prefixWord ++ tailWord_964707).sum := by decide
  have hdescent : baseEnd_964707 < baseStart_964707 := by decide
  rcases family_descends (prefixWord ++ tailWord_964707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964757 : List Nat := [1, 3, 2, 1, 1, 1, 3, 1, 3, 1, 6]
def baseStart_964757 : Nat := 118140960795 + 964757 * 2 ^ 59
def prefixEnd_964757 : Nat := 4983230072969 + 3 ^ 40 * 964757 * 2
def baseEnd_964757 : Nat := 495384055789787117500669

theorem tailTrace_964757 : CollatzResearch.WordTrace tailWord_964757 prefixEnd_964757 495384055789787117500669 := by
  unfold tailWord_964757
  simp only [CollatzResearch.WordTrace]
  refine ⟨35187578565857631222908525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23458385710571754148605683 35187578565857631222908525)
  ·
    refine ⟨13195341962196611708590697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35187578565857631222908525 13195341962196611708590697)
    ·
      refine ⟨9896506471647458781443023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13195341962196611708590697 9896506471647458781443023)
      ·
        refine ⟨14844759707471188172164535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9896506471647458781443023 14844759707471188172164535)
        ·
          refine ⟨22267139561206782258246803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14844759707471188172164535 22267139561206782258246803)
          ·
            refine ⟨33400709341810173387370205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22267139561206782258246803 33400709341810173387370205)
            ·
              refine ⟨12525266003178815020263827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33400709341810173387370205 12525266003178815020263827)
              ·
                refine ⟨18787899004768222530395741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12525266003178815020263827 18787899004768222530395741)
                ·
                  refine ⟨7045462126788083448898403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18787899004768222530395741 7045462126788083448898403)
                  ·
                    refine ⟨10568193190182125173347605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7045462126788083448898403 10568193190182125173347605)
                    ·
                      refine ⟨495384055789787117500669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10568193190182125173347605 495384055789787117500669)
                      ·
                        rfl

theorem cell23_964757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 3, 1, 6].length) (baseStart_964757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_964757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_964757 prefixEnd_964757 := by exact prefixLift 964757
  have htrace : WordTrace (prefixWord ++ tailWord_964757) baseStart_964757 baseEnd_964757 := by
    simpa [prefixWord, tailWord_964757, baseEnd_964757] using wordTrace_append hprefix tailTrace_964757
  have hstable : (prefixWord ++ tailWord_964757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964757).length < 2 ^ (prefixWord ++ tailWord_964757).sum := by decide
  have hdescent : baseEnd_964757 < baseStart_964757 := by decide
  rcases family_descends (prefixWord ++ tailWord_964757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964764 : List Nat := [2, 2, 3, 2, 1, 1, 1, 4, 1, 1, 5]
def baseStart_964764 : Nat := 118140960795 + 964764 * 2 ^ 59
def prefixEnd_964764 : Nat := 4983230072969 + 3 ^ 40 * 964764 * 2
def baseEnd_964764 : Nat := 495387650154368590113137

theorem tailTrace_964764 : CollatzResearch.WordTrace tailWord_964764 prefixEnd_964764 495387650154368590113137 := by
  unfold tailWord_964764
  simp only [CollatzResearch.WordTrace]
  refine ⟨17593916938416135709206673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23458555917888180945608897 17593916938416135709206673)
  ·
    refine ⟨13195437703812101781905005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17593916938416135709206673 13195437703812101781905005)
    ·
      refine ⟨4948289138929538168214377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13195437703812101781905005 4948289138929538168214377)
      ·
        refine ⟨3711216854197153626160783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4948289138929538168214377 3711216854197153626160783)
        ·
          refine ⟨5566825281295730439241175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3711216854197153626160783 5566825281295730439241175)
          ·
            refine ⟨8350237921943595658861763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5566825281295730439241175 8350237921943595658861763)
            ·
              refine ⟨12525356882915393488292645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8350237921943595658861763 12525356882915393488292645)
              ·
                refine ⟨2348504415546636279054871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12525356882915393488292645 2348504415546636279054871)
                ·
                  refine ⟨3522756623319954418582307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2348504415546636279054871 3522756623319954418582307)
                  ·
                    refine ⟨5284134934979931627873461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3522756623319954418582307 5284134934979931627873461)
                    ·
                      refine ⟨495387650154368590113137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5284134934979931627873461 495387650154368590113137)
                      ·
                        rfl

theorem cell23_964764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_964764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_964764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_964764 prefixEnd_964764 := by exact prefixLift 964764
  have htrace : WordTrace (prefixWord ++ tailWord_964764) baseStart_964764 baseEnd_964764 := by
    simpa [prefixWord, tailWord_964764, baseEnd_964764] using wordTrace_append hprefix tailTrace_964764
  have hstable : (prefixWord ++ tailWord_964764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964764).length < 2 ^ (prefixWord ++ tailWord_964764).sum := by decide
  have hdescent : baseEnd_964764 < baseStart_964764 := by decide
  rcases family_descends (prefixWord ++ tailWord_964764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964775 : List Nat := [1, 1, 6, 2, 3, 1, 1, 2, 1, 5]
def baseStart_964775 : Nat := 118140960795 + 964775 * 2 ^ 59
def prefixEnd_964775 : Nat := 4983230072969 + 3 ^ 40 * 964775 * 2
def baseEnd_964775 : Nat := 165131099480522682358529

theorem tailTrace_964775 : CollatzResearch.WordTrace tailWord_964775 prefixEnd_964775 165131099480522682358529 := by
  unfold tailWord_964775
  simp only [CollatzResearch.WordTrace]
  refine ⟨35188235079792420297063779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23458823386528280198042519 35188235079792420297063779)
  ·
    refine ⟨52782352619688630445595669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35188235079792420297063779 52782352619688630445595669)
    ·
      refine ⟨2474172779047904552137297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 52782352619688630445595669 2474172779047904552137297)
      ·
        refine ⟨1855629584285928414102973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2474172779047904552137297 1855629584285928414102973)
        ·
          refine ⟨695861094107223155288615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1855629584285928414102973 695861094107223155288615)
          ·
            refine ⟨1043791641160834732932923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 695861094107223155288615 1043791641160834732932923)
            ·
              refine ⟨1565687461741252099399385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1043791641160834732932923 1565687461741252099399385)
              ·
                refine ⟨1174265596305939074549539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1565687461741252099399385 1174265596305939074549539)
                ·
                  refine ⟨1761398394458908611824309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1174265596305939074549539 1761398394458908611824309)
                  ·
                    refine ⟨165131099480522682358529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1761398394458908611824309 165131099480522682358529)
                    ·
                      rfl

theorem cell23_964775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 1, 2, 1, 5].length) (baseStart_964775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_964775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_964775 prefixEnd_964775 := by exact prefixLift 964775
  have htrace : WordTrace (prefixWord ++ tailWord_964775) baseStart_964775 baseEnd_964775 := by
    simpa [prefixWord, tailWord_964775, baseEnd_964775] using wordTrace_append hprefix tailTrace_964775
  have hstable : (prefixWord ++ tailWord_964775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964775).length < 2 ^ (prefixWord ++ tailWord_964775).sum := by decide
  have hdescent : baseEnd_964775 < baseStart_964775 := by decide
  rcases family_descends (prefixWord ++ tailWord_964775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964778 : List Nat := [3, 1, 5, 1, 2, 1, 1, 1, 3, 1, 4]
def baseStart_964778 : Nat := 118140960795 + 964778 * 2 ^ 59
def prefixEnd_964778 : Nat := 4983230072969 + 3 ^ 40 * 964778 * 2
def baseEnd_964778 : Nat := 495394838883531535338073

theorem tailTrace_964778 : CollatzResearch.WordTrace tailWord_964778 prefixEnd_964778 495394838883531535338073 := by
  unfold tailWord_964778
  simp only [CollatzResearch.WordTrace]
  refine ⟨8797086124695387952355747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23458896332521034539615325 8797086124695387952355747)
  ·
    refine ⟨13195629187043081928533621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8797086124695387952355747 13195629187043081928533621)
    ·
      refine ⟨1237090236285288930800027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13195629187043081928533621 1237090236285288930800027)
      ·
        refine ⟨1855635354427933396200041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1237090236285288930800027 1855635354427933396200041)
        ·
          refine ⟨1391726515820950047150031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1855635354427933396200041 1391726515820950047150031)
          ·
            refine ⟨2087589773731425070725047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1391726515820950047150031 2087589773731425070725047)
            ·
              refine ⟨3131384660597137606087571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2087589773731425070725047 3131384660597137606087571)
              ·
                refine ⟨4697076990895706409131357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3131384660597137606087571 4697076990895706409131357)
                ·
                  refine ⟨1761403871585889903424259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4697076990895706409131357 1761403871585889903424259)
                  ·
                    refine ⟨2642105807378834855136389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1761403871585889903424259 2642105807378834855136389)
                    ·
                      refine ⟨495394838883531535338073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2642105807378834855136389 495394838883531535338073)
                      ·
                        rfl

theorem cell23_964778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_964778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_964778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_964778 prefixEnd_964778 := by exact prefixLift 964778
  have htrace : WordTrace (prefixWord ++ tailWord_964778) baseStart_964778 baseEnd_964778 := by
    simpa [prefixWord, tailWord_964778, baseEnd_964778] using wordTrace_append hprefix tailTrace_964778
  have hstable : (prefixWord ++ tailWord_964778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964778).length < 2 ^ (prefixWord ++ tailWord_964778).sum := by decide
  have hdescent : baseEnd_964778 < baseStart_964778 := by decide
  rcases family_descends (prefixWord ++ tailWord_964778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964782 : List Nat := [4, 1, 4, 2, 1, 1, 2, 1, 2, 3, 2]
def baseStart_964782 : Nat := 118140960795 + 964782 * 2 ^ 59
def prefixEnd_964782 : Nat := 4983230072969 + 3 ^ 40 * 964782 * 2
def baseEnd_964782 : Nat := 495396892806149519688055

theorem tailTrace_964782 : CollatzResearch.WordTrace tailWord_964782 prefixEnd_964782 495396892806149519688055 := by
  unfold tailWord_964782
  simp only [CollatzResearch.WordTrace]
  refine ⟨4398561298845882561571075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23458993593844706995045733 4398561298845882561571075)
  ·
    refine ⟨6597841948268823842356613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4398561298845882561571075 6597841948268823842356613)
    ·
      refine ⟨1237095365300404470441865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6597841948268823842356613 1237095365300404470441865)
      ·
        refine ⟨927821523975303352831399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1237095365300404470441865 927821523975303352831399)
        ·
          refine ⟨1391732285962955029247099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 927821523975303352831399 1391732285962955029247099)
          ·
            refine ⟨2087598428944432543870649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1391732285962955029247099 2087598428944432543870649)
            ·
              refine ⟨1565698821708324407902987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2087598428944432543870649 1565698821708324407902987)
              ·
                refine ⟨2348548232562486611854481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1565698821708324407902987 2348548232562486611854481)
                ·
                  refine ⟨1761411174421864958890861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2348548232562486611854481 1761411174421864958890861)
                  ·
                    refine ⟨660529190408199359584073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1761411174421864958890861 660529190408199359584073)
                    ·
                      refine ⟨495396892806149519688055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 660529190408199359584073 495396892806149519688055)
                      ·
                        rfl

theorem cell23_964782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_964782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_964782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_964782 prefixEnd_964782 := by exact prefixLift 964782
  have htrace : WordTrace (prefixWord ++ tailWord_964782) baseStart_964782 baseEnd_964782 := by
    simpa [prefixWord, tailWord_964782, baseEnd_964782] using wordTrace_append hprefix tailTrace_964782
  have hstable : (prefixWord ++ tailWord_964782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964782).length < 2 ^ (prefixWord ++ tailWord_964782).sum := by decide
  have hdescent : baseEnd_964782 < baseStart_964782 := by decide
  rcases family_descends (prefixWord ++ tailWord_964782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964794 : List Nat := [3, 1, 1, 1, 2, 2, 3, 1, 3, 3, 3]
def baseStart_964794 : Nat := 118140960795 + 964794 * 2 ^ 59
def prefixEnd_964794 : Nat := 4983230072969 + 3 ^ 40 * 964794 * 2
def baseEnd_964794 : Nat := 495403054574003472737999

theorem tailTrace_964794 : CollatzResearch.WordTrace tailWord_964794 prefixEnd_964794 495403054574003472737999 := by
  unfold tailWord_964794
  simp only [CollatzResearch.WordTrace]
  refine ⟨8797232016680896635501359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23459285377815724361336957 8797232016680896635501359)
  ·
    refine ⟨13195848025021344953252039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8797232016680896635501359 13195848025021344953252039)
    ·
      refine ⟨19793772037532017429878059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13195848025021344953252039 19793772037532017429878059)
      ·
        refine ⟨29690658056298026144817089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19793772037532017429878059 29690658056298026144817089)
        ·
          refine ⟨22267993542223519608612817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29690658056298026144817089 22267993542223519608612817)
          ·
            refine ⟨16700995156667639706459613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22267993542223519608612817 16700995156667639706459613)
            ·
              refine ⟨6262873183750364889922355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16700995156667639706459613 6262873183750364889922355)
              ·
                refine ⟨9394309775625547334883533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6262873183750364889922355 9394309775625547334883533)
                ·
                  refine ⟨3522866165859580250581325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9394309775625547334883533 3522866165859580250581325)
                  ·
                    refine ⟨1321074812197342593967997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3522866165859580250581325 1321074812197342593967997)
                    ·
                      refine ⟨495403054574003472737999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1321074812197342593967997 495403054574003472737999)
                      ·
                        rfl

theorem cell23_964794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 1, 3, 3, 3].length) (baseStart_964794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_964794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_964794 prefixEnd_964794 := by exact prefixLift 964794
  have htrace : WordTrace (prefixWord ++ tailWord_964794) baseStart_964794 baseEnd_964794 := by
    simpa [prefixWord, tailWord_964794, baseEnd_964794] using wordTrace_append hprefix tailTrace_964794
  have hstable : (prefixWord ++ tailWord_964794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964794).length < 2 ^ (prefixWord ++ tailWord_964794).sum := by decide
  have hdescent : baseEnd_964794 < baseStart_964794 := by decide
  rcases family_descends (prefixWord ++ tailWord_964794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964798 : List Nat := [4, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5]
def baseStart_964798 : Nat := 118140960795 + 964798 * 2 ^ 59
def prefixEnd_964798 : Nat := 4983230072969 + 3 ^ 40 * 964798 * 2
def baseEnd_964798 : Nat := 495405108496621457087981

theorem tailTrace_964798 : CollatzResearch.WordTrace tailWord_964798 prefixEnd_964798 495405108496621457087981 := by
  unfold tailWord_964798
  simp only [CollatzResearch.WordTrace]
  refine ⟨4398634244838636903143881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23459382639139396816767365 4398634244838636903143881)
  ·
    refine ⟨3298975683628977677357911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4398634244838636903143881 3298975683628977677357911)
    ·
      refine ⟨4948463525443466516036867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3298975683628977677357911 4948463525443466516036867)
      ·
        refine ⟨7422695288165199774055301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4948463525443466516036867 7422695288165199774055301)
        ·
          refine ⟨1391755366530974957635369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7422695288165199774055301 1391755366530974957635369)
          ·
            refine ⟨1043816524898231218226527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1391755366530974957635369 1043816524898231218226527)
            ·
              refine ⟨1565724787347346827339791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1043816524898231218226527 1565724787347346827339791)
              ·
                refine ⟨2348587181021020241009687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1565724787347346827339791 2348587181021020241009687)
                ·
                  refine ⟨3522880771531530361514531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2348587181021020241009687 3522880771531530361514531)
                  ·
                    refine ⟨5284321157297295542271797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3522880771531530361514531 5284321157297295542271797)
                    ·
                      refine ⟨495405108496621457087981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5284321157297295542271797 495405108496621457087981)
                      ·
                        rfl

theorem cell23_964798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5].length) (baseStart_964798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_964798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_964798 prefixEnd_964798 := by exact prefixLift 964798
  have htrace : WordTrace (prefixWord ++ tailWord_964798) baseStart_964798 baseEnd_964798 := by
    simpa [prefixWord, tailWord_964798, baseEnd_964798] using wordTrace_append hprefix tailTrace_964798
  have hstable : (prefixWord ++ tailWord_964798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964798).length < 2 ^ (prefixWord ++ tailWord_964798).sum := by decide
  have hdescent : baseEnd_964798 < baseStart_964798 := by decide
  rcases family_descends (prefixWord ++ tailWord_964798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964801 : List Nat := [1, 2, 6, 1, 3, 10]
def baseStart_964801 : Nat := 118140960795 + 964801 * 2 ^ 59
def prefixEnd_964801 : Nat := 4983230072969 + 3 ^ 40 * 964801 * 2
def baseEnd_964801 : Nat := 2038710489459197305969

theorem tailTrace_964801 : CollatzResearch.WordTrace tailWord_964801 prefixEnd_964801 2038710489459197305969 := by
  unfold tailWord_964801
  simp only [CollatzResearch.WordTrace]
  refine ⟨35189183377698226737510257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23459455585132151158340171 35189183377698226737510257)
  ·
    refine ⟨26391887533273670053132693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35189183377698226737510257 26391887533273670053132693)
    ·
      refine ⟨1237119728122203283740595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 26391887533273670053132693 1237119728122203283740595)
      ·
        refine ⟨1855679592183304925610893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1237119728122203283740595 1855679592183304925610893)
        ·
          refine ⟨695879847068739347104085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1855679592183304925610893 695879847068739347104085)
          ·
            refine ⟨2038710489459197305969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 695879847068739347104085 2038710489459197305969)
            ·
              rfl

theorem cell23_964801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 10].length) (baseStart_964801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_964801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_964801 prefixEnd_964801 := by exact prefixLift 964801
  have htrace : WordTrace (prefixWord ++ tailWord_964801) baseStart_964801 baseEnd_964801 := by
    simpa [prefixWord, tailWord_964801, baseEnd_964801] using wordTrace_append hprefix tailTrace_964801
  have hstable : (prefixWord ++ tailWord_964801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964801).length < 2 ^ (prefixWord ++ tailWord_964801).sum := by decide
  have hdescent : baseEnd_964801 < baseStart_964801 := by decide
  rcases family_descends (prefixWord ++ tailWord_964801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964807 : List Nat := [1, 1, 4, 1, 1, 1, 1, 1, 2, 3, 7]
def baseStart_964807 : Nat := 118140960795 + 964807 * 2 ^ 59
def prefixEnd_964807 : Nat := 4983230072969 + 3 ^ 40 * 964807 * 2
def baseEnd_964807 : Nat := 495409729822511921875439

theorem tailTrace_964807 : CollatzResearch.WordTrace tailWord_964807 prefixEnd_964807 495409729822511921875439 := by
  unfold tailWord_964807
  simp only [CollatzResearch.WordTrace]
  refine ⟨35189402215676489762228675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23459601477117659841485783 35189402215676489762228675)
  ·
    refine ⟨52784103323514734643343013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35189402215676489762228675 52784103323514734643343013)
    ·
      refine ⟨9897019373159012745626815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52784103323514734643343013 9897019373159012745626815)
      ·
        refine ⟨14845529059738519118440223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9897019373159012745626815 14845529059738519118440223)
        ·
          refine ⟨22268293589607778677660335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14845529059738519118440223 22268293589607778677660335)
          ·
            refine ⟨33402440384411668016490503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22268293589607778677660335 33402440384411668016490503)
            ·
              refine ⟨50103660576617502024735755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33402440384411668016490503 50103660576617502024735755)
              ·
                refine ⟨75155490864926253037103633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50103660576617502024735755 75155490864926253037103633)
                ·
                  refine ⟨56366618148694689777827725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75155490864926253037103633 56366618148694689777827725)
                  ·
                    refine ⟨21137481805760508666685397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56366618148694689777827725 21137481805760508666685397)
                    ·
                      refine ⟨495409729822511921875439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 21137481805760508666685397 495409729822511921875439)
                      ·
                        rfl

theorem cell23_964807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 3, 7].length) (baseStart_964807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_964807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_964807 prefixEnd_964807 := by exact prefixLift 964807
  have htrace : WordTrace (prefixWord ++ tailWord_964807) baseStart_964807 baseEnd_964807 := by
    simpa [prefixWord, tailWord_964807, baseEnd_964807] using wordTrace_append hprefix tailTrace_964807
  have hstable : (prefixWord ++ tailWord_964807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964807).length < 2 ^ (prefixWord ++ tailWord_964807).sum := by decide
  have hdescent : baseEnd_964807 < baseStart_964807 := by decide
  rcases family_descends (prefixWord ++ tailWord_964807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964814 : List Nat := [4, 1, 1, 1, 4, 1, 1, 1, 2, 7]
def baseStart_964814 : Nat := 118140960795 + 964814 * 2 ^ 59
def prefixEnd_964814 : Nat := 4983230072969 + 3 ^ 40 * 964814 * 2
def baseEnd_964814 : Nat := 165137774729031131495969

theorem tailTrace_964814 : CollatzResearch.WordTrace tailWord_964814 prefixEnd_964814 165137774729031131495969 := by
  unfold tailWord_964814
  simp only [CollatzResearch.WordTrace]
  refine ⟨4398707190831391244716687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23459771684434086638488997 4398707190831391244716687)
  ·
    refine ⟨6598060786247086867075031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4398707190831391244716687 6598060786247086867075031)
    ·
      refine ⟨9897091179370630300612547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6598060786247086867075031 9897091179370630300612547)
      ·
        refine ⟨14845636769055945450918821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9897091179370630300612547 14845636769055945450918821)
        ·
          refine ⟨2783556894197989772047279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14845636769055945450918821 2783556894197989772047279)
          ·
            refine ⟨4175335341296984658070919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2783556894197989772047279 4175335341296984658070919)
            ·
              refine ⟨6263003011945476987106379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4175335341296984658070919 6263003011945476987106379)
              ·
                refine ⟨9394504517918215480659569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6263003011945476987106379 9394504517918215480659569)
                ·
                  refine ⟨7045878388438661610494677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9394504517918215480659569 7045878388438661610494677)
                  ·
                    refine ⟨165137774729031131495969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7045878388438661610494677 165137774729031131495969)
                    ·
                      rfl

theorem cell23_964814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 1, 2, 7].length) (baseStart_964814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_964814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_964814 prefixEnd_964814 := by exact prefixLift 964814
  have htrace : WordTrace (prefixWord ++ tailWord_964814) baseStart_964814 baseEnd_964814 := by
    simpa [prefixWord, tailWord_964814, baseEnd_964814] using wordTrace_append hprefix tailTrace_964814
  have hstable : (prefixWord ++ tailWord_964814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964814).length < 2 ^ (prefixWord ++ tailWord_964814).sum := by decide
  have hdescent : baseEnd_964814 < baseStart_964814 := by decide
  rcases family_descends (prefixWord ++ tailWord_964814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964827 : List Nat := [1, 1, 1, 1, 1, 1, 1, 7, 1, 8]
def baseStart_964827 : Nat := 118140960795 + 964827 * 2 ^ 59
def prefixEnd_964827 : Nat := 4983230072969 + 3 ^ 40 * 964827 * 2
def baseEnd_964827 : Nat := 165139999811867281208449

theorem tailTrace_964827 : CollatzResearch.WordTrace tailWord_964827 prefixEnd_964827 165139999811867281208449 := by
  unfold tailWord_964827
  simp only [CollatzResearch.WordTrace]
  refine ⟨35190131675604033177956735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23460087783736022118637823 35190131675604033177956735)
  ·
    refine ⟨52785197513406049766935103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35190131675604033177956735 52785197513406049766935103)
    ·
      refine ⟨79177796270109074650402655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52785197513406049766935103 79177796270109074650402655)
      ·
        refine ⟨118766694405163611975603983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79177796270109074650402655 118766694405163611975603983)
        ·
          refine ⟨178150041607745417963405975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118766694405163611975603983 178150041607745417963405975)
          ·
            refine ⟨267225062411618126945108963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178150041607745417963405975 267225062411618126945108963)
            ·
              refine ⟨400837593617427190417663445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 267225062411618126945108963 400837593617427190417663445)
              ·
                refine ⟨9394631100408449775413987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 400837593617427190417663445 9394631100408449775413987)
                ·
                  refine ⟨14091946650612674663120981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9394631100408449775413987 14091946650612674663120981)
                  ·
                    refine ⟨165139999811867281208449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 14091946650612674663120981 165139999811867281208449)
                    ·
                      rfl

theorem cell23_964827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 1, 8].length) (baseStart_964827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_964827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_964827 prefixEnd_964827 := by exact prefixLift 964827
  have htrace : WordTrace (prefixWord ++ tailWord_964827) baseStart_964827 baseEnd_964827 := by
    simpa [prefixWord, tailWord_964827, baseEnd_964827] using wordTrace_append hprefix tailTrace_964827
  have hstable : (prefixWord ++ tailWord_964827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964827).length < 2 ^ (prefixWord ++ tailWord_964827).sum := by decide
  have hdescent : baseEnd_964827 < baseStart_964827 := by decide
  rcases family_descends (prefixWord ++ tailWord_964827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964851 : List Nat := [1, 1, 1, 2, 2, 4, 1, 4, 1, 4, 2]
def baseStart_964851 : Nat := 118140960795 + 964851 * 2 ^ 59
def prefixEnd_964851 : Nat := 4983230072969 + 3 ^ 40 * 964851 * 2
def baseEnd_964851 : Nat := 495432322971309749725237

theorem tailTrace_964851 : CollatzResearch.WordTrace tailWord_964851 prefixEnd_964851 495432322971309749725237 := by
  unfold tailWord_964851
  simp only [CollatzResearch.WordTrace]
  refine ⟨35191007027517085276830407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23460671351678056851220271 35191007027517085276830407)
  ·
    refine ⟨52786510541275627915245611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35191007027517085276830407 52786510541275627915245611)
    ·
      refine ⟨79179765811913441872868417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52786510541275627915245611 79179765811913441872868417)
      ·
        refine ⟨59384824358935081404651313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79179765811913441872868417 59384824358935081404651313)
        ·
          refine ⟨44538618269201311053488485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59384824358935081404651313 44538618269201311053488485)
          ·
            refine ⟨8350990925475245822529091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44538618269201311053488485 8350990925475245822529091)
            ·
              refine ⟨12526486388212868733793637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8350990925475245822529091 12526486388212868733793637)
              ·
                refine ⟨2348716197789912887586307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12526486388212868733793637 2348716197789912887586307)
                ·
                  refine ⟨3523074296684869331379461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2348716197789912887586307 3523074296684869331379461)
                  ·
                    refine ⟨660576430628412999633649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3523074296684869331379461 660576430628412999633649)
                    ·
                      refine ⟨495432322971309749725237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 660576430628412999633649 495432322971309749725237)
                      ·
                        rfl

theorem cell23_964851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 4, 1, 4, 2].length) (baseStart_964851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_964851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_964851 prefixEnd_964851 := by exact prefixLift 964851
  have htrace : WordTrace (prefixWord ++ tailWord_964851) baseStart_964851 baseEnd_964851 := by
    simpa [prefixWord, tailWord_964851, baseEnd_964851] using wordTrace_append hprefix tailTrace_964851
  have hstable : (prefixWord ++ tailWord_964851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964851).length < 2 ^ (prefixWord ++ tailWord_964851).sum := by decide
  have hdescent : baseEnd_964851 < baseStart_964851 := by decide
  rcases family_descends (prefixWord ++ tailWord_964851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964864 : List Nat := [2, 1, 1, 2, 1, 1, 5, 2, 2, 2, 4]
def baseStart_964864 : Nat := 118140960795 + 964864 * 2 ^ 59
def prefixEnd_964864 : Nat := 4983230072969 + 3 ^ 40 * 964864 * 2
def baseEnd_964864 : Nat := 495438998219818198862677

theorem tailTrace_964864 : CollatzResearch.WordTrace tailWord_964864 prefixEnd_964864 495438998219818198862677 := by
  unfold tailWord_964864
  simp only [CollatzResearch.WordTrace]
  refine ⟨17595740588234994248526823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23460987450979992331369097 17595740588234994248526823)
  ·
    refine ⟨26393610882352491372790235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17595740588234994248526823 26393610882352491372790235)
    ·
      refine ⟨39590416323528737059185353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26393610882352491372790235 39590416323528737059185353)
      ·
        refine ⟨29692812242646552794389015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39590416323528737059185353 29692812242646552794389015)
        ·
          refine ⟨44539218363969829191583523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29692812242646552794389015 44539218363969829191583523)
          ·
            refine ⟨66808827545954743787375285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44539218363969829191583523 66808827545954743787375285)
            ·
              refine ⟨6263327582433257230066433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66808827545954743787375285 6263327582433257230066433)
              ·
                refine ⟨4697495686824942922549825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6263327582433257230066433 4697495686824942922549825)
                ·
                  refine ⟨3523121765118707191912369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4697495686824942922549825 3523121765118707191912369)
                  ·
                    refine ⟨2642341323839030393934277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3523121765118707191912369 2642341323839030393934277)
                    ·
                      refine ⟨495438998219818198862677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2642341323839030393934277 495438998219818198862677)
                      ·
                        rfl

theorem cell23_964864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2, 4].length) (baseStart_964864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_964864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_964864 prefixEnd_964864 := by exact prefixLift 964864
  have htrace : WordTrace (prefixWord ++ tailWord_964864) baseStart_964864 baseEnd_964864 := by
    simpa [prefixWord, tailWord_964864, baseEnd_964864] using wordTrace_append hprefix tailTrace_964864
  have hstable : (prefixWord ++ tailWord_964864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964864).length < 2 ^ (prefixWord ++ tailWord_964864).sum := by decide
  have hdescent : baseEnd_964864 < baseStart_964864 := by decide
  rcases family_descends (prefixWord ++ tailWord_964864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964874 : List Nat := [3, 1, 2, 2, 1, 1, 3, 3, 7]
def baseStart_964874 : Nat := 118140960795 + 964874 * 2 ^ 59
def prefixEnd_964874 : Nat := 4983230072969 + 3 ^ 40 * 964874 * 2
def baseEnd_964874 : Nat := 55049348114040351081959

theorem tailTrace_964874 : CollatzResearch.WordTrace tailWord_964874 prefixEnd_964874 55049348114040351081959 := by
  unfold tailWord_964874
  simp only [CollatzResearch.WordTrace]
  refine ⟨8797961476608440051229419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23461230604289173469945117 8797961476608440051229419)
  ·
    refine ⟨13196942214912660076844129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8797961476608440051229419 13196942214912660076844129)
    ·
      refine ⟨9897706661184495057633097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13196942214912660076844129 9897706661184495057633097)
      ·
        refine ⟨7423279995888371293224823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9897706661184495057633097 7423279995888371293224823)
        ·
          refine ⟨11134919993832556939837235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7423279995888371293224823 11134919993832556939837235)
          ·
            refine ⟨16702379990748835409755853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11134919993832556939837235 16702379990748835409755853)
            ·
              refine ⟨6263392496530813278658445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16702379990748835409755853 6263392496530813278658445)
              ·
                refine ⟨2348772186199054979496917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6263392496530813278658445 2348772186199054979496917)
                ·
                  refine ⟨55049348114040351081959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2348772186199054979496917 55049348114040351081959)
                  ·
                    rfl

theorem cell23_964874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 3, 7].length) (baseStart_964874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_964874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_964874 prefixEnd_964874 := by exact prefixLift 964874
  have htrace : WordTrace (prefixWord ++ tailWord_964874) baseStart_964874 baseEnd_964874 := by
    simpa [prefixWord, tailWord_964874, baseEnd_964874] using wordTrace_append hprefix tailTrace_964874
  have hstable : (prefixWord ++ tailWord_964874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964874).length < 2 ^ (prefixWord ++ tailWord_964874).sum := by decide
  have hdescent : baseEnd_964874 < baseStart_964874 := by decide
  rcases family_descends (prefixWord ++ tailWord_964874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964921 : List Nat := [1, 2, 1, 6, 1, 1, 1, 1, 4, 5]
def baseStart_964921 : Nat := 118140960795 + 964921 * 2 ^ 59
def prefixEnd_964921 : Nat := 4983230072969 + 3 ^ 40 * 964921 * 2
def baseEnd_964921 : Nat := 165156088872374825283305

theorem tailTrace_964921 : CollatzResearch.WordTrace tailWord_964921 prefixEnd_964921 165156088872374825283305 := by
  unfold tailWord_964921
  simp only [CollatzResearch.WordTrace]
  refine ⟨35193560137263487231878617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23462373424842324821252411 35193560137263487231878617)
  ·
    refine ⟨26395170102947615423908963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35193560137263487231878617 26395170102947615423908963)
    ·
      refine ⟨39592755154421423135863445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26395170102947615423908963 39592755154421423135863445)
      ·
        refine ⟨1855910397863504209493599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 39592755154421423135863445 1855910397863504209493599)
        ·
          refine ⟨2783865596795256314240399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1855910397863504209493599 2783865596795256314240399)
          ·
            refine ⟨4175798395192884471360599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2783865596795256314240399 4175798395192884471360599)
            ·
              refine ⟨6263697592789326707040899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4175798395192884471360599 6263697592789326707040899)
              ·
                refine ⟨9395546389183990060561349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6263697592789326707040899 9395546389183990060561349)
                ·
                  refine ⟨1761664947971998136355253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9395546389183990060561349 1761664947971998136355253)
                  ·
                    refine ⟨165156088872374825283305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1761664947971998136355253 165156088872374825283305)
                    ·
                      rfl

theorem cell23_964921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 1, 4, 5].length) (baseStart_964921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_964921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_964921 prefixEnd_964921 := by exact prefixLift 964921
  have htrace : WordTrace (prefixWord ++ tailWord_964921) baseStart_964921 baseEnd_964921 := by
    simpa [prefixWord, tailWord_964921, baseEnd_964921] using wordTrace_append hprefix tailTrace_964921
  have hstable : (prefixWord ++ tailWord_964921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964921).length < 2 ^ (prefixWord ++ tailWord_964921).sum := by decide
  have hdescent : baseEnd_964921 < baseStart_964921 := by decide
  rcases family_descends (prefixWord ++ tailWord_964921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964951 : List Nat := [1, 1, 3, 2, 3, 1, 2, 1, 5, 4]
def baseStart_964951 : Nat := 118140960795 + 964951 * 2 ^ 59
def prefixEnd_964951 : Nat := 4983230072969 + 3 ^ 40 * 964951 * 2
def baseEnd_964951 : Nat := 165161223678919786158259

theorem tailTrace_964951 : CollatzResearch.WordTrace tailWord_964951 prefixEnd_964951 165161223678919786158259 := by
  unfold tailWord_964951
  simp only [CollatzResearch.WordTrace]
  refine ⟨35194654327154802355470707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23463102884769868236980471 35194654327154802355470707)
  ·
    refine ⟨52791981490732203533206061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35194654327154802355470707 52791981490732203533206061)
    ·
      refine ⟨19796993059024576324952273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52791981490732203533206061 19796993059024576324952273)
      ·
        refine ⟨14847744794268432243714205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19796993059024576324952273 14847744794268432243714205)
        ·
          refine ⟨5567904297850662091392827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14847744794268432243714205 5567904297850662091392827)
          ·
            refine ⟨8351856446775993137089241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5567904297850662091392827 8351856446775993137089241)
            ·
              refine ⟨6263892335081994852816931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8351856446775993137089241 6263892335081994852816931)
              ·
                refine ⟨9395838502622992279225397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6263892335081994852816931 9395838502622992279225397)
                ·
                  refine ⟨880859859620905526177381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9395838502622992279225397 880859859620905526177381)
                  ·
                    refine ⟨165161223678919786158259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 880859859620905526177381 165161223678919786158259)
                    ·
                      rfl

theorem cell23_964951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 1, 5, 4].length) (baseStart_964951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_964951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_964951 prefixEnd_964951 := by exact prefixLift 964951
  have htrace : WordTrace (prefixWord ++ tailWord_964951) baseStart_964951 baseEnd_964951 := by
    simpa [prefixWord, tailWord_964951, baseEnd_964951] using wordTrace_append hprefix tailTrace_964951
  have hstable : (prefixWord ++ tailWord_964951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964951).length < 2 ^ (prefixWord ++ tailWord_964951).sum := by decide
  have hdescent : baseEnd_964951 < baseStart_964951 := by decide
  rcases family_descends (prefixWord ++ tailWord_964951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964954 : List Nat := [3, 1, 1, 2, 1, 2, 1, 2, 1, 3, 6]
def baseStart_964954 : Nat := 118140960795 + 964954 * 2 ^ 59
def prefixEnd_964954 : Nat := 4983230072969 + 3 ^ 40 * 964954 * 2
def baseEnd_964954 : Nat := 495485211478722846737263

theorem tailTrace_964954 : CollatzResearch.WordTrace tailWord_964954 prefixEnd_964954 495485211478722846737263 := by
  unfold tailWord_964954
  simp only [CollatzResearch.WordTrace]
  refine ⟨8798690936535983466957479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23463175830762622578553277 8798690936535983466957479)
  ·
    refine ⟨13198036404803975200436219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8798690936535983466957479 13198036404803975200436219)
    ·
      refine ⟨19797054607205962800654329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13198036404803975200436219 19797054607205962800654329)
      ·
        refine ⟨14847790955404472100490747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19797054607205962800654329 14847790955404472100490747)
        ·
          refine ⟨22271686433106708150736121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14847790955404472100490747 22271686433106708150736121)
          ·
            refine ⟨16703764824830031113052091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22271686433106708150736121 16703764824830031113052091)
            ·
              refine ⟨25055647237245046669578137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16703764824830031113052091 25055647237245046669578137)
              ·
                refine ⟨18791735427933785002183603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25055647237245046669578137 18791735427933785002183603)
                ·
                  refine ⟨28187603141900677503275405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18791735427933785002183603 28187603141900677503275405)
                  ·
                    refine ⟨10570351178212754063728277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28187603141900677503275405 10570351178212754063728277)
                    ·
                      refine ⟨495485211478722846737263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10570351178212754063728277 495485211478722846737263)
                      ·
                        rfl

theorem cell23_964954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 1, 3, 6].length) (baseStart_964954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_964954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_964954 prefixEnd_964954 := by exact prefixLift 964954
  have htrace : WordTrace (prefixWord ++ tailWord_964954) baseStart_964954 baseEnd_964954 := by
    simpa [prefixWord, tailWord_964954, baseEnd_964954] using wordTrace_append hprefix tailTrace_964954
  have hstable : (prefixWord ++ tailWord_964954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964954).length < 2 ^ (prefixWord ++ tailWord_964954).sum := by decide
  have hdescent : baseEnd_964954 < baseStart_964954 := by decide
  rcases family_descends (prefixWord ++ tailWord_964954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964978 : List Nat := [3, 2, 1, 2, 1, 3, 2, 2, 2, 2, 3]
def baseStart_964978 : Nat := 118140960795 + 964978 * 2 ^ 59
def prefixEnd_964978 : Nat := 4983230072969 + 3 ^ 40 * 964978 * 2
def baseEnd_964978 : Nat := 495497535014430752837153

theorem tailTrace_964978 : CollatzResearch.WordTrace tailWord_964978 prefixEnd_964978 495497535014430752837153 := by
  unfold tailWord_964978
  simp only [CollatzResearch.WordTrace]
  refine ⟨8798909774514246491675897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23463759398704657311135725 8798909774514246491675897)
  ·
    refine ⟨6599182330885684868756923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8798909774514246491675897 6599182330885684868756923)
    ·
      refine ⟨9898773496328527303135385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6599182330885684868756923 9898773496328527303135385)
      ·
        refine ⟨7424080122246395477351539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9898773496328527303135385 7424080122246395477351539)
        ·
          refine ⟨11136120183369593216027309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7424080122246395477351539 11136120183369593216027309)
          ·
            refine ⟨4176045068763597456010241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11136120183369593216027309 4176045068763597456010241)
            ·
              refine ⟨3132033801572698092007681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4176045068763597456010241 3132033801572698092007681)
              ·
                refine ⟨2349025351179523569005761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3132033801572698092007681 2349025351179523569005761)
                ·
                  refine ⟨1761769013384642676754321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2349025351179523569005761 1761769013384642676754321)
                  ·
                    refine ⟨1321326760038482007565741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1761769013384642676754321 1321326760038482007565741)
                    ·
                      refine ⟨495497535014430752837153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1321326760038482007565741 495497535014430752837153)
                      ·
                        rfl

theorem cell23_964978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 2, 2, 2, 3].length) (baseStart_964978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_964978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_964978 prefixEnd_964978 := by exact prefixLift 964978
  have htrace : WordTrace (prefixWord ++ tailWord_964978) baseStart_964978 baseEnd_964978 := by
    simpa [prefixWord, tailWord_964978, baseEnd_964978] using wordTrace_append hprefix tailTrace_964978
  have hstable : (prefixWord ++ tailWord_964978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964978).length < 2 ^ (prefixWord ++ tailWord_964978).sum := by decide
  have hdescent : baseEnd_964978 < baseStart_964978 := by decide
  rcases family_descends (prefixWord ++ tailWord_964978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965012 : List Nat := [2, 4, 2, 1, 3, 2, 1, 1, 2, 2, 3]
def baseStart_965012 : Nat := 118140960795 + 965012 * 2 ^ 59
def prefixEnd_965012 : Nat := 4983230072969 + 3 ^ 40 * 965012 * 2
def baseEnd_965012 : Nat := 495514993356683619811997

theorem tailTrace_965012 : CollatzResearch.WordTrace tailWord_965012 prefixEnd_965012 495514993356683619811997 := by
  unfold tailWord_965012
  simp only [CollatzResearch.WordTrace]
  refine ⟨17598439589966904886720645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23464586119955873182294193 17598439589966904886720645)
  ·
    refine ⟨3299707423118794666260121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17598439589966904886720645 3299707423118794666260121)
    ·
      refine ⟨2474780567339095999695091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3299707423118794666260121 2474780567339095999695091)
      ·
        refine ⟨3712170851008643999542637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2474780567339095999695091 3712170851008643999542637)
        ·
          refine ⟨1392064069128241499828489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3712170851008643999542637 1392064069128241499828489)
          ·
            refine ⟨1044048051846181124871367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1392064069128241499828489 1044048051846181124871367)
            ·
              refine ⟨1566072077769271687307051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1044048051846181124871367 1566072077769271687307051)
              ·
                refine ⟨2349108116653907530960577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1566072077769271687307051 2349108116653907530960577)
                ·
                  refine ⟨1761831087490430648220433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2349108116653907530960577 1761831087490430648220433)
                  ·
                    refine ⟨1321373315617822986165325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1761831087490430648220433 1321373315617822986165325)
                    ·
                      refine ⟨495514993356683619811997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1321373315617822986165325 495514993356683619811997)
                      ·
                        rfl

theorem cell23_965012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 1, 1, 2, 2, 3].length) (baseStart_965012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_965012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_965012 prefixEnd_965012 := by exact prefixLift 965012
  have htrace : WordTrace (prefixWord ++ tailWord_965012) baseStart_965012 baseEnd_965012 := by
    simpa [prefixWord, tailWord_965012, baseEnd_965012] using wordTrace_append hprefix tailTrace_965012
  have hstable : (prefixWord ++ tailWord_965012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965012).length < 2 ^ (prefixWord ++ tailWord_965012).sum := by decide
  have hdescent : baseEnd_965012 < baseStart_965012 := by decide
  rcases family_descends (prefixWord ++ tailWord_965012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965065 : List Nat := [1, 2, 1, 1, 2, 1, 6, 2, 3, 2, 2]
def baseStart_965065 : Nat := 118140960795 + 965065 * 2 ^ 59
def prefixEnd_965065 : Nat := 4983230072969 + 3 ^ 40 * 965065 * 2
def baseEnd_965065 : Nat := 495542207831371912449253

theorem tailTrace_965065 : CollatzResearch.WordTrace tailWord_965065 prefixEnd_965065 495542207831371912449253 := by
  unfold tailWord_965065
  simp only [CollatzResearch.WordTrace]
  refine ⟨35198812248741799825120649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23465874832494533216747099 35198812248741799825120649)
  ·
    refine ⟨26399109186556349868840487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35198812248741799825120649 26399109186556349868840487)
    ·
      refine ⟨39598663779834524803260731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26399109186556349868840487 39598663779834524803260731)
      ·
        refine ⟨59397995669751787204891097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39598663779834524803260731 59397995669751787204891097)
        ·
          refine ⟨44548496752313840403668323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59397995669751787204891097 44548496752313840403668323)
          ·
            refine ⟨66822745128470760605502485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44548496752313840403668323 66822745128470760605502485)
            ·
              refine ⟨3132316177897066903382929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 66822745128470760605502485 3132316177897066903382929)
              ·
                refine ⟨2349237133422800177537197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3132316177897066903382929 2349237133422800177537197)
                ·
                  refine ⟨880963925033550066576449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2349237133422800177537197 880963925033550066576449)
                  ·
                    refine ⟨660722943775162549932337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 880963925033550066576449 660722943775162549932337)
                    ·
                      refine ⟨495542207831371912449253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 660722943775162549932337 495542207831371912449253)
                      ·
                        rfl

theorem cell23_965065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 2, 3, 2, 2].length) (baseStart_965065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_965065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_965065 prefixEnd_965065 := by exact prefixLift 965065
  have htrace : WordTrace (prefixWord ++ tailWord_965065) baseStart_965065 baseEnd_965065 := by
    simpa [prefixWord, tailWord_965065, baseEnd_965065] using wordTrace_append hprefix tailTrace_965065
  have hstable : (prefixWord ++ tailWord_965065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965065).length < 2 ^ (prefixWord ++ tailWord_965065).sum := by decide
  have hdescent : baseEnd_965065 < baseStart_965065 := by decide
  rcases family_descends (prefixWord ++ tailWord_965065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965085 : List Nat := [1, 4, 3, 1, 1, 1, 1, 5, 1, 2, 3]
def baseStart_965085 : Nat := 118140960795 + 965085 * 2 ^ 59
def prefixEnd_965085 : Nat := 4983230072969 + 3 ^ 40 * 965085 * 2
def baseEnd_965085 : Nat := 495552477444461834199161

theorem tailTrace_965085 : CollatzResearch.WordTrace tailWord_965085 prefixEnd_965085 495552477444461834199161 := by
  unfold tailWord_965085
  simp only [CollatzResearch.WordTrace]
  refine ⟨35199541708669343240848709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23466361139112895493899139 35199541708669343240848709)
  ·
    refine ⟨6599914070375501857659133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35199541708669343240848709 6599914070375501857659133)
    ·
      refine ⟨2474967776390813196622175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6599914070375501857659133 2474967776390813196622175)
      ·
        refine ⟨3712451664586219794933263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2474967776390813196622175 3712451664586219794933263)
        ·
          refine ⟨5568677496879329692399895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3712451664586219794933263 5568677496879329692399895)
          ·
            refine ⟨8353016245318994538599843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5568677496879329692399895 8353016245318994538599843)
            ·
              refine ⟨12529524367978491807899765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8353016245318994538599843 12529524367978491807899765)
              ·
                refine ⟨1174642909497983606990603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12529524367978491807899765 1174642909497983606990603)
                ·
                  refine ⟨1761964364246975410485905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1174642909497983606990603 1761964364246975410485905)
                  ·
                    refine ⟨1321473273185231557864429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1761964364246975410485905 1321473273185231557864429)
                    ·
                      refine ⟨495552477444461834199161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1321473273185231557864429 495552477444461834199161)
                      ·
                        rfl

theorem cell23_965085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 5, 1, 2, 3].length) (baseStart_965085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_965085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_965085 prefixEnd_965085 := by exact prefixLift 965085
  have htrace : WordTrace (prefixWord ++ tailWord_965085) baseStart_965085 baseEnd_965085 := by
    simpa [prefixWord, tailWord_965085, baseEnd_965085] using wordTrace_append hprefix tailTrace_965085
  have hstable : (prefixWord ++ tailWord_965085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965085).length < 2 ^ (prefixWord ++ tailWord_965085).sum := by decide
  have hdescent : baseEnd_965085 < baseStart_965085 := by decide
  rcases family_descends (prefixWord ++ tailWord_965085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965099 : List Nat := [1, 1, 1, 1, 2, 3, 7, 2, 1, 2, 2]
def baseStart_965099 : Nat := 118140960795 + 965099 * 2 ^ 59
def prefixEnd_965099 : Nat := 4983230072969 + 3 ^ 40 * 965099 * 2
def baseEnd_965099 : Nat := 495559666173624779424097

theorem tailTrace_965099 : CollatzResearch.WordTrace tailWord_965099 prefixEnd_965099 495559666173624779424097 := by
  unfold tailWord_965099
  simp only [CollatzResearch.WordTrace]
  refine ⟨35200052330618623631858351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23466701553745749087905567 35200052330618623631858351)
  ·
    refine ⟨52800078495927935447787527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35200052330618623631858351 52800078495927935447787527)
    ·
      refine ⟨79200117743891903171681291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52800078495927935447787527 79200117743891903171681291)
      ·
        refine ⟨118800176615837854757521937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79200117743891903171681291 118800176615837854757521937)
        ·
          refine ⟨89100132461878391068141453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118800176615837854757521937 89100132461878391068141453)
          ·
            refine ⟨33412549673204396650553045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89100132461878391068141453 33412549673204396650553045)
            ·
              refine ⟨783106632965728046497337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 33412549673204396650553045 783106632965728046497337)
              ·
                refine ⟨587329974724296034873003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 783106632965728046497337 587329974724296034873003)
                ·
                  refine ⟨880994962086444052309505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 587329974724296034873003 880994962086444052309505)
                  ·
                    refine ⟨660746221564833039232129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 880994962086444052309505 660746221564833039232129)
                    ·
                      refine ⟨495559666173624779424097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 660746221564833039232129 495559666173624779424097)
                      ·
                        rfl

theorem cell23_965099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 7, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 7, 2, 1, 2, 2].length) (baseStart_965099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_965099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_965099 prefixEnd_965099 := by exact prefixLift 965099
  have htrace : WordTrace (prefixWord ++ tailWord_965099) baseStart_965099 baseEnd_965099 := by
    simpa [prefixWord, tailWord_965099, baseEnd_965099] using wordTrace_append hprefix tailTrace_965099
  have hstable : (prefixWord ++ tailWord_965099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965099).length < 2 ^ (prefixWord ++ tailWord_965099).sum := by decide
  have hdescent : baseEnd_965099 < baseStart_965099 := by decide
  rcases family_descends (prefixWord ++ tailWord_965099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965151 : List Nat := [1, 1, 2, 4, 1, 1, 1, 1, 2, 3, 6]
def baseStart_965151 : Nat := 118140960795 + 965151 * 2 ^ 59
def prefixEnd_965151 : Nat := 4983230072969 + 3 ^ 40 * 965151 * 2
def baseEnd_965151 : Nat := 495586367167658575973857

theorem tailTrace_965151 : CollatzResearch.WordTrace tailWord_965151 prefixEnd_965151 495586367167658575973857 := by
  unfold tailWord_965151
  simp only [CollatzResearch.WordTrace]
  refine ⟨35201948926430236512751307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23467965950953491008500871 35201948926430236512751307)
  ·
    refine ⟨52802923389645354769126961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35201948926430236512751307 52802923389645354769126961)
    ·
      refine ⟨39602192542234016076845221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52802923389645354769126961 39602192542234016076845221)
      ·
        refine ⟨7425411101668878014408479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39602192542234016076845221 7425411101668878014408479)
        ·
          refine ⟨11138116652503317021612719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7425411101668878014408479 11138116652503317021612719)
          ·
            refine ⟨16707174978754975532419079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11138116652503317021612719 16707174978754975532419079)
            ·
              refine ⟨25060762468132463298628619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16707174978754975532419079 25060762468132463298628619)
              ·
                refine ⟨37591143702198694947942929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25060762468132463298628619 37591143702198694947942929)
                ·
                  refine ⟨28193357776649021210957197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37591143702198694947942929 28193357776649021210957197)
                  ·
                    refine ⟨10572509166243382954108949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28193357776649021210957197 10572509166243382954108949)
                    ·
                      refine ⟨495586367167658575973857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10572509166243382954108949 495586367167658575973857)
                      ·
                        rfl

theorem cell23_965151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_965151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_965151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_965151 prefixEnd_965151 := by exact prefixLift 965151
  have htrace : WordTrace (prefixWord ++ tailWord_965151) baseStart_965151 baseEnd_965151 := by
    simpa [prefixWord, tailWord_965151, baseEnd_965151] using wordTrace_append hprefix tailTrace_965151
  have hstable : (prefixWord ++ tailWord_965151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965151).length < 2 ^ (prefixWord ++ tailWord_965151).sum := by decide
  have hdescent : baseEnd_965151 < baseStart_965151 := by decide
  rcases family_descends (prefixWord ++ tailWord_965151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965178 : List Nat := [3, 1, 1, 1, 3, 4, 1, 2, 7]
def baseStart_965178 : Nat := 118140960795 + 965178 * 2 ^ 59
def prefixEnd_965178 : Nat := 4983230072969 + 3 ^ 40 * 965178 * 2
def baseEnd_965178 : Nat := 55066692349481107815137

theorem tailTrace_965178 : CollatzResearch.WordTrace tailWord_965178 prefixEnd_965178 55066692349481107815137 := by
  unfold tailWord_965178
  simp only [CollatzResearch.WordTrace]
  refine ⟨8800733424333105030996047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23468622464888280082656125 8800733424333105030996047)
  ·
    refine ⟨13201100136499657546494071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8800733424333105030996047 13201100136499657546494071)
    ·
      refine ⟨19801650204749486319741107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13201100136499657546494071 19801650204749486319741107)
      ·
        refine ⟨29702475307124229479611661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19801650204749486319741107 29702475307124229479611661)
        ·
          refine ⟨11138428240171586054854373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29702475307124229479611661 11138428240171586054854373)
          ·
            refine ⟨2088455295032172385285195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11138428240171586054854373 2088455295032172385285195)
            ·
              refine ⟨3132682942548258577927793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2088455295032172385285195 3132682942548258577927793)
              ·
                refine ⟨2349512206911193933445845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3132682942548258577927793 2349512206911193933445845)
                ·
                  refine ⟨55066692349481107815137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2349512206911193933445845 55066692349481107815137)
                  ·
                    rfl

theorem cell23_965178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 2, 7].length) (baseStart_965178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_965178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_965178 prefixEnd_965178 := by exact prefixLift 965178
  have htrace : WordTrace (prefixWord ++ tailWord_965178) baseStart_965178 baseEnd_965178 := by
    simpa [prefixWord, tailWord_965178, baseEnd_965178] using wordTrace_append hprefix tailTrace_965178
  have hstable : (prefixWord ++ tailWord_965178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965178).length < 2 ^ (prefixWord ++ tailWord_965178).sum := by decide
  have hdescent : baseEnd_965178 < baseStart_965178 := by decide
  rcases family_descends (prefixWord ++ tailWord_965178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965208 : List Nat := [2, 1, 2, 2, 1, 2, 2, 4, 2, 5]
def baseStart_965208 : Nat := 118140960795 + 965208 * 2 ^ 59
def prefixEnd_965208 : Nat := 4983230072969 + 3 ^ 40 * 965208 * 2
def baseEnd_965208 : Nat := 165205211854988284320365

theorem tailTrace_965208 : CollatzResearch.WordTrace tailWord_965208 prefixEnd_965208 165205211854988284320365 := by
  unfold tailWord_965208
  simp only [CollatzResearch.WordTrace]
  refine ⟨17602013943611867623788139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23469351924815823498384185 17602013943611867623788139)
  ·
    refine ⟨26403020915417801435682209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17602013943611867623788139 26403020915417801435682209)
    ·
      refine ⟨19802265686563351076761657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26403020915417801435682209 19802265686563351076761657)
      ·
        refine ⟨14851699264922513307571243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19802265686563351076761657 14851699264922513307571243)
        ·
          refine ⟨22277548897383769961356865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14851699264922513307571243 22277548897383769961356865)
          ·
            refine ⟨16708161673037827471017649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22277548897383769961356865 16708161673037827471017649)
            ·
              refine ⟨12531121254778370603263237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16708161673037827471017649 12531121254778370603263237)
              ·
                refine ⟨2349585235270944488111857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12531121254778370603263237 2349585235270944488111857)
                ·
                  refine ⟨1762188926453208366083893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2349585235270944488111857 1762188926453208366083893)
                  ·
                    refine ⟨165205211854988284320365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1762188926453208366083893 165205211854988284320365)
                    ·
                      rfl

theorem cell23_965208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 4, 2, 5].length) (baseStart_965208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_965208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_965208 prefixEnd_965208 := by exact prefixLift 965208
  have htrace : WordTrace (prefixWord ++ tailWord_965208) baseStart_965208 baseEnd_965208 := by
    simpa [prefixWord, tailWord_965208, baseEnd_965208] using wordTrace_append hprefix tailTrace_965208
  have hstable : (prefixWord ++ tailWord_965208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965208).length < 2 ^ (prefixWord ++ tailWord_965208).sum := by decide
  have hdescent : baseEnd_965208 < baseStart_965208 := by decide
  rcases family_descends (prefixWord ++ tailWord_965208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965228 : List Nat := [2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 4]
def baseStart_965228 : Nat := 118140960795 + 965228 * 2 ^ 59
def prefixEnd_965228 : Nat := 4983230072969 + 3 ^ 40 * 965228 * 2
def baseEnd_965228 : Nat := 495625905178054774711003

theorem tailTrace_965228 : CollatzResearch.WordTrace tailWord_965228 prefixEnd_965228 495625905178054774711003 := by
  unfold tailWord_965228
  simp only [CollatzResearch.WordTrace]
  refine ⟨17602378673575639331652169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23469838231434185775536225 17602378673575639331652169)
  ·
    refine ⟨13201784005181729498739127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17602378673575639331652169 13201784005181729498739127)
    ·
      refine ⟨19802676007772594248108691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13201784005181729498739127 19802676007772594248108691)
      ·
        refine ⟨29704014011658891372163037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19802676007772594248108691 29704014011658891372163037)
        ·
          refine ⟨11139005254372084264561139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29704014011658891372163037 11139005254372084264561139)
          ·
            refine ⟨16708507881558126396841709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11139005254372084264561139 16708507881558126396841709)
            ·
              refine ⟨6265690455584297398815641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16708507881558126396841709 6265690455584297398815641)
              ·
                refine ⟨4699267841688223049111731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6265690455584297398815641 4699267841688223049111731)
                ·
                  refine ⟨7048901762532334573667597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4699267841688223049111731 7048901762532334573667597)
                  ·
                    refine ⟨2643338160949625465125349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7048901762532334573667597 2643338160949625465125349)
                    ·
                      refine ⟨495625905178054774711003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2643338160949625465125349 495625905178054774711003)
                      ·
                        rfl

theorem cell23_965228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 4].length) (baseStart_965228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_965228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_965228 prefixEnd_965228 := by exact prefixLift 965228
  have htrace : WordTrace (prefixWord ++ tailWord_965228) baseStart_965228 baseEnd_965228 := by
    simpa [prefixWord, tailWord_965228, baseEnd_965228] using wordTrace_append hprefix tailTrace_965228
  have hstable : (prefixWord ++ tailWord_965228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965228).length < 2 ^ (prefixWord ++ tailWord_965228).sum := by decide
  have hdescent : baseEnd_965228 < baseStart_965228 := by decide
  rcases family_descends (prefixWord ++ tailWord_965228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965329 : List Nat := [1, 2, 2, 1, 2, 3, 3, 4, 1, 1, 3]
def baseStart_965329 : Nat := 118140960795 + 965329 * 2 ^ 59
def prefixEnd_965329 : Nat := 4983230072969 + 3 ^ 40 * 965329 * 2
def baseEnd_965329 : Nat := 495677766724158879548039

theorem tailTrace_965329 : CollatzResearch.WordTrace tailWord_965329 prefixEnd_965329 495677766724158879548039 := by
  unfold tailWord_965329
  simp only [CollatzResearch.WordTrace]
  refine ⟨35208441119785372912731041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23472294079856915275154027 35208441119785372912731041)
  ·
    refine ⟨26406330839839029684548281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35208441119785372912731041 26406330839839029684548281)
    ·
      refine ⟨19804748129879272263411211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26406330839839029684548281 19804748129879272263411211)
      ·
        refine ⟨29707122194818908395116817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19804748129879272263411211 29707122194818908395116817)
        ·
          refine ⟨22280341646114181296337613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29707122194818908395116817 22280341646114181296337613)
          ·
            refine ⟨8355128117292817986126605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22280341646114181296337613 8355128117292817986126605)
            ·
              refine ⟨3133173043984806744797477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8355128117292817986126605 3133173043984806744797477)
              ·
                refine ⟨587469945747151264649527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3133173043984806744797477 587469945747151264649527)
                ·
                  refine ⟨881204918620726896974291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 587469945747151264649527 881204918620726896974291)
                  ·
                    refine ⟨1321807377931090345461437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 881204918620726896974291 1321807377931090345461437)
                    ·
                      refine ⟨495677766724158879548039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1321807377931090345461437 495677766724158879548039)
                      ·
                        rfl

theorem cell23_965329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 4, 1, 1, 3].length) (baseStart_965329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_965329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_965329 prefixEnd_965329 := by exact prefixLift 965329
  have htrace : WordTrace (prefixWord ++ tailWord_965329) baseStart_965329 baseEnd_965329 := by
    simpa [prefixWord, tailWord_965329, baseEnd_965329] using wordTrace_append hprefix tailTrace_965329
  have hstable : (prefixWord ++ tailWord_965329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965329).length < 2 ^ (prefixWord ++ tailWord_965329).sum := by decide
  have hdescent : baseEnd_965329 < baseStart_965329 := by decide
  rcases family_descends (prefixWord ++ tailWord_965329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965335 : List Nat := [1, 1, 3, 2, 1, 4, 1, 2, 3, 1, 4]
def baseStart_965335 : Nat := 118140960795 + 965335 * 2 ^ 59
def prefixEnd_965335 : Nat := 4983230072969 + 3 ^ 40 * 965335 * 2
def baseEnd_965335 : Nat := 495680847608085856073011

theorem tailTrace_965335 : CollatzResearch.WordTrace tailWord_965335 prefixEnd_965335 495680847608085856073011 := by
  unfold tailWord_965335
  simp only [CollatzResearch.WordTrace]
  refine ⟨35208659957763635937449459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23472439971842423958299639 35208659957763635937449459)
  ·
    refine ⟨52812989936645453906174189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35208659957763635937449459 52812989936645453906174189)
    ·
      refine ⟨19804871226242045214815321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52812989936645453906174189 19804871226242045214815321)
      ·
        refine ⟨14853653419681533911111491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19804871226242045214815321 14853653419681533911111491)
        ·
          refine ⟨22280480129522300866667237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14853653419681533911111491 22280480129522300866667237)
          ·
            refine ⟨4177590024285431412500107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22280480129522300866667237 4177590024285431412500107)
            ·
              refine ⟨6266385036428147118750161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4177590024285431412500107 6266385036428147118750161)
              ·
                refine ⟨4699788777321110339062621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6266385036428147118750161 4699788777321110339062621)
                ·
                  refine ⟨1762420791495416377148483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4699788777321110339062621 1762420791495416377148483)
                  ·
                    refine ⟨2643631187243124565722725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1762420791495416377148483 2643631187243124565722725)
                    ·
                      refine ⟨495680847608085856073011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2643631187243124565722725 495680847608085856073011)
                      ·
                        rfl

theorem cell23_965335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 2, 3, 1, 4].length) (baseStart_965335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_965335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_965335 prefixEnd_965335 := by exact prefixLift 965335
  have htrace : WordTrace (prefixWord ++ tailWord_965335) baseStart_965335 baseEnd_965335 := by
    simpa [prefixWord, tailWord_965335, baseEnd_965335] using wordTrace_append hprefix tailTrace_965335
  have hstable : (prefixWord ++ tailWord_965335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965335).length < 2 ^ (prefixWord ++ tailWord_965335).sum := by decide
  have hdescent : baseEnd_965335 < baseStart_965335 := by decide
  rcases family_descends (prefixWord ++ tailWord_965335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965345 : List Nat := [1, 2, 3, 1, 4, 1, 1, 3, 1, 6]
def baseStart_965345 : Nat := 118140960795 + 965345 * 2 ^ 59
def prefixEnd_965345 : Nat := 4983230072969 + 3 ^ 40 * 965345 * 2
def baseEnd_965345 : Nat := 165228660804876938982655

theorem tailTrace_965345 : CollatzResearch.WordTrace tailWord_965345 prefixEnd_965345 165228660804876938982655 := by
  unfold tailWord_965345
  simp only [CollatzResearch.WordTrace]
  refine ⟨35209024687727407645313489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23472683125151605096875659 35209024687727407645313489)
  ·
    refine ⟨26406768515795555733985117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35209024687727407645313489 26406768515795555733985117)
    ·
      refine ⟨9902538193423333400244419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26406768515795555733985117 9902538193423333400244419)
      ·
        refine ⟨14853807290135000100366629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9902538193423333400244419 14853807290135000100366629)
        ·
          refine ⟨2785088866900312518818743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14853807290135000100366629 2785088866900312518818743)
          ·
            refine ⟨4177633300350468778228115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2785088866900312518818743 4177633300350468778228115)
            ·
              refine ⟨6266449950525703167342173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4177633300350468778228115 6266449950525703167342173)
              ·
                refine ⟨2349918731447138687753315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6266449950525703167342173 2349918731447138687753315)
                ·
                  refine ⟨3524878097170708031629973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2349918731447138687753315 3524878097170708031629973)
                  ·
                    refine ⟨165228660804876938982655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3524878097170708031629973 165228660804876938982655)
                    ·
                      rfl

theorem cell23_965345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 3, 1, 6].length) (baseStart_965345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_965345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_965345 prefixEnd_965345 := by exact prefixLift 965345
  have htrace : WordTrace (prefixWord ++ tailWord_965345) baseStart_965345 baseEnd_965345 := by
    simpa [prefixWord, tailWord_965345, baseEnd_965345] using wordTrace_append hprefix tailTrace_965345
  have hstable : (prefixWord ++ tailWord_965345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965345).length < 2 ^ (prefixWord ++ tailWord_965345).sum := by decide
  have hdescent : baseEnd_965345 < baseStart_965345 := by decide
  rcases family_descends (prefixWord ++ tailWord_965345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965385 : List Nat := [1, 2, 1, 1, 3, 2, 2, 2, 3, 3, 3]
def baseStart_965385 : Nat := 118140960795 + 965385 * 2 ^ 59
def prefixEnd_965385 : Nat := 4983230072969 + 3 ^ 40 * 965385 * 2
def baseEnd_965385 : Nat := 495706521640810660447781

theorem tailTrace_965385 : CollatzResearch.WordTrace tailWord_965385 prefixEnd_965385 495706521640810660447781 := by
  unfold tailWord_965385
  simp only [CollatzResearch.WordTrace]
  refine ⟨35210483607582494476769609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23473655738388329651179739 35210483607582494476769609)
  ·
    refine ⟨26407862705686870857577207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35210483607582494476769609 26407862705686870857577207)
    ·
      refine ⟨39611794058530306286365811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26407862705686870857577207 39611794058530306286365811)
      ·
        refine ⟨59417691087795459429548717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39611794058530306286365811 59417691087795459429548717)
        ·
          refine ⟨22281634157923297286080769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59417691087795459429548717 22281634157923297286080769)
          ·
            refine ⟨16711225618442472964560577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22281634157923297286080769 16711225618442472964560577)
            ·
              refine ⟨12533419213831854723420433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16711225618442472964560577 12533419213831854723420433)
              ·
                refine ⟨9400064410373891042565325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12533419213831854723420433 9400064410373891042565325)
                ·
                  refine ⟨3525024153890209140961997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9400064410373891042565325 3525024153890209140961997)
                  ·
                    refine ⟨1321884057708828427860749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3525024153890209140961997 1321884057708828427860749)
                    ·
                      refine ⟨495706521640810660447781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1321884057708828427860749 495706521640810660447781)
                      ·
                        rfl

theorem cell23_965385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 2, 3, 3, 3].length) (baseStart_965385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_965385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_965385 prefixEnd_965385 := by exact prefixLift 965385
  have htrace : WordTrace (prefixWord ++ tailWord_965385) baseStart_965385 baseEnd_965385 := by
    simpa [prefixWord, tailWord_965385, baseEnd_965385] using wordTrace_append hprefix tailTrace_965385
  have hstable : (prefixWord ++ tailWord_965385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965385).length < 2 ^ (prefixWord ++ tailWord_965385).sum := by decide
  have hdescent : baseEnd_965385 < baseStart_965385 := by decide
  rcases family_descends (prefixWord ++ tailWord_965385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965386 : List Nat := [3, 1, 2, 2, 1, 2, 1, 6, 1, 2, 2]
def baseStart_965386 : Nat := 118140960795 + 965386 * 2 ^ 59
def prefixEnd_965386 : Nat := 4983230072969 + 3 ^ 40 * 965386 * 2
def baseEnd_965386 : Nat := 495707035121465156535277

theorem tailTrace_965386 : CollatzResearch.WordTrace tailWord_965386 prefixEnd_965386 495707035121465156535277 := by
  unfold tailWord_965386
  simp only [CollatzResearch.WordTrace]
  refine ⟨8802630020144717911889003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23473680053719247765037341 8802630020144717911889003)
  ·
    refine ⟨13203945030217076867833505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8802630020144717911889003 13203945030217076867833505)
    ·
      refine ⟨9902958772662807650875129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13203945030217076867833505 9902958772662807650875129)
      ·
        refine ⟨7427219079497105738156347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9902958772662807650875129 7427219079497105738156347)
        ·
          refine ⟨11140828619245658607234521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7427219079497105738156347 11140828619245658607234521)
          ·
            refine ⟨8355621464434243955425891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11140828619245658607234521 8355621464434243955425891)
            ·
              refine ⟨12533432196651365933138837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8355621464434243955425891 12533432196651365933138837)
              ·
                refine ⟨587504634218032778115883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12533432196651365933138837 587504634218032778115883)
                ·
                  refine ⟨881256951327049167173825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 587504634218032778115883 881256951327049167173825)
                  ·
                    refine ⟨660942713495286875380369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 881256951327049167173825 660942713495286875380369)
                    ·
                      refine ⟨495707035121465156535277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 660942713495286875380369 495707035121465156535277)
                      ·
                        rfl

theorem cell23_965386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 6, 1, 2, 2].length) (baseStart_965386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_965386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_965386 prefixEnd_965386 := by exact prefixLift 965386
  have htrace : WordTrace (prefixWord ++ tailWord_965386) baseStart_965386 baseEnd_965386 := by
    simpa [prefixWord, tailWord_965386, baseEnd_965386] using wordTrace_append hprefix tailTrace_965386
  have hstable : (prefixWord ++ tailWord_965386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965386).length < 2 ^ (prefixWord ++ tailWord_965386).sum := by decide
  have hdescent : baseEnd_965386 < baseStart_965386 := by decide
  rcases family_descends (prefixWord ++ tailWord_965386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965399 : List Nat := [1, 1, 3, 4, 3, 2, 1, 1, 1, 2, 4]
def baseStart_965399 : Nat := 118140960795 + 965399 * 2 ^ 59
def prefixEnd_965399 : Nat := 4983230072969 + 3 ^ 40 * 965399 * 2
def baseEnd_965399 : Nat := 495713710369973605672717

theorem tailTrace_965399 : CollatzResearch.WordTrace tailWord_965399 prefixEnd_965399 495713710369973605672717 := by
  unfold tailWord_965399
  simp only [CollatzResearch.WordTrace]
  refine ⟨35210994229531774867779251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23473996153021183245186167 35210994229531774867779251)
  ·
    refine ⟨52816491344297662301668877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35210994229531774867779251 52816491344297662301668877)
    ·
      refine ⟨19806184254111623363125829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52816491344297662301668877 19806184254111623363125829)
      ·
        refine ⟨3713659547645929380586093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19806184254111623363125829 3713659547645929380586093)
        ·
          refine ⟨1392622330367223517719785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3713659547645929380586093 1392622330367223517719785)
          ·
            refine ⟨1044466747775417638289839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1392622330367223517719785 1044466747775417638289839)
            ·
              refine ⟨1566700121663126457434759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1044466747775417638289839 1566700121663126457434759)
              ·
                refine ⟨2350050182494689686152139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1566700121663126457434759 2350050182494689686152139)
                ·
                  refine ⟨3525075273742034529228209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2350050182494689686152139 3525075273742034529228209)
                  ·
                    refine ⟨2643806455306525896921157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3525075273742034529228209 2643806455306525896921157)
                    ·
                      refine ⟨495713710369973605672717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2643806455306525896921157 495713710369973605672717)
                      ·
                        rfl

theorem cell23_965399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 1, 1, 1, 2, 4].length) (baseStart_965399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_965399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_965399 prefixEnd_965399 := by exact prefixLift 965399
  have htrace : WordTrace (prefixWord ++ tailWord_965399) baseStart_965399 baseEnd_965399 := by
    simpa [prefixWord, tailWord_965399, baseEnd_965399] using wordTrace_append hprefix tailTrace_965399
  have hstable : (prefixWord ++ tailWord_965399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965399).length < 2 ^ (prefixWord ++ tailWord_965399).sum := by decide
  have hdescent : baseEnd_965399 < baseStart_965399 := by decide
  rcases family_descends (prefixWord ++ tailWord_965399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965453 : List Nat := [1, 6, 1, 2, 2, 1, 1, 3, 2, 1, 3]
def baseStart_965453 : Nat := 118140960795 + 965453 * 2 ^ 59
def prefixEnd_965453 : Nat := 4983230072969 + 3 ^ 40 * 965453 * 2
def baseEnd_965453 : Nat := 495741438325316394397469

theorem tailTrace_965453 : CollatzResearch.WordTrace tailWord_965453 prefixEnd_965453 495741438325316394397469 := by
  unfold tailWord_965453
  simp only [CollatzResearch.WordTrace]
  refine ⟨35212963771336142090245013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23475309180890761393496675 35212963771336142090245013)
  ·
    refine ⟨1650607676781381660480235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 35212963771336142090245013 1650607676781381660480235)
    ·
      refine ⟨2475911515172072490720353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1650607676781381660480235 2475911515172072490720353)
      ·
        refine ⟨1856933636379054368040265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2475911515172072490720353 1856933636379054368040265)
        ·
          refine ⟨1392700227284290776030199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1856933636379054368040265 1392700227284290776030199)
          ·
            refine ⟨2089050340926436164045299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1392700227284290776030199 2089050340926436164045299)
            ·
              refine ⟨3133575511389654246067949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2089050340926436164045299 3133575511389654246067949)
              ·
                refine ⟨1175090816771120342275481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3133575511389654246067949 1175090816771120342275481)
                ·
                  refine ⟨881318112578340256706611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1175090816771120342275481 881318112578340256706611)
                  ·
                    refine ⟨1321977168867510385059917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 881318112578340256706611 1321977168867510385059917)
                    ·
                      refine ⟨495741438325316394397469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1321977168867510385059917 495741438325316394397469)
                      ·
                        rfl

theorem cell23_965453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_965453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_965453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_965453 prefixEnd_965453 := by exact prefixLift 965453
  have htrace : WordTrace (prefixWord ++ tailWord_965453) baseStart_965453 baseEnd_965453 := by
    simpa [prefixWord, tailWord_965453, baseEnd_965453] using wordTrace_append hprefix tailTrace_965453
  have hstable : (prefixWord ++ tailWord_965453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965453).length < 2 ^ (prefixWord ++ tailWord_965453).sum := by decide
  have hdescent : baseEnd_965453 < baseStart_965453 := by decide
  rcases family_descends (prefixWord ++ tailWord_965453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965493 : List Nat := [1, 3, 4, 1, 1, 3, 2, 2, 2, 2, 2]
def baseStart_965493 : Nat := 118140960795 + 965493 * 2 ^ 59
def prefixEnd_965493 : Nat := 4983230072969 + 3 ^ 40 * 965493 * 2
def baseEnd_965493 : Nat := 495761977551496237897285

theorem tailTrace_965493 : CollatzResearch.WordTrace tailWord_965493 prefixEnd_965493 495761977551496237897285 := by
  unfold tailWord_965493
  simp only [CollatzResearch.WordTrace]
  refine ⟨35214422691191228921701133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23476281794127485947800755 35214422691191228921701133)
  ·
    refine ⟨13205408509196710845637925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35214422691191228921701133 13205408509196710845637925)
    ·
      refine ⟨2476014095474383283557111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13205408509196710845637925 2476014095474383283557111)
      ·
        refine ⟨3714021143211574925335667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2476014095474383283557111 3714021143211574925335667)
        ·
          refine ⟨5571031714817362388003501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3714021143211574925335667 5571031714817362388003501)
          ·
            refine ⟨2089136893056510895501313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5571031714817362388003501 2089136893056510895501313)
            ·
              refine ⟨1566852669792383171625985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2089136893056510895501313 1566852669792383171625985)
              ·
                refine ⟨1175139502344287378719489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1566852669792383171625985 1175139502344287378719489)
                ·
                  refine ⟨881354626758215534039617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1175139502344287378719489 881354626758215534039617)
                  ·
                    refine ⟨661015970068661650529713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 881354626758215534039617 661015970068661650529713)
                    ·
                      refine ⟨495761977551496237897285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 661015970068661650529713 495761977551496237897285)
                      ·
                        rfl

theorem cell23_965493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2, 2, 2, 2, 2].length) (baseStart_965493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_965493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_965493 prefixEnd_965493 := by exact prefixLift 965493
  have htrace : WordTrace (prefixWord ++ tailWord_965493) baseStart_965493 baseEnd_965493 := by
    simpa [prefixWord, tailWord_965493, baseEnd_965493] using wordTrace_append hprefix tailTrace_965493
  have hstable : (prefixWord ++ tailWord_965493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965493).length < 2 ^ (prefixWord ++ tailWord_965493).sum := by decide
  have hdescent : baseEnd_965493 < baseStart_965493 := by decide
  rcases family_descends (prefixWord ++ tailWord_965493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965499 : List Nat := [1, 1, 1, 1, 1, 5, 6, 2, 5]
def baseStart_965499 : Nat := 118140960795 + 965499 * 2 ^ 59
def prefixEnd_965499 : Nat := 4983230072969 + 3 ^ 40 * 965499 * 2
def baseEnd_965499 : Nat := 55085006492824801602473

theorem tailTrace_965499 : CollatzResearch.WordTrace tailWord_965499 prefixEnd_965499 55085006492824801602473 := by
  unfold tailWord_965499
  simp only [CollatzResearch.WordTrace]
  refine ⟨35214641529169491946419551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23476427686112994630946367 35214641529169491946419551)
  ·
    refine ⟨52821962293754237919629327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35214641529169491946419551 52821962293754237919629327)
    ·
      refine ⟨79232943440631356879443991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52821962293754237919629327 79232943440631356879443991)
      ·
        refine ⟨118849415160947035319165987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79232943440631356879443991 118849415160947035319165987)
        ·
          refine ⟨178274122741420552978748981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118849415160947035319165987 178274122741420552978748981)
          ·
            refine ⟨16713199007008176841757717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 178274122741420552978748981 16713199007008176841757717)
            ·
              refine ⟨783431203453508289457393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 16713199007008176841757717 783431203453508289457393)
              ·
                refine ⟨587573402590131217093045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 783431203453508289457393 587573402590131217093045)
                ·
                  refine ⟨55085006492824801602473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 587573402590131217093045 55085006492824801602473)
                  ·
                    rfl

theorem cell23_965499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 6, 2, 5].length) (baseStart_965499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_965499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_965499 prefixEnd_965499 := by exact prefixLift 965499
  have htrace : WordTrace (prefixWord ++ tailWord_965499) baseStart_965499 baseEnd_965499 := by
    simpa [prefixWord, tailWord_965499, baseEnd_965499] using wordTrace_append hprefix tailTrace_965499
  have hstable : (prefixWord ++ tailWord_965499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965499).length < 2 ^ (prefixWord ++ tailWord_965499).sum := by decide
  have hdescent : baseEnd_965499 < baseStart_965499 := by decide
  rcases family_descends (prefixWord ++ tailWord_965499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965545 : List Nat := [1, 2, 1, 1, 1, 1, 5, 1, 1, 3, 6]
def baseStart_965545 : Nat := 118140960795 + 965545 * 2 ^ 59
def prefixEnd_965545 : Nat := 4983230072969 + 3 ^ 40 * 965545 * 2
def baseEnd_965545 : Nat := 495788678545530034447045

theorem tailTrace_965545 : CollatzResearch.WordTrace tailWord_965545 prefixEnd_965545 495788678545530034447045 := by
  unfold tailWord_965545
  simp only [CollatzResearch.WordTrace]
  refine ⟨35216319287002841802594089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23477546191335227868396059 35216319287002841802594089)
  ·
    refine ⟨26412239465252131351945567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35216319287002841802594089 26412239465252131351945567)
    ·
      refine ⟨39618359197878197027918351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26412239465252131351945567 39618359197878197027918351)
      ·
        refine ⟨59427538796817295541877527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39618359197878197027918351 59427538796817295541877527)
        ·
          refine ⟨89141308195225943312816291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59427538796817295541877527 89141308195225943312816291)
          ·
            refine ⟨133711962292838914969224437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89141308195225943312816291 133711962292838914969224437)
            ·
              refine ⟨12535496464953648278364791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 133711962292838914969224437 12535496464953648278364791)
              ·
                refine ⟨18803244697430472417547187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12535496464953648278364791 18803244697430472417547187)
                ·
                  refine ⟨28204867046145708626320781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18803244697430472417547187 28204867046145708626320781)
                  ·
                    refine ⟨10576825142304640734870293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28204867046145708626320781 10576825142304640734870293)
                    ·
                      refine ⟨495788678545530034447045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10576825142304640734870293 495788678545530034447045)
                      ·
                        rfl

theorem cell23_965545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 3, 6].length) (baseStart_965545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_965545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_965545 prefixEnd_965545 := by exact prefixLift 965545
  have htrace : WordTrace (prefixWord ++ tailWord_965545) baseStart_965545 baseEnd_965545 := by
    simpa [prefixWord, tailWord_965545, baseEnd_965545] using wordTrace_append hprefix tailTrace_965545
  have hstable : (prefixWord ++ tailWord_965545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965545).length < 2 ^ (prefixWord ++ tailWord_965545).sum := by decide
  have hdescent : baseEnd_965545 < baseStart_965545 := by decide
  rcases family_descends (prefixWord ++ tailWord_965545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965593 : List Nat := [1, 2, 1, 2, 5, 3, 1, 3, 1, 4]
def baseStart_965593 : Nat := 118140960795 + 965593 * 2 ^ 59
def prefixEnd_965593 : Nat := 4983230072969 + 3 ^ 40 * 965593 * 2
def baseEnd_965593 : Nat := 165271108538981948882275

theorem tailTrace_965593 : CollatzResearch.WordTrace tailWord_965593 prefixEnd_965593 165271108538981948882275 := by
  unfold tailWord_965593
  simp only [CollatzResearch.WordTrace]
  refine ⟨35218069990828946000341433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23478713327219297333560955 35218069990828946000341433)
  ·
    refine ⟨26413552493121709500256075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35218069990828946000341433 26413552493121709500256075)
    ·
      refine ⟨39620328739682564250384113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26413552493121709500256075 39620328739682564250384113)
      ·
        refine ⟨29715246554761923187788085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39620328739682564250384113 29715246554761923187788085)
        ·
          refine ⟨2785804364508930298855133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29715246554761923187788085 2785804364508930298855133)
          ·
            refine ⟨1044676636690848862070675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2785804364508930298855133 1044676636690848862070675)
            ·
              refine ⟨1567014955036273293106013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1044676636690848862070675 1567014955036273293106013)
              ·
                refine ⟨587630608138602484914755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1567014955036273293106013 587630608138602484914755)
                ·
                  refine ⟨881445912207903727372133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 587630608138602484914755 881445912207903727372133)
                  ·
                    refine ⟨165271108538981948882275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 881445912207903727372133 165271108538981948882275)
                    ·
                      rfl

theorem cell23_965593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 1, 3, 1, 4].length) (baseStart_965593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_965593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_965593 prefixEnd_965593 := by exact prefixLift 965593
  have htrace : WordTrace (prefixWord ++ tailWord_965593) baseStart_965593 baseEnd_965593 := by
    simpa [prefixWord, tailWord_965593, baseEnd_965593] using wordTrace_append hprefix tailTrace_965593
  have hstable : (prefixWord ++ tailWord_965593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965593).length < 2 ^ (prefixWord ++ tailWord_965593).sum := by decide
  have hdescent : baseEnd_965593 < baseStart_965593 := by decide
  rcases family_descends (prefixWord ++ tailWord_965593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965639 : List Nat := [1, 1, 4, 3, 1, 1, 3, 1, 3, 1, 4]
def baseStart_965639 : Nat := 118140960795 + 965639 * 2 ^ 59
def prefixEnd_965639 : Nat := 4983230072969 + 3 ^ 40 * 965639 * 2
def baseEnd_965639 : Nat := 495836945727052666671613

theorem tailTrace_965639 : CollatzResearch.WordTrace tailWord_965639 prefixEnd_965639 495836945727052666671613 := by
  unfold tailWord_965639
  simp only [CollatzResearch.WordTrace]
  refine ⟨35219747748662295856515971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23479831832441530571010647 35219747748662295856515971)
  ·
    refine ⟨52829621622993443784773957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35219747748662295856515971 52829621622993443784773957)
    ·
      refine ⟨9905554054311270709645117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52829621622993443784773957 9905554054311270709645117)
      ·
        refine ⟨3714582770366726516116919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9905554054311270709645117 3714582770366726516116919)
        ·
          refine ⟨5571874155550089774175379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3714582770366726516116919 5571874155550089774175379)
          ·
            refine ⟨8357811233325134661263069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5571874155550089774175379 8357811233325134661263069)
            ·
              refine ⟨3134179212496925497973651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8357811233325134661263069 3134179212496925497973651)
              ·
                refine ⟨4701268818745388246960477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3134179212496925497973651 4701268818745388246960477)
                ·
                  refine ⟨1762975807029520592610179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4701268818745388246960477 1762975807029520592610179)
                  ·
                    refine ⟨2644463710544280888915269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1762975807029520592610179 2644463710544280888915269)
                    ·
                      refine ⟨495836945727052666671613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2644463710544280888915269 495836945727052666671613)
                      ·
                        rfl

theorem cell23_965639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_965639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_965639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_965639 prefixEnd_965639 := by exact prefixLift 965639
  have htrace : WordTrace (prefixWord ++ tailWord_965639) baseStart_965639 baseEnd_965639 := by
    simpa [prefixWord, tailWord_965639, baseEnd_965639] using wordTrace_append hprefix tailTrace_965639
  have hstable : (prefixWord ++ tailWord_965639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965639).length < 2 ^ (prefixWord ++ tailWord_965639).sum := by decide
  have hdescent : baseEnd_965639 < baseStart_965639 := by decide
  rcases family_descends (prefixWord ++ tailWord_965639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965662 : List Nat := [4, 3, 16]
def baseStart_965662 : Nat := 118140960795 + 965662 * 2 ^ 59
def prefixEnd_965662 : Nat := 4983230072969 + 3 ^ 40 * 965662 * 2
def baseEnd_965662 : Nat := 75575179969837841287

theorem tailTrace_965662 : CollatzResearch.WordTrace tailWord_965662 prefixEnd_965662 75575179969837841287 := by
  unfold tailWord_965662
  simp only [CollatzResearch.WordTrace]
  refine ⟨4402573328447371348075405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23480391085052647189735493 4402573328447371348075405)
  ·
    refine ⟨1650964998167764255528277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4402573328447371348075405 1650964998167764255528277)
    ·
      refine ⟨75575179969837841287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 16 1650964998167764255528277 75575179969837841287)
      ·
        rfl

theorem cell23_965662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 16].length) (baseStart_965662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_965662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_965662 prefixEnd_965662 := by exact prefixLift 965662
  have htrace : WordTrace (prefixWord ++ tailWord_965662) baseStart_965662 baseEnd_965662 := by
    simpa [prefixWord, tailWord_965662, baseEnd_965662] using wordTrace_append hprefix tailTrace_965662
  have hstable : (prefixWord ++ tailWord_965662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965662).length < 2 ^ (prefixWord ++ tailWord_965662).sum := by decide
  have hdescent : baseEnd_965662 < baseStart_965662 := by decide
  rcases family_descends (prefixWord ++ tailWord_965662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965666 : List Nat := [3, 3, 1, 1, 1, 3, 1, 4, 2, 4]
def baseStart_965666 : Nat := 118140960795 + 965666 * 2 ^ 59
def prefixEnd_965666 : Nat := 4983230072969 + 3 ^ 40 * 965666 * 2
def baseEnd_965666 : Nat := 165283603234908020344663

theorem tailTrace_965666 : CollatzResearch.WordTrace tailWord_965666 prefixEnd_965666 165283603234908020344663 := by
  unfold tailWord_965666
  simp only [CollatzResearch.WordTrace]
  refine ⟨8805183129891119866937213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23480488346376319645165901 8805183129891119866937213)
  ·
    refine ⟨3301943673709169950101455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8805183129891119866937213 3301943673709169950101455)
    ·
      refine ⟨4952915510563754925152183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3301943673709169950101455 4952915510563754925152183)
      ·
        refine ⟨7429373265845632387728275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4952915510563754925152183 7429373265845632387728275)
        ·
          refine ⟨11144059898768448581592413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7429373265845632387728275 11144059898768448581592413)
          ·
            refine ⟨4179022462038168218097155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11144059898768448581592413 4179022462038168218097155)
            ·
              refine ⟨6268533693057252327145733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4179022462038168218097155 6268533693057252327145733)
              ·
                refine ⟨1175350067448234811339825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6268533693057252327145733 1175350067448234811339825)
                ·
                  refine ⟨881512550586176108504869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1175350067448234811339825 881512550586176108504869)
                  ·
                    refine ⟨165283603234908020344663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 881512550586176108504869 165283603234908020344663)
                    ·
                      rfl

theorem cell23_965666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 4, 2, 4].length) (baseStart_965666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_965666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_965666 prefixEnd_965666 := by exact prefixLift 965666
  have htrace : WordTrace (prefixWord ++ tailWord_965666) baseStart_965666 baseEnd_965666 := by
    simpa [prefixWord, tailWord_965666, baseEnd_965666] using wordTrace_append hprefix tailTrace_965666
  have hstable : (prefixWord ++ tailWord_965666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965666).length < 2 ^ (prefixWord ++ tailWord_965666).sum := by decide
  have hdescent : baseEnd_965666 < baseStart_965666 := by decide
  rcases family_descends (prefixWord ++ tailWord_965666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965686 : List Nat := [5, 1, 2, 1, 1, 2, 1, 3, 1, 2, 4]
def baseStart_965686 : Nat := 118140960795 + 965686 * 2 ^ 59
def prefixEnd_965686 : Nat := 4983230072969 + 3 ^ 40 * 965686 * 2
def baseEnd_965686 : Nat := 495861079317813982783897

theorem tailTrace_965686 : CollatzResearch.WordTrace tailWord_965686 prefixEnd_965686 495861079317813982783897 := by
  unfold tailWord_965686
  simp only [CollatzResearch.WordTrace]
  refine ⟨2201341373718251430217307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23480974652994681922317941 2201341373718251430217307)
  ·
    refine ⟨3302012060577377145325961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2201341373718251430217307 3302012060577377145325961)
    ·
      refine ⟨2476509045433032858994471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3302012060577377145325961 2476509045433032858994471)
      ·
        refine ⟨3714763568149549288491707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2476509045433032858994471 3714763568149549288491707)
        ·
          refine ⟨5572145352224323932737561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3714763568149549288491707 5572145352224323932737561)
          ·
            refine ⟨4179109014168242949553171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5572145352224323932737561 4179109014168242949553171)
            ·
              refine ⟨6268663521252364424329757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4179109014168242949553171 6268663521252364424329757)
              ·
                refine ⟨2350748820469636659123659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6268663521252364424329757 2350748820469636659123659)
                ·
                  refine ⟨3526123230704454988685489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2350748820469636659123659 3526123230704454988685489)
                  ·
                    refine ⟨2644592423028341241514117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3526123230704454988685489 2644592423028341241514117)
                    ·
                      refine ⟨495861079317813982783897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2644592423028341241514117 495861079317813982783897)
                      ·
                        rfl

theorem cell23_965686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_965686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_965686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_965686 prefixEnd_965686 := by exact prefixLift 965686
  have htrace : WordTrace (prefixWord ++ tailWord_965686) baseStart_965686 baseEnd_965686 := by
    simpa [prefixWord, tailWord_965686, baseEnd_965686] using wordTrace_append hprefix tailTrace_965686
  have hstable : (prefixWord ++ tailWord_965686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965686).length < 2 ^ (prefixWord ++ tailWord_965686).sum := by decide
  have hdescent : baseEnd_965686 < baseStart_965686 := by decide
  rcases family_descends (prefixWord ++ tailWord_965686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965750 : List Nat := [5, 1, 1, 2, 1, 1, 4, 2, 1, 3, 2]
def baseStart_965750 : Nat := 118140960795 + 965750 * 2 ^ 59
def prefixEnd_965750 : Nat := 4983230072969 + 3 ^ 40 * 965750 * 2
def baseEnd_965750 : Nat := 495893942079701732383603

theorem tailTrace_965750 : CollatzResearch.WordTrace tailWord_965750 prefixEnd_965750 495893942079701732383603 := by
  unfold tailWord_965750
  simp only [CollatzResearch.WordTrace]
  refine ⟨2201487265703760113362919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23482530834173441209204469 2201487265703760113362919)
  ·
    refine ⟨3302230898555640170044379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2201487265703760113362919 3302230898555640170044379)
    ·
      refine ⟨4953346347833460255066569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3302230898555640170044379 4953346347833460255066569)
      ·
        refine ⟨3715009760875095191299927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4953346347833460255066569 3715009760875095191299927)
        ·
          refine ⟨5572514641312642786949891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3715009760875095191299927 5572514641312642786949891)
          ·
            refine ⟨8358771961968964180424837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5572514641312642786949891 8358771961968964180424837)
            ·
              refine ⟨1567269742869180783829657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8358771961968964180424837 1567269742869180783829657)
              ·
                refine ⟨1175452307151885587872243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1567269742869180783829657 1175452307151885587872243)
                ·
                  refine ⟨1763178460727828381808365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1175452307151885587872243 1763178460727828381808365)
                  ·
                    refine ⟨661191922772935643178137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1763178460727828381808365 661191922772935643178137)
                    ·
                      refine ⟨495893942079701732383603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 661191922772935643178137 495893942079701732383603)
                      ·
                        rfl

theorem cell23_965750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4, 2, 1, 3, 2].length) (baseStart_965750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_965750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_965750 prefixEnd_965750 := by exact prefixLift 965750
  have htrace : WordTrace (prefixWord ++ tailWord_965750) baseStart_965750 baseEnd_965750 := by
    simpa [prefixWord, tailWord_965750, baseEnd_965750] using wordTrace_append hprefix tailTrace_965750
  have hstable : (prefixWord ++ tailWord_965750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965750).length < 2 ^ (prefixWord ++ tailWord_965750).sum := by decide
  have hdescent : baseEnd_965750 < baseStart_965750 := by decide
  rcases family_descends (prefixWord ++ tailWord_965750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965758 : List Nat := [4, 2, 4, 1, 1, 2, 1, 3, 1, 2, 2]
def baseStart_965758 : Nat := 118140960795 + 965758 * 2 ^ 59
def prefixEnd_965758 : Nat := 4983230072969 + 3 ^ 40 * 965758 * 2
def baseEnd_965758 : Nat := 495898049924937701083567

theorem tailTrace_965758 : CollatzResearch.WordTrace tailWord_965758 prefixEnd_965758 495898049924937701083567 := by
  unfold tailWord_965758
  simp only [CollatzResearch.WordTrace]
  refine ⟨4403011004403897397512241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23482725356820786120065285 4403011004403897397512241)
  ·
    refine ⟨3302258253302923048134181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4403011004403897397512241 3302258253302923048134181)
    ·
      refine ⟨619173422494298071525159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3302258253302923048134181 619173422494298071525159)
      ·
        refine ⟨928760133741447107287739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 619173422494298071525159 928760133741447107287739)
        ·
          refine ⟨1393140200612170660931609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 928760133741447107287739 1393140200612170660931609)
          ·
            refine ⟨1044855150459127995698707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1393140200612170660931609 1044855150459127995698707)
            ·
              refine ⟨1567282725688691993548061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1044855150459127995698707 1567282725688691993548061)
              ·
                refine ⟨587731022133259497580523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1567282725688691993548061 587731022133259497580523)
                ·
                  refine ⟨881596533199889246370785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 587731022133259497580523 881596533199889246370785)
                  ·
                    refine ⟨661197399899916934778089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 881596533199889246370785 661197399899916934778089)
                    ·
                      refine ⟨495898049924937701083567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 661197399899916934778089 495898049924937701083567)
                      ·
                        rfl

theorem cell23_965758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_965758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_965758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_965758 prefixEnd_965758 := by exact prefixLift 965758
  have htrace : WordTrace (prefixWord ++ tailWord_965758) baseStart_965758 baseEnd_965758 := by
    simpa [prefixWord, tailWord_965758, baseEnd_965758] using wordTrace_append hprefix tailTrace_965758
  have hstable : (prefixWord ++ tailWord_965758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965758).length < 2 ^ (prefixWord ++ tailWord_965758).sum := by decide
  have hdescent : baseEnd_965758 < baseStart_965758 := by decide
  rcases family_descends (prefixWord ++ tailWord_965758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965779 : List Nat := [1, 1, 1, 2, 1, 2, 4, 1, 4, 3, 3]
def baseStart_965779 : Nat := 118140960795 + 965779 * 2 ^ 59
def prefixEnd_965779 : Nat := 4983230072969 + 3 ^ 40 * 965779 * 2
def baseEnd_965779 : Nat := 495908833018682118920969

theorem tailTrace_965779 : CollatzResearch.WordTrace tailWord_965779 prefixEnd_965779 495908833018682118920969 := by
  unfold tailWord_965779
  simp only [CollatzResearch.WordTrace]
  refine ⟨35224853968155099766612391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23483235978770066511074927 35224853968155099766612391)
  ·
    refine ⟨52837280952232649649918587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35224853968155099766612391 52837280952232649649918587)
    ·
      refine ⟨79255921428348974474877881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52837280952232649649918587 79255921428348974474877881)
      ·
        refine ⟨59441941071261730856158411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79255921428348974474877881 59441941071261730856158411)
        ·
          refine ⟨89162911606892596284237617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59441941071261730856158411 89162911606892596284237617)
          ·
            refine ⟨66872183705169447213178213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89162911606892596284237617 66872183705169447213178213)
            ·
              refine ⟨12538534444719271352470915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66872183705169447213178213 12538534444719271352470915)
              ·
                refine ⟨18807801667078907028706373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12538534444719271352470915 18807801667078907028706373)
                ·
                  refine ⟨3526462812577295067882445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18807801667078907028706373 3526462812577295067882445)
                  ·
                    refine ⟨1322423554716485650455917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3526462812577295067882445 1322423554716485650455917)
                    ·
                      refine ⟨495908833018682118920969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1322423554716485650455917 495908833018682118920969)
                      ·
                        rfl

theorem cell23_965779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 4, 3, 3].length) (baseStart_965779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_965779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_965779 prefixEnd_965779 := by exact prefixLift 965779
  have htrace : WordTrace (prefixWord ++ tailWord_965779) baseStart_965779 baseEnd_965779 := by
    simpa [prefixWord, tailWord_965779, baseEnd_965779] using wordTrace_append hprefix tailTrace_965779
  have hstable : (prefixWord ++ tailWord_965779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965779).length < 2 ^ (prefixWord ++ tailWord_965779).sum := by decide
  have hdescent : baseEnd_965779 < baseStart_965779 := by decide
  rcases family_descends (prefixWord ++ tailWord_965779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965786 : List Nat := [3, 1, 1, 5, 1, 1, 3, 1, 7]
def baseStart_965786 : Nat := 118140960795 + 965786 * 2 ^ 59
def prefixEnd_965786 : Nat := 4983230072969 + 3 ^ 40 * 965786 * 2
def baseEnd_965786 : Nat := 55101380820362621281493

theorem tailTrace_965786 : CollatzResearch.WordTrace tailWord_965786 prefixEnd_965786 55101380820362621281493 := by
  unfold tailWord_965786
  simp only [CollatzResearch.WordTrace]
  refine ⟨8806277319782434990529303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23483406186086493308078141 8806277319782434990529303)
  ·
    refine ⟨13209415979673652485793955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8806277319782434990529303 13209415979673652485793955)
    ·
      refine ⟨19814123969510478728690933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13209415979673652485793955 19814123969510478728690933)
      ·
        refine ⟨1857574122141607380814775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19814123969510478728690933 1857574122141607380814775)
        ·
          refine ⟨2786361183212411071222163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1857574122141607380814775 2786361183212411071222163)
          ·
            refine ⟨4179541774818616606833245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2786361183212411071222163 4179541774818616606833245)
            ·
              refine ⟨1567328165556981227562467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4179541774818616606833245 1567328165556981227562467)
              ·
                refine ⟨2350992248335471841343701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1567328165556981227562467 2350992248335471841343701)
                ·
                  refine ⟨55101380820362621281493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2350992248335471841343701 55101380820362621281493)
                  ·
                    rfl

theorem cell23_965786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3, 1, 7].length) (baseStart_965786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_965786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_965786 prefixEnd_965786 := by exact prefixLift 965786
  have htrace : WordTrace (prefixWord ++ tailWord_965786) baseStart_965786 baseEnd_965786 := by
    simpa [prefixWord, tailWord_965786, baseEnd_965786] using wordTrace_append hprefix tailTrace_965786
  have hstable : (prefixWord ++ tailWord_965786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965786).length < 2 ^ (prefixWord ++ tailWord_965786).sum := by decide
  have hdescent : baseEnd_965786 < baseStart_965786 := by decide
  rcases family_descends (prefixWord ++ tailWord_965786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965797 : List Nat := [1, 3, 1, 2, 1, 6, 2, 1, 2, 2, 2]
def baseStart_965797 : Nat := 118140960795 + 965797 * 2 ^ 59
def prefixEnd_965797 : Nat := 4983230072969 + 3 ^ 40 * 965797 * 2
def baseEnd_965797 : Nat := 495918075670463048495887

theorem tailTrace_965797 : CollatzResearch.WordTrace tailWord_965797 prefixEnd_965797 495918075670463048495887 := by
  unfold tailWord_965797
  simp only [CollatzResearch.WordTrace]
  refine ⟨35225510482089888840767645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23483673654726592560511763 35225510482089888840767645)
  ·
    refine ⟨13209566430783708315287867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35225510482089888840767645 13209566430783708315287867)
    ·
      refine ⟨19814349646175562472931801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13209566430783708315287867 19814349646175562472931801)
      ·
        refine ⟨14860762234631671854698851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19814349646175562472931801 14860762234631671854698851)
        ·
          refine ⟨22291143351947507782048277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14860762234631671854698851 22291143351947507782048277)
          ·
            refine ⟨1044897344622539427283513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 22291143351947507782048277 1044897344622539427283513)
            ·
              refine ⟨783673008466904570462635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1044897344622539427283513 783673008466904570462635)
              ·
                refine ⟨1175509512700356855693953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 783673008466904570462635 1175509512700356855693953)
                ·
                  refine ⟨881632134525267641770465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1175509512700356855693953 881632134525267641770465)
                  ·
                    refine ⟨661224100893950731327849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 881632134525267641770465 661224100893950731327849)
                    ·
                      refine ⟨495918075670463048495887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 661224100893950731327849 495918075670463048495887)
                      ·
                        rfl

theorem cell23_965797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 2, 1, 2, 2, 2].length) (baseStart_965797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_965797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_965797 prefixEnd_965797 := by exact prefixLift 965797
  have htrace : WordTrace (prefixWord ++ tailWord_965797) baseStart_965797 baseEnd_965797 := by
    simpa [prefixWord, tailWord_965797, baseEnd_965797] using wordTrace_append hprefix tailTrace_965797
  have hstable : (prefixWord ++ tailWord_965797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965797).length < 2 ^ (prefixWord ++ tailWord_965797).sum := by decide
  have hdescent : baseEnd_965797 < baseStart_965797 := by decide
  rcases family_descends (prefixWord ++ tailWord_965797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965837 : List Nat := [1, 6, 2, 2, 1, 1, 1, 4, 5]
def baseStart_965837 : Nat := 118140960795 + 965837 * 2 ^ 59
def prefixEnd_965837 : Nat := 4983230072969 + 3 ^ 40 * 965837 * 2
def baseEnd_965837 : Nat := 55104290544071432443967

theorem tailTrace_965837 : CollatzResearch.WordTrace tailWord_965837 prefixEnd_965837 55104290544071432443967 := by
  unfold tailWord_965837
  simp only [CollatzResearch.WordTrace]
  refine ⟨35226969401944975672223765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23484646267963317114815843 35226969401944975672223765)
  ·
    refine ⟨1651264190716170734635489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 35226969401944975672223765 1651264190716170734635489)
    ·
      refine ⟨1238448143037128050976617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1651264190716170734635489 1238448143037128050976617)
      ·
        refine ⟨928836107277846038232463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1238448143037128050976617 928836107277846038232463)
        ·
          refine ⟨1393254160916769057348695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 928836107277846038232463 1393254160916769057348695)
          ·
            refine ⟨2089881241375153586023043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1393254160916769057348695 2089881241375153586023043)
            ·
              refine ⟨3134821862062730379034565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2089881241375153586023043 3134821862062730379034565)
              ·
                refine ⟨587779099136761946068981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3134821862062730379034565 587779099136761946068981)
                ·
                  refine ⟨55104290544071432443967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 587779099136761946068981 55104290544071432443967)
                  ·
                    rfl

theorem cell23_965837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 4, 5].length) (baseStart_965837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_965837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_965837 prefixEnd_965837 := by exact prefixLift 965837
  have htrace : WordTrace (prefixWord ++ tailWord_965837) baseStart_965837 baseEnd_965837 := by
    simpa [prefixWord, tailWord_965837, baseEnd_965837] using wordTrace_append hprefix tailTrace_965837
  have hstable : (prefixWord ++ tailWord_965837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965837).length < 2 ^ (prefixWord ++ tailWord_965837).sum := by decide
  have hdescent : baseEnd_965837 < baseStart_965837 := by decide
  rcases family_descends (prefixWord ++ tailWord_965837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965849 : List Nat := [1, 2, 1, 2, 3, 1, 1, 2, 2, 4, 4]
def baseStart_965849 : Nat := 118140960795 + 965849 * 2 ^ 59
def prefixEnd_965849 : Nat := 4983230072969 + 3 ^ 40 * 965849 * 2
def baseEnd_965849 : Nat := 495944776664496845045647

theorem tailTrace_965849 : CollatzResearch.WordTrace tailWord_965849 prefixEnd_965849 495944776664496845045647 := by
  unfold tailWord_965849
  simp only [CollatzResearch.WordTrace]
  refine ⟨35227407077901501721660601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23484938051934334481107067 35227407077901501721660601)
  ·
    refine ⟨26420555308426126291245451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35227407077901501721660601 26420555308426126291245451)
    ·
      refine ⟨39630832962639189436868177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26420555308426126291245451 39630832962639189436868177)
      ·
        refine ⟨29723124721979392077651133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39630832962639189436868177 29723124721979392077651133)
        ·
          refine ⟨11146171770742272029119175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29723124721979392077651133 11146171770742272029119175)
          ·
            refine ⟨16719257656113408043678763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11146171770742272029119175 16719257656113408043678763)
            ·
              refine ⟨25078886484170112065518145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16719257656113408043678763 25078886484170112065518145)
              ·
                refine ⟨18809164863127584049138609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25078886484170112065518145 18809164863127584049138609)
                ·
                  refine ⟨14106873647345688036853957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18809164863127584049138609 14106873647345688036853957)
                  ·
                    refine ⟨2645038808877316506910117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14106873647345688036853957 2645038808877316506910117)
                    ·
                      refine ⟨495944776664496845045647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2645038808877316506910117 495944776664496845045647)
                      ·
                        rfl

theorem cell23_965849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 2, 4, 4].length) (baseStart_965849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_965849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_965849 prefixEnd_965849 := by exact prefixLift 965849
  have htrace : WordTrace (prefixWord ++ tailWord_965849) baseStart_965849 baseEnd_965849 := by
    simpa [prefixWord, tailWord_965849, baseEnd_965849] using wordTrace_append hprefix tailTrace_965849
  have hstable : (prefixWord ++ tailWord_965849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965849).length < 2 ^ (prefixWord ++ tailWord_965849).sum := by decide
  have hdescent : baseEnd_965849 < baseStart_965849 := by decide
  rcases family_descends (prefixWord ++ tailWord_965849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965923 : List Nat := [1, 1, 1, 4, 2, 4, 2, 2, 1, 5]
def baseStart_965923 : Nat := 118140960795 + 965923 * 2 ^ 59
def prefixEnd_965923 : Nat := 4983230072969 + 3 ^ 40 * 965923 * 2
def baseEnd_965923 : Nat := 165327591410976518506769

theorem tailTrace_965923 : CollatzResearch.WordTrace tailWord_965923 prefixEnd_965923 165327591410976518506769 := by
  unfold tailWord_965923
  simp only [CollatzResearch.WordTrace]
  refine ⟨35230106079633412359854423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23486737386422274906569615 35230106079633412359854423)
  ·
    refine ⟨52845159119450118539781635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35230106079633412359854423 52845159119450118539781635)
    ·
      refine ⟨79267738679175177809672453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52845159119450118539781635 79267738679175177809672453)
      ·
        refine ⟨14862701002345345839313585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79267738679175177809672453 14862701002345345839313585)
        ·
          refine ⟨11147025751759009379485189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14862701002345345839313585 11147025751759009379485189)
          ·
            refine ⟨2090067328454814258653473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11147025751759009379485189 2090067328454814258653473)
            ·
              refine ⟨1567550496341110693990105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2090067328454814258653473 1567550496341110693990105)
              ·
                refine ⟨1175662872255833020492579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1567550496341110693990105 1175662872255833020492579)
                ·
                  refine ⟨1763494308383749530738869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1175662872255833020492579 1763494308383749530738869)
                  ·
                    refine ⟨165327591410976518506769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1763494308383749530738869 165327591410976518506769)
                    ·
                      rfl

theorem cell23_965923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2, 2, 1, 5].length) (baseStart_965923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_965923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_965923 prefixEnd_965923 := by exact prefixLift 965923
  have htrace : WordTrace (prefixWord ++ tailWord_965923) baseStart_965923 baseEnd_965923 := by
    simpa [prefixWord, tailWord_965923, baseEnd_965923] using wordTrace_append hprefix tailTrace_965923
  have hstable : (prefixWord ++ tailWord_965923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965923).length < 2 ^ (prefixWord ++ tailWord_965923).sum := by decide
  have hdescent : baseEnd_965923 < baseStart_965923 := by decide
  rcases family_descends (prefixWord ++ tailWord_965923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965930 : List Nat := [3, 1, 4, 2, 1, 1, 2, 1, 1, 5, 2]
def baseStart_965930 : Nat := 118140960795 + 965930 * 2 ^ 59
def prefixEnd_965930 : Nat := 4983230072969 + 3 ^ 40 * 965930 * 2
def baseEnd_965930 : Nat := 495986368597511028132775

theorem tailTrace_965930 : CollatzResearch.WordTrace tailWord_965930 prefixEnd_965930 495986368597511028132775 := by
  unfold tailWord_965930
  simp only [CollatzResearch.WordTrace]
  refine ⟨8807590347652013138839811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23486907593738701703572829 8807590347652013138839811)
  ·
    refine ⟨13211385521478019708259717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8807590347652013138839811 13211385521478019708259717)
    ·
      refine ⟨2477134785277128695298697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13211385521478019708259717 2477134785277128695298697)
      ·
        refine ⟨1857851088957846521474023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2477134785277128695298697 1857851088957846521474023)
        ·
          refine ⟨2786776633436769782211035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1857851088957846521474023 2786776633436769782211035)
          ·
            refine ⟨4180164950155154673316553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2786776633436769782211035 4180164950155154673316553)
            ·
              refine ⟨3135123712616366004987415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4180164950155154673316553 3135123712616366004987415)
              ·
                refine ⟨4702685568924549007481123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3135123712616366004987415 4702685568924549007481123)
                ·
                  refine ⟨7054028353386823511221685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4702685568924549007481123 7054028353386823511221685)
                  ·
                    refine ⟨661315158130014704177033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7054028353386823511221685 661315158130014704177033)
                    ·
                      refine ⟨495986368597511028132775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 661315158130014704177033 495986368597511028132775)
                      ·
                        rfl

theorem cell23_965930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 1, 1, 5, 2].length) (baseStart_965930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_965930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_965930 prefixEnd_965930 := by exact prefixLift 965930
  have htrace : WordTrace (prefixWord ++ tailWord_965930) baseStart_965930 baseEnd_965930 := by
    simpa [prefixWord, tailWord_965930, baseEnd_965930] using wordTrace_append hprefix tailTrace_965930
  have hstable : (prefixWord ++ tailWord_965930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965930).length < 2 ^ (prefixWord ++ tailWord_965930).sum := by decide
  have hdescent : baseEnd_965930 < baseStart_965930 := by decide
  rcases family_descends (prefixWord ++ tailWord_965930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965936 : List Nat := [2, 1, 1, 1, 2, 2, 3, 1, 6, 4]
def baseStart_965936 : Nat := 118140960795 + 965936 * 2 ^ 59
def prefixEnd_965936 : Nat := 4983230072969 + 3 ^ 40 * 965936 * 2
def baseEnd_965936 : Nat := 165329816493812668219249

theorem tailTrace_965936 : CollatzResearch.WordTrace tailWord_965936 prefixEnd_965936 165329816493812668219249 := by
  unfold tailWord_965936
  simp only [CollatzResearch.WordTrace]
  refine ⟨17615290114293157790038831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23487053485724210386718441 17615290114293157790038831)
  ·
    refine ⟨26422935171439736685058247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17615290114293157790038831 26422935171439736685058247)
    ·
      refine ⟨39634402757159605027587371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26422935171439736685058247 39634402757159605027587371)
      ·
        refine ⟨59451604135739407541381057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39634402757159605027587371 59451604135739407541381057)
        ·
          refine ⟨44588703101804555656035793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59451604135739407541381057 44588703101804555656035793)
          ·
            refine ⟨33441527326353416742026845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44588703101804555656035793 33441527326353416742026845)
            ·
              refine ⟨12540572747382531278260067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33441527326353416742026845 12540572747382531278260067)
              ·
                refine ⟨18810859121073796917390101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12540572747382531278260067 18810859121073796917390101)
                ·
                  refine ⟨881759021300334230502661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 18810859121073796917390101 881759021300334230502661)
                  ·
                    refine ⟨165329816493812668219249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 881759021300334230502661 165329816493812668219249)
                    ·
                      rfl

theorem cell23_965936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 6, 4].length) (baseStart_965936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_965936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_965936 prefixEnd_965936 := by exact prefixLift 965936
  have htrace : WordTrace (prefixWord ++ tailWord_965936) baseStart_965936 baseEnd_965936 := by
    simpa [prefixWord, tailWord_965936, baseEnd_965936] using wordTrace_append hprefix tailTrace_965936
  have hstable : (prefixWord ++ tailWord_965936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965936).length < 2 ^ (prefixWord ++ tailWord_965936).sum := by decide
  have hdescent : baseEnd_965936 < baseStart_965936 := by decide
  rcases family_descends (prefixWord ++ tailWord_965936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965937 : List Nat := [1, 2, 2, 3, 3, 1, 3, 3, 1, 1, 3]
def baseStart_965937 : Nat := 118140960795 + 965937 * 2 ^ 59
def prefixEnd_965937 : Nat := 4983230072969 + 3 ^ 40 * 965937 * 2
def baseEnd_965937 : Nat := 495989962962092500745243

theorem tailTrace_965937 : CollatzResearch.WordTrace tailWord_965937 prefixEnd_965937 495989962962092500745243 := by
  unfold tailWord_965937
  simp only [CollatzResearch.WordTrace]
  refine ⟨35230616701582692750864065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23487077801055128500576043 35230616701582692750864065)
  ·
    refine ⟨26422962526187019563148049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35230616701582692750864065 26422962526187019563148049)
    ·
      refine ⟨19817221894640264672361037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26422962526187019563148049 19817221894640264672361037)
      ·
        refine ⟨7431458210490099252135389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19817221894640264672361037 7431458210490099252135389)
        ·
          refine ⟨2786796828933787219550771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7431458210490099252135389 2786796828933787219550771)
          ·
            refine ⟨4180195243400680829326157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2786796828933787219550771 4180195243400680829326157)
            ·
              refine ⟨1567573216275255310997309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4180195243400680829326157 1567573216275255310997309)
              ·
                refine ⟨587839956103220741623991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1567573216275255310997309 587839956103220741623991)
                ·
                  refine ⟨881759934154831112435987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 587839956103220741623991 881759934154831112435987)
                  ·
                    refine ⟨1322639901232246668653981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 881759934154831112435987 1322639901232246668653981)
                    ·
                      refine ⟨495989962962092500745243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1322639901232246668653981 495989962962092500745243)
                      ·
                        rfl

theorem cell23_965937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3, 3, 1, 1, 3].length) (baseStart_965937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_965937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_965937 prefixEnd_965937 := by exact prefixLift 965937
  have htrace : WordTrace (prefixWord ++ tailWord_965937) baseStart_965937 baseEnd_965937 := by
    simpa [prefixWord, tailWord_965937, baseEnd_965937] using wordTrace_append hprefix tailTrace_965937
  have hstable : (prefixWord ++ tailWord_965937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965937).length < 2 ^ (prefixWord ++ tailWord_965937).sum := by decide
  have hdescent : baseEnd_965937 < baseStart_965937 := by decide
  rcases family_descends (prefixWord ++ tailWord_965937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965966 : List Nat := [4, 1, 1, 1, 1, 1, 6, 8]
def baseStart_965966 : Nat := 118140960795 + 965966 * 2 ^ 59
def prefixEnd_965966 : Nat := 4983230072969 + 3 ^ 40 * 965966 * 2
def baseEnd_965966 : Nat := 18370550144484181010467

theorem tailTrace_965966 : CollatzResearch.WordTrace tailWord_965966 prefixEnd_965966 18370550144484181010467 := by
  unfold tailWord_965966
  simp only [CollatzResearch.WordTrace]
  refine ⟨4403959302309703837958719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23487782945651753802446501 4403959302309703837958719)
  ·
    refine ⟨6605938953464555756938079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4403959302309703837958719 6605938953464555756938079)
    ·
      refine ⟨9908908430196833635407119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6605938953464555756938079 9908908430196833635407119)
      ·
        refine ⟨14863362645295250453110679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9908908430196833635407119 14863362645295250453110679)
        ·
          refine ⟨22295043967942875679666019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14863362645295250453110679 22295043967942875679666019)
          ·
            refine ⟨33442565951914313519499029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22295043967942875679666019 33442565951914313519499029)
            ·
              refine ⟨1567620278995983446226517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 33442565951914313519499029 1567620278995983446226517)
              ·
                refine ⟨18370550144484181010467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1567620278995983446226517 18370550144484181010467)
                ·
                  rfl

theorem cell23_965966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6, 8].length) (baseStart_965966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_965966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_965966 prefixEnd_965966 := by exact prefixLift 965966
  have htrace : WordTrace (prefixWord ++ tailWord_965966) baseStart_965966 baseEnd_965966 := by
    simpa [prefixWord, tailWord_965966, baseEnd_965966] using wordTrace_append hprefix tailTrace_965966
  have hstable : (prefixWord ++ tailWord_965966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965966).length < 2 ^ (prefixWord ++ tailWord_965966).sum := by decide
  have hdescent : baseEnd_965966 < baseStart_965966 := by decide
  rcases family_descends (prefixWord ++ tailWord_965966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965974 : List Nat := [5, 2, 3, 1, 1, 1, 1, 1, 3, 5]
def baseStart_965974 : Nat := 118140960795 + 965974 * 2 ^ 59
def prefixEnd_965974 : Nat := 4983230072969 + 3 ^ 40 * 965974 * 2
def baseEnd_965974 : Nat := 165336320582102951994191

theorem tailTrace_965974 : CollatzResearch.WordTrace tailWord_965974 prefixEnd_965974 165336320582102951994191 := by
  unfold tailWord_965974
  simp only [CollatzResearch.WordTrace]
  refine ⟨2201997887653040504372561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23487977468299098713307317 2201997887653040504372561)
  ·
    refine ⟨1651498415739780378279421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2201997887653040504372561 1651498415739780378279421)
    ·
      refine ⟨619311905902417641854783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1651498415739780378279421 619311905902417641854783)
      ·
        refine ⟨928967858853626462782175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 619311905902417641854783 928967858853626462782175)
        ·
          refine ⟨1393451788280439694173263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 928967858853626462782175 1393451788280439694173263)
          ·
            refine ⟨2090177682420659541259895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1393451788280439694173263 2090177682420659541259895)
            ·
              refine ⟨3135266523630989311889843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2090177682420659541259895 3135266523630989311889843)
              ·
                refine ⟨4702899785446483967834765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3135266523630989311889843 4702899785446483967834765)
                ·
                  refine ⟨1763587419542431487938037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4702899785446483967834765 1763587419542431487938037)
                  ·
                    refine ⟨165336320582102951994191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1763587419542431487938037 165336320582102951994191)
                    ·
                      rfl

theorem cell23_965974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_965974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_965974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_965974 prefixEnd_965974 := by exact prefixLift 965974
  have htrace : WordTrace (prefixWord ++ tailWord_965974) baseStart_965974 baseEnd_965974 := by
    simpa [prefixWord, tailWord_965974, baseEnd_965974] using wordTrace_append hprefix tailTrace_965974
  have hstable : (prefixWord ++ tailWord_965974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965974).length < 2 ^ (prefixWord ++ tailWord_965974).sum := by decide
  have hdescent : baseEnd_965974 < baseStart_965974 := by decide
  rcases family_descends (prefixWord ++ tailWord_965974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965981 : List Nat := [1, 4, 5, 1, 1, 1, 2, 1, 2, 3, 2]
def baseStart_965981 : Nat := 118140960795 + 965981 * 2 ^ 59
def prefixEnd_965981 : Nat := 4983230072969 + 3 ^ 40 * 965981 * 2
def baseEnd_965981 : Nat := 496012556110890328595041

theorem tailTrace_965981 : CollatzResearch.WordTrace tailWord_965981 prefixEnd_965981 496012556110890328595041 := by
  unfold tailWord_965981
  simp only [CollatzResearch.WordTrace]
  refine ⟨35232221513423288265465797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23488147675615525510310531 35232221513423288265465797)
  ·
    refine ⟨6606041533766866549774837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35232221513423288265465797 6606041533766866549774837)
    ·
      refine ⟨619316393790643739041391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6606041533766866549774837 619316393790643739041391)
      ·
        refine ⟨928974590685965608562087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 619316393790643739041391 928974590685965608562087)
        ·
          refine ⟨1393461886028948412843131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 928974590685965608562087 1393461886028948412843131)
          ·
            refine ⟨2090192829043422619264697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1393461886028948412843131 2090192829043422619264697)
            ·
              refine ⟨1567644621782566964448523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2090192829043422619264697 1567644621782566964448523)
              ·
                refine ⟨2351466932673850446672785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1567644621782566964448523 2351466932673850446672785)
                ·
                  refine ⟨1763600199505387835004589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2351466932673850446672785 1763600199505387835004589)
                  ·
                    refine ⟨661350074814520438126721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1763600199505387835004589 661350074814520438126721)
                    ·
                      refine ⟨496012556110890328595041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 661350074814520438126721 496012556110890328595041)
                      ·
                        rfl

theorem cell23_965981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_965981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_965981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_965981 prefixEnd_965981 := by exact prefixLift 965981
  have htrace : WordTrace (prefixWord ++ tailWord_965981) baseStart_965981 baseEnd_965981 := by
    simpa [prefixWord, tailWord_965981, baseEnd_965981] using wordTrace_append hprefix tailTrace_965981
  have hstable : (prefixWord ++ tailWord_965981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965981).length < 2 ^ (prefixWord ++ tailWord_965981).sum := by decide
  have hdescent : baseEnd_965981 < baseStart_965981 := by decide
  rcases family_descends (prefixWord ++ tailWord_965981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965993 : List Nat := [1, 2, 1, 1, 1, 3, 2, 4, 4, 1, 3]
def baseStart_965993 : Nat := 118140960795 + 965993 * 2 ^ 59
def prefixEnd_965993 : Nat := 4983230072969 + 3 ^ 40 * 965993 * 2
def baseEnd_965993 : Nat := 496018717878744281644985

theorem tailTrace_965993 : CollatzResearch.WordTrace tailWord_965993 prefixEnd_965993 496018717878744281644985 := by
  unfold tailWord_965993
  simp only [CollatzResearch.WordTrace]
  refine ⟨35232659189379814314902633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23488439459586542876601755 35232659189379814314902633)
  ·
    refine ⟨26424494392034860736176975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35232659189379814314902633 26424494392034860736176975)
    ·
      refine ⟨39636741588052291104265463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26424494392034860736176975 39636741588052291104265463)
      ·
        refine ⟨59455112382078436656398195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39636741588052291104265463 59455112382078436656398195)
        ·
          refine ⟨89182668573117654984597293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59455112382078436656398195 89182668573117654984597293)
          ·
            refine ⟨33443500714919120619223985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89182668573117654984597293 33443500714919120619223985)
            ·
              refine ⟨25082625536189340464417989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33443500714919120619223985 25082625536189340464417989)
              ·
                refine ⟨4702992288035501337078373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25082625536189340464417989 4702992288035501337078373)
                ·
                  refine ⟨881811054006656500702195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4702992288035501337078373 881811054006656500702195)
                  ·
                    refine ⟨1322716581009984751053293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 881811054006656500702195 1322716581009984751053293)
                    ·
                      refine ⟨496018717878744281644985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1322716581009984751053293 496018717878744281644985)
                      ·
                        rfl

theorem cell23_965993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 4, 4, 1, 3].length) (baseStart_965993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_965993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_965993 prefixEnd_965993 := by exact prefixLift 965993
  have htrace : WordTrace (prefixWord ++ tailWord_965993) baseStart_965993 baseEnd_965993 := by
    simpa [prefixWord, tailWord_965993, baseEnd_965993] using wordTrace_append hprefix tailTrace_965993
  have hstable : (prefixWord ++ tailWord_965993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965993).length < 2 ^ (prefixWord ++ tailWord_965993).sum := by decide
  have hdescent : baseEnd_965993 < baseStart_965993 := by decide
  rcases family_descends (prefixWord ++ tailWord_965993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965997 : List Nat := [1, 5, 1, 1, 1, 4, 3, 1, 1, 2, 3]
def baseStart_965997 : Nat := 118140960795 + 965997 * 2 ^ 59
def prefixEnd_965997 : Nat := 4983230072969 + 3 ^ 40 * 965997 * 2
def baseEnd_965997 : Nat := 496020771801362265994967

theorem tailTrace_965997 : CollatzResearch.WordTrace tailWord_965997 prefixEnd_965997 496020771801362265994967 := by
  unfold tailWord_965997
  simp only [CollatzResearch.WordTrace]
  refine ⟨35232805081365322998048245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23488536720910215332032163 35232805081365322998048245)
  ·
    refine ⟨3303075476377999031067023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35232805081365322998048245 3303075476377999031067023)
    ·
      refine ⟨4954613214566998546600535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3303075476377999031067023 4954613214566998546600535)
      ·
        refine ⟨7431919821850497819900803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4954613214566998546600535 7431919821850497819900803)
        ·
          refine ⟨11147879732775746729851205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7431919821850497819900803 11147879732775746729851205)
          ·
            refine ⟨2090227449895452511847101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11147879732775746729851205 2090227449895452511847101)
            ·
              refine ⟨783835293710794691942663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2090227449895452511847101 783835293710794691942663)
              ·
                refine ⟨1175752940566192037913995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 783835293710794691942663 1175752940566192037913995)
                ·
                  refine ⟨1763629410849288056870993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1175752940566192037913995 1763629410849288056870993)
                  ·
                    refine ⟨1322722058136966042653245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1763629410849288056870993 1322722058136966042653245)
                    ·
                      refine ⟨496020771801362265994967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1322722058136966042653245 496020771801362265994967)
                      ·
                        rfl

theorem cell23_965997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 3, 1, 1, 2, 3].length) (baseStart_965997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_965997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_965997 prefixEnd_965997 := by exact prefixLift 965997
  have htrace : WordTrace (prefixWord ++ tailWord_965997) baseStart_965997 baseEnd_965997 := by
    simpa [prefixWord, tailWord_965997, baseEnd_965997] using wordTrace_append hprefix tailTrace_965997
  have hstable : (prefixWord ++ tailWord_965997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965997).length < 2 ^ (prefixWord ++ tailWord_965997).sum := by decide
  have hdescent : baseEnd_965997 < baseStart_965997 := by decide
  rcases family_descends (prefixWord ++ tailWord_965997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966003 : List Nat := [1, 1, 1, 2, 2, 1, 2, 1, 7, 3, 2]
def baseStart_966003 : Nat := 118140960795 + 966003 * 2 ^ 59
def prefixEnd_966003 : Nat := 4983230072969 + 3 ^ 40 * 966003 * 2
def baseEnd_966003 : Nat := 496023852685289242519939

theorem tailTrace_966003 : CollatzResearch.WordTrace tailWord_966003 prefixEnd_966003 496023852685289242519939 := by
  unfold tailWord_966003
  simp only [CollatzResearch.WordTrace]
  refine ⟨35233023919343586022766663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23488682612895724015177775 35233023919343586022766663)
  ·
    refine ⟨52849535879015379034149995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35233023919343586022766663 52849535879015379034149995)
    ·
      refine ⟨79274303818523068551224993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52849535879015379034149995 79274303818523068551224993)
      ·
        refine ⟨59455727863892301413418745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79274303818523068551224993 59455727863892301413418745)
        ·
          refine ⟨44591795897919226060064059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59455727863892301413418745 44591795897919226060064059)
          ·
            refine ⟨66887693846878839090096089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44591795897919226060064059 66887693846878839090096089)
            ·
              refine ⟨50165770385159129317572067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66887693846878839090096089 50165770385159129317572067)
              ·
                refine ⟨75248655577738693976358101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50165770385159129317572067 75248655577738693976358101)
                ·
                  refine ⟨1763640365103250640070893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 75248655577738693976358101 1763640365103250640070893)
                  ·
                    refine ⟨661365136913718990026585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1763640365103250640070893 661365136913718990026585)
                    ·
                      refine ⟨496023852685289242519939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 661365136913718990026585 496023852685289242519939)
                      ·
                        rfl

theorem cell23_966003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 7, 3, 2].length) (baseStart_966003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_966003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_966003 prefixEnd_966003 := by exact prefixLift 966003
  have htrace : WordTrace (prefixWord ++ tailWord_966003) baseStart_966003 baseEnd_966003 := by
    simpa [prefixWord, tailWord_966003, baseEnd_966003] using wordTrace_append hprefix tailTrace_966003
  have hstable : (prefixWord ++ tailWord_966003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966003).length < 2 ^ (prefixWord ++ tailWord_966003).sum := by decide
  have hdescent : baseEnd_966003 < baseStart_966003 := by decide
  rcases family_descends (prefixWord ++ tailWord_966003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966020 : List Nat := [2, 3, 2, 1, 1, 3, 1, 2, 3, 3, 2]
def baseStart_966020 : Nat := 118140960795 + 966020 * 2 ^ 59
def prefixEnd_966020 : Nat := 4983230072969 + 3 ^ 40 * 966020 * 2
def baseEnd_966020 : Nat := 496032581856415676007361

theorem tailTrace_966020 : CollatzResearch.WordTrace tailWord_966020 prefixEnd_966020 496032581856415676007361 := by
  unfold tailWord_966020
  simp only [CollatzResearch.WordTrace]
  refine ⟨17616821980140998963067757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23489095973521331950757009 17616821980140998963067757)
  ·
    refine ⟨6606308242552874611150409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17616821980140998963067757 6606308242552874611150409)
    ·
      refine ⟨4954731181914655958362807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6606308242552874611150409 4954731181914655958362807)
      ·
        refine ⟨7432096772871983937544211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4954731181914655958362807 7432096772871983937544211)
        ·
          refine ⟨11148145159307975906316317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7432096772871983937544211 11148145159307975906316317)
          ·
            refine ⟨4180554434740490964868619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11148145159307975906316317 4180554434740490964868619)
            ·
              refine ⟨6270831652110736447302929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4180554434740490964868619 6270831652110736447302929)
              ·
                refine ⟨4703123739083052335477197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6270831652110736447302929 4703123739083052335477197)
                ·
                  refine ⟨1763671402156144625803949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4703123739083052335477197 1763671402156144625803949)
                  ·
                    refine ⟨661376775808554234676481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1763671402156144625803949 661376775808554234676481)
                    ·
                      refine ⟨496032581856415676007361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 661376775808554234676481 496032581856415676007361)
                      ·
                        rfl

theorem cell23_966020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 2, 3, 3, 2].length) (baseStart_966020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_966020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_966020 prefixEnd_966020 := by exact prefixLift 966020
  have htrace : WordTrace (prefixWord ++ tailWord_966020) baseStart_966020 baseEnd_966020 := by
    simpa [prefixWord, tailWord_966020, baseEnd_966020] using wordTrace_append hprefix tailTrace_966020
  have hstable : (prefixWord ++ tailWord_966020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966020).length < 2 ^ (prefixWord ++ tailWord_966020).sum := by decide
  have hdescent : baseEnd_966020 < baseStart_966020 := by decide
  rcases family_descends (prefixWord ++ tailWord_966020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966033 : List Nat := [1, 2, 2, 1, 1, 1, 2, 2, 5, 4, 2]
def baseStart_966033 : Nat := 118140960795 + 966033 * 2 ^ 59
def prefixEnd_966033 : Nat := 4983230072969 + 3 ^ 40 * 966033 * 2
def baseEnd_966033 : Nat := 496039257104924125144801

theorem tailTrace_966033 : CollatzResearch.WordTrace tailWord_966033 prefixEnd_966033 496039257104924125144801 := by
  unfold tailWord_966033
  simp only [CollatzResearch.WordTrace]
  refine ⟨35234118109234901146358753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23489412072823267430905835 35234118109234901146358753)
  ·
    refine ⟨26425588581926175859769065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35234118109234901146358753 26425588581926175859769065)
    ·
      refine ⟨19819191436444631894826799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26425588581926175859769065 19819191436444631894826799)
      ·
        refine ⟨29728787154666947842240199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19819191436444631894826799 29728787154666947842240199)
        ·
          refine ⟨44593180732000421763360299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29728787154666947842240199 44593180732000421763360299)
          ·
            refine ⟨66889771098000632645040449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44593180732000421763360299 66889771098000632645040449)
            ·
              refine ⟨50167328323500474483780337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66889771098000632645040449 50167328323500474483780337)
              ·
                refine ⟨37625496242625355862835253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50167328323500474483780337 37625496242625355862835253)
                ·
                  refine ⟨3527390272746127112140805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37625496242625355862835253 3527390272746127112140805)
                  ·
                    refine ⟨661385676139898833526401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3527390272746127112140805 661385676139898833526401)
                    ·
                      refine ⟨496039257104924125144801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 661385676139898833526401 496039257104924125144801)
                      ·
                        rfl

theorem cell23_966033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 4, 2].length) (baseStart_966033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_966033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_966033 prefixEnd_966033 := by exact prefixLift 966033
  have htrace : WordTrace (prefixWord ++ tailWord_966033) baseStart_966033 baseEnd_966033 := by
    simpa [prefixWord, tailWord_966033, baseEnd_966033] using wordTrace_append hprefix tailTrace_966033
  have hstable : (prefixWord ++ tailWord_966033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966033).length < 2 ^ (prefixWord ++ tailWord_966033).sum := by decide
  have hdescent : baseEnd_966033 < baseStart_966033 := by decide
  rcases family_descends (prefixWord ++ tailWord_966033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966066 : List Nat := [3, 2, 1, 1, 1, 1, 2, 1, 1, 1, 9]
def baseStart_966066 : Nat := 118140960795 + 966066 * 2 ^ 59
def prefixEnd_966066 : Nat := 4983230072969 + 3 ^ 40 * 966066 * 2
def baseEnd_966066 : Nat := 496056201966522496032149

theorem tailTrace_966066 : CollatzResearch.WordTrace tailWord_966066 prefixEnd_966066 496056201966522496032149 := by
  unfold tailWord_966066
  simp only [CollatzResearch.WordTrace]
  refine ⟨8808830429528836945577513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23490214478743565188206701 8808830429528836945577513)
  ·
    refine ⟨6606622822146627709183135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8808830429528836945577513 6606622822146627709183135)
    ·
      refine ⟨9909934233219941563774703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6606622822146627709183135 9909934233219941563774703)
      ·
        refine ⟨14864901349829912345662055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9909934233219941563774703 14864901349829912345662055)
        ·
          refine ⟨22297352024744868518493083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14864901349829912345662055 22297352024744868518493083)
          ·
            refine ⟨33446028037117302777739625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22297352024744868518493083 33446028037117302777739625)
            ·
              refine ⟨25084521027837977083304719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33446028037117302777739625 25084521027837977083304719)
              ·
                refine ⟨37626781541756965624957079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25084521027837977083304719 37626781541756965624957079)
                ·
                  refine ⟨56440172312635448437435619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37626781541756965624957079 56440172312635448437435619)
                  ·
                    refine ⟨84660258468953172656153429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56440172312635448437435619 84660258468953172656153429)
                    ·
                      refine ⟨496056201966522496032149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 84660258468953172656153429 496056201966522496032149)
                      ·
                        rfl

theorem cell23_966066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 1, 1, 9].length) (baseStart_966066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_966066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_966066 prefixEnd_966066 := by exact prefixLift 966066
  have htrace : WordTrace (prefixWord ++ tailWord_966066) baseStart_966066 baseEnd_966066 := by
    simpa [prefixWord, tailWord_966066, baseEnd_966066] using wordTrace_append hprefix tailTrace_966066
  have hstable : (prefixWord ++ tailWord_966066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966066).length < 2 ^ (prefixWord ++ tailWord_966066).sum := by decide
  have hdescent : baseEnd_966066 < baseStart_966066 := by decide
  rcases family_descends (prefixWord ++ tailWord_966066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966083 : List Nat := [1, 1, 1, 3, 1, 1, 6, 1, 2, 3, 3]
def baseStart_966083 : Nat := 118140960795 + 966083 * 2 ^ 59
def prefixEnd_966083 : Nat := 4983230072969 + 3 ^ 40 * 966083 * 2
def baseEnd_966083 : Nat := 496064931137648929519571

theorem tailTrace_966083 : CollatzResearch.WordTrace tailWord_966083 prefixEnd_966083 496064931137648929519571 := by
  unfold tailWord_966083
  simp only [CollatzResearch.WordTrace]
  refine ⟨35235941759053759685678903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23490627839369173123785935 35235941759053759685678903)
  ·
    refine ⟨52853912638580639528518355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35235941759053759685678903 52853912638580639528518355)
    ·
      refine ⟨79280868957870959292777533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52853912638580639528518355 79280868957870959292777533)
      ·
        refine ⟨29730325859201609734791575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79280868957870959292777533 29730325859201609734791575)
        ·
          refine ⟨44595488788802414602187363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29730325859201609734791575 44595488788802414602187363)
          ·
            refine ⟨66893233183203621903281045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44595488788802414602187363 66893233183203621903281045)
            ·
              refine ⟨3135620305462669776716299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 66893233183203621903281045 3135620305462669776716299)
              ·
                refine ⟨4703430458194004665074449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3135620305462669776716299 4703430458194004665074449)
                ·
                  refine ⟨3527572843645503498805837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4703430458194004665074449 3527572843645503498805837)
                  ·
                    refine ⟨1322839816367063812052189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3527572843645503498805837 1322839816367063812052189)
                    ·
                      refine ⟨496064931137648929519571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1322839816367063812052189 496064931137648929519571)
                      ·
                        rfl

theorem cell23_966083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 1, 2, 3, 3].length) (baseStart_966083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_966083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_966083 prefixEnd_966083 := by exact prefixLift 966083
  have htrace : WordTrace (prefixWord ++ tailWord_966083) baseStart_966083 baseEnd_966083 := by
    simpa [prefixWord, tailWord_966083, baseEnd_966083] using wordTrace_append hprefix tailTrace_966083
  have hstable : (prefixWord ++ tailWord_966083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966083).length < 2 ^ (prefixWord ++ tailWord_966083).sum := by decide
  have hdescent : baseEnd_966083 < baseStart_966083 := by decide
  rcases family_descends (prefixWord ++ tailWord_966083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966084 : List Nat := [2, 3, 3, 2, 1, 3, 1, 1, 1, 4, 2]
def baseStart_966084 : Nat := 118140960795 + 966084 * 2 ^ 59
def prefixEnd_966084 : Nat := 4983230072969 + 3 ^ 40 * 966084 * 2
def baseEnd_966084 : Nat := 496065444618303425607067

theorem tailTrace_966084 : CollatzResearch.WordTrace tailWord_966084 prefixEnd_966084 496065444618303425607067 := by
  unfold tailWord_966084
  simp only [CollatzResearch.WordTrace]
  refine ⟨17617989116025068428232653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23490652154700091237643537 17617989116025068428232653)
  ·
    refine ⟨6606745918509400660587245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17617989116025068428232653 6606745918509400660587245)
    ·
      refine ⟨2477529719441025247720217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6606745918509400660587245 2477529719441025247720217)
      ·
        refine ⟨1858147289580768935790163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2477529719441025247720217 1858147289580768935790163)
        ·
          refine ⟨2787220934371153403685245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1858147289580768935790163 2787220934371153403685245)
          ·
            refine ⟨1045207850389182526381967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2787220934371153403685245 1045207850389182526381967)
            ·
              refine ⟨1567811775583773789572951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1045207850389182526381967 1567811775583773789572951)
              ·
                refine ⟨2351717663375660684359427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1567811775583773789572951 2351717663375660684359427)
                ·
                  refine ⟨3527576495063491026539141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2351717663375660684359427 3527576495063491026539141)
                  ·
                    refine ⟨661420592824404567476089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3527576495063491026539141 661420592824404567476089)
                    ·
                      refine ⟨496065444618303425607067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 661420592824404567476089 496065444618303425607067)
                      ·
                        rfl

theorem cell23_966084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 1, 1, 1, 4, 2].length) (baseStart_966084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_966084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_966084 prefixEnd_966084 := by exact prefixLift 966084
  have htrace : WordTrace (prefixWord ++ tailWord_966084) baseStart_966084 baseEnd_966084 := by
    simpa [prefixWord, tailWord_966084, baseEnd_966084] using wordTrace_append hprefix tailTrace_966084
  have hstable : (prefixWord ++ tailWord_966084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966084).length < 2 ^ (prefixWord ++ tailWord_966084).sum := by decide
  have hdescent : baseEnd_966084 < baseStart_966084 := by decide
  rcases family_descends (prefixWord ++ tailWord_966084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966096 : List Nat := [2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 7]
def baseStart_966096 : Nat := 118140960795 + 966096 * 2 ^ 59
def prefixEnd_966096 : Nat := 4983230072969 + 3 ^ 40 * 966096 * 2
def baseEnd_966096 : Nat := 496071606386157378657011

theorem tailTrace_966096 : CollatzResearch.WordTrace tailWord_966096 prefixEnd_966096 496071606386157378657011 := by
  unfold tailWord_966096
  simp only [CollatzResearch.WordTrace]
  refine ⟨17618207954003331452951071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23490943938671108603934761 17618207954003331452951071)
  ·
    refine ⟨26427311931004997179426607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17618207954003331452951071 26427311931004997179426607)
    ·
      refine ⟨39640967896507495769139911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26427311931004997179426607 39640967896507495769139911)
      ·
        refine ⟨59461451844761243653709867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39640967896507495769139911 59461451844761243653709867)
        ·
          refine ⟨89192177767141865480564801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59461451844761243653709867 89192177767141865480564801)
          ·
            refine ⟨66894133325356399110423601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89192177767141865480564801 66894133325356399110423601)
            ·
              refine ⟨50170599994017299332817701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66894133325356399110423601 50170599994017299332817701)
              ·
                refine ⟨9406987498878243624903319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50170599994017299332817701 9406987498878243624903319)
                ·
                  refine ⟨14110481248317365437354979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9406987498878243624903319 14110481248317365437354979)
                  ·
                    refine ⟨21165721872476048156032469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14110481248317365437354979 21165721872476048156032469)
                    ·
                      refine ⟨496071606386157378657011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 21165721872476048156032469 496071606386157378657011)
                      ·
                        rfl

theorem cell23_966096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 7].length) (baseStart_966096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_966096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_966096 prefixEnd_966096 := by exact prefixLift 966096
  have htrace : WordTrace (prefixWord ++ tailWord_966096) baseStart_966096 baseEnd_966096 := by
    simpa [prefixWord, tailWord_966096, baseEnd_966096] using wordTrace_append hprefix tailTrace_966096
  have hstable : (prefixWord ++ tailWord_966096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966096).length < 2 ^ (prefixWord ++ tailWord_966096).sum := by decide
  have hdescent : baseEnd_966096 < baseStart_966096 := by decide
  rcases family_descends (prefixWord ++ tailWord_966096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966130 : List Nat := [3, 2, 1, 4, 1, 2, 1, 1, 1, 2, 5]
def baseStart_966130 : Nat := 118140960795 + 966130 * 2 ^ 59
def prefixEnd_966130 : Nat := 4983230072969 + 3 ^ 40 * 966130 * 2
def baseEnd_966130 : Nat := 496089064728410245631855

theorem tailTrace_966130 : CollatzResearch.WordTrace tailWord_966130 prefixEnd_966130 496089064728410245631855 := by
  unfold tailWord_966130
  simp only [CollatzResearch.WordTrace]
  refine ⟨8809413997470871678159961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23491770659922324475093229 8809413997470871678159961)
  ·
    refine ⟨6607060498103153758619971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8809413997470871678159961 6607060498103153758619971)
    ·
      refine ⟨9910590747154730637929957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6607060498103153758619971 9910590747154730637929957)
      ·
        refine ⟨1858235765091511994611867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9910590747154730637929957 1858235765091511994611867)
        ·
          refine ⟨2787353647637267991917801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1858235765091511994611867 2787353647637267991917801)
          ·
            refine ⟨2090515235727950993938351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2787353647637267991917801 2090515235727950993938351)
            ·
              refine ⟨3135772853591926490907527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2090515235727950993938351 3135772853591926490907527)
              ·
                refine ⟨4703659280387889736361291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3135772853591926490907527 4703659280387889736361291)
                ·
                  refine ⟨7055488920581834604541937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4703659280387889736361291 7055488920581834604541937)
                  ·
                    refine ⟨5291616690436375953406453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7055488920581834604541937 5291616690436375953406453)
                    ·
                      refine ⟨496089064728410245631855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5291616690436375953406453 496089064728410245631855)
                      ·
                        rfl

theorem cell23_966130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_966130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_966130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_966130 prefixEnd_966130 := by exact prefixLift 966130
  have htrace : WordTrace (prefixWord ++ tailWord_966130) baseStart_966130 baseEnd_966130 := by
    simpa [prefixWord, tailWord_966130, baseEnd_966130] using wordTrace_append hprefix tailTrace_966130
  have hstable : (prefixWord ++ tailWord_966130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966130).length < 2 ^ (prefixWord ++ tailWord_966130).sum := by decide
  have hdescent : baseEnd_966130 < baseStart_966130 := by decide
  rcases family_descends (prefixWord ++ tailWord_966130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966140 : List Nat := [2, 2, 2, 1, 2, 1, 2, 3, 2, 4, 2]
def baseStart_966140 : Nat := 118140960795 + 966140 * 2 ^ 59
def prefixEnd_966140 : Nat := 4983230072969 + 3 ^ 40 * 966140 * 2
def baseEnd_966140 : Nat := 496094199534955206506809

theorem tailTrace_966140 : CollatzResearch.WordTrace tailWord_966140 prefixEnd_966140 496094199534955206506809 := by
  unfold tailWord_966140
  simp only [CollatzResearch.WordTrace]
  refine ⟨17619010359923629210251937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23492013813231505613669249 17619010359923629210251937)
  ·
    refine ⟨13214257769942721907688953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17619010359923629210251937 13214257769942721907688953)
    ·
      refine ⟨9910693327457041430766715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13214257769942721907688953 9910693327457041430766715)
      ·
        refine ⟨14866039991185562146150073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9910693327457041430766715 14866039991185562146150073)
        ·
          refine ⟨11149529993389171609612555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14866039991185562146150073 11149529993389171609612555)
          ·
            refine ⟨16724294990083757414418833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11149529993389171609612555 16724294990083757414418833)
            ·
              refine ⟨12543221242562818060814125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16724294990083757414418833 12543221242562818060814125)
              ·
                refine ⟨4703707965961056772805297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12543221242562818060814125 4703707965961056772805297)
                ·
                  refine ⟨3527780974470792579603973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4703707965961056772805297 3527780974470792579603973)
                  ·
                    refine ⟨661458932713273608675745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3527780974470792579603973 661458932713273608675745)
                    ·
                      refine ⟨496094199534955206506809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 661458932713273608675745 496094199534955206506809)
                      ·
                        rfl

theorem cell23_966140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 3, 2, 4, 2].length) (baseStart_966140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_966140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_966140 prefixEnd_966140 := by exact prefixLift 966140
  have htrace : WordTrace (prefixWord ++ tailWord_966140) baseStart_966140 baseEnd_966140 := by
    simpa [prefixWord, tailWord_966140, baseEnd_966140] using wordTrace_append hprefix tailTrace_966140
  have hstable : (prefixWord ++ tailWord_966140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966140).length < 2 ^ (prefixWord ++ tailWord_966140).sum := by decide
  have hdescent : baseEnd_966140 < baseStart_966140 := by decide
  rcases family_descends (prefixWord ++ tailWord_966140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966143 : List Nat := [1, 1, 2, 2, 1, 2, 2, 4, 1, 4, 3]
def baseStart_966143 : Nat := 118140960795 + 966143 * 2 ^ 59
def prefixEnd_966143 : Nat := 4983230072969 + 3 ^ 40 * 966143 * 2
def baseEnd_966143 : Nat := 496095739976918694769295

theorem tailTrace_966143 : CollatzResearch.WordTrace tailWord_966143 prefixEnd_966143 496095739976918694769295 := by
  unfold tailWord_966143
  simp only [CollatzResearch.WordTrace]
  refine ⟨35238130138836389932863083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23492086759224259955242055 35238130138836389932863083)
  ·
    refine ⟨52857195208254584899294625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35238130138836389932863083 52857195208254584899294625)
    ·
      refine ⟨39642896406190938674470969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52857195208254584899294625 39642896406190938674470969)
      ·
        refine ⟨29732172304643204005853227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39642896406190938674470969 29732172304643204005853227)
        ·
          refine ⟨44598258456964806008779841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29732172304643204005853227 44598258456964806008779841)
          ·
            refine ⟨33448693842723604506584881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44598258456964806008779841 33448693842723604506584881)
            ·
              refine ⟨25086520382042703379938661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33448693842723604506584881 25086520382042703379938661)
              ·
                refine ⟨4703722571633006883738499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25086520382042703379938661 4703722571633006883738499)
                ·
                  refine ⟨7055583857449510325607749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4703722571633006883738499 7055583857449510325607749)
                  ·
                    refine ⟨1322921973271783186051453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7055583857449510325607749 1322921973271783186051453)
                    ·
                      refine ⟨496095739976918694769295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1322921973271783186051453 496095739976918694769295)
                      ·
                        rfl

theorem cell23_966143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 4, 1, 4, 3].length) (baseStart_966143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_966143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_966143 prefixEnd_966143 := by exact prefixLift 966143
  have htrace : WordTrace (prefixWord ++ tailWord_966143) baseStart_966143 baseEnd_966143 := by
    simpa [prefixWord, tailWord_966143, baseEnd_966143] using wordTrace_append hprefix tailTrace_966143
  have hstable : (prefixWord ++ tailWord_966143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966143).length < 2 ^ (prefixWord ++ tailWord_966143).sum := by decide
  have hdescent : baseEnd_966143 < baseStart_966143 := by decide
  rcases family_descends (prefixWord ++ tailWord_966143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966207 : List Nat := [1, 1, 2, 2, 3, 4, 1, 2, 3, 1, 3]
def baseStart_966207 : Nat := 118140960795 + 966207 * 2 ^ 59
def prefixEnd_966207 : Nat := 4983230072969 + 3 ^ 40 * 966207 * 2
def baseEnd_966207 : Nat := 496128602738806444369001

theorem tailTrace_966207 : CollatzResearch.WordTrace tailWord_966207 prefixEnd_966207 496128602738806444369001 := by
  unfold tailWord_966207
  simp only [CollatzResearch.WordTrace]
  refine ⟨35240464410604528863192875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23493642940403019242128583 35240464410604528863192875)
  ·
    refine ⟨52860696615906793294789313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35240464410604528863192875 52860696615906793294789313)
    ·
      refine ⟨39645522461930094971091985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52860696615906793294789313 39645522461930094971091985)
      ·
        refine ⟨29734141846447571228318989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39645522461930094971091985 29734141846447571228318989)
        ·
          refine ⟨11150303192417839210619621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29734141846447571228318989 11150303192417839210619621)
          ·
            refine ⟨2090681848578344851991179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11150303192417839210619621 2090681848578344851991179)
            ·
              refine ⟨3136022772867517277986769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2090681848578344851991179 3136022772867517277986769)
              ·
                refine ⟨2352017079650637958490077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3136022772867517277986769 2352017079650637958490077)
                ·
                  refine ⟨882006404868989234433779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2352017079650637958490077 882006404868989234433779)
                  ·
                    refine ⟨1323009607303483851650669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 882006404868989234433779 1323009607303483851650669)
                    ·
                      refine ⟨496128602738806444369001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1323009607303483851650669 496128602738806444369001)
                      ·
                        rfl

theorem cell23_966207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 2, 3, 1, 3].length) (baseStart_966207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_966207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_966207 prefixEnd_966207 := by exact prefixLift 966207
  have htrace : WordTrace (prefixWord ++ tailWord_966207) baseStart_966207 baseEnd_966207 := by
    simpa [prefixWord, tailWord_966207, baseEnd_966207] using wordTrace_append hprefix tailTrace_966207
  have hstable : (prefixWord ++ tailWord_966207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966207).length < 2 ^ (prefixWord ++ tailWord_966207).sum := by decide
  have hdescent : baseEnd_966207 < baseStart_966207 := by decide
  rcases family_descends (prefixWord ++ tailWord_966207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966224 : List Nat := [2, 1, 1, 1, 1, 3, 6, 3, 1, 1, 3]
def baseStart_966224 : Nat := 118140960795 + 966224 * 2 ^ 59
def prefixEnd_966224 : Nat := 4983230072969 + 3 ^ 40 * 966224 * 2
def baseEnd_966224 : Nat := 496137331909932877856423

theorem tailTrace_966224 : CollatzResearch.WordTrace tailWord_966224 prefixEnd_966224 496137331909932877856423 := by
  unfold tailWord_966224
  simp only [CollatzResearch.WordTrace]
  refine ⟨17620542225771470383280863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23494056301028627177707817 17620542225771470383280863)
  ·
    refine ⟨26430813338657205574921295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17620542225771470383280863 26430813338657205574921295)
    ·
      refine ⟨39646220007985808362381943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26430813338657205574921295 39646220007985808362381943)
      ·
        refine ⟨59469330011978712543572915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39646220007985808362381943 59469330011978712543572915)
        ·
          refine ⟨89203995017968068815359373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59469330011978712543572915 89203995017968068815359373)
          ·
            refine ⟨33451498131738025805759765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89203995017968068815359373 33451498131738025805759765)
            ·
              refine ⟨1568038974925219959644989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 33451498131738025805759765 1568038974925219959644989)
              ·
                refine ⟨588014615596957484866871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1568038974925219959644989 588014615596957484866871)
                ·
                  refine ⟨882021923395436227300307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 588014615596957484866871 882021923395436227300307)
                  ·
                    refine ⟨1323032885093154340950461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 882021923395436227300307 1323032885093154340950461)
                    ·
                      refine ⟨496137331909932877856423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1323032885093154340950461 496137331909932877856423)
                      ·
                        rfl

theorem cell23_966224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6, 3, 1, 1, 3].length) (baseStart_966224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_966224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_966224 prefixEnd_966224 := by exact prefixLift 966224
  have htrace : WordTrace (prefixWord ++ tailWord_966224) baseStart_966224 baseEnd_966224 := by
    simpa [prefixWord, tailWord_966224, baseEnd_966224] using wordTrace_append hprefix tailTrace_966224
  have hstable : (prefixWord ++ tailWord_966224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966224).length < 2 ^ (prefixWord ++ tailWord_966224).sum := by decide
  have hdescent : baseEnd_966224 < baseStart_966224 := by decide
  rcases family_descends (prefixWord ++ tailWord_966224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966233 : List Nat := [1, 2, 1, 2, 2, 1, 1, 2, 5, 1, 5]
def baseStart_966233 : Nat := 118140960795 + 966233 * 2 ^ 59
def prefixEnd_966233 : Nat := 4983230072969 + 3 ^ 40 * 966233 * 2
def baseEnd_966233 : Nat := 496141953235823342643881

theorem tailTrace_966233 : CollatzResearch.WordTrace tailWord_966233 prefixEnd_966233 496141953235823342643881 := by
  unfold tailWord_966233
  simp only [CollatzResearch.WordTrace]
  refine ⟨35241412708510335303639353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23494275139006890202426235 35241412708510335303639353)
  ·
    refine ⟨26431059531382751477729515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35241412708510335303639353 26431059531382751477729515)
    ·
      refine ⟨39646589297074127216594273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26431059531382751477729515 39646589297074127216594273)
      ·
        refine ⟨29734941972805595412445705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39646589297074127216594273 29734941972805595412445705)
        ·
          refine ⟨22301206479604196559334279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29734941972805595412445705 22301206479604196559334279)
          ·
            refine ⟨33451809719406294839001419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22301206479604196559334279 33451809719406294839001419)
            ·
              refine ⟨50177714579109442258502129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33451809719406294839001419 50177714579109442258502129)
              ·
                refine ⟨37633285934332081693876597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50177714579109442258502129 37633285934332081693876597)
                ·
                  refine ⟨3528120556343632658800931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37633285934332081693876597 3528120556343632658800931)
                  ·
                    refine ⟨5292180834515448988201397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3528120556343632658800931 5292180834515448988201397)
                    ·
                      refine ⟨496141953235823342643881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5292180834515448988201397 496141953235823342643881)
                      ·
                        rfl

theorem cell23_966233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 5, 1, 5].length) (baseStart_966233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_966233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_966233 prefixEnd_966233 := by exact prefixLift 966233
  have htrace : WordTrace (prefixWord ++ tailWord_966233) baseStart_966233 baseEnd_966233 := by
    simpa [prefixWord, tailWord_966233, baseEnd_966233] using wordTrace_append hprefix tailTrace_966233
  have hstable : (prefixWord ++ tailWord_966233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966233).length < 2 ^ (prefixWord ++ tailWord_966233).sum := by decide
  have hdescent : baseEnd_966233 < baseStart_966233 := by decide
  rcases family_descends (prefixWord ++ tailWord_966233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966250 : List Nat := [3, 1, 3, 2, 1, 2, 1, 1, 3, 1, 5]
def baseStart_966250 : Nat := 118140960795 + 966250 * 2 ^ 59
def prefixEnd_966250 : Nat := 4983230072969 + 3 ^ 40 * 966250 * 2
def baseEnd_966250 : Nat := 496150682406949776131303

theorem tailTrace_966250 : CollatzResearch.WordTrace tailWord_966250 prefixEnd_966250 496150682406949776131303 := by
  unfold tailWord_966250
  simp only [CollatzResearch.WordTrace]
  refine ⟨8810508187362186801752051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23494688499632498138005469 8810508187362186801752051)
  ·
    refine ⟨13215762281043280202628077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8810508187362186801752051 13215762281043280202628077)
    ·
      refine ⟨4955910855391230075985529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13215762281043280202628077 4955910855391230075985529)
      ·
        refine ⟨3716933141543422556989147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4955910855391230075985529 3716933141543422556989147)
        ·
          refine ⟨5575399712315133835483721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3716933141543422556989147 5575399712315133835483721)
          ·
            refine ⟨4181549784236350376612791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5575399712315133835483721 4181549784236350376612791)
            ·
              refine ⟨6272324676354525564919187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4181549784236350376612791 6272324676354525564919187)
              ·
                refine ⟨9408487014531788347378781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6272324676354525564919187 9408487014531788347378781)
                ·
                  refine ⟨3528182630449420630267043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9408487014531788347378781 3528182630449420630267043)
                  ·
                    refine ⟨5292273945674130945400565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3528182630449420630267043 5292273945674130945400565)
                    ·
                      refine ⟨496150682406949776131303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5292273945674130945400565 496150682406949776131303)
                      ·
                        rfl

theorem cell23_966250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_966250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_966250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_966250 prefixEnd_966250 := by exact prefixLift 966250
  have htrace : WordTrace (prefixWord ++ tailWord_966250) baseStart_966250 baseEnd_966250 := by
    simpa [prefixWord, tailWord_966250, baseEnd_966250] using wordTrace_append hprefix tailTrace_966250
  have hstable : (prefixWord ++ tailWord_966250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966250).length < 2 ^ (prefixWord ++ tailWord_966250).sum := by decide
  have hdescent : baseEnd_966250 < baseStart_966250 := by decide
  rcases family_descends (prefixWord ++ tailWord_966250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966267 : List Nat := [1, 1, 1, 1, 1, 4, 6, 2, 1, 2, 3]
def baseStart_966267 : Nat := 118140960795 + 966267 * 2 ^ 59
def prefixEnd_966267 : Nat := 4983230072969 + 3 ^ 40 * 966267 * 2
def baseEnd_966267 : Nat := 496159411578076209618725

theorem tailTrace_966267 : CollatzResearch.WordTrace tailWord_966267 prefixEnd_966267 496159411578076209618725 := by
  unfold tailWord_966267
  simp only [CollatzResearch.WordTrace]
  refine ⟨35242652790387159110377055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23495101860258106073584703 35242652790387159110377055)
  ·
    refine ⟨52863979185580738665565583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35242652790387159110377055 52863979185580738665565583)
    ·
      refine ⟨79295968778371107998348375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52863979185580738665565583 79295968778371107998348375)
      ·
        refine ⟨118943953167556661997522563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79295968778371107998348375 118943953167556661997522563)
        ·
          refine ⟨178415929751334992996283845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118943953167556661997522563 178415929751334992996283845)
          ·
            refine ⟨33452986828375311186803221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 178415929751334992996283845 33452986828375311186803221)
            ·
              refine ⟨1568108757580092711881401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 33452986828375311186803221 1568108757580092711881401)
              ·
                refine ⟨1176081568185069533911051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1568108757580092711881401 1176081568185069533911051)
                ·
                  refine ⟨1764122352277604300866577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1176081568185069533911051 1764122352277604300866577)
                  ·
                    refine ⟨1323091764208203225649933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1764122352277604300866577 1323091764208203225649933)
                    ·
                      refine ⟨496159411578076209618725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1323091764208203225649933 496159411578076209618725)
                      ·
                        rfl

theorem cell23_966267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6, 2, 1, 2, 3].length) (baseStart_966267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_966267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_966267 prefixEnd_966267 := by exact prefixLift 966267
  have htrace : WordTrace (prefixWord ++ tailWord_966267) baseStart_966267 baseEnd_966267 := by
    simpa [prefixWord, tailWord_966267, baseEnd_966267] using wordTrace_append hprefix tailTrace_966267
  have hstable : (prefixWord ++ tailWord_966267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966267).length < 2 ^ (prefixWord ++ tailWord_966267).sum := by decide
  have hdescent : baseEnd_966267 < baseStart_966267 := by decide
  rcases family_descends (prefixWord ++ tailWord_966267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966281 : List Nat := [1, 2, 1, 1, 4, 1, 5, 3, 1, 2, 2]
def baseStart_966281 : Nat := 118140960795 + 966281 * 2 ^ 59
def prefixEnd_966281 : Nat := 4983230072969 + 3 ^ 40 * 966281 * 2
def baseEnd_966281 : Nat := 496166600307239154843661

theorem tailTrace_966281 : CollatzResearch.WordTrace tailWord_966281 prefixEnd_966281 496166600307239154843661 := by
  unfold tailWord_966281
  simp only [CollatzResearch.WordTrace]
  refine ⟨35243163412336439501386697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23495442274890959667591131 35243163412336439501386697)
  ·
    refine ⟨26432372559252329626040023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35243163412336439501386697 26432372559252329626040023)
    ·
      refine ⟨39648558838878494439060035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26432372559252329626040023 39648558838878494439060035)
      ·
        refine ⟨59472838258317741658590053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39648558838878494439060035 59472838258317741658590053)
        ·
          refine ⟨11151157173434576560985635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59472838258317741658590053 11151157173434576560985635)
          ·
            refine ⟨16726735760151864841478453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11151157173434576560985635 16726735760151864841478453)
            ·
              refine ⟨1568131477514237328888605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16726735760151864841478453 1568131477514237328888605)
              ·
                refine ⟨588049304067838998333227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1568131477514237328888605 588049304067838998333227)
                ·
                  refine ⟨882073956101758497499841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 588049304067838998333227 882073956101758497499841)
                  ·
                    refine ⟨661555467076318873124881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 882073956101758497499841 661555467076318873124881)
                    ·
                      refine ⟨496166600307239154843661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 661555467076318873124881 496166600307239154843661)
                      ·
                        rfl

theorem cell23_966281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5, 3, 1, 2, 2].length) (baseStart_966281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_966281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_966281 prefixEnd_966281 := by exact prefixLift 966281
  have htrace : WordTrace (prefixWord ++ tailWord_966281) baseStart_966281 baseEnd_966281 := by
    simpa [prefixWord, tailWord_966281, baseEnd_966281] using wordTrace_append hprefix tailTrace_966281
  have hstable : (prefixWord ++ tailWord_966281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966281).length < 2 ^ (prefixWord ++ tailWord_966281).sum := by decide
  have hdescent : baseEnd_966281 < baseStart_966281 := by decide
  rcases family_descends (prefixWord ++ tailWord_966281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966307 : List Nat := [1, 1, 1, 4, 1, 1, 4, 2, 3, 3, 2]
def baseStart_966307 : Nat := 118140960795 + 966307 * 2 ^ 59
def prefixEnd_966307 : Nat := 4983230072969 + 3 ^ 40 * 966307 * 2
def baseEnd_966307 : Nat := 496179950804256053118541

theorem tailTrace_966307 : CollatzResearch.WordTrace tailWord_966307 prefixEnd_966307 496179950804256053118541 := by
  unfold tailWord_966307
  simp only [CollatzResearch.WordTrace]
  refine ⟨35244111710242245941833175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23496074473494830627888783 35244111710242245941833175)
  ·
    refine ⟨52866167565363368912749763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35244111710242245941833175 52866167565363368912749763)
    ·
      refine ⟨79299251348045053369124645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52866167565363368912749763 79299251348045053369124645)
      ·
        refine ⟨14868609627758447506710871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79299251348045053369124645 14868609627758447506710871)
        ·
          refine ⟨22302914441637671260066307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14868609627758447506710871 22302914441637671260066307)
          ·
            refine ⟨33454371662456506890099461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22302914441637671260066307 33454371662456506890099461)
            ·
              refine ⟨6272694686710595041893649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33454371662456506890099461 6272694686710595041893649)
              ·
                refine ⟨4704521015032946281420237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6272694686710595041893649 4704521015032946281420237)
                ·
                  refine ⟨1764195380637354855532589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4704521015032946281420237 1764195380637354855532589)
                  ·
                    refine ⟨661573267739008070824721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1764195380637354855532589 661573267739008070824721)
                    ·
                      refine ⟨496179950804256053118541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 661573267739008070824721 496179950804256053118541)
                      ·
                        rfl

theorem cell23_966307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 2, 3, 3, 2].length) (baseStart_966307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_966307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_966307 prefixEnd_966307 := by exact prefixLift 966307
  have htrace : WordTrace (prefixWord ++ tailWord_966307) baseStart_966307 baseEnd_966307 := by
    simpa [prefixWord, tailWord_966307, baseEnd_966307] using wordTrace_append hprefix tailTrace_966307
  have hstable : (prefixWord ++ tailWord_966307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966307).length < 2 ^ (prefixWord ++ tailWord_966307).sum := by decide
  have hdescent : baseEnd_966307 < baseStart_966307 := by decide
  rcases family_descends (prefixWord ++ tailWord_966307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966318 : List Nat := [4, 1, 4, 1, 2, 2, 1, 2, 1, 2, 3]
def baseStart_966318 : Nat := 118140960795 + 966318 * 2 ^ 59
def prefixEnd_966318 : Nat := 4983230072969 + 3 ^ 40 * 966318 * 2
def baseEnd_966318 : Nat := 496185599091455510080991

theorem tailTrace_966318 : CollatzResearch.WordTrace tailWord_966318 prefixEnd_966318 496185599091455510080991 := by
  unfold tailWord_966318
  simp only [CollatzResearch.WordTrace]
  refine ⟨4405564114150299352560451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23496341942134929880322405 4405564114150299352560451)
  ·
    refine ⟨6608346171225449028840677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4405564114150299352560451 6608346171225449028840677)
    ·
      refine ⟨1239064907104771692907627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6608346171225449028840677 1239064907104771692907627)
      ·
        refine ⟨1858597360657157539361441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1239064907104771692907627 1858597360657157539361441)
        ·
          refine ⟨1393948020492868154521081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1858597360657157539361441 1393948020492868154521081)
          ·
            refine ⟨1045461015369651115890811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1393948020492868154521081 1045461015369651115890811)
            ·
              refine ⟨1568191523054476673836217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1045461015369651115890811 1568191523054476673836217)
              ·
                refine ⟨1176143642290857505377163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1568191523054476673836217 1176143642290857505377163)
                ·
                  refine ⟨1764215463436286258065745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1176143642290857505377163 1764215463436286258065745)
                  ·
                    refine ⟨1323161597577214693549309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1764215463436286258065745 1323161597577214693549309)
                    ·
                      refine ⟨496185599091455510080991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1323161597577214693549309 496185599091455510080991)
                      ·
                        rfl

theorem cell23_966318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_966318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_966318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_966318 prefixEnd_966318 := by exact prefixLift 966318
  have htrace : WordTrace (prefixWord ++ tailWord_966318) baseStart_966318 baseEnd_966318 := by
    simpa [prefixWord, tailWord_966318, baseEnd_966318] using wordTrace_append hprefix tailTrace_966318
  have hstable : (prefixWord ++ tailWord_966318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966318).length < 2 ^ (prefixWord ++ tailWord_966318).sum := by decide
  have hdescent : baseEnd_966318 < baseStart_966318 := by decide
  rcases family_descends (prefixWord ++ tailWord_966318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966360 : List Nat := [2, 1, 2, 2, 3, 1, 2, 3, 7]
def baseStart_966360 : Nat := 118140960795 + 966360 * 2 ^ 59
def prefixEnd_966360 : Nat := 4983230072969 + 3 ^ 40 * 966360 * 2
def baseEnd_966360 : Nat := 55134129475438260639533

theorem tailTrace_966360 : CollatzResearch.WordTrace tailWord_966360 prefixEnd_966360 55134129475438260639533 := by
  unfold tailWord_966360
  simp only [CollatzResearch.WordTrace]
  refine ⟨17623022389525117996756267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23497363186033490662341689 17623022389525117996756267)
  ·
    refine ⟨26434533584287676995134401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17623022389525117996756267 26434533584287676995134401)
    ·
      refine ⟨19825900188215757746350801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26434533584287676995134401 19825900188215757746350801)
      ·
        refine ⟨14869425141161818309763101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19825900188215757746350801 14869425141161818309763101)
        ·
          refine ⟨5576034427935681866161163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14869425141161818309763101 5576034427935681866161163)
          ·
            refine ⟨8364051641903522799241745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5576034427935681866161163 8364051641903522799241745)
            ·
              refine ⟨6273038731427642099431309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8364051641903522799241745 6273038731427642099431309)
              ·
                refine ⟨2352389524285365787286741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6273038731427642099431309 2352389524285365787286741)
                ·
                  refine ⟨55134129475438260639533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2352389524285365787286741 55134129475438260639533)
                  ·
                    rfl

theorem cell23_966360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 3, 7].length) (baseStart_966360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_966360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_966360 prefixEnd_966360 := by exact prefixLift 966360
  have htrace : WordTrace (prefixWord ++ tailWord_966360) baseStart_966360 baseEnd_966360 := by
    simpa [prefixWord, tailWord_966360, baseEnd_966360] using wordTrace_append hprefix tailTrace_966360
  have hstable : (prefixWord ++ tailWord_966360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966360).length < 2 ^ (prefixWord ++ tailWord_966360).sum := by decide
  have hdescent : baseEnd_966360 < baseStart_966360 := by decide
  rcases family_descends (prefixWord ++ tailWord_966360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966364 : List Nat := [2, 2, 5, 1, 2, 1, 1, 1, 2, 6]
def baseStart_966364 : Nat := 118140960795 + 966364 * 2 ^ 59
def prefixEnd_966364 : Nat := 4983230072969 + 3 ^ 40 * 966364 * 2
def baseEnd_966364 : Nat := 165403073067187443368593

theorem tailTrace_966364 : CollatzResearch.WordTrace tailWord_966364 prefixEnd_966364 165403073067187443368593 := by
  unfold tailWord_966364
  simp only [CollatzResearch.WordTrace]
  refine ⟨17623095335517872338329073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23497460447357163117772097 17623095335517872338329073)
  ·
    refine ⟨13217321501638404253746805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17623095335517872338329073 13217321501638404253746805)
    ·
      refine ⟨1239123890778600398788763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13217321501638404253746805 1239123890778600398788763)
      ·
        refine ⟨1858685836167900598183145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1239123890778600398788763 1858685836167900598183145)
        ·
          refine ⟨1394014377125925448637359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1858685836167900598183145 1394014377125925448637359)
          ·
            refine ⟨2091021565688888172956039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1394014377125925448637359 2091021565688888172956039)
            ·
              refine ⟨3136532348533332259434059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2091021565688888172956039 3136532348533332259434059)
              ·
                refine ⟨4704798522799998389151089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3136532348533332259434059 4704798522799998389151089)
                ·
                  refine ⟨3528598892099998791863317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4704798522799998389151089 3528598892099998791863317)
                  ·
                    refine ⟨165403073067187443368593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3528598892099998791863317 165403073067187443368593)
                    ·
                      rfl

theorem cell23_966364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_966364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_966364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_966364 prefixEnd_966364 := by exact prefixLift 966364
  have htrace : WordTrace (prefixWord ++ tailWord_966364) baseStart_966364 baseEnd_966364 := by
    simpa [prefixWord, tailWord_966364, baseEnd_966364] using wordTrace_append hprefix tailTrace_966364
  have hstable : (prefixWord ++ tailWord_966364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966364).length < 2 ^ (prefixWord ++ tailWord_966364).sum := by decide
  have hdescent : baseEnd_966364 < baseStart_966364 := by decide
  rcases family_descends (prefixWord ++ tailWord_966364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966371 : List Nat := [1, 1, 1, 7, 2, 1, 2, 1, 1, 4, 2]
def baseStart_966371 : Nat := 118140960795 + 966371 * 2 ^ 59
def prefixEnd_966371 : Nat := 4983230072969 + 3 ^ 40 * 966371 * 2
def baseEnd_966371 : Nat := 496212813566143802718247

theorem tailTrace_966371 : CollatzResearch.WordTrace tailWord_966371 prefixEnd_966371 496212813566143802718247 := by
  unfold tailWord_966371
  simp only [CollatzResearch.WordTrace]
  refine ⟨35246445982010384872162967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23497630654673589914775311 35246445982010384872162967)
  ·
    refine ⟨52869668973015577308244451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35246445982010384872162967 52869668973015577308244451)
    ·
      refine ⟨79304503459523365962366677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52869668973015577308244451 79304503459523365962366677)
      ·
        refine ⟨1858699299832578889742969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 79304503459523365962366677 1858699299832578889742969)
        ·
          refine ⟨1394024474874434167307227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1858699299832578889742969 1394024474874434167307227)
          ·
            refine ⟨2091036712311651250960841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1394024474874434167307227 2091036712311651250960841)
            ·
              refine ⟨1568277534233738438220631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2091036712311651250960841 1568277534233738438220631)
              ·
                refine ⟨2352416301350607657330947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1568277534233738438220631 2352416301350607657330947)
                ·
                  refine ⟨3528624452025911485996421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2352416301350607657330947 3528624452025911485996421)
                  ·
                    refine ⟨661617084754858403624329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3528624452025911485996421 661617084754858403624329)
                    ·
                      refine ⟨496212813566143802718247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 661617084754858403624329 496212813566143802718247)
                      ·
                        rfl

theorem cell23_966371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 2, 1, 1, 4, 2].length) (baseStart_966371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_966371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_966371 prefixEnd_966371 := by exact prefixLift 966371
  have htrace : WordTrace (prefixWord ++ tailWord_966371) baseStart_966371 baseEnd_966371 := by
    simpa [prefixWord, tailWord_966371, baseEnd_966371] using wordTrace_append hprefix tailTrace_966371
  have hstable : (prefixWord ++ tailWord_966371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966371).length < 2 ^ (prefixWord ++ tailWord_966371).sum := by decide
  have hdescent : baseEnd_966371 < baseStart_966371 := by decide
  rcases family_descends (prefixWord ++ tailWord_966371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966388 : List Nat := [2, 6, 1, 1, 1, 1, 2, 2, 1, 4, 2]
def baseStart_966388 : Nat := 118140960795 + 966388 * 2 ^ 59
def prefixEnd_966388 : Nat := 4983230072969 + 3 ^ 40 * 966388 * 2
def baseEnd_966388 : Nat := 496221542737270236205669

theorem tailTrace_966388 : CollatzResearch.WordTrace tailWord_966388 prefixEnd_966388 496221542737270236205669 := by
  unfold tailWord_966388
  simp only [CollatzResearch.WordTrace]
  refine ⟨17623533011474398387765909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23498044015299197850354545 17623533011474398387765909)
  ·
    refine ⟨826103109912862424426527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 17623533011474398387765909 826103109912862424426527)
    ·
      refine ⟨1239154664869293636639791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 826103109912862424426527 1239154664869293636639791)
      ·
        refine ⟨1858731997303940454959687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1239154664869293636639791 1858731997303940454959687)
        ·
          refine ⟨2788097995955910682439531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1858731997303940454959687 2788097995955910682439531)
          ·
            refine ⟨4182146993933866023659297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2788097995955910682439531 4182146993933866023659297)
            ·
              refine ⟨3136610245450399517744473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4182146993933866023659297 3136610245450399517744473)
              ·
                refine ⟨2352457684087799638308355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3136610245450399517744473 2352457684087799638308355)
                ·
                  refine ⟨3528686526131699457462533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2352457684087799638308355 3528686526131699457462533)
                  ·
                    refine ⟨661628723649693648274225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3528686526131699457462533 661628723649693648274225)
                    ·
                      refine ⟨496221542737270236205669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 661628723649693648274225 496221542737270236205669)
                      ·
                        rfl

theorem cell23_966388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 2, 1, 4, 2].length) (baseStart_966388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_966388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_966388 prefixEnd_966388 := by exact prefixLift 966388
  have htrace : WordTrace (prefixWord ++ tailWord_966388) baseStart_966388 baseEnd_966388 := by
    simpa [prefixWord, tailWord_966388, baseEnd_966388] using wordTrace_append hprefix tailTrace_966388
  have hstable : (prefixWord ++ tailWord_966388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966388).length < 2 ^ (prefixWord ++ tailWord_966388).sum := by decide
  have hdescent : baseEnd_966388 < baseStart_966388 := by decide
  rcases family_descends (prefixWord ++ tailWord_966388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966397 : List Nat := [1, 4, 1, 1, 1, 1, 2, 2, 1, 7, 2]
def baseStart_966397 : Nat := 118140960795 + 966397 * 2 ^ 59
def prefixEnd_966397 : Nat := 4983230072969 + 3 ^ 40 * 966397 * 2
def baseEnd_966397 : Nat := 496226164063160700993127

theorem tailTrace_966397 : CollatzResearch.WordTrace tailWord_966397 prefixEnd_966397 496226164063160700993127 := by
  unfold tailWord_966397
  simp only [CollatzResearch.WordTrace]
  refine ⟨35247394279916191312609445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23498262853277460875072963 35247394279916191312609445)
  ·
    refine ⟨6608886427484285871114271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35247394279916191312609445 6608886427484285871114271)
    ·
      refine ⟨9913329641226428806671407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6608886427484285871114271 9913329641226428806671407)
      ·
        refine ⟨14869994461839643210007111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9913329641226428806671407 14869994461839643210007111)
        ·
          refine ⟨22304991692759464815010667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14869994461839643210007111 22304991692759464815010667)
          ·
            refine ⟨33457487539139197222516001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22304991692759464815010667 33457487539139197222516001)
            ·
              refine ⟨25093115654354397916887001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33457487539139197222516001 25093115654354397916887001)
              ·
                refine ⟨18819836740765798437665251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25093115654354397916887001 18819836740765798437665251)
                ·
                  refine ⟨28229755111148697656497877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18819836740765798437665251 28229755111148697656497877)
                  ·
                    refine ⟨661634885417547601324169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28229755111148697656497877 661634885417547601324169)
                    ·
                      refine ⟨496226164063160700993127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 661634885417547601324169 496226164063160700993127)
                      ·
                        rfl

theorem cell23_966397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 7, 2].length) (baseStart_966397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_966397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_966397 prefixEnd_966397 := by exact prefixLift 966397
  have htrace : WordTrace (prefixWord ++ tailWord_966397) baseStart_966397 baseEnd_966397 := by
    simpa [prefixWord, tailWord_966397, baseEnd_966397] using wordTrace_append hprefix tailTrace_966397
  have hstable : (prefixWord ++ tailWord_966397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966397).length < 2 ^ (prefixWord ++ tailWord_966397).sum := by decide
  have hdescent : baseEnd_966397 < baseStart_966397 := by decide
  rcases family_descends (prefixWord ++ tailWord_966397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966480 : List Nat := [2, 1, 1, 1, 1, 4, 1, 1, 2, 9]
def baseStart_966480 : Nat := 118140960795 + 966480 * 2 ^ 59
def prefixEnd_966480 : Nat := 4983230072969 + 3 ^ 40 * 966480 * 2
def baseEnd_966480 : Nat := 165422927652494625418415

theorem tailTrace_966480 : CollatzResearch.WordTrace tailWord_966480 prefixEnd_966480 165422927652494625418415 := by
  unfold tailWord_966480
  simp only [CollatzResearch.WordTrace]
  refine ⟨17625210769307748243940447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23500281025743664325253929 17625210769307748243940447)
  ·
    refine ⟨26437816153961622365910671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17625210769307748243940447 26437816153961622365910671)
    ·
      refine ⟨39656724230942433548866007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26437816153961622365910671 39656724230942433548866007)
      ·
        refine ⟨59485086346413650323299011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39656724230942433548866007 59485086346413650323299011)
        ·
          refine ⟨89227629519620475484948517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59485086346413650323299011 89227629519620475484948517)
          ·
            refine ⟨16730180534928839153427847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89227629519620475484948517 16730180534928839153427847)
            ·
              refine ⟨25095270802393258730141771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16730180534928839153427847 25095270802393258730141771)
              ·
                refine ⟨37642906203589888095212657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25095270802393258730141771 37642906203589888095212657)
                ·
                  refine ⟨28232179652692416071409493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37642906203589888095212657 28232179652692416071409493)
                  ·
                    refine ⟨165422927652494625418415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 28232179652692416071409493 165422927652494625418415)
                    ·
                      rfl

theorem cell23_966480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 2, 9].length) (baseStart_966480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_966480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_966480 prefixEnd_966480 := by exact prefixLift 966480
  have htrace : WordTrace (prefixWord ++ tailWord_966480) baseStart_966480 baseEnd_966480 := by
    simpa [prefixWord, tailWord_966480, baseEnd_966480] using wordTrace_append hprefix tailTrace_966480
  have hstable : (prefixWord ++ tailWord_966480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966480).length < 2 ^ (prefixWord ++ tailWord_966480).sum := by decide
  have hdescent : baseEnd_966480 < baseStart_966480 := by decide
  rcases family_descends (prefixWord ++ tailWord_966480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966484 : List Nat := [2, 4, 1, 1, 3, 2, 1, 3, 6]
def baseStart_966484 : Nat := 118140960795 + 966484 * 2 ^ 59
def prefixEnd_966484 : Nat := 4983230072969 + 3 ^ 40 * 966484 * 2
def baseEnd_966484 : Nat := 55141204097789095622803

theorem tailTrace_966484 : CollatzResearch.WordTrace tailWord_966484 prefixEnd_966484 55141204097789095622803 := by
  unfold tailWord_966484
  simp only [CollatzResearch.WordTrace]
  refine ⟨17625283715300502585513253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23500378287067336780684337 17625283715300502585513253)
  ·
    refine ⟨3304740696618844234783735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17625283715300502585513253 3304740696618844234783735)
    ·
      refine ⟨4957111044928266352175603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3304740696618844234783735 4957111044928266352175603)
      ·
        refine ⟨7435666567392399528263405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4957111044928266352175603 7435666567392399528263405)
        ·
          refine ⟨2788374962772149823098777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7435666567392399528263405 2788374962772149823098777)
          ·
            refine ⟨2091281222079112367324083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2788374962772149823098777 2091281222079112367324083)
            ·
              refine ⟨3136921833118668550986125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2091281222079112367324083 3136921833118668550986125)
              ·
                refine ⟨1176345687419500706619797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3136921833118668550986125 1176345687419500706619797)
                ·
                  refine ⟨55141204097789095622803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1176345687419500706619797 55141204097789095622803)
                  ·
                    rfl

theorem cell23_966484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 3, 6].length) (baseStart_966484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_966484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_966484 prefixEnd_966484 := by exact prefixLift 966484
  have htrace : WordTrace (prefixWord ++ tailWord_966484) baseStart_966484 baseEnd_966484 := by
    simpa [prefixWord, tailWord_966484, baseEnd_966484] using wordTrace_append hprefix tailTrace_966484
  have hstable : (prefixWord ++ tailWord_966484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966484).length < 2 ^ (prefixWord ++ tailWord_966484).sum := by decide
  have hdescent : baseEnd_966484 < baseStart_966484 := by decide
  rcases family_descends (prefixWord ++ tailWord_966484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966497 : List Nat := [1, 2, 3, 1, 1, 1, 5, 1, 3, 5]
def baseStart_966497 : Nat := 118140960795 + 966497 * 2 ^ 59
def prefixEnd_966497 : Nat := 4983230072969 + 3 ^ 40 * 966497 * 2
def baseEnd_966497 : Nat := 165425837376203436580889

theorem tailTrace_966497 : CollatzResearch.WordTrace tailWord_966497 prefixEnd_966497 165425837376203436580889 := by
  unfold tailWord_966497
  simp only [CollatzResearch.WordTrace]
  refine ⟨35251041579553908391249745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23500694386369272260833163 35251041579553908391249745)
  ·
    refine ⟨26438281184665431293437309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35251041579553908391249745 26438281184665431293437309)
    ·
      refine ⟨9914355444249536735038991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26438281184665431293437309 9914355444249536735038991)
      ·
        refine ⟨14871533166374305102558487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9914355444249536735038991 14871533166374305102558487)
        ·
          refine ⟨22307299749561457653837731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14871533166374305102558487 22307299749561457653837731)
          ·
            refine ⟨33460949624342186480756597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22307299749561457653837731 33460949624342186480756597)
            ·
              refine ⟨3136964027282079982570931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33460949624342186480756597 3136964027282079982570931)
              ·
                refine ⟨4705446040923119973856397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3136964027282079982570931 4705446040923119973856397)
                ·
                  refine ⟨1764542265346169990196149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4705446040923119973856397 1764542265346169990196149)
                  ·
                    refine ⟨165425837376203436580889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1764542265346169990196149 165425837376203436580889)
                    ·
                      rfl

theorem cell23_966497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 1, 3, 5].length) (baseStart_966497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_966497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_966497 prefixEnd_966497 := by exact prefixLift 966497
  have htrace : WordTrace (prefixWord ++ tailWord_966497) baseStart_966497 baseEnd_966497 := by
    simpa [prefixWord, tailWord_966497, baseEnd_966497] using wordTrace_append hprefix tailTrace_966497
  have hstable : (prefixWord ++ tailWord_966497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966497).length < 2 ^ (prefixWord ++ tailWord_966497).sum := by decide
  have hdescent : baseEnd_966497 < baseStart_966497 := by decide
  rcases family_descends (prefixWord ++ tailWord_966497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966537 : List Nat := [1, 2, 1, 1, 5, 1, 2, 1, 3, 1, 5]
def baseStart_966537 : Nat := 118140960795 + 966537 * 2 ^ 59
def prefixEnd_966537 : Nat := 4983230072969 + 3 ^ 40 * 966537 * 2
def baseEnd_966537 : Nat := 496298051354790153242483

theorem tailTrace_966537 : CollatzResearch.WordTrace tailWord_966537 prefixEnd_966537 496298051354790153242483 := by
  unfold tailWord_966537
  simp only [CollatzResearch.WordTrace]
  refine ⟨35252500499408995222705865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23501666999605996815137243 35252500499408995222705865)
  ·
    refine ⟨26439375374556746417029399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35252500499408995222705865 26439375374556746417029399)
    ·
      refine ⟨39659063061835119625544099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26439375374556746417029399 39659063061835119625544099)
      ·
        refine ⟨59488594592752679438316149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39659063061835119625544099 59488594592752679438316149)
        ·
          refine ⟨5577055743070563697342139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59488594592752679438316149 5577055743070563697342139)
          ·
            refine ⟨8365583614605845546013209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5577055743070563697342139 8365583614605845546013209)
            ·
              refine ⟨6274187710954384159509907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8365583614605845546013209 6274187710954384159509907)
              ·
                refine ⟨9411281566431576239264861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6274187710954384159509907 9411281566431576239264861)
                ·
                  refine ⟨3529230587411841089724323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9411281566431576239264861 3529230587411841089724323)
                  ·
                    refine ⟨5293845881117761634586485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3529230587411841089724323 5293845881117761634586485)
                    ·
                      refine ⟨496298051354790153242483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5293845881117761634586485 496298051354790153242483)
                      ·
                        rfl

theorem cell23_966537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 1, 3, 1, 5].length) (baseStart_966537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_966537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_966537 prefixEnd_966537 := by exact prefixLift 966537
  have htrace : WordTrace (prefixWord ++ tailWord_966537) baseStart_966537 baseEnd_966537 := by
    simpa [prefixWord, tailWord_966537, baseEnd_966537] using wordTrace_append hprefix tailTrace_966537
  have hstable : (prefixWord ++ tailWord_966537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966537).length < 2 ^ (prefixWord ++ tailWord_966537).sum := by decide
  have hdescent : baseEnd_966537 < baseStart_966537 := by decide
  rcases family_descends (prefixWord ++ tailWord_966537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966551 : List Nat := [1, 1, 3, 3, 1, 3, 1, 1, 5, 2, 2]
def baseStart_966551 : Nat := 118140960795 + 966551 * 2 ^ 59
def prefixEnd_966551 : Nat := 4983230072969 + 3 ^ 40 * 966551 * 2
def baseEnd_966551 : Nat := 496305240083953098467419

theorem tailTrace_966551 : CollatzResearch.WordTrace tailWord_966551 prefixEnd_966551 496305240083953098467419 := by
  unfold tailWord_966551
  simp only [CollatzResearch.WordTrace]
  refine ⟨35253011121358275613715507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23502007414238850409143671 35253011121358275613715507)
  ·
    refine ⟨52879516682037413420573261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35253011121358275613715507 52879516682037413420573261)
    ·
      refine ⟨19829818755764030032714973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52879516682037413420573261 19829818755764030032714973)
      ·
        refine ⟨7436182033411511262268115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19829818755764030032714973 7436182033411511262268115)
        ·
          refine ⟨11154273050117266893402173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7436182033411511262268115 11154273050117266893402173)
          ·
            refine ⟨4182852393793975085025815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11154273050117266893402173 4182852393793975085025815)
            ·
              refine ⟨6274278590690962627538723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4182852393793975085025815 6274278590690962627538723)
              ·
                refine ⟨9411417886036443941308085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6274278590690962627538723 9411417886036443941308085)
                ·
                  refine ⟨882320426815916619497633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9411417886036443941308085 882320426815916619497633)
                  ·
                    refine ⟨661740320111937464623225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 882320426815916619497633 661740320111937464623225)
                    ·
                      refine ⟨496305240083953098467419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 661740320111937464623225 496305240083953098467419)
                      ·
                        rfl

theorem cell23_966551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 1, 5, 2, 2].length) (baseStart_966551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_966551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_966551 prefixEnd_966551 := by exact prefixLift 966551
  have htrace : WordTrace (prefixWord ++ tailWord_966551) baseStart_966551 baseEnd_966551 := by
    simpa [prefixWord, tailWord_966551, baseEnd_966551] using wordTrace_append hprefix tailTrace_966551
  have hstable : (prefixWord ++ tailWord_966551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966551).length < 2 ^ (prefixWord ++ tailWord_966551).sum := by decide
  have hdescent : baseEnd_966551 < baseStart_966551 := by decide
  rcases family_descends (prefixWord ++ tailWord_966551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966564 : List Nat := [2, 3, 1, 2, 1, 3, 2, 2, 1, 2, 4]
def baseStart_966564 : Nat := 118140960795 + 966564 * 2 ^ 59
def prefixEnd_966564 : Nat := 4983230072969 + 3 ^ 40 * 966564 * 2
def baseEnd_966564 : Nat := 496311915332461547604859

theorem tailTrace_966564 : CollatzResearch.WordTrace tailWord_966564 prefixEnd_966564 496311915332461547604859 := by
  unfold tailWord_966564
  simp only [CollatzResearch.WordTrace]
  refine ⟨17626742635155589416969373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23502323513540785889292497 17626742635155589416969373)
  ·
    refine ⟨6610028488183346031363515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17626742635155589416969373 6610028488183346031363515)
    ·
      refine ⟨9915042732275019047045273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6610028488183346031363515 9915042732275019047045273)
      ·
        refine ⟨7436282049206264285283955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9915042732275019047045273 7436282049206264285283955)
        ·
          refine ⟨11154423073809396427925933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7436282049206264285283955 11154423073809396427925933)
          ·
            refine ⟨4182908652678523660472225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11154423073809396427925933 4182908652678523660472225)
            ·
              refine ⟨3137181489508892745354169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4182908652678523660472225 3137181489508892745354169)
              ·
                refine ⟨2352886117131669559015627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3137181489508892745354169 2352886117131669559015627)
                ·
                  refine ⟨3529329175697504338523441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2352886117131669559015627 3529329175697504338523441)
                  ·
                    refine ⟨2646996881773128253892581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3529329175697504338523441 2646996881773128253892581)
                    ·
                      refine ⟨496311915332461547604859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2646996881773128253892581 496311915332461547604859)
                      ·
                        rfl

theorem cell23_966564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 2, 1, 2, 4].length) (baseStart_966564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_966564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_966564 prefixEnd_966564 := by exact prefixLift 966564
  have htrace : WordTrace (prefixWord ++ tailWord_966564) baseStart_966564 baseEnd_966564 := by
    simpa [prefixWord, tailWord_966564, baseEnd_966564] using wordTrace_append hprefix tailTrace_966564
  have hstable : (prefixWord ++ tailWord_966564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966564).length < 2 ^ (prefixWord ++ tailWord_966564).sum := by decide
  have hdescent : baseEnd_966564 < baseStart_966564 := by decide
  rcases family_descends (prefixWord ++ tailWord_966564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966692 : List Nat := [2, 3, 1, 4, 2, 1, 2, 2, 2, 2, 2]
def baseStart_966692 : Nat := 118140960795 + 966692 * 2 ^ 59
def prefixEnd_966692 : Nat := 4983230072969 + 3 ^ 40 * 966692 * 2
def baseEnd_966692 : Nat := 496377640856237046804271

theorem tailTrace_966692 : CollatzResearch.WordTrace tailWord_966692 prefixEnd_966692 496377640856237046804271 := by
  unfold tailWord_966692
  simp only [CollatzResearch.WordTrace]
  refine ⟨17629076906923728347299165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23505435875898304463065553 17629076906923728347299165)
  ·
    refine ⟨6610903840096398130237187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17629076906923728347299165 6610903840096398130237187)
    ·
      refine ⟨9916355760144597195355781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6610903840096398130237187 9916355760144597195355781)
      ·
        refine ⟨1859316705027111974129209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9916355760144597195355781 1859316705027111974129209)
        ·
          refine ⟨1394487528770333980596907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1859316705027111974129209 1394487528770333980596907)
          ·
            refine ⟨2091731293155500970895361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1394487528770333980596907 2091731293155500970895361)
            ·
              refine ⟨1568798469866625728171521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2091731293155500970895361 1568798469866625728171521)
              ·
                refine ⟨1176598852399969296128641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1568798469866625728171521 1176598852399969296128641)
                ·
                  refine ⟨882449139299976972096481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1176598852399969296128641 882449139299976972096481)
                  ·
                    refine ⟨661836854474982729072361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 882449139299976972096481 661836854474982729072361)
                    ·
                      refine ⟨496377640856237046804271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 661836854474982729072361 496377640856237046804271)
                      ·
                        rfl

theorem cell23_966692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 2, 2, 2, 2, 2].length) (baseStart_966692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_966692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_966692 prefixEnd_966692 := by exact prefixLift 966692
  have htrace : WordTrace (prefixWord ++ tailWord_966692) baseStart_966692 baseEnd_966692 := by
    simpa [prefixWord, tailWord_966692, baseEnd_966692] using wordTrace_append hprefix tailTrace_966692
  have hstable : (prefixWord ++ tailWord_966692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966692).length < 2 ^ (prefixWord ++ tailWord_966692).sum := by decide
  have hdescent : baseEnd_966692 < baseStart_966692 := by decide
  rcases family_descends (prefixWord ++ tailWord_966692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966698 : List Nat := [3, 1, 4, 1, 2, 2, 1, 4, 5]
def baseStart_966698 : Nat := 118140960795 + 966698 * 2 ^ 59
def prefixEnd_966698 : Nat := 4983230072969 + 3 ^ 40 * 966698 * 2
def baseEnd_966698 : Nat := 55153413526684891481027

theorem tailTrace_966698 : CollatzResearch.WordTrace tailWord_966698 prefixEnd_966698 55153413526684891481027 := by
  unfold tailWord_966698
  simp only [CollatzResearch.WordTrace]
  refine ⟨8814593162956429929829187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23505581767883813146211165 8814593162956429929829187)
  ·
    refine ⟨13221889744434644894743781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8814593162956429929829187 13221889744434644894743781)
    ·
      refine ⟨2479104327081495917764459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13221889744434644894743781 2479104327081495917764459)
      ·
        refine ⟨3718656490622243876646689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2479104327081495917764459 3718656490622243876646689)
        ·
          refine ⟨2788992367966682907485017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3718656490622243876646689 2788992367966682907485017)
          ·
            refine ⟨2091744275975012180613763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2788992367966682907485017 2091744275975012180613763)
            ·
              refine ⟨3137616413962518270920645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2091744275975012180613763 3137616413962518270920645)
              ·
                refine ⟨588303077617972175797621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3137616413962518270920645 588303077617972175797621)
                ·
                  refine ⟨55153413526684891481027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 588303077617972175797621 55153413526684891481027)
                  ·
                    rfl

theorem cell23_966698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 4, 5].length) (baseStart_966698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_966698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_966698 prefixEnd_966698 := by exact prefixLift 966698
  have htrace : WordTrace (prefixWord ++ tailWord_966698) baseStart_966698 baseEnd_966698 := by
    simpa [prefixWord, tailWord_966698, baseEnd_966698] using wordTrace_append hprefix tailTrace_966698
  have hstable : (prefixWord ++ tailWord_966698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966698).length < 2 ^ (prefixWord ++ tailWord_966698).sum := by decide
  have hdescent : baseEnd_966698 < baseStart_966698 := by decide
  rcases family_descends (prefixWord ++ tailWord_966698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966704 : List Nat := [2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 5]
def baseStart_966704 : Nat := 118140960795 + 966704 * 2 ^ 59
def prefixEnd_966704 : Nat := 4983230072969 + 3 ^ 40 * 966704 * 2
def baseEnd_966704 : Nat := 496383802624090999854215

theorem tailTrace_966704 : CollatzResearch.WordTrace tailWord_966704 prefixEnd_966704 496383802624090999854215 := by
  unfold tailWord_966704
  simp only [CollatzResearch.WordTrace]
  refine ⟨17629295744901991372017583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23505727659869321829356777 17629295744901991372017583)
  ·
    refine ⟨26443943617352987058026375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17629295744901991372017583 26443943617352987058026375)
    ·
      refine ⟨39665915426029480587039563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26443943617352987058026375 39665915426029480587039563)
      ·
        refine ⟨59498873139044220880559345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39665915426029480587039563 59498873139044220880559345)
        ·
          refine ⟨44624154854283165660419509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59498873139044220880559345 44624154854283165660419509)
          ·
            refine ⟨4183514517589046780664329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44624154854283165660419509 4183514517589046780664329)
            ·
              refine ⟨3137635888191785085498247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4183514517589046780664329 3137635888191785085498247)
              ·
                refine ⟨4706453832287677628247371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3137635888191785085498247 4706453832287677628247371)
                ·
                  refine ⟨7059680748431516442371057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4706453832287677628247371 7059680748431516442371057)
                  ·
                    refine ⟨5294760561323637331778293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7059680748431516442371057 5294760561323637331778293)
                    ·
                      refine ⟨496383802624090999854215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5294760561323637331778293 496383802624090999854215)
                      ·
                        rfl

theorem cell23_966704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 5].length) (baseStart_966704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_966704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_966704 prefixEnd_966704 := by exact prefixLift 966704
  have htrace : WordTrace (prefixWord ++ tailWord_966704) baseStart_966704 baseEnd_966704 := by
    simpa [prefixWord, tailWord_966704, baseEnd_966704] using wordTrace_append hprefix tailTrace_966704
  have hstable : (prefixWord ++ tailWord_966704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966704).length < 2 ^ (prefixWord ++ tailWord_966704).sum := by decide
  have hdescent : baseEnd_966704 < baseStart_966704 := by decide
  rcases family_descends (prefixWord ++ tailWord_966704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966714 : List Nat := [3, 1, 1, 1, 3, 1, 1, 4, 1, 3, 4]
def baseStart_966714 : Nat := 118140960795 + 966714 * 2 ^ 59
def prefixEnd_966714 : Nat := 4983230072969 + 3 ^ 40 * 966714 * 2
def baseEnd_966714 : Nat := 496388937430635960729169

theorem tailTrace_966714 : CollatzResearch.WordTrace tailWord_966714 prefixEnd_966714 496388937430635960729169 := by
  unfold tailWord_966714
  simp only [CollatzResearch.WordTrace]
  refine ⟨8814739054941938612974799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23505970813178502967932797 8814739054941938612974799)
  ·
    refine ⟨13222108582412907919462199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8814739054941938612974799 13222108582412907919462199)
    ·
      refine ⟨19833162873619361879193299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13222108582412907919462199 19833162873619361879193299)
      ·
        refine ⟨29749744310429042818789949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19833162873619361879193299 29749744310429042818789949)
        ·
          refine ⟨11156154116410891057046231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29749744310429042818789949 11156154116410891057046231)
          ·
            refine ⟨16734231174616336585569347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11156154116410891057046231 16734231174616336585569347)
            ·
              refine ⟨25101346761924504878354021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16734231174616336585569347 25101346761924504878354021)
              ·
                refine ⟨4706502517860844664691379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25101346761924504878354021 4706502517860844664691379)
                ·
                  refine ⟨7059753776791266997037069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4706502517860844664691379 7059753776791266997037069)
                  ·
                    refine ⟨2647407666296725123888901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7059753776791266997037069 2647407666296725123888901)
                    ·
                      refine ⟨496388937430635960729169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2647407666296725123888901 496388937430635960729169)
                      ·
                        rfl

theorem cell23_966714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 4, 1, 3, 4].length) (baseStart_966714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_966714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_966714 prefixEnd_966714 := by exact prefixLift 966714
  have htrace : WordTrace (prefixWord ++ tailWord_966714) baseStart_966714 baseEnd_966714 := by
    simpa [prefixWord, tailWord_966714, baseEnd_966714] using wordTrace_append hprefix tailTrace_966714
  have hstable : (prefixWord ++ tailWord_966714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966714).length < 2 ^ (prefixWord ++ tailWord_966714).sum := by decide
  have hdescent : baseEnd_966714 < baseStart_966714 := by decide
  rcases family_descends (prefixWord ++ tailWord_966714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966744 : List Nat := [2, 1, 2, 2, 1, 4, 1, 1, 2, 1, 6]
def baseStart_966744 : Nat := 118140960795 + 966744 * 2 ^ 59
def prefixEnd_966744 : Nat := 4983230072969 + 3 ^ 40 * 966744 * 2
def baseEnd_966744 : Nat := 496404341850270843354031

theorem tailTrace_966744 : CollatzResearch.WordTrace tailWord_966744 prefixEnd_966744 496404341850270843354031 := by
  unfold tailWord_966744
  simp only [CollatzResearch.WordTrace]
  refine ⟨17630025204829534787745643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23506700273106046383660857 17630025204829534787745643)
  ·
    refine ⟨26445037807244302181618465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17630025204829534787745643 26445037807244302181618465)
    ·
      refine ⟨19833778355433226636213849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26445037807244302181618465 19833778355433226636213849)
      ·
        refine ⟨14875333766574919977160387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19833778355433226636213849 14875333766574919977160387)
        ·
          refine ⟨22313000649862379965740581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14875333766574919977160387 22313000649862379965740581)
          ·
            refine ⟨4183687621849196243576359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22313000649862379965740581 4183687621849196243576359)
            ·
              refine ⟨6275531432773794365364539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4183687621849196243576359 6275531432773794365364539)
              ·
                refine ⟨9413297149160691548046809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6275531432773794365364539 9413297149160691548046809)
                ·
                  refine ⟨7059972861870518661035107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9413297149160691548046809 7059972861870518661035107)
                  ·
                    refine ⟨10589959292805777991552661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7059972861870518661035107 10589959292805777991552661)
                    ·
                      refine ⟨496404341850270843354031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10589959292805777991552661 496404341850270843354031)
                      ·
                        rfl

theorem cell23_966744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 1, 2, 1, 6].length) (baseStart_966744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_966744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_966744 prefixEnd_966744 := by exact prefixLift 966744
  have htrace : WordTrace (prefixWord ++ tailWord_966744) baseStart_966744 baseEnd_966744 := by
    simpa [prefixWord, tailWord_966744, baseEnd_966744] using wordTrace_append hprefix tailTrace_966744
  have hstable : (prefixWord ++ tailWord_966744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966744).length < 2 ^ (prefixWord ++ tailWord_966744).sum := by decide
  have hdescent : baseEnd_966744 < baseStart_966744 := by decide
  rcases family_descends (prefixWord ++ tailWord_966744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966748 : List Nat := [2, 2, 4, 1, 1, 2, 1, 2, 2, 4, 2]
def baseStart_966748 : Nat := 118140960795 + 966748 * 2 ^ 59
def prefixEnd_966748 : Nat := 4983230072969 + 3 ^ 40 * 966748 * 2
def baseEnd_966748 : Nat := 496406395772888827704013

theorem tailTrace_966748 : CollatzResearch.WordTrace tailWord_966748 prefixEnd_966748 496406395772888827704013 := by
  unfold tailWord_966748
  simp only [CollatzResearch.WordTrace]
  refine ⟨17630098150822289129318449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23506797534429718839091265 17630098150822289129318449)
  ·
    refine ⟨13222573613116716846988837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17630098150822289129318449 13222573613116716846988837)
    ·
      refine ⟨2479232552459384408810407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13222573613116716846988837 2479232552459384408810407)
      ·
        refine ⟨3718848828689076613215611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2479232552459384408810407 3718848828689076613215611)
        ·
          refine ⟨5578273243033614919823417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3718848828689076613215611 5578273243033614919823417)
          ·
            refine ⟨4183704932275211189867563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5578273243033614919823417 4183704932275211189867563)
            ·
              refine ⟨6275557398412816784801345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4183704932275211189867563 6275557398412816784801345)
              ·
                refine ⟨4706668048809612588601009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6275557398412816784801345 4706668048809612588601009)
                ·
                  refine ⟨3530001036607209441450757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4706668048809612588601009 3530001036607209441450757)
                  ·
                    refine ⟨661875194363851770272017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3530001036607209441450757 661875194363851770272017)
                    ·
                      refine ⟨496406395772888827704013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 661875194363851770272017 496406395772888827704013)
                      ·
                        rfl

theorem cell23_966748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 2, 2, 4, 2].length) (baseStart_966748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_966748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_966748 prefixEnd_966748 := by exact prefixLift 966748
  have htrace : WordTrace (prefixWord ++ tailWord_966748) baseStart_966748 baseEnd_966748 := by
    simpa [prefixWord, tailWord_966748, baseEnd_966748] using wordTrace_append hprefix tailTrace_966748
  have hstable : (prefixWord ++ tailWord_966748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966748).length < 2 ^ (prefixWord ++ tailWord_966748).sum := by decide
  have hdescent : baseEnd_966748 < baseStart_966748 := by decide
  rcases family_descends (prefixWord ++ tailWord_966748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966792 : List Nat := [2, 1, 3, 4, 1, 3, 1, 3, 1, 4]
def baseStart_966792 : Nat := 118140960795 + 966792 * 2 ^ 59
def prefixEnd_966792 : Nat := 4983230072969 + 3 ^ 40 * 966792 * 2
def baseEnd_966792 : Nat := 165476329640562218517937

theorem tailTrace_966792 : CollatzResearch.WordTrace tailWord_966792 prefixEnd_966792 165476329640562218517937 := by
  unfold tailWord_966792
  simp only [CollatzResearch.WordTrace]
  refine ⟨17630900556742586886619315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23507867408990115848825753 17630900556742586886619315)
  ·
    refine ⟨26446350835113880329928973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17630900556742586886619315 26446350835113880329928973)
    ·
      refine ⟨9917381563167705123723365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26446350835113880329928973 9917381563167705123723365)
      ·
        refine ⟨1859509043093944710698131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9917381563167705123723365 1859509043093944710698131)
        ·
          refine ⟨2789263564640917066047197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1859509043093944710698131 2789263564640917066047197)
          ·
            refine ⟨1045973836740343899767699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2789263564640917066047197 1045973836740343899767699)
            ·
              refine ⟨1568960755110515849651549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1045973836740343899767699 1568960755110515849651549)
              ·
                refine ⟨588360283166443443619331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1568960755110515849651549 588360283166443443619331)
                ·
                  refine ⟨882540424749665165428997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 588360283166443443619331 882540424749665165428997)
                  ·
                    refine ⟨165476329640562218517937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 882540424749665165428997 165476329640562218517937)
                    ·
                      rfl

theorem cell23_966792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 1, 3, 1, 4].length) (baseStart_966792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_966792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_966792 prefixEnd_966792 := by exact prefixLift 966792
  have htrace : WordTrace (prefixWord ++ tailWord_966792) baseStart_966792 baseEnd_966792 := by
    simpa [prefixWord, tailWord_966792, baseEnd_966792] using wordTrace_append hprefix tailTrace_966792
  have hstable : (prefixWord ++ tailWord_966792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966792).length < 2 ^ (prefixWord ++ tailWord_966792).sum := by decide
  have hdescent : baseEnd_966792 < baseStart_966792 := by decide
  rcases family_descends (prefixWord ++ tailWord_966792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966815 : List Nat := [1, 1, 2, 6, 1, 1, 3, 1, 3, 1, 3]
def baseStart_966815 : Nat := 118140960795 + 966815 * 2 ^ 59
def prefixEnd_966815 : Nat := 4983230072969 + 3 ^ 40 * 966815 * 2
def baseEnd_966815 : Nat := 496440798976740065566205

theorem tailTrace_966815 : CollatzResearch.WordTrace tailWord_966815 prefixEnd_966815 496440798976740065566205 := by
  unfold tailWord_966815
  simp only [CollatzResearch.WordTrace]
  refine ⟨35262639992401848701325899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23508426661601232467550599 35262639992401848701325899)
  ·
    refine ⟨52893959988602773051988849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35262639992401848701325899 52893959988602773051988849)
    ·
      refine ⟨39670469991452079788991637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52893959988602773051988849 39670469991452079788991637)
      ·
        refine ⟨1859553280849316240108983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 39670469991452079788991637 1859553280849316240108983)
        ·
          refine ⟨2789329921273974360163475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1859553280849316240108983 2789329921273974360163475)
          ·
            refine ⟨4183994881910961540245213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2789329921273974360163475 4183994881910961540245213)
            ·
              refine ⟨1568998080716610577591955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4183994881910961540245213 1568998080716610577591955)
              ·
                refine ⟨2353497121074915866387933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1568998080716610577591955 2353497121074915866387933)
                ·
                  refine ⟨882561420403093449895475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2353497121074915866387933 882561420403093449895475)
                  ·
                    refine ⟨1323842130604640174843213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 882561420403093449895475 1323842130604640174843213)
                    ·
                      refine ⟨496440798976740065566205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1323842130604640174843213 496440798976740065566205)
                      ·
                        rfl

theorem cell23_966815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_966815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_966815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_966815 prefixEnd_966815 := by exact prefixLift 966815
  have htrace : WordTrace (prefixWord ++ tailWord_966815) baseStart_966815 baseEnd_966815 := by
    simpa [prefixWord, tailWord_966815, baseEnd_966815] using wordTrace_append hprefix tailTrace_966815
  have hstable : (prefixWord ++ tailWord_966815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966815).length < 2 ^ (prefixWord ++ tailWord_966815).sum := by decide
  have hdescent : baseEnd_966815 < baseStart_966815 := by decide
  rcases family_descends (prefixWord ++ tailWord_966815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966821 : List Nat := [1, 3, 1, 2, 1, 3, 2, 2, 3, 1, 4]
def baseStart_966821 : Nat := 118140960795 + 966821 * 2 ^ 59
def prefixEnd_966821 : Nat := 4983230072969 + 3 ^ 40 * 966821 * 2
def baseEnd_966821 : Nat := 496443879860667042091177

theorem tailTrace_966821 : CollatzResearch.WordTrace tailWord_966821 prefixEnd_966821 496443879860667042091177 := by
  unfold tailWord_966821
  simp only [CollatzResearch.WordTrace]
  refine ⟨35262858830380111726044317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23508572553586741150696211 35262858830380111726044317)
  ·
    refine ⟨13223572061392541897266619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35262858830380111726044317 13223572061392541897266619)
    ·
      refine ⟨19835358092088812845899929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13223572061392541897266619 19835358092088812845899929)
      ·
        refine ⟨14876518569066609634424947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19835358092088812845899929 14876518569066609634424947)
        ·
          refine ⟨22314777853599914451637421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14876518569066609634424947 22314777853599914451637421)
          ·
            refine ⟨8368041695099967919364033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22314777853599914451637421 8368041695099967919364033)
            ·
              refine ⟨6276031271324975939523025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8368041695099967919364033 6276031271324975939523025)
              ·
                refine ⟨4707023453493731954642269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6276031271324975939523025 4707023453493731954642269)
                ·
                  refine ⟨1765133795060149482990851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4707023453493731954642269 1765133795060149482990851)
                  ·
                    refine ⟨2647700692590224224486277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1765133795060149482990851 2647700692590224224486277)
                    ·
                      refine ⟨496443879860667042091177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2647700692590224224486277 496443879860667042091177)
                      ·
                        rfl

theorem cell23_966821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 2, 3, 1, 4].length) (baseStart_966821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_966821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_966821 prefixEnd_966821 := by exact prefixLift 966821
  have htrace : WordTrace (prefixWord ++ tailWord_966821) baseStart_966821 baseEnd_966821 := by
    simpa [prefixWord, tailWord_966821, baseEnd_966821] using wordTrace_append hprefix tailTrace_966821
  have hstable : (prefixWord ++ tailWord_966821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966821).length < 2 ^ (prefixWord ++ tailWord_966821).sum := by decide
  have hdescent : baseEnd_966821 < baseStart_966821 := by decide
  rcases family_descends (prefixWord ++ tailWord_966821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966861 : List Nat := [1, 6, 2, 14]
def baseStart_966861 : Nat := 118140960795 + 966861 * 2 ^ 59
def prefixEnd_966861 : Nat := 4983230072969 + 3 ^ 40 * 966861 * 2
def baseEnd_966861 : Nat := 227007050336921301139

theorem tailTrace_966861 : CollatzResearch.WordTrace tailWord_966861 prefixEnd_966861 227007050336921301139 := by
  unfold tailWord_966861
  simp only [CollatzResearch.WordTrace]
  refine ⟨35264317750235198557500437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23509545166823465705000291 35264317750235198557500437)
  ·
    refine ⟨1653014894542274932382833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 35264317750235198557500437 1653014894542274932382833)
    ·
      refine ⟨1239761170906706199287125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1653014894542274932382833 1239761170906706199287125)
      ·
        refine ⟨227007050336921301139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 14 1239761170906706199287125 227007050336921301139)
        ·
          rfl

theorem cell23_966861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 14].length) (baseStart_966861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_966861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_966861 prefixEnd_966861 := by exact prefixLift 966861
  have htrace : WordTrace (prefixWord ++ tailWord_966861) baseStart_966861 baseEnd_966861 := by
    simpa [prefixWord, tailWord_966861, baseEnd_966861] using wordTrace_append hprefix tailTrace_966861
  have hstable : (prefixWord ++ tailWord_966861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966861).length < 2 ^ (prefixWord ++ tailWord_966861).sum := by decide
  have hdescent : baseEnd_966861 < baseStart_966861 := by decide
  rcases family_descends (prefixWord ++ tailWord_966861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966864 : List Nat := [2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 8]
def baseStart_966864 : Nat := 118140960795 + 966864 * 2 ^ 59
def prefixEnd_966864 : Nat := 4983230072969 + 3 ^ 40 * 966864 * 2
def baseEnd_966864 : Nat := 496465959528810373853479

theorem tailTrace_966864 : CollatzResearch.WordTrace tailWord_966864 prefixEnd_966864 496465959528810373853479 := by
  unfold tailWord_966864
  simp only [CollatzResearch.WordTrace]
  refine ⟨17632213584612165034929823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23509618112816220046573097 17632213584612165034929823)
  ·
    refine ⟨26448320376918247552394735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17632213584612165034929823 26448320376918247552394735)
    ·
      refine ⟨39672480565377371328592103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26448320376918247552394735 39672480565377371328592103)
      ·
        refine ⟨59508720848066056992888155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39672480565377371328592103 59508720848066056992888155)
        ·
          refine ⟨89263081272099085489332233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59508720848066056992888155 89263081272099085489332233)
          ·
            refine ⟨66947310954074314116999175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89263081272099085489332233 66947310954074314116999175)
            ·
              refine ⟨100420966431111471175498763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66947310954074314116999175 100420966431111471175498763)
              ·
                refine ⟨150631449646667206763248145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100420966431111471175498763 150631449646667206763248145)
                ·
                  refine ⟨112973587235000405072436109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 150631449646667206763248145 112973587235000405072436109)
                  ·
                    refine ⟨42365095213125151902163541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 112973587235000405072436109 42365095213125151902163541)
                    ·
                      refine ⟨496465959528810373853479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 42365095213125151902163541 496465959528810373853479)
                      ·
                        rfl

theorem cell23_966864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 8].length) (baseStart_966864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_966864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_966864 prefixEnd_966864 := by exact prefixLift 966864
  have htrace : WordTrace (prefixWord ++ tailWord_966864) baseStart_966864 baseEnd_966864 := by
    simpa [prefixWord, tailWord_966864, baseEnd_966864] using wordTrace_append hprefix tailTrace_966864
  have hstable : (prefixWord ++ tailWord_966864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966864).length < 2 ^ (prefixWord ++ tailWord_966864).sum := by decide
  have hdescent : baseEnd_966864 < baseStart_966864 := by decide
  rcases family_descends (prefixWord ++ tailWord_966864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966871 : List Nat := [1, 1, 3, 2, 1, 2, 1, 1, 5, 3, 3]
def baseStart_966871 : Nat := 118140960795 + 966871 * 2 ^ 59
def prefixEnd_966871 : Nat := 4983230072969 + 3 ^ 40 * 966871 * 2
def baseEnd_966871 : Nat := 496469553893391846465947

theorem tailTrace_966871 : CollatzResearch.WordTrace tailWord_966871 prefixEnd_966871 496469553893391846465947 := by
  unfold tailWord_966871
  simp only [CollatzResearch.WordTrace]
  refine ⟨35264682480198970265364467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23509788320132646843576311 35264682480198970265364467)
  ·
    refine ⟨52897023720298455398046701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35264682480198970265364467 52897023720298455398046701)
    ·
      refine ⟨19836383895111920774267513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52897023720298455398046701 19836383895111920774267513)
      ·
        refine ⟨14877287921333940580700635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19836383895111920774267513 14877287921333940580700635)
        ·
          refine ⟨22315931882000910871050953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14877287921333940580700635 22315931882000910871050953)
          ·
            refine ⟨16736948911500683153288215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22315931882000910871050953 16736948911500683153288215)
            ·
              refine ⟨25105423367251024729932323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16736948911500683153288215 25105423367251024729932323)
              ·
                refine ⟨37658135050876537094898485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25105423367251024729932323 37658135050876537094898485)
                ·
                  refine ⟨3530450161019675352646733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37658135050876537094898485 3530450161019675352646733)
                  ·
                    refine ⟨1323918810382378257242525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3530450161019675352646733 1323918810382378257242525)
                    ·
                      refine ⟨496469553893391846465947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1323918810382378257242525 496469553893391846465947)
                      ·
                        rfl

theorem cell23_966871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 5, 3, 3].length) (baseStart_966871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_966871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_966871 prefixEnd_966871 := by exact prefixLift 966871
  have htrace : WordTrace (prefixWord ++ tailWord_966871) baseStart_966871 baseEnd_966871 := by
    simpa [prefixWord, tailWord_966871, baseEnd_966871] using wordTrace_append hprefix tailTrace_966871
  have hstable : (prefixWord ++ tailWord_966871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966871).length < 2 ^ (prefixWord ++ tailWord_966871).sum := by decide
  have hdescent : baseEnd_966871 < baseStart_966871 := by decide
  rcases family_descends (prefixWord ++ tailWord_966871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966888 : List Nat := [2, 1, 4, 1, 2, 2, 1, 3, 1, 3, 3]
def baseStart_966888 : Nat := 118140960795 + 966888 * 2 ^ 59
def prefixEnd_966888 : Nat := 4983230072969 + 3 ^ 40 * 966888 * 2
def baseEnd_966888 : Nat := 496478283064518279953369

theorem tailTrace_966888 : CollatzResearch.WordTrace tailWord_966888 prefixEnd_966888 496478283064518279953369 := by
  unfold tailWord_966888
  simp only [CollatzResearch.WordTrace]
  refine ⟨17632651260568691084366659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23510201680758254779155545 17632651260568691084366659)
  ·
    refine ⟨26448976890853036626549989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17632651260568691084366659 26448976890853036626549989)
    ·
      refine ⟨4959183167034944367478123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26448976890853036626549989 4959183167034944367478123)
      ·
        refine ⟨7438774750552416551217185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4959183167034944367478123 7438774750552416551217185)
        ·
          refine ⟨5579081062914312413412889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7438774750552416551217185 5579081062914312413412889)
          ·
            refine ⟨4184310797185734310059667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5579081062914312413412889 4184310797185734310059667)
            ·
              refine ⟨6276466195778601465089501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4184310797185734310059667 6276466195778601465089501)
              ·
                refine ⟨2353674823416975549408563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6276466195778601465089501 2353674823416975549408563)
                ·
                  refine ⟨3530512235125463324112845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2353674823416975549408563 3530512235125463324112845)
                  ·
                    refine ⟨1323942088172048746542317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3530512235125463324112845 1323942088172048746542317)
                    ·
                      refine ⟨496478283064518279953369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1323942088172048746542317 496478283064518279953369)
                      ·
                        rfl

theorem cell23_966888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 3, 1, 3, 3].length) (baseStart_966888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_966888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_966888 prefixEnd_966888 := by exact prefixLift 966888
  have htrace : WordTrace (prefixWord ++ tailWord_966888) baseStart_966888 baseEnd_966888 := by
    simpa [prefixWord, tailWord_966888, baseEnd_966888] using wordTrace_append hprefix tailTrace_966888
  have hstable : (prefixWord ++ tailWord_966888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966888).length < 2 ^ (prefixWord ++ tailWord_966888).sum := by decide
  have hdescent : baseEnd_966888 < baseStart_966888 := by decide
  rcases family_descends (prefixWord ++ tailWord_966888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966915 : List Nat := [1, 1, 1, 3, 2, 3, 3, 3, 1, 3, 2]
def baseStart_966915 : Nat := 118140960795 + 966915 * 2 ^ 59
def prefixEnd_966915 : Nat := 4983230072969 + 3 ^ 40 * 966915 * 2
def baseEnd_966915 : Nat := 496492147042189674315745

theorem tailTrace_966915 : CollatzResearch.WordTrace tailWord_966915 prefixEnd_966915 496492147042189674315745 := by
  unfold tailWord_966915
  simp only [CollatzResearch.WordTrace]
  refine ⟨35266287292039565779966199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23510858194693043853310799 35266287292039565779966199)
  ·
    refine ⟨52899430938059348669949299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35266287292039565779966199 52899430938059348669949299)
    ·
      refine ⟨79349146407089023004923949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52899430938059348669949299 79349146407089023004923949)
      ·
        refine ⟨29755929902658383626846481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79349146407089023004923949 29755929902658383626846481)
        ·
          refine ⟨22316947426993787720134861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29755929902658383626846481 22316947426993787720134861)
          ·
            refine ⟨8368855285122670395050573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22316947426993787720134861 8368855285122670395050573)
            ·
              refine ⟨3138320731921001398143965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8368855285122670395050573 3138320731921001398143965)
              ·
                refine ⟨1176870274470375524303987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3138320731921001398143965 1176870274470375524303987)
                ·
                  refine ⟨1765305411705563286455981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1176870274470375524303987 1765305411705563286455981)
                  ·
                    refine ⟨661989529389586232420993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1765305411705563286455981 661989529389586232420993)
                    ·
                      refine ⟨496492147042189674315745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 661989529389586232420993 496492147042189674315745)
                      ·
                        rfl

theorem cell23_966915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 3, 1, 3, 2].length) (baseStart_966915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_966915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_966915 prefixEnd_966915 := by exact prefixLift 966915
  have htrace : WordTrace (prefixWord ++ tailWord_966915) baseStart_966915 baseEnd_966915 := by
    simpa [prefixWord, tailWord_966915, baseEnd_966915] using wordTrace_append hprefix tailTrace_966915
  have hstable : (prefixWord ++ tailWord_966915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966915).length < 2 ^ (prefixWord ++ tailWord_966915).sum := by decide
  have hdescent : baseEnd_966915 < baseStart_966915 := by decide
  rcases family_descends (prefixWord ++ tailWord_966915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966921 : List Nat := [1, 2, 1, 1, 3, 4, 1, 2, 2, 6]
def baseStart_966921 : Nat := 118140960795 + 966921 * 2 ^ 59
def prefixEnd_966921 : Nat := 4983230072969 + 3 ^ 40 * 966921 * 2
def baseEnd_966921 : Nat := 165498409308705550280239

theorem tailTrace_966921 : CollatzResearch.WordTrace tailWord_966921 prefixEnd_966921 165498409308705550280239 := by
  unfold tailWord_966921
  simp only [CollatzResearch.WordTrace]
  refine ⟨35266506130017828804684617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23511004086678552536456411 35266506130017828804684617)
  ·
    refine ⟨26449879597513371603513463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35266506130017828804684617 26449879597513371603513463)
    ·
      refine ⟨39674819396270057405270195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26449879597513371603513463 39674819396270057405270195)
      ·
        refine ⟨59512229094405086107905293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39674819396270057405270195 59512229094405086107905293)
        ·
          refine ⟨22317085910401907290464485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59512229094405086107905293 22317085910401907290464485)
          ·
            refine ⟨4184453608200357616962091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22317085910401907290464485 4184453608200357616962091)
            ·
              refine ⟨6276680412300536425443137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4184453608200357616962091 6276680412300536425443137)
              ·
                refine ⟨4707510309225402319082353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6276680412300536425443137 4707510309225402319082353)
                ·
                  refine ⟨3530632731919051739311765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4707510309225402319082353 3530632731919051739311765)
                  ·
                    refine ⟨165498409308705550280239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3530632731919051739311765 165498409308705550280239)
                    ·
                      rfl

theorem cell23_966921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 2, 2, 6].length) (baseStart_966921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_966921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_966921 prefixEnd_966921 := by exact prefixLift 966921
  have htrace : WordTrace (prefixWord ++ tailWord_966921) baseStart_966921 baseEnd_966921 := by
    simpa [prefixWord, tailWord_966921, baseEnd_966921] using wordTrace_append hprefix tailTrace_966921
  have hstable : (prefixWord ++ tailWord_966921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966921).length < 2 ^ (prefixWord ++ tailWord_966921).sum := by decide
  have hdescent : baseEnd_966921 < baseStart_966921 := by decide
  rcases family_descends (prefixWord ++ tailWord_966921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966931 : List Nat := [1, 1, 1, 2, 1, 3, 1, 3, 1, 6, 3]
def baseStart_966931 : Nat := 118140960795 + 966931 * 2 ^ 59
def prefixEnd_966931 : Nat := 4983230072969 + 3 ^ 40 * 966931 * 2
def baseEnd_966931 : Nat := 496500362732661611715671

theorem tailTrace_966931 : CollatzResearch.WordTrace tailWord_966931 prefixEnd_966931 496500362732661611715671 := by
  unfold tailWord_966931
  simp only [CollatzResearch.WordTrace]
  refine ⟨35266870859981600512548647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23511247239987733675032431 35266870859981600512548647)
  ·
    refine ⟨52900306289972400768822971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35266870859981600512548647 52900306289972400768822971)
    ·
      refine ⟨79350459434958601153234457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52900306289972400768822971 79350459434958601153234457)
      ·
        refine ⟨59512844576218950864925843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79350459434958601153234457 59512844576218950864925843)
        ·
          refine ⟨89269266864328426297388765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59512844576218950864925843 89269266864328426297388765)
          ·
            refine ⟨33475975074123159861520787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89269266864328426297388765 33475975074123159861520787)
            ·
              refine ⟨50213962611184739792281181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33475975074123159861520787 50213962611184739792281181)
              ·
                refine ⟨18830235979194277422105443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50213962611184739792281181 18830235979194277422105443)
                ·
                  refine ⟨28245353968791416133158165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18830235979194277422105443 28245353968791416133158165)
                  ·
                    refine ⟨1324000967287097631241789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28245353968791416133158165 1324000967287097631241789)
                    ·
                      refine ⟨496500362732661611715671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1324000967287097631241789 496500362732661611715671)
                      ·
                        rfl

theorem cell23_966931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 6, 3].length) (baseStart_966931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_966931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_966931 prefixEnd_966931 := by exact prefixLift 966931
  have htrace : WordTrace (prefixWord ++ tailWord_966931) baseStart_966931 baseEnd_966931 := by
    simpa [prefixWord, tailWord_966931, baseEnd_966931] using wordTrace_append hprefix tailTrace_966931
  have hstable : (prefixWord ++ tailWord_966931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966931).length < 2 ^ (prefixWord ++ tailWord_966931).sum := by decide
  have hdescent : baseEnd_966931 < baseStart_966931 := by decide
  rcases family_descends (prefixWord ++ tailWord_966931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966945 : List Nat := [1, 2, 3, 2, 1, 1, 5, 1, 1, 4, 2]
def baseStart_966945 : Nat := 118140960795 + 966945 * 2 ^ 59
def prefixEnd_966945 : Nat := 4983230072969 + 3 ^ 40 * 966945 * 2
def baseEnd_966945 : Nat := 496507551461824556940607

theorem tailTrace_966945 : CollatzResearch.WordTrace tailWord_966945 prefixEnd_966945 496507551461824556940607 := by
  unfold tailWord_966945
  simp only [CollatzResearch.WordTrace]
  refine ⟨35267381481930880903558289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23511587654620587269038859 35267381481930880903558289)
  ·
    refine ⟨26450536111448160677668717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35267381481930880903558289 26450536111448160677668717)
    ·
      refine ⟨9918951041793060254125769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26450536111448160677668717 9918951041793060254125769)
      ·
        refine ⟨7439213281344795190594327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9918951041793060254125769 7439213281344795190594327)
        ·
          refine ⟨11158819922017192785891491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7439213281344795190594327 11158819922017192785891491)
          ·
            refine ⟨16738229883025789178837237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11158819922017192785891491 16738229883025789178837237)
            ·
              refine ⟨1569209051533667735515991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16738229883025789178837237 1569209051533667735515991)
              ·
                refine ⟨2353813577300501603273987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1569209051533667735515991 2353813577300501603273987)
                ·
                  refine ⟨3530720365950752404910981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2353813577300501603273987 3530720365950752404910981)
                  ·
                    refine ⟨662010068615766075920809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3530720365950752404910981 662010068615766075920809)
                    ·
                      refine ⟨496507551461824556940607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 662010068615766075920809 496507551461824556940607)
                      ·
                        rfl

theorem cell23_966945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5, 1, 1, 4, 2].length) (baseStart_966945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_966945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_966945 prefixEnd_966945 := by exact prefixLift 966945
  have htrace : WordTrace (prefixWord ++ tailWord_966945) baseStart_966945 baseEnd_966945 := by
    simpa [prefixWord, tailWord_966945, baseEnd_966945] using wordTrace_append hprefix tailTrace_966945
  have hstable : (prefixWord ++ tailWord_966945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966945).length < 2 ^ (prefixWord ++ tailWord_966945).sum := by decide
  have hdescent : baseEnd_966945 < baseStart_966945 := by decide
  rcases family_descends (prefixWord ++ tailWord_966945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966996 : List Nat := [2, 4, 1, 1, 2, 4, 2, 1, 2, 2, 2]
def baseStart_966996 : Nat := 118140960795 + 966996 * 2 ^ 59
def prefixEnd_966996 : Nat := 4983230072969 + 3 ^ 40 * 966996 * 2
def baseEnd_966996 : Nat := 496533738975203857402873

theorem tailTrace_966996 : CollatzResearch.WordTrace tailWord_966996 prefixEnd_966996 496533738975203857402873 := by
  unfold tailWord_966996
  simp only [CollatzResearch.WordTrace]
  refine ⟨17634620802373058306832421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23512827736497411075776561 17634620802373058306832421)
  ·
    refine ⟨3306491400444948432531079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17634620802373058306832421 3306491400444948432531079)
    ·
      refine ⟨4959737100667422648796619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3306491400444948432531079 4959737100667422648796619)
      ·
        refine ⟨7439605651001133973194929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4959737100667422648796619 7439605651001133973194929)
        ·
          refine ⟨5579704238250850479896197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7439605651001133973194929 5579704238250850479896197)
          ·
            refine ⟨1046194544672034464980537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5579704238250850479896197 1046194544672034464980537)
            ·
              refine ⟨784645908504025848735403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1046194544672034464980537 784645908504025848735403)
              ·
                refine ⟨1176968862756038773103105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 784645908504025848735403 1176968862756038773103105)
                ·
                  refine ⟨882726647067029079827329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1176968862756038773103105 882726647067029079827329)
                  ·
                    refine ⟨662044985300271809870497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 882726647067029079827329 662044985300271809870497)
                    ·
                      refine ⟨496533738975203857402873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 662044985300271809870497 496533738975203857402873)
                      ·
                        rfl

theorem cell23_966996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 2, 1, 2, 2, 2].length) (baseStart_966996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_966996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_966996 prefixEnd_966996 := by exact prefixLift 966996
  have htrace : WordTrace (prefixWord ++ tailWord_966996) baseStart_966996 baseEnd_966996 := by
    simpa [prefixWord, tailWord_966996, baseEnd_966996] using wordTrace_append hprefix tailTrace_966996
  have hstable : (prefixWord ++ tailWord_966996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966996).length < 2 ^ (prefixWord ++ tailWord_966996).sum := by decide
  have hdescent : baseEnd_966996 < baseStart_966996 := by decide
  rcases family_descends (prefixWord ++ tailWord_966996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967015 : List Nat := [1, 1, 5, 1, 3, 2, 2, 1, 2, 5]
def baseStart_967015 : Nat := 118140960795 + 967015 * 2 ^ 59
def prefixEnd_967015 : Nat := 4983230072969 + 3 ^ 40 * 967015 * 2
def baseEnd_967015 : Nat := 165514498369213094355095

theorem tailTrace_967015 : CollatzResearch.WordTrace tailWord_967015 prefixEnd_967015 165514498369213094355095 := by
  unfold tailWord_967015
  simp only [CollatzResearch.WordTrace]
  refine ⟨35269934591677282858606499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23513289727784855239070999 35269934591677282858606499)
  ·
    refine ⟨52904901887515924287909749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35269934591677282858606499 52904901887515924287909749)
    ·
      refine ⟨4959834551954617901991539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52904901887515924287909749 4959834551954617901991539)
      ·
        refine ⟨7439751827931926852987309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4959834551954617901991539 7439751827931926852987309)
        ·
          refine ⟨2789906935474472569870241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7439751827931926852987309 2789906935474472569870241)
          ·
            refine ⟨2092430201605854427402681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2789906935474472569870241 2092430201605854427402681)
            ·
              refine ⟨1569322651204390820552011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2092430201605854427402681 1569322651204390820552011)
              ·
                refine ⟨2353983976806586230828017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1569322651204390820552011 2353983976806586230828017)
                ·
                  refine ⟨1765487982604939673121013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2353983976806586230828017 1765487982604939673121013)
                  ·
                    refine ⟨165514498369213094355095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1765487982604939673121013 165514498369213094355095)
                    ·
                      rfl

theorem cell23_967015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 1, 2, 5].length) (baseStart_967015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_967015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_967015 prefixEnd_967015 := by exact prefixLift 967015
  have htrace : WordTrace (prefixWord ++ tailWord_967015) baseStart_967015 baseEnd_967015 := by
    simpa [prefixWord, tailWord_967015, baseEnd_967015] using wordTrace_append hprefix tailTrace_967015
  have hstable : (prefixWord ++ tailWord_967015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967015).length < 2 ^ (prefixWord ++ tailWord_967015).sum := by decide
  have hdescent : baseEnd_967015 < baseStart_967015 := by decide
  rcases family_descends (prefixWord ++ tailWord_967015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967069 : List Nat := [1, 4, 2, 1, 5, 1, 1, 1, 2, 1, 4]
def baseStart_967069 : Nat := 118140960795 + 967069 * 2 ^ 59
def prefixEnd_967069 : Nat := 4983230072969 + 3 ^ 40 * 967069 * 2
def baseEnd_967069 : Nat := 496571223062982071790037

theorem tailTrace_967069 : CollatzResearch.WordTrace tailWord_967069 prefixEnd_967069 496571223062982071790037 := by
  unfold tailWord_967069
  simp only [CollatzResearch.WordTrace]
  refine ⟨35271904133481650081072261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23514602755654433387381507 35271904133481650081072261)
  ·
    refine ⟨6613482025027809390201049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35271904133481650081072261 6613482025027809390201049)
    ·
      refine ⟨4960111518770857042650787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6613482025027809390201049 4960111518770857042650787)
      ·
        refine ⟨7440167278156285563976181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4960111518770857042650787 7440167278156285563976181)
        ·
          refine ⟨697515682327151771622767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7440167278156285563976181 697515682327151771622767)
          ·
            refine ⟨1046273523490727657434151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 697515682327151771622767 1046273523490727657434151)
            ·
              refine ⟨1569410285236091486151227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1046273523490727657434151 1569410285236091486151227)
              ·
                refine ⟨2354115427854137229226841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1569410285236091486151227 2354115427854137229226841)
                ·
                  refine ⟨1765586570890602921920131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2354115427854137229226841 1765586570890602921920131)
                  ·
                    refine ⟨2648379856335904382880197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1765586570890602921920131 2648379856335904382880197)
                    ·
                      refine ⟨496571223062982071790037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2648379856335904382880197 496571223062982071790037)
                      ·
                        rfl

theorem cell23_967069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 1, 1, 2, 1, 4].length) (baseStart_967069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_967069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_967069 prefixEnd_967069 := by exact prefixLift 967069
  have htrace : WordTrace (prefixWord ++ tailWord_967069) baseStart_967069 baseEnd_967069 := by
    simpa [prefixWord, tailWord_967069, baseEnd_967069] using wordTrace_append hprefix tailTrace_967069
  have hstable : (prefixWord ++ tailWord_967069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967069).length < 2 ^ (prefixWord ++ tailWord_967069).sum := by decide
  have hdescent : baseEnd_967069 < baseStart_967069 := by decide
  rcases family_descends (prefixWord ++ tailWord_967069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967072 : List Nat := [2, 1, 1, 4, 1, 5, 1, 1, 2, 2, 3]
def baseStart_967072 : Nat := 118140960795 + 967072 * 2 ^ 59
def prefixEnd_967072 : Nat := 4983230072969 + 3 ^ 40 * 967072 * 2
def baseEnd_967072 : Nat := 496572763504945560052523

theorem tailTrace_967072 : CollatzResearch.WordTrace tailWord_967072 prefixEnd_967072 496572763504945560052523 := by
  unfold tailWord_967072
  simp only [CollatzResearch.WordTrace]
  refine ⟨17636006776235390796715735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23514675701647187728954313 17636006776235390796715735)
  ·
    refine ⟨26454010164353086195073603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17636006776235390796715735 26454010164353086195073603)
    ·
      refine ⟨39681015246529629292610405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26454010164353086195073603 39681015246529629292610405)
      ·
        refine ⟨7440190358724305492364451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39681015246529629292610405 7440190358724305492364451)
        ·
          refine ⟨11160285538086458238546677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7440190358724305492364451 11160285538086458238546677)
          ·
            refine ⟨1046276769195605459863751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11160285538086458238546677 1046276769195605459863751)
            ·
              refine ⟨1569415153793408189795627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1046276769195605459863751 1569415153793408189795627)
              ·
                refine ⟨2354122730690112284693441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1569415153793408189795627 2354122730690112284693441)
                ·
                  refine ⟨1765592048017584213520081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2354122730690112284693441 1765592048017584213520081)
                  ·
                    refine ⟨1324194036013188160140061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1765592048017584213520081 1324194036013188160140061)
                    ·
                      refine ⟨496572763504945560052523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1324194036013188160140061 496572763504945560052523)
                      ·
                        rfl

theorem cell23_967072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 1, 1, 2, 2, 3].length) (baseStart_967072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_967072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_967072 prefixEnd_967072 := by exact prefixLift 967072
  have htrace : WordTrace (prefixWord ++ tailWord_967072) baseStart_967072 baseEnd_967072 := by
    simpa [prefixWord, tailWord_967072, baseEnd_967072] using wordTrace_append hprefix tailTrace_967072
  have hstable : (prefixWord ++ tailWord_967072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967072).length < 2 ^ (prefixWord ++ tailWord_967072).sum := by decide
  have hdescent : baseEnd_967072 < baseStart_967072 := by decide
  rcases family_descends (prefixWord ++ tailWord_967072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967079 : List Nat := [1, 1, 6, 1, 1, 3, 2, 3, 1, 4]
def baseStart_967079 : Nat := 118140960795 + 967079 * 2 ^ 59
def prefixEnd_967079 : Nat := 4983230072969 + 3 ^ 40 * 967079 * 2
def baseEnd_967079 : Nat := 165525452623175677554997

theorem tailTrace_967079 : CollatzResearch.WordTrace tailWord_967079 prefixEnd_967079 165525452623175677554997 := by
  unfold tailWord_967079
  simp only [CollatzResearch.WordTrace]
  refine ⟨35272268863445421788936291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23514845908963614525957527 35272268863445421788936291)
  ·
    refine ⟨52908403295168132683404437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35272268863445421788936291 52908403295168132683404437)
    ·
      refine ⟨2480081404461006219534583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 52908403295168132683404437 2480081404461006219534583)
      ·
        refine ⟨3720122106691509329301875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2480081404461006219534583 3720122106691509329301875)
        ·
          refine ⟨5580183160037263993952813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3720122106691509329301875 5580183160037263993952813)
          ·
            refine ⟨2092568685013973997732305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5580183160037263993952813 2092568685013973997732305)
            ·
              refine ⟨1569426513760480498299229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2092568685013973997732305 1569426513760480498299229)
              ·
                refine ⟨588534942660180186862211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1569426513760480498299229 588534942660180186862211)
                ·
                  refine ⟨882802413990270280293317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 588534942660180186862211 882802413990270280293317)
                  ·
                    refine ⟨165525452623175677554997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 882802413990270280293317 165525452623175677554997)
                    ·
                      rfl

theorem cell23_967079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2, 3, 1, 4].length) (baseStart_967079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_967079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_967079 prefixEnd_967079 := by exact prefixLift 967079
  have htrace : WordTrace (prefixWord ++ tailWord_967079) baseStart_967079 baseEnd_967079 := by
    simpa [prefixWord, tailWord_967079, baseEnd_967079] using wordTrace_append hprefix tailTrace_967079
  have hstable : (prefixWord ++ tailWord_967079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967079).length < 2 ^ (prefixWord ++ tailWord_967079).sum := by decide
  have hdescent : baseEnd_967079 < baseStart_967079 := by decide
  rcases family_descends (prefixWord ++ tailWord_967079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967102 : List Nat := [4, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3]
def baseStart_967102 : Nat := 118140960795 + 967102 * 2 ^ 59
def prefixEnd_967102 : Nat := 4983230072969 + 3 ^ 40 * 967102 * 2
def baseEnd_967102 : Nat := 496588167924580442677385

theorem tailTrace_967102 : CollatzResearch.WordTrace tailWord_967102 prefixEnd_967102 496588167924580442677385 := by
  unfold tailWord_967102
  simp only [CollatzResearch.WordTrace]
  refine ⟨4409138467795262089627945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23515405161574731144682373 4409138467795262089627945)
  ·
    refine ⟨3306853850846446567220959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4409138467795262089627945 3306853850846446567220959)
    ·
      refine ⟨4960280776269669850831439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3306853850846446567220959 4960280776269669850831439)
      ·
        refine ⟨7440421164404504776247159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4960280776269669850831439 7440421164404504776247159)
        ·
          refine ⟨11160631746606757164370739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7440421164404504776247159 11160631746606757164370739)
          ·
            refine ⟨16740947619910135746556109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11160631746606757164370739 16740947619910135746556109)
            ·
              refine ⟨6277855357466300904958541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16740947619910135746556109 6277855357466300904958541)
              ·
                refine ⟨2354195759049862839359453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6277855357466300904958541 2354195759049862839359453)
                ·
                  refine ⟨882823409643698564759795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2354195759049862839359453 882823409643698564759795)
                  ·
                    refine ⟨1324235114465547847139693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 882823409643698564759795 1324235114465547847139693)
                    ·
                      refine ⟨496588167924580442677385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1324235114465547847139693 496588167924580442677385)
                      ·
                        rfl

theorem cell23_967102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3].length) (baseStart_967102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_967102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_967102 prefixEnd_967102 := by exact prefixLift 967102
  have htrace : WordTrace (prefixWord ++ tailWord_967102) baseStart_967102 baseEnd_967102 := by
    simpa [prefixWord, tailWord_967102, baseEnd_967102] using wordTrace_append hprefix tailTrace_967102
  have hstable : (prefixWord ++ tailWord_967102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967102).length < 2 ^ (prefixWord ++ tailWord_967102).sum := by decide
  have hdescent : baseEnd_967102 < baseStart_967102 := by decide
  rcases family_descends (prefixWord ++ tailWord_967102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967128 : List Nat := [2, 1, 2, 2, 2, 1, 1, 1, 5, 1, 5]
def baseStart_967128 : Nat := 118140960795 + 967128 * 2 ^ 59
def prefixEnd_967128 : Nat := 4983230072969 + 3 ^ 40 * 967128 * 2
def baseEnd_967128 : Nat := 496601518421597340952265

theorem tailTrace_967128 : CollatzResearch.WordTrace tailWord_967128 prefixEnd_967128 496601518421597340952265 := by
  unfold tailWord_967128
  simp only [CollatzResearch.WordTrace]
  refine ⟨17637028020133951578735019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23516037360178602104980025 17637028020133951578735019)
  ·
    refine ⟨26455542030200927368102529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17637028020133951578735019 26455542030200927368102529)
    ·
      refine ⟨19841656522650695526076897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26455542030200927368102529 19841656522650695526076897)
      ·
        refine ⟨14881242391988021644557673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19841656522650695526076897 14881242391988021644557673)
        ·
          refine ⟨11160931793991016233418255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14881242391988021644557673 11160931793991016233418255)
          ·
            refine ⟨16741397690986524350127383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11160931793991016233418255 16741397690986524350127383)
            ·
              refine ⟨25112096536479786525191075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16741397690986524350127383 25112096536479786525191075)
              ·
                refine ⟨37668144804719679787786613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25112096536479786525191075 37668144804719679787786613)
                ·
                  refine ⟨3531388575442469980104995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37668144804719679787786613 3531388575442469980104995)
                  ·
                    refine ⟨5297082863163704970157493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3531388575442469980104995 5297082863163704970157493)
                    ·
                      refine ⟨496601518421597340952265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5297082863163704970157493 496601518421597340952265)
                      ·
                        rfl

theorem cell23_967128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 5, 1, 5].length) (baseStart_967128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_967128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_967128 prefixEnd_967128 := by exact prefixLift 967128
  have htrace : WordTrace (prefixWord ++ tailWord_967128) baseStart_967128 baseEnd_967128 := by
    simpa [prefixWord, tailWord_967128, baseEnd_967128] using wordTrace_append hprefix tailTrace_967128
  have hstable : (prefixWord ++ tailWord_967128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967128).length < 2 ^ (prefixWord ++ tailWord_967128).sum := by decide
  have hdescent : baseEnd_967128 < baseStart_967128 := by decide
  rcases family_descends (prefixWord ++ tailWord_967128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967135 : List Nat := [1, 1, 2, 3, 3, 2, 1, 2, 4, 4]
def baseStart_967135 : Nat := 118140960795 + 967135 * 2 ^ 59
def prefixEnd_967135 : Nat := 4983230072969 + 3 ^ 40 * 967135 * 2
def baseEnd_967135 : Nat := 165535037595392937854911

theorem tailTrace_967135 : CollatzResearch.WordTrace tailWord_967135 prefixEnd_967135 165535037595392937854911 := by
  unfold tailWord_967135
  simp only [CollatzResearch.WordTrace]
  refine ⟨35274311351242543352974859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23516207567495028901983239 35274311351242543352974859)
  ·
    refine ⟨52911467026863815029462289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35274311351242543352974859 52911467026863815029462289)
    ·
      refine ⟨39683600270147861272096717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52911467026863815029462289 39683600270147861272096717)
      ·
        refine ⟨14881350101305447977036269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39683600270147861272096717 14881350101305447977036269)
        ·
          refine ⟨5580506287989542991388601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14881350101305447977036269 5580506287989542991388601)
          ·
            refine ⟨4185379715992157243541451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5580506287989542991388601 4185379715992157243541451)
            ·
              refine ⟨6278069573988235865312177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4185379715992157243541451 6278069573988235865312177)
              ·
                refine ⟨4708552180491176898984133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6278069573988235865312177 4708552180491176898984133)
                ·
                  refine ⟨882853533842095668559525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4708552180491176898984133 882853533842095668559525)
                  ·
                    refine ⟨165535037595392937854911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 882853533842095668559525 165535037595392937854911)
                    ·
                      rfl

theorem cell23_967135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 2, 4, 4].length) (baseStart_967135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_967135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_967135 prefixEnd_967135 := by exact prefixLift 967135
  have htrace : WordTrace (prefixWord ++ tailWord_967135) baseStart_967135 baseEnd_967135 := by
    simpa [prefixWord, tailWord_967135, baseEnd_967135] using wordTrace_append hprefix tailTrace_967135
  have hstable : (prefixWord ++ tailWord_967135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967135).length < 2 ^ (prefixWord ++ tailWord_967135).sum := by decide
  have hdescent : baseEnd_967135 < baseStart_967135 := by decide
  rcases family_descends (prefixWord ++ tailWord_967135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967169 : List Nat := [1, 2, 4, 1, 3, 1, 4, 1, 2, 4]
def baseStart_967169 : Nat := 118140960795 + 967169 * 2 ^ 59
def prefixEnd_967169 : Nat := 4983230072969 + 3 ^ 40 * 967169 * 2
def baseEnd_967169 : Nat := 165540857042810560179859

theorem tailTrace_967169 : CollatzResearch.WordTrace tailWord_967169 prefixEnd_967169 165540857042810560179859 := by
  unfold tailWord_967169
  simp only [CollatzResearch.WordTrace]
  refine ⟨35275551433119367159712561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23517034288746244773141707 35275551433119367159712561)
  ·
    refine ⟨26456663574839525369784421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35275551433119367159712561 26456663574839525369784421)
    ·
      refine ⟨4960624420282411006834579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26456663574839525369784421 4960624420282411006834579)
      ·
        refine ⟨7440936630423616510251869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4960624420282411006834579 7440936630423616510251869)
        ·
          refine ⟨2790351236408856191344451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7440936630423616510251869 2790351236408856191344451)
          ·
            refine ⟨4185526854613284287016677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2790351236408856191344451 4185526854613284287016677)
            ·
              refine ⟨784786285239990803815627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4185526854613284287016677 784786285239990803815627)
              ·
                refine ⟨1177179427859986205723441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 784786285239990803815627 1177179427859986205723441)
                ·
                  refine ⟨882884570894989654292581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1177179427859986205723441 882884570894989654292581)
                  ·
                    refine ⟨165540857042810560179859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 882884570894989654292581 165540857042810560179859)
                    ·
                      rfl

theorem cell23_967169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 4, 1, 2, 4].length) (baseStart_967169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_967169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_967169 prefixEnd_967169 := by exact prefixLift 967169
  have htrace : WordTrace (prefixWord ++ tailWord_967169) baseStart_967169 baseEnd_967169 := by
    simpa [prefixWord, tailWord_967169, baseEnd_967169] using wordTrace_append hprefix tailTrace_967169
  have hstable : (prefixWord ++ tailWord_967169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967169).length < 2 ^ (prefixWord ++ tailWord_967169).sum := by decide
  have hdescent : baseEnd_967169 < baseStart_967169 := by decide
  rcases family_descends (prefixWord ++ tailWord_967169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967179 : List Nat := [1, 1, 1, 1, 7, 3, 1, 2, 1, 2, 3]
def baseStart_967179 : Nat := 118140960795 + 967179 * 2 ^ 59
def prefixEnd_967179 : Nat := 4983230072969 + 3 ^ 40 * 967179 * 2
def baseEnd_967179 : Nat := 496627705934976641414531

theorem tailTrace_967179 : CollatzResearch.WordTrace tailWord_967179 prefixEnd_967179 496627705934976641414531 := by
  unfold tailWord_967179
  simp only [CollatzResearch.WordTrace]
  refine ⟨35275916163083138867576591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23517277442055425911717727 35275916163083138867576591)
  ·
    refine ⟨52913874244624708301364887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35275916163083138867576591 52913874244624708301364887)
    ·
      refine ⟨79370811366937062452047331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52913874244624708301364887 79370811366937062452047331)
      ·
        refine ⟨119056217050405593678070997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79370811366937062452047331 119056217050405593678070997)
        ·
          refine ⟨2790380087118881101829789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 119056217050405593678070997 2790380087118881101829789)
          ·
            refine ⟨1046392532669580413186171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2790380087118881101829789 1046392532669580413186171)
            ·
              refine ⟨1569588799004370619779257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1046392532669580413186171 1569588799004370619779257)
              ·
                refine ⟨1177191599253277964834443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1569588799004370619779257 1177191599253277964834443)
                ·
                  refine ⟨1765787398879916947251665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1177191599253277964834443 1765787398879916947251665)
                  ·
                    refine ⟨1324340549159937710438749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1765787398879916947251665 1324340549159937710438749)
                    ·
                      refine ⟨496627705934976641414531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1324340549159937710438749 496627705934976641414531)
                      ·
                        rfl

theorem cell23_967179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 1, 2, 1, 2, 3].length) (baseStart_967179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_967179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_967179 prefixEnd_967179 := by exact prefixLift 967179
  have htrace : WordTrace (prefixWord ++ tailWord_967179) baseStart_967179 baseEnd_967179 := by
    simpa [prefixWord, tailWord_967179, baseEnd_967179] using wordTrace_append hprefix tailTrace_967179
  have hstable : (prefixWord ++ tailWord_967179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967179).length < 2 ^ (prefixWord ++ tailWord_967179).sum := by decide
  have hdescent : baseEnd_967179 < baseStart_967179 := by decide
  rcases family_descends (prefixWord ++ tailWord_967179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967192 : List Nat := [2, 1, 2, 3, 3, 2, 1, 2, 1, 3, 3]
def baseStart_967192 : Nat := 118140960795 + 967192 * 2 ^ 59
def prefixEnd_967192 : Nat := 4983230072969 + 3 ^ 40 * 967192 * 2
def baseEnd_967192 : Nat := 496634381183485090551971

theorem tailTrace_967192 : CollatzResearch.WordTrace tailWord_967192 prefixEnd_967192 496634381183485090551971 := by
  unfold tailWord_967192
  simp only [CollatzResearch.WordTrace]
  refine ⟨17638195156018021043899915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23517593541357361391866553 17638195156018021043899915)
  ·
    refine ⟨26457292734027031565849873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17638195156018021043899915 26457292734027031565849873)
    ·
      refine ⟨19842969550520273674387405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26457292734027031565849873 19842969550520273674387405)
      ·
        refine ⟨7441113581445102627895277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19842969550520273674387405 7441113581445102627895277)
        ·
          refine ⟨2790417593041913485460729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7441113581445102627895277 2790417593041913485460729)
          ·
            refine ⟨2092813194781435114095547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2790417593041913485460729 2092813194781435114095547)
            ·
              refine ⟨3139219792172152671143321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2092813194781435114095547 3139219792172152671143321)
              ·
                refine ⟨2354414844129114503357491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3139219792172152671143321 2354414844129114503357491)
                ·
                  refine ⟨3531622266193671755036237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2354414844129114503357491 3531622266193671755036237)
                  ·
                    refine ⟨1324358349822626908138589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3531622266193671755036237 1324358349822626908138589)
                    ·
                      refine ⟨496634381183485090551971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1324358349822626908138589 496634381183485090551971)
                      ·
                        rfl

theorem cell23_967192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 2, 1, 3, 3].length) (baseStart_967192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_967192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_967192 prefixEnd_967192 := by exact prefixLift 967192
  have htrace : WordTrace (prefixWord ++ tailWord_967192) baseStart_967192 baseEnd_967192 := by
    simpa [prefixWord, tailWord_967192, baseEnd_967192] using wordTrace_append hprefix tailTrace_967192
  have hstable : (prefixWord ++ tailWord_967192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967192).length < 2 ^ (prefixWord ++ tailWord_967192).sum := by decide
  have hdescent : baseEnd_967192 < baseStart_967192 := by decide
  rcases family_descends (prefixWord ++ tailWord_967192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967210 : List Nat := [3, 1, 4, 1, 1, 4, 2, 2, 1, 2, 2]
def baseStart_967210 : Nat := 118140960795 + 967210 * 2 ^ 59
def prefixEnd_967210 : Nat := 4983230072969 + 3 ^ 40 * 967210 * 2
def baseEnd_967210 : Nat := 496643623835266020126889

theorem tailTrace_967210 : CollatzResearch.WordTrace tailWord_967210 prefixEnd_967210 496643623835266020126889 := by
  unfold tailWord_967210
  simp only [CollatzResearch.WordTrace]
  refine ⟨8819261706492707790488771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23518031217313887441303389 8819261706492707790488771)
  ·
    refine ⟨13228892559739061685733157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8819261706492707790488771 13228892559739061685733157)
    ·
      refine ⟨2480417354951074066074967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13228892559739061685733157 2480417354951074066074967)
      ·
        refine ⟨3720626032426611099112451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2480417354951074066074967 3720626032426611099112451)
        ·
          refine ⟨5580939048639916648668677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3720626032426611099112451 5580939048639916648668677)
          ·
            refine ⟨1046426071619984371625377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5580939048639916648668677 1046426071619984371625377)
            ·
              refine ⟨784819553714988278719033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1046426071619984371625377 784819553714988278719033)
              ·
                refine ⟨588614665286241209039275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 784819553714988278719033 588614665286241209039275)
                ·
                  refine ⟨882921997929361813558913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 588614665286241209039275 882921997929361813558913)
                  ·
                    refine ⟨662191498447021360169185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 882921997929361813558913 662191498447021360169185)
                    ·
                      refine ⟨496643623835266020126889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 662191498447021360169185 496643623835266020126889)
                      ·
                        rfl

theorem cell23_967210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 2, 2, 1, 2, 2].length) (baseStart_967210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_967210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_967210 prefixEnd_967210 := by exact prefixLift 967210
  have htrace : WordTrace (prefixWord ++ tailWord_967210) baseStart_967210 baseEnd_967210 := by
    simpa [prefixWord, tailWord_967210, baseEnd_967210] using wordTrace_append hprefix tailTrace_967210
  have hstable : (prefixWord ++ tailWord_967210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967210).length < 2 ^ (prefixWord ++ tailWord_967210).sum := by decide
  have hdescent : baseEnd_967210 < baseStart_967210 := by decide
  rcases family_descends (prefixWord ++ tailWord_967210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967225 : List Nat := [1, 2, 1, 5, 1, 1, 3, 1, 2, 6]
def baseStart_967225 : Nat := 118140960795 + 967225 * 2 ^ 59
def prefixEnd_967225 : Nat := 4983230072969 + 3 ^ 40 * 967225 * 2
def baseEnd_967225 : Nat := 165550442015027820479773

theorem tailTrace_967225 : CollatzResearch.WordTrace tailWord_967225 prefixEnd_967225 165550442015027820479773 := by
  unfold tailWord_967225
  simp only [CollatzResearch.WordTrace]
  refine ⟨35277593920916488723751129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23518395947277659149167419 35277593920916488723751129)
  ·
    refine ⟨26458195440687366542813347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35277593920916488723751129 26458195440687366542813347)
    ·
      refine ⟨39687293161031049814220021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26458195440687366542813347 39687293161031049814220021)
      ·
        refine ⟨3720683733846660920083127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39687293161031049814220021 3720683733846660920083127)
        ·
          refine ⟨5581025600769991380124691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3720683733846660920083127 5581025600769991380124691)
          ·
            refine ⟨8371538401154987070187037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5581025600769991380124691 8371538401154987070187037)
            ·
              refine ⟨3139326900433120151320139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8371538401154987070187037 3139326900433120151320139)
              ·
                refine ⟨4708990350649680226980209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3139326900433120151320139 4708990350649680226980209)
                ·
                  refine ⟨3531742762987260170235157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4708990350649680226980209 3531742762987260170235157)
                  ·
                    refine ⟨165550442015027820479773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3531742762987260170235157 165550442015027820479773)
                    ·
                      rfl

theorem cell23_967225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 1, 2, 6].length) (baseStart_967225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_967225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_967225 prefixEnd_967225 := by exact prefixLift 967225
  have htrace : WordTrace (prefixWord ++ tailWord_967225) baseStart_967225 baseEnd_967225 := by
    simpa [prefixWord, tailWord_967225, baseEnd_967225] using wordTrace_append hprefix tailTrace_967225
  have hstable : (prefixWord ++ tailWord_967225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967225).length < 2 ^ (prefixWord ++ tailWord_967225).sum := by decide
  have hdescent : baseEnd_967225 < baseStart_967225 := by decide
  rcases family_descends (prefixWord ++ tailWord_967225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967232 : List Nat := [2, 1, 1, 2, 2, 2, 3, 3, 1, 4, 2]
def baseStart_967232 : Nat := 118140960795 + 967232 * 2 ^ 59
def prefixEnd_967232 : Nat := 4983230072969 + 3 ^ 40 * 967232 * 2
def baseEnd_967232 : Nat := 496654920409664934051787

theorem tailTrace_967232 : CollatzResearch.WordTrace tailWord_967232 prefixEnd_967232 496654920409664934051787 := by
  unfold tailWord_967232
  simp only [CollatzResearch.WordTrace]
  refine ⟨17638924615945564459627975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23518566154594085946170633 17638924615945564459627975)
  ·
    refine ⟨26458386923918346689441963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17638924615945564459627975 26458386923918346689441963)
    ·
      refine ⟨39687580385877520034162945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26458386923918346689441963 39687580385877520034162945)
      ·
        refine ⟨29765685289408140025622209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39687580385877520034162945 29765685289408140025622209)
        ·
          refine ⟨22324263967056105019216657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29765685289408140025622209 22324263967056105019216657)
          ·
            refine ⟨16743197975292078764412493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22324263967056105019216657 16743197975292078764412493)
            ·
              refine ⟨6278699240734529536654685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16743197975292078764412493 6278699240734529536654685)
              ·
                refine ⟨2354512215275448576245507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6278699240734529536654685 2354512215275448576245507)
                ·
                  refine ⟨3531768322913172864368261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2354512215275448576245507 3531768322913172864368261)
                  ·
                    refine ⟨662206560546219912069049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3531768322913172864368261 662206560546219912069049)
                    ·
                      refine ⟨496654920409664934051787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 662206560546219912069049 496654920409664934051787)
                      ·
                        rfl

theorem cell23_967232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 3, 1, 4, 2].length) (baseStart_967232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_967232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_967232 prefixEnd_967232 := by exact prefixLift 967232
  have htrace : WordTrace (prefixWord ++ tailWord_967232) baseStart_967232 baseEnd_967232 := by
    simpa [prefixWord, tailWord_967232, baseEnd_967232] using wordTrace_append hprefix tailTrace_967232
  have hstable : (prefixWord ++ tailWord_967232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967232).length < 2 ^ (prefixWord ++ tailWord_967232).sum := by decide
  have hdescent : baseEnd_967232 < baseStart_967232 := by decide
  rcases family_descends (prefixWord ++ tailWord_967232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967292 : List Nat := [2, 2, 2, 1, 1, 2, 2, 2, 2, 5, 2]
def baseStart_967292 : Nat := 118140960795 + 967292 * 2 ^ 59
def prefixEnd_967292 : Nat := 4983230072969 + 3 ^ 40 * 967292 * 2
def baseEnd_967292 : Nat := 496685729248934699301511

theorem tailTrace_967292 : CollatzResearch.WordTrace tailWord_967292 prefixEnd_967292 496685729248934699301511 := by
  unfold tailWord_967292
  simp only [CollatzResearch.WordTrace]
  refine ⟨17640018805836879583220065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23520025074449172777626753 17640018805836879583220065)
  ·
    refine ⟨13230014104377659687415049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17640018805836879583220065 13230014104377659687415049)
    ·
      refine ⟨9922510578283244765561287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13230014104377659687415049 9922510578283244765561287)
      ·
        refine ⟨14883765867424867148341931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9922510578283244765561287 14883765867424867148341931)
        ·
          refine ⟨22325648801137300722512897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14883765867424867148341931 22325648801137300722512897)
          ·
            refine ⟨16744236600852975541884673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22325648801137300722512897 16744236600852975541884673)
            ·
              refine ⟨12558177450639731656413505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16744236600852975541884673 12558177450639731656413505)
              ·
                refine ⟨9418633087979798742310129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12558177450639731656413505 9418633087979798742310129)
                ·
                  refine ⟨7063974815984849056732597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9418633087979798742310129 7063974815984849056732597)
                  ·
                    refine ⟨662247638998579599068681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7063974815984849056732597 662247638998579599068681)
                    ·
                      refine ⟨496685729248934699301511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 662247638998579599068681 496685729248934699301511)
                      ·
                        rfl

theorem cell23_967292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 2, 5, 2].length) (baseStart_967292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_967292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_967292 prefixEnd_967292 := by exact prefixLift 967292
  have htrace : WordTrace (prefixWord ++ tailWord_967292) baseStart_967292 baseEnd_967292 := by
    simpa [prefixWord, tailWord_967292, baseEnd_967292] using wordTrace_append hprefix tailTrace_967292
  have hstable : (prefixWord ++ tailWord_967292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967292).length < 2 ^ (prefixWord ++ tailWord_967292).sum := by decide
  have hdescent : baseEnd_967292 < baseStart_967292 := by decide
  rcases family_descends (prefixWord ++ tailWord_967292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967306 : List Nat := [3, 1, 2, 3, 3, 2, 1, 3, 5]
def baseStart_967306 : Nat := 118140960795 + 967306 * 2 ^ 59
def prefixEnd_967306 : Nat := 4983230072969 + 3 ^ 40 * 967306 * 2
def baseEnd_967306 : Nat := 55188101997566404947383

theorem tailTrace_967306 : CollatzResearch.WordTrace tailWord_967306 prefixEnd_967306 55188101997566404947383 := by
  unfold tailWord_967306
  simp only [CollatzResearch.WordTrace]
  refine ⟨8820137058405759889362443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23520365489082026371633181 8820137058405759889362443)
  ·
    refine ⟨13230205587608639834043665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8820137058405759889362443 13230205587608639834043665)
    ·
      refine ⟨9922654190706479875532749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13230205587608639834043665 9922654190706479875532749)
      ·
        refine ⟨3720995321514929953324781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9922654190706479875532749 3720995321514929953324781)
        ·
          refine ⟨1395373245568098732496793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3720995321514929953324781 1395373245568098732496793)
          ·
            refine ⟨1046529934176074049372595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1395373245568098732496793 1046529934176074049372595)
            ·
              refine ⟨1569794901264111074058893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1046529934176074049372595 1569794901264111074058893)
              ·
                refine ⟨588673087974041652772085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1569794901264111074058893 588673087974041652772085)
                ·
                  refine ⟨55188101997566404947383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 588673087974041652772085 55188101997566404947383)
                  ·
                    rfl

theorem cell23_967306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 1, 3, 5].length) (baseStart_967306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_967306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_967306 prefixEnd_967306 := by exact prefixLift 967306
  have htrace : WordTrace (prefixWord ++ tailWord_967306) baseStart_967306 baseEnd_967306 := by
    simpa [prefixWord, tailWord_967306, baseEnd_967306] using wordTrace_append hprefix tailTrace_967306
  have hstable : (prefixWord ++ tailWord_967306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967306).length < 2 ^ (prefixWord ++ tailWord_967306).sum := by decide
  have hdescent : baseEnd_967306 < baseStart_967306 := by decide
  rcases family_descends (prefixWord ++ tailWord_967306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967359 : List Nat := [1, 1, 2, 2, 2, 5, 2, 1, 2, 2, 3]
def baseStart_967359 : Nat := 118140960795 + 967359 * 2 ^ 59
def prefixEnd_967359 : Nat := 4983230072969 + 3 ^ 40 * 967359 * 2
def baseEnd_967359 : Nat := 496720132452785937163703

theorem tailTrace_967359 : CollatzResearch.WordTrace tailWord_967359 prefixEnd_967359 496720132452785937163703 := by
  unfold tailWord_967359
  simp only [CollatzResearch.WordTrace]
  refine ⟨35282481302431029609129131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23521654201620686406086087 35282481302431029609129131)
  ·
    refine ⟨52923721953646544413693697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35282481302431029609129131 52923721953646544413693697)
    ·
      refine ⟨39692791465234908310270273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52923721953646544413693697 39692791465234908310270273)
      ·
        refine ⟨29769593598926181232702705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39692791465234908310270273 29769593598926181232702705)
        ·
          refine ⟨22327195199194635924527029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29769593598926181232702705 22327195199194635924527029)
          ·
            refine ⟨2093174549924497117924409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22327195199194635924527029 2093174549924497117924409)
            ·
              refine ⟨1569880912443372838443307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2093174549924497117924409 1569880912443372838443307)
              ·
                refine ⟨2354821368665059257664961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1569880912443372838443307 2354821368665059257664961)
                ·
                  refine ⟨1766116026498794443248721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2354821368665059257664961 1766116026498794443248721)
                  ·
                    refine ⟨1324587019874095832436541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1766116026498794443248721 1324587019874095832436541)
                    ·
                      refine ⟨496720132452785937163703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1324587019874095832436541 496720132452785937163703)
                      ·
                        rfl

theorem cell23_967359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2, 1, 2, 2, 3].length) (baseStart_967359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_967359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_967359 prefixEnd_967359 := by exact prefixLift 967359
  have htrace : WordTrace (prefixWord ++ tailWord_967359) baseStart_967359 baseEnd_967359 := by
    simpa [prefixWord, tailWord_967359, baseEnd_967359] using wordTrace_append hprefix tailTrace_967359
  have hstable : (prefixWord ++ tailWord_967359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967359).length < 2 ^ (prefixWord ++ tailWord_967359).sum := by decide
  have hdescent : baseEnd_967359 < baseStart_967359 := by decide
  rcases family_descends (prefixWord ++ tailWord_967359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967383 : List Nat := [1, 1, 3, 2, 1, 6, 2, 2, 1, 4]
def baseStart_967383 : Nat := 118140960795 + 967383 * 2 ^ 59
def prefixEnd_967383 : Nat := 4983230072969 + 3 ^ 40 * 967383 * 2
def baseEnd_967383 : Nat := 165577485329497947754531

theorem tailTrace_967383 : CollatzResearch.WordTrace tailWord_967383 prefixEnd_967383 165577485329497947754531 := by
  unfold tailWord_967383
  simp only [CollatzResearch.WordTrace]
  refine ⟨35283356654344081708002803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23522237769562721138668535 35283356654344081708002803)
  ·
    refine ⟨52925034981516122562004205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35283356654344081708002803 52925034981516122562004205)
    ·
      refine ⟨19846888118068545960751577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52925034981516122562004205 19846888118068545960751577)
      ·
        refine ⟨14885166088551409470563683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19846888118068545960751577 14885166088551409470563683)
        ·
          refine ⟨22327749132827114205845525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14885166088551409470563683 22327749132827114205845525)
          ·
            refine ⟨1046613240601270978399009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 22327749132827114205845525 1046613240601270978399009)
            ·
              refine ⟨784959930450953233799257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1046613240601270978399009 784959930450953233799257)
              ·
                refine ⟨588719947838214925349443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 784959930450953233799257 588719947838214925349443)
                ·
                  refine ⟨883079921757322388024165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 588719947838214925349443 883079921757322388024165)
                  ·
                    refine ⟨165577485329497947754531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 883079921757322388024165 165577485329497947754531)
                    ·
                      rfl

theorem cell23_967383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 2, 2, 1, 4].length) (baseStart_967383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_967383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_967383 prefixEnd_967383 := by exact prefixLift 967383
  have htrace : WordTrace (prefixWord ++ tailWord_967383) baseStart_967383 baseEnd_967383 := by
    simpa [prefixWord, tailWord_967383, baseEnd_967383] using wordTrace_append hprefix tailTrace_967383
  have hstable : (prefixWord ++ tailWord_967383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967383).length < 2 ^ (prefixWord ++ tailWord_967383).sum := by decide
  have hdescent : baseEnd_967383 < baseStart_967383 := by decide
  rcases family_descends (prefixWord ++ tailWord_967383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967406 : List Nat := [4, 1, 2, 1, 1, 4, 1, 2, 3, 1, 3]
def baseStart_967406 : Nat := 118140960795 + 967406 * 2 ^ 59
def prefixEnd_967406 : Nat := 4983230072969 + 3 ^ 40 * 967406 * 2
def baseEnd_967406 : Nat := 496744266043547253275987

theorem tailTrace_967406 : CollatzResearch.WordTrace tailWord_967406 prefixEnd_967406 496744266043547253275987 := by
  unfold tailWord_967406
  simp only [CollatzResearch.WordTrace]
  refine ⟨4410524441657594579511259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23522797022173837757393381 4410524441657594579511259)
  ·
    refine ⟨6615786662486391869266889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4410524441657594579511259 6615786662486391869266889)
    ·
      refine ⟨4961839996864793901950167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6615786662486391869266889 4961839996864793901950167)
      ·
        refine ⟨7442759995297190852925251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4961839996864793901950167 7442759995297190852925251)
        ·
          refine ⟨11164139992945786279387877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7442759995297190852925251 11164139992945786279387877)
          ·
            refine ⟨2093276248677334927385227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11164139992945786279387877 2093276248677334927385227)
            ·
              refine ⟨3139914373016002391077841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2093276248677334927385227 3139914373016002391077841)
              ·
                refine ⟨2354935779762001793308381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3139914373016002391077841 2354935779762001793308381)
                ·
                  refine ⟨883100917410750672490643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2354935779762001793308381 883100917410750672490643)
                  ·
                    refine ⟨1324651376116126008735965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 883100917410750672490643 1324651376116126008735965)
                    ·
                      refine ⟨496744266043547253275987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1324651376116126008735965 496744266043547253275987)
                      ·
                        rfl

theorem cell23_967406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 2, 3, 1, 3].length) (baseStart_967406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_967406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_967406 prefixEnd_967406 := by exact prefixLift 967406
  have htrace : WordTrace (prefixWord ++ tailWord_967406) baseStart_967406 baseEnd_967406 := by
    simpa [prefixWord, tailWord_967406, baseEnd_967406] using wordTrace_append hprefix tailTrace_967406
  have hstable : (prefixWord ++ tailWord_967406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967406).length < 2 ^ (prefixWord ++ tailWord_967406).sum := by decide
  have hdescent : baseEnd_967406 < baseStart_967406 := by decide
  rcases family_descends (prefixWord ++ tailWord_967406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967426 : List Nat := [3, 4, 1, 1, 1, 3, 1, 3, 1, 5]
def baseStart_967426 : Nat := 118140960795 + 967426 * 2 ^ 59
def prefixEnd_967426 : Nat := 4983230072969 + 3 ^ 40 * 967426 * 2
def baseEnd_967426 : Nat := 165584845218879058341965

theorem tailTrace_967426 : CollatzResearch.WordTrace tailWord_967426 prefixEnd_967426 165584845218879058341965 := by
  unfold tailWord_967426
  simp only [CollatzResearch.WordTrace]
  refine ⟨8821231248297075012954533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23523283328792200034545421 8821231248297075012954533)
  ·
    refine ⟨1653980859055701564928975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8821231248297075012954533 1653980859055701564928975)
    ·
      refine ⟨2480971288583552347393463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1653980859055701564928975 2480971288583552347393463)
      ·
        refine ⟨3721456932875328521090195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2480971288583552347393463 3721456932875328521090195)
        ·
          refine ⟨5582185399312992781635293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3721456932875328521090195 5582185399312992781635293)
          ·
            refine ⟨2093319524742372293113235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5582185399312992781635293 2093319524742372293113235)
            ·
              refine ⟨3139979287113558439669853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2093319524742372293113235 3139979287113558439669853)
              ·
                refine ⟨1177492232667584414876195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3139979287113558439669853 1177492232667584414876195)
                ·
                  refine ⟨1766238349001376622314293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1177492232667584414876195 1766238349001376622314293)
                  ·
                    refine ⟨165584845218879058341965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1766238349001376622314293 165584845218879058341965)
                    ·
                      rfl

theorem cell23_967426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 3, 1, 5].length) (baseStart_967426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_967426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_967426 prefixEnd_967426 := by exact prefixLift 967426
  have htrace : WordTrace (prefixWord ++ tailWord_967426) baseStart_967426 baseEnd_967426 := by
    simpa [prefixWord, tailWord_967426, baseEnd_967426] using wordTrace_append hprefix tailTrace_967426
  have hstable : (prefixWord ++ tailWord_967426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967426).length < 2 ^ (prefixWord ++ tailWord_967426).sum := by decide
  have hdescent : baseEnd_967426 < baseStart_967426 := by decide
  rcases family_descends (prefixWord ++ tailWord_967426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967479 : List Nat := [1, 1, 3, 1, 2, 1, 3, 1, 6, 1, 3]
def baseStart_967479 : Nat := 118140960795 + 967479 * 2 ^ 59
def prefixEnd_967479 : Nat := 4983230072969 + 3 ^ 40 * 967479 * 2
def baseEnd_967479 : Nat := 496781750131325467663151

theorem tailTrace_967479 : CollatzResearch.WordTrace tailWord_967479 prefixEnd_967479 496781750131325467663151 := by
  unfold tailWord_967479
  simp only [CollatzResearch.WordTrace]
  refine ⟨35286858061996290103497491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23524572041330860068998327 35286858061996290103497491)
  ·
    refine ⟨52930287092994435155246237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35286858061996290103497491 52930287092994435155246237)
    ·
      refine ⟨19848857659872913183217339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52930287092994435155246237 19848857659872913183217339)
      ·
        refine ⟨29773286489809369774826009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19848857659872913183217339 29773286489809369774826009)
        ·
          refine ⟨22329964867357027331119507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29773286489809369774826009 22329964867357027331119507)
          ·
            refine ⟨33494947301035540996679261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22329964867357027331119507 33494947301035540996679261)
            ·
              refine ⟨12560605237888327873754723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33494947301035540996679261 12560605237888327873754723)
              ·
                refine ⟨18840907856832491810632085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12560605237888327873754723 18840907856832491810632085)
                ·
                  refine ⟨883167555789023053623379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 18840907856832491810632085 883167555789023053623379)
                  ·
                    refine ⟨1324751333683534580435069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 883167555789023053623379 1324751333683534580435069)
                    ·
                      refine ⟨496781750131325467663151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1324751333683534580435069 496781750131325467663151)
                      ·
                        rfl

theorem cell23_967479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 6, 1, 3].length) (baseStart_967479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_967479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_967479 prefixEnd_967479 := by exact prefixLift 967479
  have htrace : WordTrace (prefixWord ++ tailWord_967479) baseStart_967479 baseEnd_967479 := by
    simpa [prefixWord, tailWord_967479, baseEnd_967479] using wordTrace_append hprefix tailTrace_967479
  have hstable : (prefixWord ++ tailWord_967479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967479).length < 2 ^ (prefixWord ++ tailWord_967479).sum := by decide
  have hdescent : baseEnd_967479 < baseStart_967479 := by decide
  rcases family_descends (prefixWord ++ tailWord_967479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967486 : List Nat := [4, 2, 1, 2, 4, 1, 9]
def baseStart_967486 : Nat := 118140960795 + 967486 * 2 ^ 59
def prefixEnd_967486 : Nat := 4983230072969 + 3 ^ 40 * 967486 * 2
def baseEnd_967486 : Nat := 6133152401184036299699

theorem tailTrace_967486 : CollatzResearch.WordTrace tailWord_967486 prefixEnd_967486 6133152401184036299699 := by
  unfold tailWord_967486
  simp only [CollatzResearch.WordTrace]
  refine ⟨4410889171621366287375289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23524742248647286866001541 4410889171621366287375289)
  ·
    refine ⟨3308166878716024715531467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4410889171621366287375289 3308166878716024715531467)
    ·
      refine ⟨4962250318074037073297201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3308166878716024715531467 4962250318074037073297201)
      ·
        refine ⟨3721687738555527804972901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4962250318074037073297201 3721687738555527804972901)
        ·
          refine ⟨697816450979161463432419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3721687738555527804972901 697816450979161463432419)
          ·
            refine ⟨1046724676468742195148629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 697816450979161463432419 1046724676468742195148629)
            ·
              refine ⟨6133152401184036299699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1046724676468742195148629 6133152401184036299699)
              ·
                rfl

theorem cell23_967486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 9].length) (baseStart_967486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_967486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_967486 prefixEnd_967486 := by exact prefixLift 967486
  have htrace : WordTrace (prefixWord ++ tailWord_967486) baseStart_967486 baseEnd_967486 := by
    simpa [prefixWord, tailWord_967486, baseEnd_967486] using wordTrace_append hprefix tailTrace_967486
  have hstable : (prefixWord ++ tailWord_967486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967486).length < 2 ^ (prefixWord ++ tailWord_967486).sum := by decide
  have hdescent : baseEnd_967486 < baseStart_967486 := by decide
  rcases family_descends (prefixWord ++ tailWord_967486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967496 : List Nat := [2, 1, 3, 1, 1, 3, 2, 4, 2, 1, 3]
def baseStart_967496 : Nat := 118140960795 + 967496 * 2 ^ 59
def prefixEnd_967496 : Nat := 4983230072969 + 3 ^ 40 * 967496 * 2
def baseEnd_967496 : Nat := 496790479302451901150573

theorem tailTrace_967496 : CollatzResearch.WordTrace tailWord_967496 prefixEnd_967496 496790479302451901150573 := by
  unfold tailWord_967496
  simp only [CollatzResearch.WordTrace]
  refine ⟨17643739051467351003433171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23524985401956468004577561 17643739051467351003433171)
  ·
    refine ⟨26465608577201026505149757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17643739051467351003433171 26465608577201026505149757)
    ·
      refine ⟨9924603216450384939431159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26465608577201026505149757 9924603216450384939431159)
      ·
        refine ⟨14886904824675577409146739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9924603216450384939431159 14886904824675577409146739)
        ·
          refine ⟨22330357237013366113720109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14886904824675577409146739 22330357237013366113720109)
          ·
            refine ⟨8373883963880012292645041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22330357237013366113720109 8373883963880012292645041)
            ·
              refine ⟨6280412972910009219483781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8373883963880012292645041 6280412972910009219483781)
              ·
                refine ⟨1177577432420626728653209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6280412972910009219483781 1177577432420626728653209)
                ·
                  refine ⟨883183074315470046489907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1177577432420626728653209 883183074315470046489907)
                  ·
                    refine ⟨1324774611473205069734861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 883183074315470046489907 1324774611473205069734861)
                    ·
                      refine ⟨496790479302451901150573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1324774611473205069734861 496790479302451901150573)
                      ·
                        rfl

theorem cell23_967496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 4, 2, 1, 3].length) (baseStart_967496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_967496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_967496 prefixEnd_967496 := by exact prefixLift 967496
  have htrace : WordTrace (prefixWord ++ tailWord_967496) baseStart_967496 baseEnd_967496 := by
    simpa [prefixWord, tailWord_967496, baseEnd_967496] using wordTrace_append hprefix tailTrace_967496
  have hstable : (prefixWord ++ tailWord_967496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967496).length < 2 ^ (prefixWord ++ tailWord_967496).sum := by decide
  have hdescent : baseEnd_967496 < baseStart_967496 := by decide
  rcases family_descends (prefixWord ++ tailWord_967496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967506 : List Nat := [3, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2]
def baseStart_967506 : Nat := 118140960795 + 967506 * 2 ^ 59
def prefixEnd_967506 : Nat := 4983230072969 + 3 ^ 40 * 967506 * 2
def baseEnd_967506 : Nat := 496795614108996862025527

theorem tailTrace_967506 : CollatzResearch.WordTrace tailWord_967506 prefixEnd_967506 496795614108996862025527 := by
  unfold tailWord_967506
  simp only [CollatzResearch.WordTrace]
  refine ⟨8821960708224618428682593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23525228555265649143153581 8821960708224618428682593)
  ·
    refine ⟨6616470531168463821511945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8821960708224618428682593 6616470531168463821511945)
    ·
      refine ⟨4962352898376347866133959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6616470531168463821511945 4962352898376347866133959)
      ·
        refine ⟨7443529347564521799200939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4962352898376347866133959 7443529347564521799200939)
        ·
          refine ⟨11165294021346782698801409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7443529347564521799200939 11165294021346782698801409)
          ·
            refine ⟨8373970516010087024101057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11165294021346782698801409 8373970516010087024101057)
            ·
              refine ⟨6280477887007565268075793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8373970516010087024101057 6280477887007565268075793)
              ·
                refine ⟨4710358415255673951056845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6280477887007565268075793 4710358415255673951056845)
                ·
                  refine ⟨1766384405720877731646317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4710358415255673951056845 1766384405720877731646317)
                  ·
                    refine ⟨662394152145329149367369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1766384405720877731646317 662394152145329149367369)
                    ·
                      refine ⟨496795614108996862025527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 662394152145329149367369 496795614108996862025527)
                      ·
                        rfl

theorem cell23_967506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2].length) (baseStart_967506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_967506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_967506 prefixEnd_967506 := by exact prefixLift 967506
  have htrace : WordTrace (prefixWord ++ tailWord_967506) baseStart_967506 baseEnd_967506 := by
    simpa [prefixWord, tailWord_967506, baseEnd_967506] using wordTrace_append hprefix tailTrace_967506
  have hstable : (prefixWord ++ tailWord_967506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967506).length < 2 ^ (prefixWord ++ tailWord_967506).sum := by decide
  have hdescent : baseEnd_967506 < baseStart_967506 := by decide
  rcases family_descends (prefixWord ++ tailWord_967506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967512 : List Nat := [2, 1, 2, 2, 1, 1, 1, 5, 2, 6]
def baseStart_967512 : Nat := 118140960795 + 967512 * 2 ^ 59
def prefixEnd_967512 : Nat := 4983230072969 + 3 ^ 40 * 967512 * 2
def baseEnd_967512 : Nat := 165599564997641279516833

theorem tailTrace_967512 : CollatzResearch.WordTrace tailWord_967512 prefixEnd_967512 165599564997641279516833 := by
  unfold tailWord_967512
  simp only [CollatzResearch.WordTrace]
  refine ⟨17644030835438368369724395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23525374447251157826299193 17644030835438368369724395)
  ·
    refine ⟨26466046253157552554586593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17644030835438368369724395 26466046253157552554586593)
    ·
      refine ⟨19849534689868164415939945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26466046253157552554586593 19849534689868164415939945)
      ·
        refine ⟨14887151017401123311954959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19849534689868164415939945 14887151017401123311954959)
        ·
          refine ⟨22330726526101684967932439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14887151017401123311954959 22330726526101684967932439)
          ·
            refine ⟨33496089789152527451898659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22330726526101684967932439 33496089789152527451898659)
            ·
              refine ⟨50244134683728791177847989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33496089789152527451898659 50244134683728791177847989)
              ·
                refine ⟨4710387626599574172923249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50244134683728791177847989 4710387626599574172923249)
                ·
                  refine ⟨3532790719949680629692437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4710387626599574172923249 3532790719949680629692437)
                  ·
                    refine ⟨165599564997641279516833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3532790719949680629692437 165599564997641279516833)
                    ·
                      rfl

theorem cell23_967512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 5, 2, 6].length) (baseStart_967512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_967512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_967512 prefixEnd_967512 := by exact prefixLift 967512
  have htrace : WordTrace (prefixWord ++ tailWord_967512) baseStart_967512 baseEnd_967512 := by
    simpa [prefixWord, tailWord_967512, baseEnd_967512] using wordTrace_append hprefix tailTrace_967512
  have hstable : (prefixWord ++ tailWord_967512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967512).length < 2 ^ (prefixWord ++ tailWord_967512).sum := by decide
  have hdescent : baseEnd_967512 < baseStart_967512 := by decide
  rcases family_descends (prefixWord ++ tailWord_967512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967513 : List Nat := [1, 2, 1, 2, 2, 4, 4, 1, 2, 1, 3]
def baseStart_967513 : Nat := 118140960795 + 967513 * 2 ^ 59
def prefixEnd_967513 : Nat := 4983230072969 + 3 ^ 40 * 967513 * 2
def baseEnd_967513 : Nat := 496799208473578334637995

theorem tailTrace_967513 : CollatzResearch.WordTrace tailWord_967513 prefixEnd_967513 496799208473578334637995 := by
  unfold tailWord_967513
  simp only [CollatzResearch.WordTrace]
  refine ⟨35288098143873113910235193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23525398762582075940156795 35288098143873113910235193)
  ·
    refine ⟨26466073607904835432676395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35288098143873113910235193 26466073607904835432676395)
    ·
      refine ⟨39699110411857253149014593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26466073607904835432676395 39699110411857253149014593)
      ·
        refine ⟨29774332808892939861760945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39699110411857253149014593 29774332808892939861760945)
        ·
          refine ⟨22330749606669704896320709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29774332808892939861760945 22330749606669704896320709)
          ·
            refine ⟨4187015551250569668060133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22330749606669704896320709 4187015551250569668060133)
            ·
              refine ⟨785065415859481812761275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4187015551250569668060133 785065415859481812761275)
              ·
                refine ⟨1177598123789222719141913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 785065415859481812761275 1177598123789222719141913)
                ·
                  refine ⟨883198592841917039356435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1177598123789222719141913 883198592841917039356435)
                  ·
                    refine ⟨1324797889262875559034653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 883198592841917039356435 1324797889262875559034653)
                    ·
                      refine ⟨496799208473578334637995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1324797889262875559034653 496799208473578334637995)
                      ·
                        rfl

theorem cell23_967513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 4, 1, 2, 1, 3].length) (baseStart_967513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_967513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_967513 prefixEnd_967513 := by exact prefixLift 967513
  have htrace : WordTrace (prefixWord ++ tailWord_967513) baseStart_967513 baseEnd_967513 := by
    simpa [prefixWord, tailWord_967513, baseEnd_967513] using wordTrace_append hprefix tailTrace_967513
  have hstable : (prefixWord ++ tailWord_967513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967513).length < 2 ^ (prefixWord ++ tailWord_967513).sum := by decide
  have hdescent : baseEnd_967513 < baseStart_967513 := by decide
  rcases family_descends (prefixWord ++ tailWord_967513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967523 : List Nat := [1, 1, 1, 5, 3, 1, 3, 2, 1, 3, 2]
def baseStart_967523 : Nat := 118140960795 + 967523 * 2 ^ 59
def prefixEnd_967523 : Nat := 4983230072969 + 3 ^ 40 * 967523 * 2
def baseEnd_967523 : Nat := 496804343280123295512949

theorem tailTrace_967523 : CollatzResearch.WordTrace tailWord_967523 prefixEnd_967523 496804343280123295512949 := by
  unfold tailWord_967523
  simp only [CollatzResearch.WordTrace]
  refine ⟨35288462873836885618099223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23525641915891257078732815 35288462873836885618099223)
  ·
    refine ⟨52932694310755328427148835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35288462873836885618099223 52932694310755328427148835)
    ·
      refine ⟨79399041466132992640723253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52932694310755328427148835 79399041466132992640723253)
      ·
        refine ⟨7443660137449968060067805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 79399041466132992640723253 7443660137449968060067805)
        ·
          refine ⟨2791372551543738022525427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7443660137449968060067805 2791372551543738022525427)
          ·
            refine ⟨4187058827315607033788141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2791372551543738022525427 4187058827315607033788141)
            ·
              refine ⟨1570147060243352637670553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4187058827315607033788141 1570147060243352637670553)
              ·
                refine ⟨1177610295182514478252915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1570147060243352637670553 1177610295182514478252915)
                ·
                  refine ⟨1766415442773771717379373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1177610295182514478252915 1766415442773771717379373)
                  ·
                    refine ⟨662405791040164394017265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1766415442773771717379373 662405791040164394017265)
                    ·
                      refine ⟨496804343280123295512949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 662405791040164394017265 496804343280123295512949)
                      ·
                        rfl

theorem cell23_967523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3, 2, 1, 3, 2].length) (baseStart_967523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_967523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_967523 prefixEnd_967523 := by exact prefixLift 967523
  have htrace : WordTrace (prefixWord ++ tailWord_967523) baseStart_967523 baseEnd_967523 := by
    simpa [prefixWord, tailWord_967523, baseEnd_967523] using wordTrace_append hprefix tailTrace_967523
  have hstable : (prefixWord ++ tailWord_967523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967523).length < 2 ^ (prefixWord ++ tailWord_967523).sum := by decide
  have hdescent : baseEnd_967523 < baseStart_967523 := by decide
  rcases family_descends (prefixWord ++ tailWord_967523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967536 : List Nat := [2, 1, 1, 1, 4, 1, 2, 1, 6, 2, 2]
def baseStart_967536 : Nat := 118140960795 + 967536 * 2 ^ 59
def prefixEnd_967536 : Nat := 4983230072969 + 3 ^ 40 * 967536 * 2
def baseEnd_967536 : Nat := 496811018528631744650389

theorem tailTrace_967536 : CollatzResearch.WordTrace tailWord_967536 prefixEnd_967536 496811018528631744650389 := by
  unfold tailWord_967536
  simp only [CollatzResearch.WordTrace]
  refine ⟨17644468511394894419161231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23525958015193192558881641 17644468511394894419161231)
  ·
    refine ⟨26466702767092341628741847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17644468511394894419161231 26466702767092341628741847)
    ·
      refine ⟨39700054150638512443112771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26466702767092341628741847 39700054150638512443112771)
      ·
        refine ⟨59550081225957768664669157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39700054150638512443112771 59550081225957768664669157)
        ·
          refine ⟨11165640229867081624625467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59550081225957768664669157 11165640229867081624625467)
          ·
            refine ⟨16748460344800622436938201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11165640229867081624625467 16748460344800622436938201)
            ·
              refine ⟨12561345258600466827703651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16748460344800622436938201 12561345258600466827703651)
              ·
                refine ⟨18842017887900700241555477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12561345258600466827703651 18842017887900700241555477)
                ·
                  refine ⟨883219588495345323822913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 18842017887900700241555477 883219588495345323822913)
                  ·
                    refine ⟨662414691371508992867185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 883219588495345323822913 662414691371508992867185)
                    ·
                      refine ⟨496811018528631744650389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 662414691371508992867185 496811018528631744650389)
                      ·
                        rfl

theorem cell23_967536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 6, 2, 2].length) (baseStart_967536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_967536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_967536 prefixEnd_967536 := by exact prefixLift 967536
  have htrace : WordTrace (prefixWord ++ tailWord_967536) baseStart_967536 baseEnd_967536 := by
    simpa [prefixWord, tailWord_967536, baseEnd_967536] using wordTrace_append hprefix tailTrace_967536
  have hstable : (prefixWord ++ tailWord_967536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967536).length < 2 ^ (prefixWord ++ tailWord_967536).sum := by decide
  have hdescent : baseEnd_967536 < baseStart_967536 := by decide
  rcases family_descends (prefixWord ++ tailWord_967536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967570 : List Nat := [3, 2, 3, 2, 2, 1, 2, 1, 1, 4, 2]
def baseStart_967570 : Nat := 118140960795 + 967570 * 2 ^ 59
def prefixEnd_967570 : Nat := 4983230072969 + 3 ^ 40 * 967570 * 2
def baseEnd_967570 : Nat := 496828476870884611625233

theorem tailTrace_967570 : CollatzResearch.WordTrace tailWord_967570 prefixEnd_967570 496828476870884611625233 := by
  unfold tailWord_967570
  simp only [CollatzResearch.WordTrace]
  refine ⟨8822544276166653161265041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23526784736444408430040109 8822544276166653161265041)
  ·
    refine ⟨6616908207124989870948781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8822544276166653161265041 6616908207124989870948781)
    ·
      refine ⟨2481340577671871201605793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6616908207124989870948781 2481340577671871201605793)
      ·
        refine ⟨1861005433253903401204345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2481340577671871201605793 1861005433253903401204345)
        ·
          refine ⟨1395754074940427550903259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1861005433253903401204345 1395754074940427550903259)
          ·
            refine ⟨2093631112410641326354889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1395754074940427550903259 2093631112410641326354889)
            ·
              refine ⟨1570223334307980994766167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2093631112410641326354889 1570223334307980994766167)
              ·
                refine ⟨2355335001461971492149251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1570223334307980994766167 2355335001461971492149251)
                ·
                  refine ⟨3533002502192957238223877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2355335001461971492149251 3533002502192957238223877)
                  ·
                    refine ⟨662437969161179482166977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3533002502192957238223877 662437969161179482166977)
                    ·
                      refine ⟨496828476870884611625233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 662437969161179482166977 496828476870884611625233)
                      ·
                        rfl

theorem cell23_967570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 2, 1, 1, 4, 2].length) (baseStart_967570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_967570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_967570 prefixEnd_967570 := by exact prefixLift 967570
  have htrace : WordTrace (prefixWord ++ tailWord_967570) baseStart_967570 baseEnd_967570 := by
    simpa [prefixWord, tailWord_967570, baseEnd_967570] using wordTrace_append hprefix tailTrace_967570
  have hstable : (prefixWord ++ tailWord_967570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967570).length < 2 ^ (prefixWord ++ tailWord_967570).sum := by decide
  have hdescent : baseEnd_967570 < baseStart_967570 := by decide
  rcases family_descends (prefixWord ++ tailWord_967570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967604 : List Nat := [2, 5, 2, 1, 1, 3, 1, 2, 2, 2, 2]
def baseStart_967604 : Nat := 118140960795 + 967604 * 2 ^ 59
def prefixEnd_967604 : Nat := 4983230072969 + 3 ^ 40 * 967604 * 2
def baseEnd_967604 : Nat := 496845935213137478600077

theorem tailTrace_967604 : CollatzResearch.WordTrace tailWord_967604 prefixEnd_967604 496845935213137478600077 := by
  unfold tailWord_967604
  simp only [CollatzResearch.WordTrace]
  refine ⟨17645708593271718225898933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23527611457695624301198577 17645708593271718225898933)
  ·
    refine ⟨1654285180619223583678025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17645708593271718225898933 1654285180619223583678025)
    ·
      refine ⟨1240713885464417687758519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1654285180619223583678025 1240713885464417687758519)
      ·
        refine ⟨1861070828196626531637779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1240713885464417687758519 1861070828196626531637779)
        ·
          refine ⟨2791606242294939797456669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1861070828196626531637779 2791606242294939797456669)
          ·
            refine ⟨1046852340860602424046251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2791606242294939797456669 1046852340860602424046251)
            ·
              refine ⟨1570278511290903636069377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1046852340860602424046251 1570278511290903636069377)
              ·
                refine ⟨1177708883468177727052033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1570278511290903636069377 1177708883468177727052033)
                ·
                  refine ⟨883281662601133295289025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1177708883468177727052033 883281662601133295289025)
                  ·
                    refine ⟨662461246950849971466769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 883281662601133295289025 662461246950849971466769)
                    ·
                      refine ⟨496845935213137478600077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 662461246950849971466769 496845935213137478600077)
                      ·
                        rfl

theorem cell23_967604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 1, 2, 2, 2, 2].length) (baseStart_967604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_967604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_967604 prefixEnd_967604 := by exact prefixLift 967604
  have htrace : WordTrace (prefixWord ++ tailWord_967604) baseStart_967604 baseEnd_967604 := by
    simpa [prefixWord, tailWord_967604, baseEnd_967604] using wordTrace_append hprefix tailTrace_967604
  have hstable : (prefixWord ++ tailWord_967604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967604).length < 2 ^ (prefixWord ++ tailWord_967604).sum := by decide
  have hdescent : baseEnd_967604 < baseStart_967604 := by decide
  rcases family_descends (prefixWord ++ tailWord_967604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967619 : List Nat := [1, 1, 1, 3, 1, 1, 2, 2, 7, 4]
def baseStart_967619 : Nat := 118140960795 + 967619 * 2 ^ 59
def prefixEnd_967619 : Nat := 4983230072969 + 3 ^ 40 * 967619 * 2
def baseEnd_967619 : Nat := 165617879140984973304169

theorem tailTrace_967619 : CollatzResearch.WordTrace tailWord_967619 prefixEnd_967619 165617879140984973304169 := by
  unfold tailWord_967619
  simp only [CollatzResearch.WordTrace]
  refine ⟨35291964281489094013593911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23527976187659396009062607 35291964281489094013593911)
  ·
    refine ⟨52937946422233641020390867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35291964281489094013593911 52937946422233641020390867)
    ·
      refine ⟨79406919633350461530586301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52937946422233641020390867 79406919633350461530586301)
      ·
        refine ⟨29777594862506423073969863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79406919633350461530586301 29777594862506423073969863)
        ·
          refine ⟨44666392293759634610954795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29777594862506423073969863 44666392293759634610954795)
          ·
            refine ⟨66999588440639451916432193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44666392293759634610954795 66999588440639451916432193)
            ·
              refine ⟨50249691330479588937324145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66999588440639451916432193 50249691330479588937324145)
              ·
                refine ⟨37687268497859691702993109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50249691330479588937324145 37687268497859691702993109)
                ·
                  refine ⟨883295355418586524288901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 37687268497859691702993109 883295355418586524288901)
                  ·
                    refine ⟨165617879140984973304169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 883295355418586524288901 165617879140984973304169)
                    ·
                      rfl

theorem cell23_967619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 7, 4].length) (baseStart_967619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_967619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_967619 prefixEnd_967619 := by exact prefixLift 967619
  have htrace : WordTrace (prefixWord ++ tailWord_967619) baseStart_967619 baseEnd_967619 := by
    simpa [prefixWord, tailWord_967619, baseEnd_967619] using wordTrace_append hprefix tailTrace_967619
  have hstable : (prefixWord ++ tailWord_967619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967619).length < 2 ^ (prefixWord ++ tailWord_967619).sum := by decide
  have hdescent : baseEnd_967619 < baseStart_967619 := by decide
  rcases family_descends (prefixWord ++ tailWord_967619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967670 : List Nat := [5, 1, 1, 1, 3, 3, 1, 1, 3, 4]
def baseStart_967670 : Nat := 118140960795 + 967670 * 2 ^ 59
def prefixEnd_967670 : Nat := 4983230072969 + 3 ^ 40 * 967670 * 2
def baseEnd_967670 : Nat := 165626608312111406791591

theorem tailTrace_967670 : CollatzResearch.WordTrace tailWord_967670 prefixEnd_967670 165626608312111406791591 := by
  unfold tailWord_967670
  simp only [CollatzResearch.WordTrace]
  refine ⟨2205864025269020607731279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23529216269536219815800309 2205864025269020607731279)
  ·
    refine ⟨3308796037903530911596919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2205864025269020607731279 3308796037903530911596919)
    ·
      refine ⟨4963194056855296367395379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3308796037903530911596919 4963194056855296367395379)
      ·
        refine ⟨7444791085282944551093069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4963194056855296367395379 7444791085282944551093069)
        ·
          refine ⟨2791796656981104206659901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7444791085282944551093069 2791796656981104206659901)
          ·
            refine ⟨1046923746367914077497463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2791796656981104206659901 1046923746367914077497463)
            ·
              refine ⟨1570385619551871116246195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1046923746367914077497463 1570385619551871116246195)
              ·
                refine ⟨2355578429327806674369293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1570385619551871116246195 2355578429327806674369293)
                ·
                  refine ⟨883341910997927502888485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2355578429327806674369293 883341910997927502888485)
                  ·
                    refine ⟨165626608312111406791591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 883341910997927502888485 165626608312111406791591)
                    ·
                      rfl

theorem cell23_967670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 1, 1, 3, 4].length) (baseStart_967670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_967670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_967670 prefixEnd_967670 := by exact prefixLift 967670
  have htrace : WordTrace (prefixWord ++ tailWord_967670) baseStart_967670 baseEnd_967670 := by
    simpa [prefixWord, tailWord_967670, baseEnd_967670] using wordTrace_append hprefix tailTrace_967670
  have hstable : (prefixWord ++ tailWord_967670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967670).length < 2 ^ (prefixWord ++ tailWord_967670).sum := by decide
  have hdescent : baseEnd_967670 < baseStart_967670 := by decide
  rcases family_descends (prefixWord ++ tailWord_967670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967726 : List Nat := [4, 1, 3, 1, 1, 1, 1, 2, 3, 6]
def baseStart_967726 : Nat := 118140960795 + 967726 * 2 ^ 59
def prefixEnd_967726 : Nat := 4983230072969 + 3 ^ 40 * 967726 * 2
def baseEnd_967726 : Nat := 165636193284328667091505

theorem tailTrace_967726 : CollatzResearch.WordTrace tailWord_967726 prefixEnd_967726 165636193284328667091505 := by
  unfold tailWord_967726
  simp only [CollatzResearch.WordTrace]
  refine ⟨4411983361512681410967379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23530577928067634191826021 4411983361512681410967379)
  ·
    refine ⟨6617975042269022116451069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4411983361512681410967379 6617975042269022116451069)
    ·
      refine ⟨2481740640850883293669151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6617975042269022116451069 2481740640850883293669151)
      ·
        refine ⟨3722610961276324940503727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2481740640850883293669151 3722610961276324940503727)
        ·
          refine ⟨5583916441914487410755591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3722610961276324940503727 5583916441914487410755591)
          ·
            refine ⟨8375874662871731116133387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5583916441914487410755591 8375874662871731116133387)
            ·
              refine ⟨12563811994307596674200081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8375874662871731116133387 12563811994307596674200081)
              ·
                refine ⟨9422858995730697505650061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12563811994307596674200081 9422858995730697505650061)
                ·
                  refine ⟨3533572123399011564618773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9422858995730697505650061 3533572123399011564618773)
                  ·
                    refine ⟨165636193284328667091505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3533572123399011564618773 165636193284328667091505)
                    ·
                      rfl

theorem cell23_967726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_967726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_967726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_967726 prefixEnd_967726 := by exact prefixLift 967726
  have htrace : WordTrace (prefixWord ++ tailWord_967726) baseStart_967726 baseEnd_967726 := by
    simpa [prefixWord, tailWord_967726, baseEnd_967726] using wordTrace_append hprefix tailTrace_967726
  have hstable : (prefixWord ++ tailWord_967726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967726).length < 2 ^ (prefixWord ++ tailWord_967726).sum := by decide
  have hdescent : baseEnd_967726 < baseStart_967726 := by decide
  rcases family_descends (prefixWord ++ tailWord_967726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967750 : List Nat := [6, 1, 1, 1, 1, 2, 2, 1, 3, 1, 4]
def baseStart_967750 : Nat := 118140960795 + 967750 * 2 ^ 59
def prefixEnd_967750 : Nat := 4983230072969 + 3 ^ 40 * 967750 * 2
def baseEnd_967750 : Nat := 496920903388693907374405

theorem tailTrace_967750 : CollatzResearch.WordTrace tailWord_967750 prefixEnd_967750 496920903388693907374405 := by
  unfold tailWord_967750
  simp only [CollatzResearch.WordTrace]
  refine ⟨1103023195125453230831647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 23531161496009668924408469 1103023195125453230831647)
  ·
    refine ⟨1654534792688179846247471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1103023195125453230831647 1654534792688179846247471)
    ·
      refine ⟨2481802189032269769371207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1654534792688179846247471 2481802189032269769371207)
      ·
        refine ⟨3722703283548404654056811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2481802189032269769371207 3722703283548404654056811)
        ·
          refine ⟨5584054925322606981085217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3722703283548404654056811 5584054925322606981085217)
          ·
            refine ⟨4188041193991955235813913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5584054925322606981085217 4188041193991955235813913)
            ·
              refine ⟨3141030895493966426860435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4188041193991955235813913 3141030895493966426860435)
              ·
                refine ⟨4711546343240949640290653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3141030895493966426860435 4711546343240949640290653)
                ·
                  refine ⟨1766829878715356115108995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4711546343240949640290653 1766829878715356115108995)
                  ·
                    refine ⟨2650244818073034172663493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1766829878715356115108995 2650244818073034172663493)
                    ·
                      refine ⟨496920903388693907374405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2650244818073034172663493 496920903388693907374405)
                      ·
                        rfl

theorem cell23_967750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_967750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_967750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_967750 prefixEnd_967750 := by exact prefixLift 967750
  have htrace : WordTrace (prefixWord ++ tailWord_967750) baseStart_967750 baseEnd_967750 := by
    simpa [prefixWord, tailWord_967750, baseEnd_967750] using wordTrace_append hprefix tailTrace_967750
  have hstable : (prefixWord ++ tailWord_967750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967750).length < 2 ^ (prefixWord ++ tailWord_967750).sum := by decide
  have hdescent : baseEnd_967750 < baseStart_967750 := by decide
  rcases family_descends (prefixWord ++ tailWord_967750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967769 : List Nat := [1, 2, 1, 2, 2, 1, 2, 2, 1, 9]
def baseStart_967769 : Nat := 118140960795 + 967769 * 2 ^ 59
def prefixEnd_967769 : Nat := 4983230072969 + 3 ^ 40 * 967769 * 2
def baseEnd_967769 : Nat := 165643553173709777678939

theorem tailTrace_967769 : CollatzResearch.WordTrace tailWord_967769 prefixEnd_967769 165643553173709777678939 := by
  unfold tailWord_967769
  simp only [CollatzResearch.WordTrace]
  refine ⟨35297435230945669631554361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23531623487297113087702907 35297435230945669631554361)
  ·
    refine ⟨26473076423209252223665771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35297435230945669631554361 26473076423209252223665771)
    ·
      refine ⟨39709614634813878335498657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26473076423209252223665771 39709614634813878335498657)
      ·
        refine ⟨29782210976110408751623993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39709614634813878335498657 29782210976110408751623993)
        ·
          refine ⟨22336658232082806563717995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29782210976110408751623993 22336658232082806563717995)
          ·
            refine ⟨33504987348124209845576993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22336658232082806563717995 33504987348124209845576993)
            ·
              refine ⟨25128740511093157384182745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33504987348124209845576993 25128740511093157384182745)
              ·
                refine ⟨18846555383319868038137059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25128740511093157384182745 18846555383319868038137059)
                ·
                  refine ⟨28269833074979802057205589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18846555383319868038137059 28269833074979802057205589)
                  ·
                    refine ⟨165643553173709777678939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 28269833074979802057205589 165643553173709777678939)
                    ·
                      rfl

theorem cell23_967769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 9].length) (baseStart_967769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_967769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_967769 prefixEnd_967769 := by exact prefixLift 967769
  have htrace : WordTrace (prefixWord ++ tailWord_967769) baseStart_967769 baseEnd_967769 := by
    simpa [prefixWord, tailWord_967769, baseEnd_967769] using wordTrace_append hprefix tailTrace_967769
  have hstable : (prefixWord ++ tailWord_967769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967769).length < 2 ^ (prefixWord ++ tailWord_967769).sum := by decide
  have hdescent : baseEnd_967769 < baseStart_967769 := by decide
  rcases family_descends (prefixWord ++ tailWord_967769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967773 : List Nat := [1, 4, 4, 1, 2, 1, 10]
def baseStart_967773 : Nat := 118140960795 + 967773 * 2 ^ 59
def prefixEnd_967773 : Nat := 4983230072969 + 3 ^ 40 * 967773 * 2
def baseEnd_967773 : Nat := 6134971770910460708479

theorem tailTrace_967773 : CollatzResearch.WordTrace tailWord_967773 prefixEnd_967773 6134971770910460708479 := by
  unfold tailWord_967773
  simp only [CollatzResearch.WordTrace]
  refine ⟨35297581122931178314699973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23531720748620785543133315 35297581122931178314699973)
  ·
    refine ⟨6618296460549595934006245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35297581122931178314699973 6618296460549595934006245)
    ·
      refine ⟨1240930586353049237626171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6618296460549595934006245 1240930586353049237626171)
      ·
        refine ⟨1861395879529573856439257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1240930586353049237626171 1861395879529573856439257)
        ·
          refine ⟨1396046909647180392329443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1861395879529573856439257 1396046909647180392329443)
          ·
            refine ⟨2094070364470770588494165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1396046909647180392329443 2094070364470770588494165)
            ·
              refine ⟨6134971770910460708479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2094070364470770588494165 6134971770910460708479)
              ·
                rfl

theorem cell23_967773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 10].length) (baseStart_967773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_967773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_967773 prefixEnd_967773 := by exact prefixLift 967773
  have htrace : WordTrace (prefixWord ++ tailWord_967773) baseStart_967773 baseEnd_967773 := by
    simpa [prefixWord, tailWord_967773, baseEnd_967773] using wordTrace_append hprefix tailTrace_967773
  have hstable : (prefixWord ++ tailWord_967773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967773).length < 2 ^ (prefixWord ++ tailWord_967773).sum := by decide
  have hdescent : baseEnd_967773 < baseStart_967773 := by decide
  rcases family_descends (prefixWord ++ tailWord_967773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967784 : List Nat := [2, 1, 4, 4, 1, 1, 2, 1, 3, 2, 2]
def baseStart_967784 : Nat := 118140960795 + 967784 * 2 ^ 59
def prefixEnd_967784 : Nat := 4983230072969 + 3 ^ 40 * 967784 * 2
def baseEnd_967784 : Nat := 496938361730946774349249

theorem tailTrace_967784 : CollatzResearch.WordTrace tailWord_967784 prefixEnd_967784 496938361730946774349249 := by
  unfold tailWord_967784
  simp only [CollatzResearch.WordTrace]
  refine ⟨17648991162945663596675203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23531988217260884795566937 17648991162945663596675203)
  ·
    refine ⟨26473486744418495395012805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17648991162945663596675203 26473486744418495395012805)
    ·
      refine ⟨4963778764578467886564901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26473486744418495395012805 4963778764578467886564901)
      ·
        refine ⟨930708518358462728730919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4963778764578467886564901 930708518358462728730919)
        ·
          refine ⟨1396062777537694093096379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 930708518358462728730919 1396062777537694093096379)
          ·
            refine ⟨2094094166306541139644569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1396062777537694093096379 2094094166306541139644569)
            ·
              refine ⟨1570570624729905854733427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2094094166306541139644569 1570570624729905854733427)
              ·
                refine ⟨2355855937094858782100141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1570570624729905854733427 2355855937094858782100141)
                ·
                  refine ⟨883445976410572043287553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2355855937094858782100141 883445976410572043287553)
                  ·
                    refine ⟨662584482307929032465665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 883445976410572043287553 662584482307929032465665)
                    ·
                      refine ⟨496938361730946774349249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 662584482307929032465665 496938361730946774349249)
                      ·
                        rfl

theorem cell23_967784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_967784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_967784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_967784 prefixEnd_967784 := by exact prefixLift 967784
  have htrace : WordTrace (prefixWord ++ tailWord_967784) baseStart_967784 baseEnd_967784 := by
    simpa [prefixWord, tailWord_967784, baseEnd_967784] using wordTrace_append hprefix tailTrace_967784
  have hstable : (prefixWord ++ tailWord_967784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967784).length < 2 ^ (prefixWord ++ tailWord_967784).sum := by decide
  have hdescent : baseEnd_967784 < baseStart_967784 := by decide
  rcases family_descends (prefixWord ++ tailWord_967784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967793 : List Nat := [1, 2, 2, 2, 1, 1, 2, 4, 3, 3, 2]
def baseStart_967793 : Nat := 118140960795 + 967793 * 2 ^ 59
def prefixEnd_967793 : Nat := 4983230072969 + 3 ^ 40 * 967793 * 2
def baseEnd_967793 : Nat := 496942983056837239136707

theorem tailTrace_967793 : CollatzResearch.WordTrace tailWord_967793 prefixEnd_967793 496942983056837239136707 := by
  unfold tailWord_967793
  simp only [CollatzResearch.WordTrace]
  refine ⟨35298310582858721730428033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23532207055239147820285355 35298310582858721730428033)
  ·
    refine ⟨26473732937144041297821025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35298310582858721730428033 26473732937144041297821025)
    ·
      refine ⟨19855299702858030973365769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26473732937144041297821025 19855299702858030973365769)
      ·
        refine ⟨14891474777143523230024327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19855299702858030973365769 14891474777143523230024327)
        ·
          refine ⟨22337212165715284845036491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14891474777143523230024327 22337212165715284845036491)
          ·
            refine ⟨33505818248572927267554737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22337212165715284845036491 33505818248572927267554737)
            ·
              refine ⟨25129363686429695450666053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33505818248572927267554737 25129363686429695450666053)
              ·
                refine ⟨4711755691205567896999885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25129363686429695450666053 4711755691205567896999885)
                ·
                  refine ⟨1766908384202087961374957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4711755691205567896999885 1766908384202087961374957)
                  ·
                    refine ⟨662590644075782985515609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1766908384202087961374957 662590644075782985515609)
                    ·
                      refine ⟨496942983056837239136707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 662590644075782985515609 496942983056837239136707)
                      ·
                        rfl

theorem cell23_967793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 4, 3, 3, 2].length) (baseStart_967793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_967793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_967793 prefixEnd_967793 := by exact prefixLift 967793
  have htrace : WordTrace (prefixWord ++ tailWord_967793) baseStart_967793 baseEnd_967793 := by
    simpa [prefixWord, tailWord_967793, baseEnd_967793] using wordTrace_append hprefix tailTrace_967793
  have hstable : (prefixWord ++ tailWord_967793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967793).length < 2 ^ (prefixWord ++ tailWord_967793).sum := by decide
  have hdescent : baseEnd_967793 < baseStart_967793 := by decide
  rcases family_descends (prefixWord ++ tailWord_967793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967797 : List Nat := [1, 3, 4, 3, 1, 2, 1, 1, 1, 2, 4]
def baseStart_967797 : Nat := 118140960795 + 967797 * 2 ^ 59
def prefixEnd_967797 : Nat := 4983230072969 + 3 ^ 40 * 967797 * 2
def baseEnd_967797 : Nat := 496945036979455223486689

theorem tailTrace_967797 : CollatzResearch.WordTrace tailWord_967797 prefixEnd_967797 496945036979455223486689 := by
  unfold tailWord_967797
  simp only [CollatzResearch.WordTrace]
  refine ⟨35298456474844230413573645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23532304316562820275715763 35298456474844230413573645)
  ·
    refine ⟨13236921178066586405090117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35298456474844230413573645 13236921178066586405090117)
    ·
      refine ⟨2481922720887484950954397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13236921178066586405090117 2481922720887484950954397)
      ·
        refine ⟨930721020332806856607899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2481922720887484950954397 930721020332806856607899)
        ·
          refine ⟨1396081530499210284911849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 930721020332806856607899 1396081530499210284911849)
          ·
            refine ⟨1047061147874407713683887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1396081530499210284911849 1047061147874407713683887)
            ·
              refine ⟨1570591721811611570525831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1047061147874407713683887 1570591721811611570525831)
              ·
                refine ⟨2355887582717417355788747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1570591721811611570525831 2355887582717417355788747)
                ·
                  refine ⟨3533831374076126033683121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2355887582717417355788747 3533831374076126033683121)
                  ·
                    refine ⟨2650373530557094525262341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3533831374076126033683121 2650373530557094525262341)
                    ·
                      refine ⟨496945036979455223486689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2650373530557094525262341 496945036979455223486689)
                      ·
                        rfl

theorem cell23_967797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_967797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_967797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_967797 prefixEnd_967797 := by exact prefixLift 967797
  have htrace : WordTrace (prefixWord ++ tailWord_967797) baseStart_967797 baseEnd_967797 := by
    simpa [prefixWord, tailWord_967797, baseEnd_967797] using wordTrace_append hprefix tailTrace_967797
  have hstable : (prefixWord ++ tailWord_967797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967797).length < 2 ^ (prefixWord ++ tailWord_967797).sum := by decide
  have hdescent : baseEnd_967797 < baseStart_967797 := by decide
  rcases family_descends (prefixWord ++ tailWord_967797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967840 : List Nat := [2, 1, 1, 4, 2, 1, 1, 3, 4, 2, 2]
def baseStart_967840 : Nat := 118140960795 + 967840 * 2 ^ 59
def prefixEnd_967840 : Nat := 4983230072969 + 3 ^ 40 * 967840 * 2
def baseEnd_967840 : Nat := 496967116647598555248991

theorem tailTrace_967840 : CollatzResearch.WordTrace tailWord_967840 prefixEnd_967840 496967116647598555248991 := by
  unfold tailWord_967840
  simp only [CollatzResearch.WordTrace]
  refine ⟨17650012406844224378694487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23533349875792299171592649 17650012406844224378694487)
  ·
    refine ⟨26475018610266336568041731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17650012406844224378694487 26475018610266336568041731)
    ·
      refine ⟨39712527915399504852062597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26475018610266336568041731 39712527915399504852062597)
      ·
        refine ⟨7446098984137407159761737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39712527915399504852062597 7446098984137407159761737)
        ·
          refine ⟨5584574238103055369821303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7446098984137407159761737 5584574238103055369821303)
          ·
            refine ⟨8376861357154583054731955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5584574238103055369821303 8376861357154583054731955)
            ·
              refine ⟨12565292035731874582097933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8376861357154583054731955 12565292035731874582097933)
              ·
                refine ⟨4711984513399452968286725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12565292035731874582097933 4711984513399452968286725)
                ·
                  refine ⟨883497096262397431553761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4711984513399452968286725 883497096262397431553761)
                  ·
                    refine ⟨662622822196798073665321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 883497096262397431553761 662622822196798073665321)
                    ·
                      refine ⟨496967116647598555248991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 662622822196798073665321 496967116647598555248991)
                      ·
                        rfl

theorem cell23_967840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 3, 4, 2, 2].length) (baseStart_967840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_967840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_967840 prefixEnd_967840 := by exact prefixLift 967840
  have htrace : WordTrace (prefixWord ++ tailWord_967840) baseStart_967840 baseEnd_967840 := by
    simpa [prefixWord, tailWord_967840, baseEnd_967840] using wordTrace_append hprefix tailTrace_967840
  have hstable : (prefixWord ++ tailWord_967840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967840).length < 2 ^ (prefixWord ++ tailWord_967840).sum := by decide
  have hdescent : baseEnd_967840 < baseStart_967840 := by decide
  rcases family_descends (prefixWord ++ tailWord_967840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967923 : List Nat := [1, 1, 1, 2, 2, 5, 1, 1, 5, 4]
def baseStart_967923 : Nat := 118140960795 + 967923 * 2 ^ 59
def prefixEnd_967923 : Nat := 4983230072969 + 3 ^ 40 * 967923 * 2
def baseEnd_967923 : Nat := 165669911847307243503703

theorem tailTrace_967923 : CollatzResearch.WordTrace tailWord_967923 prefixEnd_967923 165669911847307243503703 := by
  unfold tailWord_967923
  simp only [CollatzResearch.WordTrace]
  refine ⟨35303052072387753932660423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23535368048258502621773615 35303052072387753932660423)
  ·
    refine ⟨52954578108581630898990635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35303052072387753932660423 52954578108581630898990635)
    ·
      refine ⟨79431867162872446348485953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52954578108581630898990635 79431867162872446348485953)
      ·
        refine ⟨59573900372154334761364465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79431867162872446348485953 59573900372154334761364465)
        ·
          refine ⟨44680425279115751071023349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59573900372154334761364465 44680425279115751071023349)
          ·
            refine ⟨4188789869917101662908439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44680425279115751071023349 4188789869917101662908439)
            ·
              refine ⟨6283184804875652494362659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4188789869917101662908439 6283184804875652494362659)
              ·
                refine ⟨9424777207313478741543989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6283184804875652494362659 9424777207313478741543989)
                ·
                  refine ⟨883572863185638632019749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9424777207313478741543989 883572863185638632019749)
                  ·
                    refine ⟨165669911847307243503703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 883572863185638632019749 165669911847307243503703)
                    ·
                      rfl

theorem cell23_967923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 1, 5, 4].length) (baseStart_967923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_967923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_967923 prefixEnd_967923 := by exact prefixLift 967923
  have htrace : WordTrace (prefixWord ++ tailWord_967923) baseStart_967923 baseEnd_967923 := by
    simpa [prefixWord, tailWord_967923, baseEnd_967923] using wordTrace_append hprefix tailTrace_967923
  have hstable : (prefixWord ++ tailWord_967923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967923).length < 2 ^ (prefixWord ++ tailWord_967923).sum := by decide
  have hdescent : baseEnd_967923 < baseStart_967923 := by decide
  rcases family_descends (prefixWord ++ tailWord_967923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967936 : List Nat := [2, 1, 1, 2, 1, 1, 3, 4, 8]
def baseStart_967936 : Nat := 118140960795 + 967936 * 2 ^ 59
def prefixEnd_967936 : Nat := 4983230072969 + 3 ^ 40 * 967936 * 2
def baseEnd_967936 : Nat := 55224045643381131072061

theorem tailTrace_967936 : CollatzResearch.WordTrace tailWord_967936 prefixEnd_967936 55224045643381131072061 := by
  unfold tailWord_967936
  simp only [CollatzResearch.WordTrace]
  refine ⟨17651763110670328576441831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23535684147560438101922441 17651763110670328576441831)
  ·
    refine ⟨26477644666005492864662747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17651763110670328576441831 26477644666005492864662747)
    ·
      refine ⟨39716466999008239296994121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26477644666005492864662747 39716466999008239296994121)
      ·
        refine ⟨29787350249256179472745591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39716466999008239296994121 29787350249256179472745591)
        ·
          refine ⟨44681025373884269209118387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29787350249256179472745591 44681025373884269209118387)
          ·
            refine ⟨67021538060826403813677581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44681025373884269209118387 67021538060826403813677581)
            ·
              refine ⟨25133076772809901430129093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67021538060826403813677581 25133076772809901430129093)
              ·
                refine ⟨4712451894901856518149205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25133076772809901430129093 4712451894901856518149205)
                ·
                  refine ⟨55224045643381131072061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4712451894901856518149205 55224045643381131072061)
                  ·
                    rfl

theorem cell23_967936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 4, 8].length) (baseStart_967936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_967936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_967936 prefixEnd_967936 := by exact prefixLift 967936
  have htrace : WordTrace (prefixWord ++ tailWord_967936) baseStart_967936 baseEnd_967936 := by
    simpa [prefixWord, tailWord_967936, baseEnd_967936] using wordTrace_append hprefix tailTrace_967936
  have hstable : (prefixWord ++ tailWord_967936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967936).length < 2 ^ (prefixWord ++ tailWord_967936).sum := by decide
  have hdescent : baseEnd_967936 < baseStart_967936 := by decide
  rcases family_descends (prefixWord ++ tailWord_967936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968003 : List Nat := [1, 1, 1, 3, 1, 3, 1, 2, 5, 1, 4]
def baseStart_968003 : Nat := 118140960795 + 968003 * 2 ^ 59
def prefixEnd_968003 : Nat := 4983230072969 + 3 ^ 40 * 968003 * 2
def baseEnd_968003 : Nat := 497050813994281417510741

theorem tailTrace_968003 : CollatzResearch.WordTrace tailWord_968003 prefixEnd_968003 497050813994281417510741 := by
  unfold tailWord_968003
  simp only [CollatzResearch.WordTrace]
  refine ⟨35305969912097927595572663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23537313274731951730381775 35305969912097927595572663)
  ·
    refine ⟨52958954868146891393358995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35305969912097927595572663 52958954868146891393358995)
    ·
      refine ⟨79438432302220337090038493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52958954868146891393358995 79438432302220337090038493)
      ·
        refine ⟨29789412113332626408764435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79438432302220337090038493 29789412113332626408764435)
        ·
          refine ⟨44684118169998939613146653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29789412113332626408764435 44684118169998939613146653)
          ·
            refine ⟨16756544313749602354929995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44684118169998939613146653 16756544313749602354929995)
            ·
              refine ⟨25134816470624403532394993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16756544313749602354929995 25134816470624403532394993)
              ·
                refine ⟨18851112352968302649296245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25134816470624403532394993 18851112352968302649296245)
                ·
                  refine ⟨1767291783090778373371523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18851112352968302649296245 1767291783090778373371523)
                  ·
                    refine ⟨2650937674636167560057285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1767291783090778373371523 2650937674636167560057285)
                    ·
                      refine ⟨497050813994281417510741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2650937674636167560057285 497050813994281417510741)
                      ·
                        rfl

theorem cell23_968003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 5, 1, 4].length) (baseStart_968003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_968003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_968003 prefixEnd_968003 := by exact prefixLift 968003
  have htrace : WordTrace (prefixWord ++ tailWord_968003) baseStart_968003 baseEnd_968003 := by
    simpa [prefixWord, tailWord_968003, baseEnd_968003] using wordTrace_append hprefix tailTrace_968003
  have hstable : (prefixWord ++ tailWord_968003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968003).length < 2 ^ (prefixWord ++ tailWord_968003).sum := by decide
  have hdescent : baseEnd_968003 < baseStart_968003 := by decide
  rcases family_descends (prefixWord ++ tailWord_968003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968007 : List Nat := [1, 1, 4, 1, 2, 4, 1, 2, 2, 3, 2]
def baseStart_968007 : Nat := 118140960795 + 968007 * 2 ^ 59
def prefixEnd_968007 : Nat := 4983230072969 + 3 ^ 40 * 968007 * 2
def baseEnd_968007 : Nat := 497052867916899401860723

theorem tailTrace_968007 : CollatzResearch.WordTrace tailWord_968007 prefixEnd_968007 497052867916899401860723 := by
  unfold tailWord_968007
  simp only [CollatzResearch.WordTrace]
  refine ⟨35306115804083436278718275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23537410536055624185812183 35306115804083436278718275)
  ·
    refine ⟨52959173706125154418077413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35306115804083436278718275 52959173706125154418077413)
    ·
      refine ⟨9929845069898466453389515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52959173706125154418077413 9929845069898466453389515)
      ·
        refine ⟨14894767604847699680084273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9929845069898466453389515 14894767604847699680084273)
        ·
          refine ⟨11171075703635774760063205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14894767604847699680084273 11171075703635774760063205)
          ·
            refine ⟨2094576694431707767511851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11171075703635774760063205 2094576694431707767511851)
            ·
              refine ⟨3141865041647561651267777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2094576694431707767511851 3141865041647561651267777)
              ·
                refine ⟨2356398781235671238450833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3141865041647561651267777 2356398781235671238450833)
                ·
                  refine ⟨1767299085926753428838125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2356398781235671238450833 1767299085926753428838125)
                  ·
                    refine ⟨662737157222532535814297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1767299085926753428838125 662737157222532535814297)
                    ·
                      refine ⟨497052867916899401860723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 662737157222532535814297 497052867916899401860723)
                      ·
                        rfl

theorem cell23_968007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 2, 2, 3, 2].length) (baseStart_968007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_968007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_968007 prefixEnd_968007 := by exact prefixLift 968007
  have htrace : WordTrace (prefixWord ++ tailWord_968007) baseStart_968007 baseEnd_968007 := by
    simpa [prefixWord, tailWord_968007, baseEnd_968007] using wordTrace_append hprefix tailTrace_968007
  have hstable : (prefixWord ++ tailWord_968007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968007).length < 2 ^ (prefixWord ++ tailWord_968007).sum := by decide
  have hdescent : baseEnd_968007 < baseStart_968007 := by decide
  rcases family_descends (prefixWord ++ tailWord_968007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968020 : List Nat := [2, 4, 1, 1, 2, 1, 2, 2, 3, 1, 4]
def baseStart_968020 : Nat := 118140960795 + 968020 * 2 ^ 59
def prefixEnd_968020 : Nat := 4983230072969 + 3 ^ 40 * 968020 * 2
def baseEnd_968020 : Nat := 497059543165407850998163

theorem tailTrace_968020 : CollatzResearch.WordTrace tailWord_968020 prefixEnd_968020 497059543165407850998163 := by
  unfold tailWord_968020
  simp only [CollatzResearch.WordTrace]
  refine ⟨17653294976518169749470757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23537726635357559665961009 17653294976518169749470757)
  ·
    refine ⟨3309992808097156828025767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17653294976518169749470757 3309992808097156828025767)
    ·
      refine ⟨4964989212145735242038651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3309992808097156828025767 4964989212145735242038651)
      ·
        refine ⟨7447483818218602863057977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4964989212145735242038651 7447483818218602863057977)
        ·
          refine ⟨5585612863663952147293483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7447483818218602863057977 5585612863663952147293483)
          ·
            refine ⟨8378419295495928220940225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5585612863663952147293483 8378419295495928220940225)
            ·
              refine ⟨6283814471621946165705169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8378419295495928220940225 6283814471621946165705169)
              ·
                refine ⟨4712860853716459624278877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6283814471621946165705169 4712860853716459624278877)
                ·
                  refine ⟨1767322820143672359104579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4712860853716459624278877 1767322820143672359104579)
                  ·
                    refine ⟨2650984230215508538656869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1767322820143672359104579 2650984230215508538656869)
                    ·
                      refine ⟨497059543165407850998163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2650984230215508538656869 497059543165407850998163)
                      ·
                        rfl

theorem cell23_968020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 2, 3, 1, 4].length) (baseStart_968020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_968020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_968020 prefixEnd_968020 := by exact prefixLift 968020
  have htrace : WordTrace (prefixWord ++ tailWord_968020) baseStart_968020 baseEnd_968020 := by
    simpa [prefixWord, tailWord_968020, baseEnd_968020] using wordTrace_append hprefix tailTrace_968020
  have hstable : (prefixWord ++ tailWord_968020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968020).length < 2 ^ (prefixWord ++ tailWord_968020).sum := by decide
  have hdescent : baseEnd_968020 < baseStart_968020 := by decide
  rcases family_descends (prefixWord ++ tailWord_968020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968033 : List Nat := [1, 2, 3, 1, 1, 1, 1, 2, 5, 2, 4]
def baseStart_968033 : Nat := 118140960795 + 968033 * 2 ^ 59
def prefixEnd_968033 : Nat := 4983230072969 + 3 ^ 40 * 968033 * 2
def baseEnd_968033 : Nat := 497066218413916300135603

theorem tailTrace_968033 : CollatzResearch.WordTrace tailWord_968033 prefixEnd_968033 497066218413916300135603 := by
  unfold tailWord_968033
  simp only [CollatzResearch.WordTrace]
  refine ⟨35307064101989242719164753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23538042734659495146109835 35307064101989242719164753)
  ·
    refine ⟨26480298076491932039373565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35307064101989242719164753 26480298076491932039373565)
    ·
      refine ⟨9930111778684474514765087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26480298076491932039373565 9930111778684474514765087)
      ·
        refine ⟨14895167668026711772147631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9930111778684474514765087 14895167668026711772147631)
        ·
          refine ⟨22342751502040067658221447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14895167668026711772147631 22342751502040067658221447)
          ·
            refine ⟨33514127253060101487332171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22342751502040067658221447 33514127253060101487332171)
            ·
              refine ⟨50271190879590152230998257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33514127253060101487332171 50271190879590152230998257)
              ·
                refine ⟨37703393159692614173248693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50271190879590152230998257 37703393159692614173248693)
                ·
                  refine ⟨3534693108721182578742065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37703393159692614173248693 3534693108721182578742065)
                  ·
                    refine ⟨2651019831540886934056549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3534693108721182578742065 2651019831540886934056549)
                    ·
                      refine ⟨497066218413916300135603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2651019831540886934056549 497066218413916300135603)
                      ·
                        rfl

theorem cell23_968033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 5, 2, 4].length) (baseStart_968033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_968033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_968033 prefixEnd_968033 := by exact prefixLift 968033
  have htrace : WordTrace (prefixWord ++ tailWord_968033) baseStart_968033 baseEnd_968033 := by
    simpa [prefixWord, tailWord_968033, baseEnd_968033] using wordTrace_append hprefix tailTrace_968033
  have hstable : (prefixWord ++ tailWord_968033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968033).length < 2 ^ (prefixWord ++ tailWord_968033).sum := by decide
  have hdescent : baseEnd_968033 < baseStart_968033 := by decide
  rcases family_descends (prefixWord ++ tailWord_968033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968037 : List Nat := [1, 3, 1, 3, 1, 2, 2, 1, 5, 2, 2]
def baseStart_968037 : Nat := 118140960795 + 968037 * 2 ^ 59
def prefixEnd_968037 : Nat := 4983230072969 + 3 ^ 40 * 968037 * 2
def baseEnd_968037 : Nat := 497068272336534284485585

theorem tailTrace_968037 : CollatzResearch.WordTrace tailWord_968037 prefixEnd_968037 497068272336534284485585 := by
  unfold tailWord_968037
  simp only [CollatzResearch.WordTrace]
  refine ⟨35307209993974751402310365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23538139995983167601540243 35307209993974751402310365)
  ·
    refine ⟨13240203747740531775866387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35307209993974751402310365 13240203747740531775866387)
    ·
      refine ⟨19860305621610797663799581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13240203747740531775866387 19860305621610797663799581)
      ·
        refine ⟨7447614608104049123924843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19860305621610797663799581 7447614608104049123924843)
        ·
          refine ⟨11171421912156073685887265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7447614608104049123924843 11171421912156073685887265)
          ·
            refine ⟨8378566434117055264415449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11171421912156073685887265 8378566434117055264415449)
            ·
              refine ⟨6283924825587791448311587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8378566434117055264415449 6283924825587791448311587)
              ·
                refine ⟨9425887238381687172467381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6283924825587791448311587 9425887238381687172467381)
                ·
                  refine ⟨883676928598283172418817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9425887238381687172467381 883676928598283172418817)
                  ·
                    refine ⟨662757696448712379314113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 883676928598283172418817 662757696448712379314113)
                    ·
                      refine ⟨497068272336534284485585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 662757696448712379314113 497068272336534284485585)
                      ·
                        rfl

theorem cell23_968037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 1, 5, 2, 2].length) (baseStart_968037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_968037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_968037 prefixEnd_968037 := by exact prefixLift 968037
  have htrace : WordTrace (prefixWord ++ tailWord_968037) baseStart_968037 baseEnd_968037 := by
    simpa [prefixWord, tailWord_968037, baseEnd_968037] using wordTrace_append hprefix tailTrace_968037
  have hstable : (prefixWord ++ tailWord_968037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968037).length < 2 ^ (prefixWord ++ tailWord_968037).sum := by decide
  have hdescent : baseEnd_968037 < baseStart_968037 := by decide
  rcases family_descends (prefixWord ++ tailWord_968037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968050 : List Nat := [3, 2, 1, 2, 1, 2, 3, 2, 1, 2, 4]
def baseStart_968050 : Nat := 118140960795 + 968050 * 2 ^ 59
def prefixEnd_968050 : Nat := 4983230072969 + 3 ^ 40 * 968050 * 2
def baseEnd_968050 : Nat := 497074947585042733623025

theorem tailTrace_968050 : CollatzResearch.WordTrace tailWord_968050 prefixEnd_968050 497074947585042733623025 := by
  unfold tailWord_968050
  simp only [CollatzResearch.WordTrace]
  refine ⟨8826921035731913655633401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23538456095285103081689069 8826921035731913655633401)
  ·
    refine ⟨6620190776798935241725051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8826921035731913655633401 6620190776798935241725051)
    ·
      refine ⟨9930286165198402862587577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6620190776798935241725051 9930286165198402862587577)
      ·
        refine ⟨7447714623898802146940683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9930286165198402862587577 7447714623898802146940683)
        ·
          refine ⟨11171571935848203220411025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7447714623898802146940683 11171571935848203220411025)
          ·
            refine ⟨8378678951886152415308269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11171571935848203220411025 8378678951886152415308269)
            ·
              refine ⟨3142004606957307155740601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8378678951886152415308269 3142004606957307155740601)
              ·
                refine ⟨2356503455217980366805451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3142004606957307155740601 2356503455217980366805451)
                ·
                  refine ⟨3534755182826970550208177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2356503455217980366805451 3534755182826970550208177)
                  ·
                    refine ⟨2651066387120227912656133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3534755182826970550208177 2651066387120227912656133)
                    ·
                      refine ⟨497074947585042733623025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2651066387120227912656133 497074947585042733623025)
                      ·
                        rfl

theorem cell23_968050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 2, 1, 2, 4].length) (baseStart_968050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_968050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_968050 prefixEnd_968050 := by exact prefixLift 968050
  have htrace : WordTrace (prefixWord ++ tailWord_968050) baseStart_968050 baseEnd_968050 := by
    simpa [prefixWord, tailWord_968050, baseEnd_968050] using wordTrace_append hprefix tailTrace_968050
  have hstable : (prefixWord ++ tailWord_968050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968050).length < 2 ^ (prefixWord ++ tailWord_968050).sum := by decide
  have hdescent : baseEnd_968050 < baseStart_968050 := by decide
  rcases family_descends (prefixWord ++ tailWord_968050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968065 : List Nat := [1, 2, 4, 3, 3, 1, 2, 2, 1, 1, 3]
def baseStart_968065 : Nat := 118140960795 + 968065 * 2 ^ 59
def prefixEnd_968065 : Nat := 4983230072969 + 3 ^ 40 * 968065 * 2
def baseEnd_968065 : Nat := 497082649794860174935457

theorem tailTrace_968065 : CollatzResearch.WordTrace tailWord_968065 prefixEnd_968065 497082649794860174935457 := by
  unfold tailWord_968065
  simp only [CollatzResearch.WordTrace]
  refine ⟨35308231237873312184329649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23538820825248874789553099 35308231237873312184329649)
  ·
    refine ⟨26481173428404984138247237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35308231237873312184329649 26481173428404984138247237)
    ·
      refine ⟨4965220017825934525921357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26481173428404984138247237 4965220017825934525921357)
      ·
        refine ⟨1861957506684725447220509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4965220017825934525921357 1861957506684725447220509)
        ·
          refine ⟨698234065006772042707691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1861957506684725447220509 698234065006772042707691)
          ·
            refine ⟨1047351097510158064061537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 698234065006772042707691 1047351097510158064061537)
            ·
              refine ⟨785513323132618548046153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1047351097510158064061537 785513323132618548046153)
              ·
                refine ⟨589134992349463911034615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 785513323132618548046153 589134992349463911034615)
                ·
                  refine ⟨883702488524195866551923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 589134992349463911034615 883702488524195866551923)
                  ·
                    refine ⟨1325553732786293799827885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 883702488524195866551923 1325553732786293799827885)
                    ·
                      refine ⟨497082649794860174935457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1325553732786293799827885 497082649794860174935457)
                      ·
                        rfl

theorem cell23_968065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 2, 2, 1, 1, 3].length) (baseStart_968065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_968065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_968065 prefixEnd_968065 := by exact prefixLift 968065
  have htrace : WordTrace (prefixWord ++ tailWord_968065) baseStart_968065 baseEnd_968065 := by
    simpa [prefixWord, tailWord_968065, baseEnd_968065] using wordTrace_append hprefix tailTrace_968065
  have hstable : (prefixWord ++ tailWord_968065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968065).length < 2 ^ (prefixWord ++ tailWord_968065).sum := by decide
  have hdescent : baseEnd_968065 < baseStart_968065 := by decide
  rcases family_descends (prefixWord ++ tailWord_968065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968071 : List Nat := [1, 1, 4, 2, 2, 3, 1, 4, 1, 2, 2]
def baseStart_968071 : Nat := 118140960795 + 968071 * 2 ^ 59
def prefixEnd_968071 : Nat := 4983230072969 + 3 ^ 40 * 968071 * 2
def baseEnd_968071 : Nat := 497085730678787151460429

theorem tailTrace_968071 : CollatzResearch.WordTrace tailWord_968071 prefixEnd_968071 497085730678787151460429 := by
  unfold tailWord_968071
  simp only [CollatzResearch.WordTrace]
  refine ⟨35308450075851575209048067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23538966717234383472698711 35308450075851575209048067)
  ·
    refine ⟨52962675113777362813572101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35308450075851575209048067 52962675113777362813572101)
    ·
      refine ⟨9930501583833255527544769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52962675113777362813572101 9930501583833255527544769)
      ·
        refine ⟨7447876187874941645658577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9930501583833255527544769 7447876187874941645658577)
        ·
          refine ⟨5585907140906206234243933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7447876187874941645658577 5585907140906206234243933)
          ·
            refine ⟨2094715177839827337841475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5585907140906206234243933 2094715177839827337841475)
            ·
              refine ⟨3142072766759741006762213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2094715177839827337841475 3142072766759741006762213)
              ·
                refine ⟨589138643767451438767915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3142072766759741006762213 589138643767451438767915)
                ·
                  refine ⟨883707965651177158151873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 589138643767451438767915 883707965651177158151873)
                  ·
                    refine ⟨662780974238382868613905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 883707965651177158151873 662780974238382868613905)
                    ·
                      refine ⟨497085730678787151460429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 662780974238382868613905 497085730678787151460429)
                      ·
                        rfl

theorem cell23_968071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 4, 1, 2, 2].length) (baseStart_968071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_968071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_968071 prefixEnd_968071 := by exact prefixLift 968071
  have htrace : WordTrace (prefixWord ++ tailWord_968071) baseStart_968071 baseEnd_968071 := by
    simpa [prefixWord, tailWord_968071, baseEnd_968071] using wordTrace_append hprefix tailTrace_968071
  have hstable : (prefixWord ++ tailWord_968071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968071).length < 2 ^ (prefixWord ++ tailWord_968071).sum := by decide
  have hdescent : baseEnd_968071 < baseStart_968071 := by decide
  rcases family_descends (prefixWord ++ tailWord_968071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968094 : List Nat := [4, 3, 1, 2, 2, 1, 3, 7]
def baseStart_968094 : Nat := 118140960795 + 968094 * 2 ^ 59
def prefixEnd_968094 : Nat := 4983230072969 + 3 ^ 40 * 968094 * 2
def baseEnd_968094 : Nat := 18411020027179280054549

theorem tailTrace_968094 : CollatzResearch.WordTrace tailWord_968094 prefixEnd_968094 18411020027179280054549 := by
  unfold tailWord_968094
  simp only [CollatzResearch.WordTrace]
  refine ⟨4413661119346031267141917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23539525969845500091423557 4413661119346031267141917)
  ·
    refine ⟨1655122919754761725178219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4413661119346031267141917 1655122919754761725178219)
    ·
      refine ⟨2482684379632142587767329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1655122919754761725178219 2482684379632142587767329)
      ·
        refine ⟨1862013284724106940825497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2482684379632142587767329 1862013284724106940825497)
        ·
          refine ⟨1396509963543080205619123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1862013284724106940825497 1396509963543080205619123)
          ·
            refine ⟨2094764945314620308428685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1396509963543080205619123 2094764945314620308428685)
            ·
              refine ⟨785536854492982615660757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2094764945314620308428685 785536854492982615660757)
              ·
                refine ⟨18411020027179280054549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 785536854492982615660757 18411020027179280054549)
                ·
                  rfl

theorem cell23_968094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 3, 7].length) (baseStart_968094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_968094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_968094 prefixEnd_968094 := by exact prefixLift 968094
  have htrace : WordTrace (prefixWord ++ tailWord_968094) baseStart_968094 baseEnd_968094 := by
    simpa [prefixWord, tailWord_968094, baseEnd_968094] using wordTrace_append hprefix tailTrace_968094
  have hstable : (prefixWord ++ tailWord_968094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968094).length < 2 ^ (prefixWord ++ tailWord_968094).sum := by decide
  have hdescent : baseEnd_968094 < baseStart_968094 := by decide
  rcases family_descends (prefixWord ++ tailWord_968094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968121 : List Nat := [1, 2, 1, 4, 4, 2, 1, 2, 2, 1, 3]
def baseStart_968121 : Nat := 118140960795 + 968121 * 2 ^ 59
def prefixEnd_968121 : Nat := 4983230072969 + 3 ^ 40 * 968121 * 2
def baseEnd_968121 : Nat := 497111404711511955835199

theorem tailTrace_968121 : CollatzResearch.WordTrace tailWord_968121 prefixEnd_968121 497111404711511955835199 := by
  unfold tailWord_968121
  simp only [CollatzResearch.WordTrace]
  refine ⟨35310273725670433748368217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23540182483780289165578811 35310273725670433748368217)
  ·
    refine ⟨26482705294252825311276163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35310273725670433748368217 26482705294252825311276163)
    ·
      refine ⟨39724057941379237966914245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26482705294252825311276163 39724057941379237966914245)
      ·
        refine ⟨7448260864008607118796421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39724057941379237966914245 7448260864008607118796421)
        ·
          refine ⟨1396548912001613834774329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7448260864008607118796421 1396548912001613834774329)
          ·
            refine ⟨1047411684001210376080747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1396548912001613834774329 1047411684001210376080747)
            ·
              refine ⟨1571117526001815564121121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1047411684001210376080747 1571117526001815564121121)
              ·
                refine ⟨1178338144501361673090841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1571117526001815564121121 1178338144501361673090841)
                ·
                  refine ⟨883753608376021254818131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1178338144501361673090841 883753608376021254818131)
                  ·
                    refine ⟨1325630412564031882227197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 883753608376021254818131 1325630412564031882227197)
                    ·
                      refine ⟨497111404711511955835199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1325630412564031882227197 497111404711511955835199)
                      ·
                        rfl

theorem cell23_968121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 1, 2, 2, 1, 3].length) (baseStart_968121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_968121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_968121 prefixEnd_968121 := by exact prefixLift 968121
  have htrace : WordTrace (prefixWord ++ tailWord_968121) baseStart_968121 baseEnd_968121 := by
    simpa [prefixWord, tailWord_968121, baseEnd_968121] using wordTrace_append hprefix tailTrace_968121
  have hstable : (prefixWord ++ tailWord_968121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968121).length < 2 ^ (prefixWord ++ tailWord_968121).sum := by decide
  have hdescent : baseEnd_968121 < baseStart_968121 := by decide
  rcases family_descends (prefixWord ++ tailWord_968121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968160 : List Nat := [2, 1, 1, 3, 1, 1, 2, 2, 4, 3, 3]
def baseStart_968160 : Nat := 118140960795 + 968160 * 2 ^ 59
def prefixEnd_968160 : Nat := 4983230072969 + 3 ^ 40 * 968160 * 2
def baseEnd_968160 : Nat := 497131430457037303247519

theorem tailTrace_968160 : CollatzResearch.WordTrace tailWord_968160 prefixEnd_968160 497131430457037303247519 := by
  unfold tailWord_968160
  simp only [CollatzResearch.WordTrace]
  refine ⟨17655848086264571704518967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23541130781686095606025289 17655848086264571704518967)
  ·
    refine ⟨26483772129396857556778451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17655848086264571704518967 26483772129396857556778451)
    ·
      refine ⟨39725658194095286335167677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26483772129396857556778451 39725658194095286335167677)
      ·
        refine ⟨14897121822785732375687879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39725658194095286335167677 14897121822785732375687879)
        ·
          refine ⟨22345682734178598563531819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14897121822785732375687879 22345682734178598563531819)
          ·
            refine ⟨33518524101267897845297729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22345682734178598563531819 33518524101267897845297729)
            ·
              refine ⟨25138893075950923383973297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33518524101267897845297729 25138893075950923383973297)
              ·
                refine ⟨18854169806963192537979973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25138893075950923383973297 18854169806963192537979973)
                ·
                  refine ⟨3535156838805598600871245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18854169806963192537979973 3535156838805598600871245)
                  ·
                    refine ⟨1325683814552099475326717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3535156838805598600871245 1325683814552099475326717)
                    ·
                      refine ⟨497131430457037303247519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1325683814552099475326717 497131430457037303247519)
                      ·
                        rfl

theorem cell23_968160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 4, 3, 3].length) (baseStart_968160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_968160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_968160 prefixEnd_968160 := by exact prefixLift 968160
  have htrace : WordTrace (prefixWord ++ tailWord_968160) baseStart_968160 baseEnd_968160 := by
    simpa [prefixWord, tailWord_968160, baseEnd_968160] using wordTrace_append hprefix tailTrace_968160
  have hstable : (prefixWord ++ tailWord_968160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968160).length < 2 ^ (prefixWord ++ tailWord_968160).sum := by decide
  have hdescent : baseEnd_968160 < baseStart_968160 := by decide
  rcases family_descends (prefixWord ++ tailWord_968160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968184 : List Nat := [2, 1, 2, 1, 1, 6, 3, 2, 5]
def baseStart_968184 : Nat := 118140960795 + 968184 * 2 ^ 59
def prefixEnd_968184 : Nat := 4983230072969 + 3 ^ 40 * 968184 * 2
def baseEnd_968184 : Nat := 55238194888082801038601

theorem tailTrace_968184 : CollatzResearch.WordTrace tailWord_968184 prefixEnd_968184 55238194888082801038601 := by
  unfold tailWord_968184
  simp only [CollatzResearch.WordTrace]
  refine ⟨17656285762221097753955803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23541714349628130338607737 17656285762221097753955803)
  ·
    refine ⟨26484428643331646630933705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17656285762221097753955803 26484428643331646630933705)
    ·
      refine ⟨19863321482498734973200279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26484428643331646630933705 19863321482498734973200279)
      ·
        refine ⟨29794982223748102459800419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19863321482498734973200279 29794982223748102459800419)
        ·
          refine ⟨44692473335622153689700629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29794982223748102459800419 44692473335622153689700629)
          ·
            refine ⟨2094959687607288454204717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 44692473335622153689700629 2094959687607288454204717)
            ·
              refine ⟨785609882852733170326769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2094959687607288454204717 785609882852733170326769)
              ·
                refine ⟨589207412139549877745077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 785609882852733170326769 589207412139549877745077)
                ·
                  refine ⟨55238194888082801038601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 589207412139549877745077 55238194888082801038601)
                  ·
                    rfl

theorem cell23_968184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 3, 2, 5].length) (baseStart_968184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_968184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_968184 prefixEnd_968184 := by exact prefixLift 968184
  have htrace : WordTrace (prefixWord ++ tailWord_968184) baseStart_968184 baseEnd_968184 := by
    simpa [prefixWord, tailWord_968184, baseEnd_968184] using wordTrace_append hprefix tailTrace_968184
  have hstable : (prefixWord ++ tailWord_968184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968184).length < 2 ^ (prefixWord ++ tailWord_968184).sum := by decide
  have hdescent : baseEnd_968184 < baseStart_968184 := by decide
  rcases family_descends (prefixWord ++ tailWord_968184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968200 : List Nat := [2, 1, 3, 2, 1, 1, 2, 1, 3, 3, 4]
def baseStart_968200 : Nat := 118140960795 + 968200 * 2 ^ 59
def prefixEnd_968200 : Nat := 4983230072969 + 3 ^ 40 * 968200 * 2
def baseEnd_968200 : Nat := 497151969683217146747335

theorem tailTrace_968200 : CollatzResearch.WordTrace tailWord_968200 prefixEnd_968200 497151969683217146747335 := by
  unfold tailWord_968200
  simp only [CollatzResearch.WordTrace]
  refine ⟨17656577546192115120247027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23542103394922820160329369 17656577546192115120247027)
  ·
    refine ⟨26484866319288172680370541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17656577546192115120247027 26484866319288172680370541)
    ·
      refine ⟨9931824869733064755138953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26484866319288172680370541 9931824869733064755138953)
      ·
        refine ⟨7448868652299798566354215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9931824869733064755138953 7448868652299798566354215)
        ·
          refine ⟨11173302978449697849531323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7448868652299798566354215 11173302978449697849531323)
          ·
            refine ⟨16759954467674546774296985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11173302978449697849531323 16759954467674546774296985)
            ·
              refine ⟨12569965850755910080722739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16759954467674546774296985 12569965850755910080722739)
              ·
                refine ⟨18854948776133865121084109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12569965850755910080722739 18854948776133865121084109)
                ·
                  refine ⟨7070605791050199420406541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18854948776133865121084109 7070605791050199420406541)
                  ·
                    refine ⟨2651477171643824782652453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7070605791050199420406541 2651477171643824782652453)
                    ·
                      refine ⟨497151969683217146747335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2651477171643824782652453 497151969683217146747335)
                      ·
                        rfl

theorem cell23_968200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 3, 3, 4].length) (baseStart_968200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_968200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_968200 prefixEnd_968200 := by exact prefixLift 968200
  have htrace : WordTrace (prefixWord ++ tailWord_968200) baseStart_968200 baseEnd_968200 := by
    simpa [prefixWord, tailWord_968200, baseEnd_968200] using wordTrace_append hprefix tailTrace_968200
  have hstable : (prefixWord ++ tailWord_968200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968200).length < 2 ^ (prefixWord ++ tailWord_968200).sum := by decide
  have hdescent : baseEnd_968200 < baseStart_968200 := by decide
  rcases family_descends (prefixWord ++ tailWord_968200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968234 : List Nat := [3, 1, 4, 1, 1, 1, 2, 2, 2, 4, 2]
def baseStart_968234 : Nat := 118140960795 + 968234 * 2 ^ 59
def prefixEnd_968234 : Nat := 4983230072969 + 3 ^ 40 * 968234 * 2
def baseEnd_968234 : Nat := 497169428025470013722179

theorem tailTrace_968234 : CollatzResearch.WordTrace tailWord_968234 prefixEnd_968234 497169428025470013722179 := by
  unfold tailWord_968234
  simp only [CollatzResearch.WordTrace]
  refine ⟨8828598793565263511807939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23542930116174036031487837 8828598793565263511807939)
  ·
    refine ⟨13242898190347895267711909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8828598793565263511807939 13242898190347895267711909)
    ·
      refine ⟨2483043410690230362695983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13242898190347895267711909 2483043410690230362695983)
      ·
        refine ⟨3724565116035345544043975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2483043410690230362695983 3724565116035345544043975)
        ·
          refine ⟨5586847674053018316065963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3724565116035345544043975 5586847674053018316065963)
          ·
            refine ⟨8380271511079527474098945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5586847674053018316065963 8380271511079527474098945)
            ·
              refine ⟨6285203633309645605574209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8380271511079527474098945 6285203633309645605574209)
              ·
                refine ⟨4713902724982234204180657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6285203633309645605574209 4713902724982234204180657)
                ·
                  refine ⟨3535427043736675653135493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4713902724982234204180657 3535427043736675653135493)
                  ·
                    refine ⟨662892570700626684962905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3535427043736675653135493 662892570700626684962905)
                    ·
                      refine ⟨497169428025470013722179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 662892570700626684962905 497169428025470013722179)
                      ·
                        rfl

theorem cell23_968234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 2, 2, 4, 2].length) (baseStart_968234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_968234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_968234 prefixEnd_968234 := by exact prefixLift 968234
  have htrace : WordTrace (prefixWord ++ tailWord_968234) baseStart_968234 baseEnd_968234 := by
    simpa [prefixWord, tailWord_968234, baseEnd_968234] using wordTrace_append hprefix tailTrace_968234
  have hstable : (prefixWord ++ tailWord_968234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968234).length < 2 ^ (prefixWord ++ tailWord_968234).sum := by decide
  have hdescent : baseEnd_968234 < baseStart_968234 := by decide
  rcases family_descends (prefixWord ++ tailWord_968234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968257 : List Nat := [1, 2, 5, 1, 1, 1, 1, 5, 6]
def baseStart_968257 : Nat := 118140960795 + 968257 * 2 ^ 59
def prefixEnd_968257 : Nat := 4983230072969 + 3 ^ 40 * 968257 * 2
def baseEnd_968257 : Nat := 55242359786724824859397

theorem tailTrace_968257 : CollatzResearch.WordTrace tailWord_968257 prefixEnd_968257 55242359786724824859397 := by
  unfold tailWord_968257
  simp only [CollatzResearch.WordTrace]
  refine ⟨35315234053177728975319025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23543489368785152650212683 35315234053177728975319025)
  ·
    refine ⟨26486425539883296731489269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35315234053177728975319025 26486425539883296731489269)
    ·
      refine ⟨2483102394364059068577119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26486425539883296731489269 2483102394364059068577119)
      ·
        refine ⟨3724653591546088602865679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2483102394364059068577119 3724653591546088602865679)
        ·
          refine ⟨5586980387319132904298519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3724653591546088602865679 5586980387319132904298519)
          ·
            refine ⟨8380470580978699356447779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5586980387319132904298519 8380470580978699356447779)
            ·
              refine ⟨12570705871468049034671669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8380470580978699356447779 12570705871468049034671669)
              ·
                refine ⟨1178503675450129597000469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12570705871468049034671669 1178503675450129597000469)
                ·
                  refine ⟨55242359786724824859397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1178503675450129597000469 55242359786724824859397)
                  ·
                    rfl

theorem cell23_968257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 5, 6].length) (baseStart_968257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_968257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_968257 prefixEnd_968257 := by exact prefixLift 968257
  have htrace : WordTrace (prefixWord ++ tailWord_968257) baseStart_968257 baseEnd_968257 := by
    simpa [prefixWord, tailWord_968257, baseEnd_968257] using wordTrace_append hprefix tailTrace_968257
  have hstable : (prefixWord ++ tailWord_968257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968257).length < 2 ^ (prefixWord ++ tailWord_968257).sum := by decide
  have hdescent : baseEnd_968257 < baseStart_968257 := by decide
  rcases family_descends (prefixWord ++ tailWord_968257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968280 : List Nat := [2, 1, 2, 2, 1, 2, 1, 1, 2, 4, 5]
def baseStart_968280 : Nat := 118140960795 + 968280 * 2 ^ 59
def prefixEnd_968280 : Nat := 4983230072969 + 3 ^ 40 * 968280 * 2
def baseEnd_968280 : Nat := 497193048135576833746967

theorem tailTrace_968280 : CollatzResearch.WordTrace tailWord_968280 prefixEnd_968280 497193048135576833746967 := by
  unfold tailWord_968280
  simp only [CollatzResearch.WordTrace]
  refine ⟨17658036466047201951703147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23544048621396269268937529 17658036466047201951703147)
  ·
    refine ⟨26487054699070802927554721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17658036466047201951703147 26487054699070802927554721)
    ·
      refine ⟨19865291024303102195666041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26487054699070802927554721 19865291024303102195666041)
      ·
        refine ⟨14898968268227326646749531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19865291024303102195666041 14898968268227326646749531)
        ·
          refine ⟨22348452402340989970124297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14898968268227326646749531 22348452402340989970124297)
          ·
            refine ⟨16761339301755742477593223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22348452402340989970124297 16761339301755742477593223)
            ·
              refine ⟨25142008952633613716389835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16761339301755742477593223 25142008952633613716389835)
              ·
                refine ⟨37713013428950420574584753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25142008952633613716389835 37713013428950420574584753)
                ·
                  refine ⟨28284760071712815430938565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37713013428950420574584753 28284760071712815430938565)
                  ·
                    refine ⟨5303392513446152893300981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28284760071712815430938565 5303392513446152893300981)
                    ·
                      refine ⟨497193048135576833746967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5303392513446152893300981 497193048135576833746967)
                      ·
                        rfl

theorem cell23_968280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 2, 4, 5].length) (baseStart_968280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_968280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_968280 prefixEnd_968280 := by exact prefixLift 968280
  have htrace : WordTrace (prefixWord ++ tailWord_968280) baseStart_968280 baseEnd_968280 := by
    simpa [prefixWord, tailWord_968280, baseEnd_968280] using wordTrace_append hprefix tailTrace_968280
  have hstable : (prefixWord ++ tailWord_968280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968280).length < 2 ^ (prefixWord ++ tailWord_968280).sum := by decide
  have hdescent : baseEnd_968280 < baseStart_968280 := by decide
  rcases family_descends (prefixWord ++ tailWord_968280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968334 : List Nat := [4, 1, 1, 3, 1, 2, 1, 2, 4, 4]
def baseStart_968334 : Nat := 118140960795 + 968334 * 2 ^ 59
def prefixEnd_968334 : Nat := 4983230072969 + 3 ^ 40 * 968334 * 2
def baseEnd_968334 : Nat := 165740258696973207490573

theorem tailTrace_968334 : CollatzResearch.WordTrace tailWord_968334 prefixEnd_968334 165740258696973207490573 := by
  unfold tailWord_968334
  simp only [CollatzResearch.WordTrace]
  refine ⟨4414755309237346390734007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23545361649265847417248037 4414755309237346390734007)
  ·
    refine ⟨6622132963856019586101011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4414755309237346390734007 6622132963856019586101011)
    ·
      refine ⟨9933199445784029379151517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6622132963856019586101011 9933199445784029379151517)
      ·
        refine ⟨3724949792169011017181819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9933199445784029379151517 3724949792169011017181819)
        ·
          refine ⟨5587424688253516525772729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3724949792169011017181819 5587424688253516525772729)
          ·
            refine ⟨4190568516190137394329547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5587424688253516525772729 4190568516190137394329547)
            ·
              refine ⟨6285852774285206091494321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4190568516190137394329547 6285852774285206091494321)
              ·
                refine ⟨4714389580713904568620741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6285852774285206091494321 4714389580713904568620741)
                ·
                  refine ⟨883948046383857106616389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4714389580713904568620741 883948046383857106616389)
                  ·
                    refine ⟨165740258696973207490573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 883948046383857106616389 165740258696973207490573)
                    ·
                      rfl

theorem cell23_968334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 2, 4, 4].length) (baseStart_968334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_968334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_968334 prefixEnd_968334 := by exact prefixLift 968334
  have htrace : WordTrace (prefixWord ++ tailWord_968334) baseStart_968334 baseEnd_968334 := by
    simpa [prefixWord, tailWord_968334, baseEnd_968334] using wordTrace_append hprefix tailTrace_968334
  have hstable : (prefixWord ++ tailWord_968334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968334).length < 2 ^ (prefixWord ++ tailWord_968334).sum := by decide
  have hdescent : baseEnd_968334 < baseStart_968334 := by decide
  rcases family_descends (prefixWord ++ tailWord_968334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968344 : List Nat := [2, 1, 2, 4, 1, 3, 2, 1, 1, 1, 5]
def baseStart_968344 : Nat := 118140960795 + 968344 * 2 ^ 59
def prefixEnd_968344 : Nat := 4983230072969 + 3 ^ 40 * 968344 * 2
def baseEnd_968344 : Nat := 497225910897464583346673

theorem tailTrace_968344 : CollatzResearch.WordTrace tailWord_968344 prefixEnd_968344 497225910897464583346673 := by
  unfold tailWord_968344
  simp only [CollatzResearch.WordTrace]
  refine ⟨17659203601931271416868043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23545604802575028555824057 17659203601931271416868043)
  ·
    refine ⟨26488805402896907125302065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17659203601931271416868043 26488805402896907125302065)
    ·
      refine ⟨19866604052172680343976549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26488805402896907125302065 19866604052172680343976549)
      ·
        refine ⟨3724988259782377564495603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19866604052172680343976549 3724988259782377564495603)
        ·
          refine ⟨5587482389673566346743405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3724988259782377564495603 5587482389673566346743405)
          ·
            refine ⟨2095305896127587380028777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5587482389673566346743405 2095305896127587380028777)
            ·
              refine ⟨1571479422095690535021583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2095305896127587380028777 1571479422095690535021583)
              ·
                refine ⟨2357219133143535802532375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1571479422095690535021583 2357219133143535802532375)
                ·
                  refine ⟨3535828699715303703798563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2357219133143535802532375 3535828699715303703798563)
                  ·
                    refine ⟨5303743049572955555697845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3535828699715303703798563 5303743049572955555697845)
                    ·
                      refine ⟨497225910897464583346673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5303743049572955555697845 497225910897464583346673)
                      ·
                        rfl

theorem cell23_968344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2, 1, 1, 1, 5].length) (baseStart_968344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_968344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_968344 prefixEnd_968344 := by exact prefixLift 968344
  have htrace : WordTrace (prefixWord ++ tailWord_968344) baseStart_968344 baseEnd_968344 := by
    simpa [prefixWord, tailWord_968344, baseEnd_968344] using wordTrace_append hprefix tailTrace_968344
  have hstable : (prefixWord ++ tailWord_968344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968344).length < 2 ^ (prefixWord ++ tailWord_968344).sum := by decide
  have hdescent : baseEnd_968344 < baseStart_968344 := by decide
  rcases family_descends (prefixWord ++ tailWord_968344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968407 : List Nat := [1, 1, 3, 2, 1, 3, 2, 2, 2, 6]
def baseStart_968407 : Nat := 118140960795 + 968407 * 2 ^ 59
def prefixEnd_968407 : Nat := 4983230072969 + 3 ^ 40 * 968407 * 2
def baseEnd_968407 : Nat := 165752753392899278952961

theorem tailTrace_968407 : CollatzResearch.WordTrace tailWord_968407 prefixEnd_968407 165752753392899278952961 := by
  unfold tailWord_968407
  simp only [CollatzResearch.WordTrace]
  refine ⟨35320705002634304593279475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23547136668422869728852983 35320705002634304593279475)
  ·
    refine ⟨52981057503951456889919213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35320705002634304593279475 52981057503951456889919213)
    ·
      refine ⟨19867896563981796333719705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52981057503951456889919213 19867896563981796333719705)
      ·
        refine ⟨14900922422986347250289779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19867896563981796333719705 14900922422986347250289779)
        ·
          refine ⟨22351383634479520875434669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14900922422986347250289779 22351383634479520875434669)
          ·
            refine ⟨8381768862929820328288001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22351383634479520875434669 8381768862929820328288001)
            ·
              refine ⟨6286326647197365246216001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8381768862929820328288001 6286326647197365246216001)
              ·
                refine ⟨4714744985398023934662001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6286326647197365246216001 4714744985398023934662001)
                ·
                  refine ⟨3536058739048517950996501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4714744985398023934662001 3536058739048517950996501)
                  ·
                    refine ⟨165752753392899278952961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3536058739048517950996501 165752753392899278952961)
                    ·
                      rfl

theorem cell23_968407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 2, 2, 6].length) (baseStart_968407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_968407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_968407 prefixEnd_968407 := by exact prefixLift 968407
  have htrace : WordTrace (prefixWord ++ tailWord_968407) baseStart_968407 baseEnd_968407 := by
    simpa [prefixWord, tailWord_968407, baseEnd_968407] using wordTrace_append hprefix tailTrace_968407
  have hstable : (prefixWord ++ tailWord_968407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968407).length < 2 ^ (prefixWord ++ tailWord_968407).sum := by decide
  have hdescent : baseEnd_968407 < baseStart_968407 := by decide
  rcases family_descends (prefixWord ++ tailWord_968407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968424 : List Nat := [2, 1, 4, 1, 3, 2, 1, 1, 2, 6]
def baseStart_968424 : Nat := 118140960795 + 968424 * 2 ^ 59
def prefixEnd_968424 : Nat := 4983230072969 + 3 ^ 40 * 968424 * 2
def baseEnd_968424 : Nat := 165755663116608090115435

theorem tailTrace_968424 : CollatzResearch.WordTrace tailWord_968424 prefixEnd_968424 165755663116608090115435 := by
  unfold tailWord_968424
  simp only [CollatzResearch.WordTrace]
  refine ⟨17660662521786358248324163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23547550029048477664432217 17660662521786358248324163)
  ·
    refine ⟨26490993782679537372486245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17660662521786358248324163 26490993782679537372486245)
    ·
      refine ⟨4967061334252413257341171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26490993782679537372486245 4967061334252413257341171)
      ·
        refine ⟨7450592001378619886011757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4967061334252413257341171 7450592001378619886011757)
        ·
          refine ⟨2793972000516982457254409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7450592001378619886011757 2793972000516982457254409)
          ·
            refine ⟨2095479000387736842940807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2793972000516982457254409 2095479000387736842940807)
            ·
              refine ⟨3143218500581605264411211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2095479000387736842940807 3143218500581605264411211)
              ·
                refine ⟨4714827750872407896616817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3143218500581605264411211 4714827750872407896616817)
                ·
                  refine ⟨3536120813154305922462613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4714827750872407896616817 3536120813154305922462613)
                  ·
                    refine ⟨165755663116608090115435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3536120813154305922462613 165755663116608090115435)
                    ·
                      rfl

theorem cell23_968424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 1, 2, 6].length) (baseStart_968424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_968424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_968424 prefixEnd_968424 := by exact prefixLift 968424
  have htrace : WordTrace (prefixWord ++ tailWord_968424) baseStart_968424 baseEnd_968424 := by
    simpa [prefixWord, tailWord_968424, baseEnd_968424] using wordTrace_append hprefix tailTrace_968424
  have hstable : (prefixWord ++ tailWord_968424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968424).length < 2 ^ (prefixWord ++ tailWord_968424).sum := by decide
  have hdescent : baseEnd_968424 < baseStart_968424 := by decide
  rcases family_descends (prefixWord ++ tailWord_968424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968427 : List Nat := [1, 1, 1, 1, 2, 4, 3, 1, 1, 4, 4]
def baseStart_968427 : Nat := 118140960795 + 968427 * 2 ^ 59
def prefixEnd_968427 : Nat := 4983230072969 + 3 ^ 40 * 968427 * 2
def baseEnd_968427 : Nat := 497268529791787758608791

theorem tailTrace_968427 : CollatzResearch.WordTrace tailWord_968427 prefixEnd_968427 497268529791787758608791 := by
  unfold tailWord_968427
  simp only [CollatzResearch.WordTrace]
  refine ⟨35321434462561848009007535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23547622975041232006005023 35321434462561848009007535)
  ·
    refine ⟨52982151693842772013511303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35321434462561848009007535 52982151693842772013511303)
    ·
      refine ⟨79473227540764158020266955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52982151693842772013511303 79473227540764158020266955)
      ·
        refine ⟨119209841311146237030400433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79473227540764158020266955 119209841311146237030400433)
        ·
          refine ⟨89407380983359677772800325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119209841311146237030400433 89407380983359677772800325)
          ·
            refine ⟨16763883934379939582400061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89407380983359677772800325 16763883934379939582400061)
            ·
              refine ⟨6286456475392477343400023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16763883934379939582400061 6286456475392477343400023)
              ·
                refine ⟨9429684713088716015100035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6286456475392477343400023 9429684713088716015100035)
                ·
                  refine ⟨14144527069633074022650053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9429684713088716015100035 14144527069633074022650053)
                  ·
                    refine ⟨2652098825556201379246885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14144527069633074022650053 2652098825556201379246885)
                    ·
                      refine ⟨497268529791787758608791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2652098825556201379246885 497268529791787758608791)
                      ·
                        rfl

theorem cell23_968427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 1, 1, 4, 4].length) (baseStart_968427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_968427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_968427 prefixEnd_968427 := by exact prefixLift 968427
  have htrace : WordTrace (prefixWord ++ tailWord_968427) baseStart_968427 baseEnd_968427 := by
    simpa [prefixWord, tailWord_968427, baseEnd_968427] using wordTrace_append hprefix tailTrace_968427
  have hstable : (prefixWord ++ tailWord_968427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968427).length < 2 ^ (prefixWord ++ tailWord_968427).sum := by decide
  have hdescent : baseEnd_968427 < baseStart_968427 := by decide
  rcases family_descends (prefixWord ++ tailWord_968427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968431 : List Nat := [1, 1, 2, 1, 5, 1, 4, 1, 1, 4, 2]
def baseStart_968431 : Nat := 118140960795 + 968431 * 2 ^ 59
def prefixEnd_968431 : Nat := 4983230072969 + 3 ^ 40 * 968431 * 2
def baseEnd_968431 : Nat := 497270583714405742958773

theorem tailTrace_968431 : CollatzResearch.WordTrace tailWord_968431 prefixEnd_968431 497270583714405742958773 := by
  unfold tailWord_968431
  simp only [CollatzResearch.WordTrace]
  refine ⟨35321580354547356692153147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23547720236364904461435431 35321580354547356692153147)
  ·
    refine ⟨52982370531821035038229721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35321580354547356692153147 52982370531821035038229721)
    ·
      refine ⟨39736777898865776278672291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52982370531821035038229721 39736777898865776278672291)
      ·
        refine ⟨59605166848298664418008437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39736777898865776278672291 59605166848298664418008437)
        ·
          refine ⟨5587984392027999789188291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59605166848298664418008437 5587984392027999789188291)
          ·
            refine ⟨8381976588041999683782437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5587984392027999789188291 8381976588041999683782437)
            ·
              refine ⟨1571620610257874940709207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8381976588041999683782437 1571620610257874940709207)
              ·
                refine ⟨2357430915386812411063811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1571620610257874940709207 2357430915386812411063811)
                ·
                  refine ⟨3536146373080218616595717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2357430915386812411063811 3536146373080218616595717)
                  ·
                    refine ⟨663027444952540990611697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3536146373080218616595717 663027444952540990611697)
                    ·
                      refine ⟨497270583714405742958773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 663027444952540990611697 497270583714405742958773)
                      ·
                        rfl

theorem cell23_968431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4, 1, 1, 4, 2].length) (baseStart_968431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_968431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_968431 prefixEnd_968431 := by exact prefixLift 968431
  have htrace : WordTrace (prefixWord ++ tailWord_968431) baseStart_968431 baseEnd_968431 := by
    simpa [prefixWord, tailWord_968431, baseEnd_968431] using wordTrace_append hprefix tailTrace_968431
  have hstable : (prefixWord ++ tailWord_968431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968431).length < 2 ^ (prefixWord ++ tailWord_968431).sum := by decide
  have hdescent : baseEnd_968431 < baseStart_968431 := by decide
  rcases family_descends (prefixWord ++ tailWord_968431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968434 : List Nat := [3, 2, 1, 3, 1, 1, 1, 2, 2, 4, 3]
def baseStart_968434 : Nat := 118140960795 + 968434 * 2 ^ 59
def prefixEnd_968434 : Nat := 4983230072969 + 3 ^ 40 * 968434 * 2
def baseEnd_968434 : Nat := 497272124156369231221259

theorem tailTrace_968434 : CollatzResearch.WordTrace tailWord_968434 prefixEnd_968434 497272124156369231221259 := by
  unfold tailWord_968434
  simp only [CollatzResearch.WordTrace]
  refine ⟨8830422443384122051128089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23547793182357658803008237 8830422443384122051128089)
  ·
    refine ⟨6622816832538091538346067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8830422443384122051128089 6622816832538091538346067)
    ·
      refine ⟨9934225248807137307519101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6622816832538091538346067 9934225248807137307519101)
      ·
        refine ⟨3725334468302676490319663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9934225248807137307519101 3725334468302676490319663)
        ·
          refine ⟨5588001702454014735479495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3725334468302676490319663 5588001702454014735479495)
          ·
            refine ⟨8382002553681022103219243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5588001702454014735479495 8382002553681022103219243)
            ·
              refine ⟨12573003830521533154828865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8382002553681022103219243 12573003830521533154828865)
              ·
                refine ⟨9429752872891149866121649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12573003830521533154828865 9429752872891149866121649)
                ·
                  refine ⟨7072314654668362399591237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9429752872891149866121649 7072314654668362399591237)
                  ·
                    refine ⟨1326058997750317949923357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7072314654668362399591237 1326058997750317949923357)
                    ·
                      refine ⟨497272124156369231221259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1326058997750317949923357 497272124156369231221259)
                      ·
                        rfl

theorem cell23_968434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 2, 2, 4, 3].length) (baseStart_968434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_968434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_968434 prefixEnd_968434 := by exact prefixLift 968434
  have htrace : WordTrace (prefixWord ++ tailWord_968434) baseStart_968434 baseEnd_968434 := by
    simpa [prefixWord, tailWord_968434, baseEnd_968434] using wordTrace_append hprefix tailTrace_968434
  have hstable : (prefixWord ++ tailWord_968434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968434).length < 2 ^ (prefixWord ++ tailWord_968434).sum := by decide
  have hdescent : baseEnd_968434 < baseStart_968434 := by decide
  rcases family_descends (prefixWord ++ tailWord_968434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968471 : List Nat := [1, 1, 3, 4, 2, 1, 2, 4, 5]
def baseStart_968471 : Nat := 118140960795 + 968471 * 2 ^ 59
def prefixEnd_968471 : Nat := 4983230072969 + 3 ^ 40 * 968471 * 2
def baseEnd_968471 : Nat := 55254569215620620717621

theorem tailTrace_968471 : CollatzResearch.WordTrace tailWord_968471 prefixEnd_968471 55254569215620620717621 := by
  unfold tailWord_968471
  simp only [CollatzResearch.WordTrace]
  refine ⟨35323039274402443523609267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23548692849601629015739511 35323039274402443523609267)
  ·
    refine ⟨52984558911603665285413901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35323039274402443523609267 52984558911603665285413901)
    ·
      refine ⟨19869209591851374482030213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52984558911603665285413901 19869209591851374482030213)
      ·
        refine ⟨3725476798472132715380665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19869209591851374482030213 3725476798472132715380665)
        ·
          refine ⟨2794107598854099536535499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3725476798472132715380665 2794107598854099536535499)
          ·
            refine ⟨4191161398281149304803249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2794107598854099536535499 4191161398281149304803249)
            ·
              refine ⟨3143371048710861978602437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4191161398281149304803249 3143371048710861978602437)
              ·
                refine ⟨589382071633286620987957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3143371048710861978602437 589382071633286620987957)
                ·
                  refine ⟨55254569215620620717621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 589382071633286620987957 55254569215620620717621)
                  ·
                    rfl

theorem cell23_968471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 4, 5].length) (baseStart_968471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_968471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_968471 prefixEnd_968471 := by exact prefixLift 968471
  have htrace : WordTrace (prefixWord ++ tailWord_968471) baseStart_968471 baseEnd_968471 := by
    simpa [prefixWord, tailWord_968471, baseEnd_968471] using wordTrace_append hprefix tailTrace_968471
  have hstable : (prefixWord ++ tailWord_968471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968471).length < 2 ^ (prefixWord ++ tailWord_968471).sum := by decide
  have hdescent : baseEnd_968471 < baseStart_968471 := by decide
  rcases family_descends (prefixWord ++ tailWord_968471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968484 : List Nat := [2, 3, 1, 3, 2, 1, 1, 2, 1, 7]
def baseStart_968484 : Nat := 118140960795 + 968484 * 2 ^ 59
def prefixEnd_968484 : Nat := 4983230072969 + 3 ^ 40 * 968484 * 2
def baseEnd_968484 : Nat := 165765932729698011865343

theorem tailTrace_968484 : CollatzResearch.WordTrace tailWord_968484 prefixEnd_968484 165765932729698011865343 := by
  unfold tailWord_968484
  simp only [CollatzResearch.WordTrace]
  refine ⟨17661756711677673371916253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23549008948903564495888337 17661756711677673371916253)
  ·
    refine ⟨6623158766879127514468595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17661756711677673371916253 6623158766879127514468595)
    ·
      refine ⟨9934738150318691271702893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6623158766879127514468595 9934738150318691271702893)
      ·
        refine ⟨3725526806369509226888585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9934738150318691271702893 3725526806369509226888585)
        ·
          refine ⟨2794145104777131920166439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3725526806369509226888585 2794145104777131920166439)
          ·
            refine ⟨4191217657165697880249659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2794145104777131920166439 4191217657165697880249659)
            ·
              refine ⟨6286826485748546820374489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4191217657165697880249659 6286826485748546820374489)
              ·
                refine ⟨4715119864311410115280867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6286826485748546820374489 4715119864311410115280867)
                ·
                  refine ⟨7072679796467115172921301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4715119864311410115280867 7072679796467115172921301)
                  ·
                    refine ⟨165765932729698011865343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7072679796467115172921301 165765932729698011865343)
                    ·
                      rfl

theorem cell23_968484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 2, 1, 7].length) (baseStart_968484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_968484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_968484 prefixEnd_968484 := by exact prefixLift 968484
  have htrace : WordTrace (prefixWord ++ tailWord_968484) baseStart_968484 baseEnd_968484 := by
    simpa [prefixWord, tailWord_968484, baseEnd_968484] using wordTrace_append hprefix tailTrace_968484
  have hstable : (prefixWord ++ tailWord_968484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968484).length < 2 ^ (prefixWord ++ tailWord_968484).sum := by decide
  have hdescent : baseEnd_968484 < baseStart_968484 := by decide
  rcases family_descends (prefixWord ++ tailWord_968484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968504 : List Nat := [2, 1, 2, 1, 3, 3, 2, 1, 1, 3, 4]
def baseStart_968504 : Nat := 118140960795 + 968504 * 2 ^ 59
def prefixEnd_968504 : Nat := 4983230072969 + 3 ^ 40 * 968504 * 2
def baseEnd_968504 : Nat := 497308067802183957345937

theorem tailTrace_968504 : CollatzResearch.WordTrace tailWord_968504 prefixEnd_968504 497308067802183957345937 := by
  unfold tailWord_968504
  simp only [CollatzResearch.WordTrace]
  refine ⟨17662121441641445079780283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23549495255521926773040377 17662121441641445079780283)
  ·
    refine ⟨26493182162462167619670425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17662121441641445079780283 26493182162462167619670425)
    ·
      refine ⟨19869886621846625714752819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26493182162462167619670425 19869886621846625714752819)
      ·
        refine ⟨29804829932769938572129229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19869886621846625714752819 29804829932769938572129229)
        ·
          refine ⟨11176811224788726964548461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29804829932769938572129229 11176811224788726964548461)
          ·
            refine ⟨4191304209295772611705673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11176811224788726964548461 4191304209295772611705673)
            ·
              refine ⟨3143478156971829458779255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4191304209295772611705673 3143478156971829458779255)
              ·
                refine ⟨4715217235457744188168883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3143478156971829458779255 4715217235457744188168883)
                ·
                  refine ⟨7072825853186616282253325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4715217235457744188168883 7072825853186616282253325)
                  ·
                    refine ⟨2652309694944981105844997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7072825853186616282253325 2652309694944981105844997)
                    ·
                      refine ⟨497308067802183957345937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2652309694944981105844997 497308067802183957345937)
                      ·
                        rfl

theorem cell23_968504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 1, 1, 3, 4].length) (baseStart_968504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_968504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_968504 prefixEnd_968504 := by exact prefixLift 968504
  have htrace : WordTrace (prefixWord ++ tailWord_968504) baseStart_968504 baseEnd_968504 := by
    simpa [prefixWord, tailWord_968504, baseEnd_968504] using wordTrace_append hprefix tailTrace_968504
  have hstable : (prefixWord ++ tailWord_968504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968504).length < 2 ^ (prefixWord ++ tailWord_968504).sum := by decide
  have hdescent : baseEnd_968504 < baseStart_968504 := by decide
  rcases family_descends (prefixWord ++ tailWord_968504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968505 : List Nat := [1, 2, 1, 7, 1, 2, 1, 3, 5]
def baseStart_968505 : Nat := 118140960795 + 968505 * 2 ^ 59
def prefixEnd_968505 : Nat := 4983230072969 + 3 ^ 40 * 968505 * 2
def baseEnd_968505 : Nat := 55256509031426494825937

theorem tailTrace_968505 : CollatzResearch.WordTrace tailWord_968505 prefixEnd_968505 55256509031426494825937 := by
  unfold tailWord_968505
  simp only [CollatzResearch.WordTrace]
  refine ⟨35324279356279267330346969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23549519570852844886897979 35324279356279267330346969)
  ·
    refine ⟨26493209517209450497760227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35324279356279267330346969 26493209517209450497760227)
    ·
      refine ⟨39739814275814175746640341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26493209517209450497760227 39739814275814175746640341)
      ·
        refine ⟨931401897089394744061883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 39739814275814175746640341 931401897089394744061883)
        ·
          refine ⟨1397102845634092116092825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 931401897089394744061883 1397102845634092116092825)
          ·
            refine ⟨1047827134225569087069619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1397102845634092116092825 1047827134225569087069619)
            ·
              refine ⟨1571740701338353630604429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1047827134225569087069619 1571740701338353630604429)
              ·
                refine ⟨589402763001882611476661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1571740701338353630604429 589402763001882611476661)
                ·
                  refine ⟨55256509031426494825937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 589402763001882611476661 55256509031426494825937)
                  ·
                    rfl

theorem cell23_968505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 1, 3, 5].length) (baseStart_968505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_968505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_968505 prefixEnd_968505 := by exact prefixLift 968505
  have htrace : WordTrace (prefixWord ++ tailWord_968505) baseStart_968505 baseEnd_968505 := by
    simpa [prefixWord, tailWord_968505, baseEnd_968505] using wordTrace_append hprefix tailTrace_968505
  have hstable : (prefixWord ++ tailWord_968505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968505).length < 2 ^ (prefixWord ++ tailWord_968505).sum := by decide
  have hdescent : baseEnd_968505 < baseStart_968505 := by decide
  rcases family_descends (prefixWord ++ tailWord_968505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968518 : List Nat := [6, 1, 1, 2, 1, 1, 1, 1, 4, 5]
def baseStart_968518 : Nat := 118140960795 + 968518 * 2 ^ 59
def prefixEnd_968518 : Nat := 4983230072969 + 3 ^ 40 * 968518 * 2
def baseEnd_968518 : Nat := 165771752177115634190291

theorem tailTrace_968518 : CollatzResearch.WordTrace tailWord_968518 prefixEnd_968518 165771752177115634190291 := by
  unfold tailWord_968518
  simp only [CollatzResearch.WordTrace]
  refine ⟨1103898547038505329705319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 23549835670154780367046805 1103898547038505329705319)
  ·
    refine ⟨1655847820557757994557979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1103898547038505329705319 1655847820557757994557979)
    ·
      refine ⟨2483771730836636991836969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1655847820557757994557979 2483771730836636991836969)
      ·
        refine ⟨1862828798127477743877727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2483771730836636991836969 1862828798127477743877727)
        ·
          refine ⟨2794243197191216615816591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1862828798127477743877727 2794243197191216615816591)
          ·
            refine ⟨4191364795786824923724887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2794243197191216615816591 4191364795786824923724887)
            ·
              refine ⟨6287047193680237385587331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4191364795786824923724887 6287047193680237385587331)
              ·
                refine ⟨9430570790520356078380997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6287047193680237385587331 9430570790520356078380997)
                ·
                  refine ⟨1768232023222566764696437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9430570790520356078380997 1768232023222566764696437)
                  ·
                    refine ⟨165771752177115634190291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1768232023222566764696437 165771752177115634190291)
                    ·
                      rfl

theorem cell23_968518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_968518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_968518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_968518 prefixEnd_968518 := by exact prefixLift 968518
  have htrace : WordTrace (prefixWord ++ tailWord_968518) baseStart_968518 baseEnd_968518 := by
    simpa [prefixWord, tailWord_968518, baseEnd_968518] using wordTrace_append hprefix tailTrace_968518
  have hstable : (prefixWord ++ tailWord_968518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968518).length < 2 ^ (prefixWord ++ tailWord_968518).sum := by decide
  have hdescent : baseEnd_968518 < baseStart_968518 := by decide
  rcases family_descends (prefixWord ++ tailWord_968518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968558 : List Nat := [4, 1, 2, 3, 1, 1, 1, 3, 2, 2, 3]
def baseStart_968558 : Nat := 118140960795 + 968558 * 2 ^ 59
def prefixEnd_968558 : Nat := 4983230072969 + 3 ^ 40 * 968558 * 2
def baseEnd_968558 : Nat := 497335795757526746070689

theorem tailTrace_968558 : CollatzResearch.WordTrace tailWord_968558 prefixEnd_968558 497335795757526746070689 := by
  unfold tailWord_968558
  simp only [CollatzResearch.WordTrace]
  refine ⟨4415776553135907172753291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23550808283391504921350885 4415776553135907172753291)
  ·
    refine ⟨6623664829703860759129937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4415776553135907172753291 6623664829703860759129937)
    ·
      refine ⟨4967748622277895569347453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6623664829703860759129937 4967748622277895569347453)
      ·
        refine ⟨1862905733354210838505295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4967748622277895569347453 1862905733354210838505295)
        ·
          refine ⟨2794358600031316257757943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1862905733354210838505295 2794358600031316257757943)
          ·
            refine ⟨4191537900046974386636915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2794358600031316257757943 4191537900046974386636915)
            ·
              refine ⟨6287306850070461579955373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4191537900046974386636915 6287306850070461579955373)
              ·
                refine ⟨2357740068776423092483265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6287306850070461579955373 2357740068776423092483265)
                ·
                  refine ⟨1768305051582317319362449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2357740068776423092483265 1768305051582317319362449)
                  ·
                    refine ⟨1326228788686737989521837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1768305051582317319362449 1326228788686737989521837)
                    ·
                      refine ⟨497335795757526746070689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1326228788686737989521837 497335795757526746070689)
                      ·
                        rfl

theorem cell23_968558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_968558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_968558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_968558 prefixEnd_968558 := by exact prefixLift 968558
  have htrace : WordTrace (prefixWord ++ tailWord_968558) baseStart_968558 baseEnd_968558 := by
    simpa [prefixWord, tailWord_968558, baseEnd_968558] using wordTrace_append hprefix tailTrace_968558
  have hstable : (prefixWord ++ tailWord_968558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968558).length < 2 ^ (prefixWord ++ tailWord_968558).sum := by decide
  have hdescent : baseEnd_968558 < baseStart_968558 := by decide
  rcases family_descends (prefixWord ++ tailWord_968558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968611 : List Nat := [1, 1, 1, 4, 1, 2, 1, 6, 1, 1, 4]
def baseStart_968611 : Nat := 118140960795 + 968611 * 2 ^ 59
def prefixEnd_968611 : Nat := 4983230072969 + 3 ^ 40 * 968611 * 2
def baseEnd_968611 : Nat := 497363010232215038707945

theorem tailTrace_968611 : CollatzResearch.WordTrace tailWord_968611 prefixEnd_968611 497363010232215038707945 := by
  unfold tailWord_968611
  simp only [CollatzResearch.WordTrace]
  refine ⟨35328145493895247433705687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23552096995930164955803791 35328145493895247433705687)
  ·
    refine ⟨52992218240842871150558531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35328145493895247433705687 52992218240842871150558531)
    ·
      refine ⟨79488327361264306725837797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52992218240842871150558531 79488327361264306725837797)
      ·
        refine ⟨14904061380237057511094587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79488327361264306725837797 14904061380237057511094587)
        ·
          refine ⟨22356092070355586266641881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14904061380237057511094587 22356092070355586266641881)
          ·
            refine ⟨16767069052766689699981411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22356092070355586266641881 16767069052766689699981411)
            ·
              refine ⟨25150603579150034549972117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16767069052766689699981411 25150603579150034549972117)
              ·
                refine ⟨1178934542772657869529943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 25150603579150034549972117 1178934542772657869529943)
                ·
                  refine ⟨1768401814158986804294915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1178934542772657869529943 1768401814158986804294915)
                  ·
                    refine ⟨2652602721238480206442373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1768401814158986804294915 2652602721238480206442373)
                    ·
                      refine ⟨497363010232215038707945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2652602721238480206442373 497363010232215038707945)
                      ·
                        rfl

theorem cell23_968611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 6, 1, 1, 4].length) (baseStart_968611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_968611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_968611 prefixEnd_968611 := by exact prefixLift 968611
  have htrace : WordTrace (prefixWord ++ tailWord_968611) baseStart_968611 baseEnd_968611 := by
    simpa [prefixWord, tailWord_968611, baseEnd_968611] using wordTrace_append hprefix tailTrace_968611
  have hstable : (prefixWord ++ tailWord_968611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968611).length < 2 ^ (prefixWord ++ tailWord_968611).sum := by decide
  have hdescent : baseEnd_968611 < baseStart_968611 := by decide
  rcases family_descends (prefixWord ++ tailWord_968611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968615 : List Nat := [1, 1, 6, 1, 2, 1, 3, 1, 2, 3, 2]
def baseStart_968615 : Nat := 118140960795 + 968615 * 2 ^ 59
def prefixEnd_968615 : Nat := 4983230072969 + 3 ^ 40 * 968615 * 2
def baseEnd_968615 : Nat := 497365064154833023057927

theorem tailTrace_968615 : CollatzResearch.WordTrace tailWord_968615 prefixEnd_968615 497365064154833023057927 := by
  unfold tailWord_968615
  simp only [CollatzResearch.WordTrace]
  refine ⟨35328291385880756116851299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23552194257253837411234199 35328291385880756116851299)
  ·
    refine ⟨52992437078821134175276949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35328291385880756116851299 52992437078821134175276949)
    ·
      refine ⟨2484020488069740664466107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 52992437078821134175276949 2484020488069740664466107)
      ·
        refine ⟨3726030732104610996699161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2484020488069740664466107 3726030732104610996699161)
        ·
          refine ⟨2794523049078458247524371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3726030732104610996699161 2794523049078458247524371)
          ·
            refine ⟨4191784573617687371286557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2794523049078458247524371 4191784573617687371286557)
            ·
              refine ⟨1571919215106632764232459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4191784573617687371286557 1571919215106632764232459)
              ·
                refine ⟨2357878822659949146348689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1571919215106632764232459 2357878822659949146348689)
                ·
                  refine ⟨1768409116994961859761517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2357878822659949146348689 1768409116994961859761517)
                  ·
                    refine ⟨663153418873110697410569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1768409116994961859761517 663153418873110697410569)
                    ·
                      refine ⟨497365064154833023057927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 663153418873110697410569 497365064154833023057927)
                      ·
                        rfl

theorem cell23_968615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3, 1, 2, 3, 2].length) (baseStart_968615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_968615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_968615 prefixEnd_968615 := by exact prefixLift 968615
  have htrace : WordTrace (prefixWord ++ tailWord_968615) baseStart_968615 baseEnd_968615 := by
    simpa [prefixWord, tailWord_968615, baseEnd_968615] using wordTrace_append hprefix tailTrace_968615
  have hstable : (prefixWord ++ tailWord_968615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968615).length < 2 ^ (prefixWord ++ tailWord_968615).sum := by decide
  have hdescent : baseEnd_968615 < baseStart_968615 := by decide
  rcases family_descends (prefixWord ++ tailWord_968615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968625 : List Nat := [1, 2, 2, 4, 2, 3, 2, 1, 1, 5]
def baseStart_968625 : Nat := 118140960795 + 968625 * 2 ^ 59
def prefixEnd_968625 : Nat := 4983230072969 + 3 ^ 40 * 968625 * 2
def baseEnd_968625 : Nat := 165790066320459327977627

theorem tailTrace_968625 : CollatzResearch.WordTrace tailWord_968625 prefixEnd_968625 165790066320459327977627 := by
  unfold tailWord_968625
  simp only [CollatzResearch.WordTrace]
  refine ⟨35328656115844527824715329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23552437410563018549810219 35328656115844527824715329)
  ·
    refine ⟨26496492086883395868536497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35328656115844527824715329 26496492086883395868536497)
    ·
      refine ⟨19872369065162546901402373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26496492086883395868536497 19872369065162546901402373)
      ·
        refine ⟨3726069199717977544012945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19872369065162546901402373 3726069199717977544012945)
        ·
          refine ⟨2794551899788483158009709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3726069199717977544012945 2794551899788483158009709)
          ·
            refine ⟨1047956962420681184253641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2794551899788483158009709 1047956962420681184253641)
            ·
              refine ⟨785967721815510888190231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1047956962420681184253641 785967721815510888190231)
              ·
                refine ⟨1178951582723266332285347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 785967721815510888190231 1178951582723266332285347)
                ·
                  refine ⟨1768427374084899498428021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1178951582723266332285347 1768427374084899498428021)
                  ·
                    refine ⟨165790066320459327977627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1768427374084899498428021 165790066320459327977627)
                    ·
                      rfl

theorem cell23_968625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 2, 1, 1, 5].length) (baseStart_968625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_968625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_968625 prefixEnd_968625 := by exact prefixLift 968625
  have htrace : WordTrace (prefixWord ++ tailWord_968625) baseStart_968625 baseEnd_968625 := by
    simpa [prefixWord, tailWord_968625, baseEnd_968625] using wordTrace_append hprefix tailTrace_968625
  have hstable : (prefixWord ++ tailWord_968625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968625).length < 2 ^ (prefixWord ++ tailWord_968625).sum := by decide
  have hdescent : baseEnd_968625 < baseStart_968625 := by decide
  rcases family_descends (prefixWord ++ tailWord_968625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968638 : List Nat := [4, 2, 1, 1, 1, 4, 1, 1, 4, 4]
def baseStart_968638 : Nat := 118140960795 + 968638 * 2 ^ 59
def prefixEnd_968638 : Nat := 4983230072969 + 3 ^ 40 * 968638 * 2
def baseEnd_968638 : Nat := 165792291403295477690107

theorem tailTrace_968638 : CollatzResearch.WordTrace tailWord_968638 prefixEnd_968638 165792291403295477690107 := by
  unfold tailWord_968638
  simp only [CollatzResearch.WordTrace]
  refine ⟨4416141283099678880617321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23552753509864954029959045 4416141283099678880617321)
  ·
    refine ⟨3312105962324759160462991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4416141283099678880617321 3312105962324759160462991)
    ·
      refine ⟨4968158943487138740694487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3312105962324759160462991 4968158943487138740694487)
      ·
        refine ⟨7452238415230708111041731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4968158943487138740694487 7452238415230708111041731)
        ·
          refine ⟨11178357622846062166562597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7452238415230708111041731 11178357622846062166562597)
          ·
            refine ⟨2095942054283636656230487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11178357622846062166562597 2095942054283636656230487)
            ·
              refine ⟨3143913081425454984345731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2095942054283636656230487 3143913081425454984345731)
              ·
                refine ⟨4715869622138182476518597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3143913081425454984345731 4715869622138182476518597)
                ·
                  refine ⟨884225554150909214347237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4715869622138182476518597 884225554150909214347237)
                  ·
                    refine ⟨165792291403295477690107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 884225554150909214347237 165792291403295477690107)
                    ·
                      rfl

theorem cell23_968638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 1, 4, 4].length) (baseStart_968638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_968638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_968638 prefixEnd_968638 := by exact prefixLift 968638
  have htrace : WordTrace (prefixWord ++ tailWord_968638) baseStart_968638 baseEnd_968638 := by
    simpa [prefixWord, tailWord_968638, baseEnd_968638] using wordTrace_append hprefix tailTrace_968638
  have hstable : (prefixWord ++ tailWord_968638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968638).length < 2 ^ (prefixWord ++ tailWord_968638).sum := by decide
  have hdescent : baseEnd_968638 < baseStart_968638 := by decide
  rcases family_descends (prefixWord ++ tailWord_968638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968658 : List Nat := [3, 2, 2, 3, 2, 1, 1, 1, 1, 1, 6]
def baseStart_968658 : Nat := 118140960795 + 968658 * 2 ^ 59
def prefixEnd_968658 : Nat := 4983230072969 + 3 ^ 40 * 968658 * 2
def baseEnd_968658 : Nat := 497387143822976354820229

theorem tailTrace_968658 : CollatzResearch.WordTrace tailWord_968658 prefixEnd_968658 497387143822976354820229 := by
  unfold tailWord_968658
  simp only [CollatzResearch.WordTrace]
  refine ⟨8832464931181243615166657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23553239816483316307111085 8832464931181243615166657)
  ·
    refine ⟨6624348698385932711374993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8832464931181243615166657 6624348698385932711374993)
    ·
      refine ⟨4968261523789449533531245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6624348698385932711374993 4968261523789449533531245)
      ·
        refine ⟨1863098071421043575074217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4968261523789449533531245 1863098071421043575074217)
        ·
          refine ⟨1397323553565782681305663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1863098071421043575074217 1397323553565782681305663)
          ·
            refine ⟨2095985330348674021958495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1397323553565782681305663 2095985330348674021958495)
            ·
              refine ⟨3143977995523011032937743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2095985330348674021958495 3143977995523011032937743)
              ·
                refine ⟨4715966993284516549406615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3143977995523011032937743 4715966993284516549406615)
                ·
                  refine ⟨7073950489926774824109923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4715966993284516549406615 7073950489926774824109923)
                  ·
                    refine ⟨10610925734890162236164885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7073950489926774824109923 10610925734890162236164885)
                    ·
                      refine ⟨497387143822976354820229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10610925734890162236164885 497387143822976354820229)
                      ·
                        rfl

theorem cell23_968658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_968658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_968658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_968658 prefixEnd_968658 := by exact prefixLift 968658
  have htrace : WordTrace (prefixWord ++ tailWord_968658) baseStart_968658 baseEnd_968658 := by
    simpa [prefixWord, tailWord_968658, baseEnd_968658] using wordTrace_append hprefix tailTrace_968658
  have hstable : (prefixWord ++ tailWord_968658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968658).length < 2 ^ (prefixWord ++ tailWord_968658).sum := by decide
  have hdescent : baseEnd_968658 < baseStart_968658 := by decide
  rcases family_descends (prefixWord ++ tailWord_968658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968662 : List Nat := [5, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4]
def baseStart_968662 : Nat := 118140960795 + 968662 * 2 ^ 59
def prefixEnd_968662 : Nat := 4983230072969 + 3 ^ 40 * 968662 * 2
def baseEnd_968662 : Nat := 497389197745594339170211

theorem tailTrace_968662 : CollatzResearch.WordTrace tailWord_968662 prefixEnd_968662 497389197745594339170211 := by
  unfold tailWord_968662
  simp only [CollatzResearch.WordTrace]
  refine ⟨2208125351044405196488265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23553337077806988762541493 2208125351044405196488265)
  ·
    refine ⟨1656094013283303897366199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2208125351044405196488265 1656094013283303897366199)
    ·
      refine ⟨2484141019924955846049299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1656094013283303897366199 2484141019924955846049299)
      ·
        refine ⟨3726211529887433769073949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2484141019924955846049299 3726211529887433769073949)
        ·
          refine ⟨1397329323707787663402731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3726211529887433769073949 1397329323707787663402731)
          ·
            refine ⟨2095993985561681495104097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1397329323707787663402731 2095993985561681495104097)
            ·
              refine ⟨1571995489171261121328073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2095993985561681495104097 1571995489171261121328073)
              ·
                refine ⟨1178996616878445840996055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1571995489171261121328073 1178996616878445840996055)
                ·
                  refine ⟨1768494925317668761494083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1178996616878445840996055 1768494925317668761494083)
                  ·
                    refine ⟨2652742387976503142241125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1768494925317668761494083 2652742387976503142241125)
                    ·
                      refine ⟨497389197745594339170211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2652742387976503142241125 497389197745594339170211)
                      ·
                        rfl

theorem cell23_968662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4].length) (baseStart_968662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_968662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_968662 prefixEnd_968662 := by exact prefixLift 968662
  have htrace : WordTrace (prefixWord ++ tailWord_968662) baseStart_968662 baseEnd_968662 := by
    simpa [prefixWord, tailWord_968662, baseEnd_968662] using wordTrace_append hprefix tailTrace_968662
  have hstable : (prefixWord ++ tailWord_968662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968662).length < 2 ^ (prefixWord ++ tailWord_968662).sum := by decide
  have hdescent : baseEnd_968662 < baseStart_968662 := by decide
  rcases family_descends (prefixWord ++ tailWord_968662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968665 : List Nat := [1, 2, 1, 2, 6, 1, 2, 2, 1, 2, 3]
def baseStart_968665 : Nat := 118140960795 + 968665 * 2 ^ 59
def prefixEnd_968665 : Nat := 4983230072969 + 3 ^ 40 * 968665 * 2
def baseEnd_968665 : Nat := 497390738187557827432697

theorem tailTrace_968665 : CollatzResearch.WordTrace tailWord_968665 prefixEnd_968665 497390738187557827432697 := by
  unfold tailWord_968665
  simp only [CollatzResearch.WordTrace]
  refine ⟨35330115035699614656171449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23553410023799743104114299 35330115035699614656171449)
  ·
    refine ⟨26497586276774710992128587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35330115035699614656171449 26497586276774710992128587)
    ·
      refine ⟨39746379415162066488192881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26497586276774710992128587 39746379415162066488192881)
      ·
        refine ⟨29809784561371549866144661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39746379415162066488192881 29809784561371549866144661)
        ·
          refine ⟨1397333651314291399975531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 29809784561371549866144661 1397333651314291399975531)
          ·
            refine ⟨2096000476971437099963297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1397333651314291399975531 2096000476971437099963297)
            ·
              refine ⟨1572000357728577824972473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2096000476971437099963297 1572000357728577824972473)
              ·
                refine ⟨1179000268296433368729355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1572000357728577824972473 1179000268296433368729355)
                ·
                  refine ⟨1768500402444650053094033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1179000268296433368729355 1768500402444650053094033)
                  ·
                    refine ⟨1326375301833487539820525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1768500402444650053094033 1326375301833487539820525)
                    ·
                      refine ⟨497390738187557827432697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1326375301833487539820525 497390738187557827432697)
                      ·
                        rfl

theorem cell23_968665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 2, 2, 1, 2, 3].length) (baseStart_968665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_968665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_968665 prefixEnd_968665 := by exact prefixLift 968665
  have htrace : WordTrace (prefixWord ++ tailWord_968665) baseStart_968665 baseEnd_968665 := by
    simpa [prefixWord, tailWord_968665, baseEnd_968665] using wordTrace_append hprefix tailTrace_968665
  have hstable : (prefixWord ++ tailWord_968665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968665).length < 2 ^ (prefixWord ++ tailWord_968665).sum := by decide
  have hdescent : baseEnd_968665 < baseStart_968665 := by decide
  rcases family_descends (prefixWord ++ tailWord_968665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968684 : List Nat := [2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 8]
def baseStart_968684 : Nat := 118140960795 + 968684 * 2 ^ 59
def prefixEnd_968684 : Nat := 4983230072969 + 3 ^ 40 * 968684 * 2
def baseEnd_968684 : Nat := 497400494319993253095109

theorem tailTrace_968684 : CollatzResearch.WordTrace tailWord_968684 prefixEnd_968684 497400494319993253095109 := by
  unfold tailWord_968684
  simp only [CollatzResearch.WordTrace]
  refine ⟨17665404011315390450556553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23553872015087187267408737 17665404011315390450556553)
  ·
    refine ⟨13249053008486542837917415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17665404011315390450556553 13249053008486542837917415)
    ·
      refine ⟨19873579512729814256876123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13249053008486542837917415 19873579512729814256876123)
      ·
        refine ⟨29810369269094721385314185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19873579512729814256876123 29810369269094721385314185)
        ·
          refine ⟨22357776951821041038985639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29810369269094721385314185 22357776951821041038985639)
          ·
            refine ⟨33536665427731561558478459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22357776951821041038985639 33536665427731561558478459)
            ·
              refine ⟨50304998141597342337717689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33536665427731561558478459 50304998141597342337717689)
              ·
                refine ⟨37728748606198006753288267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50304998141597342337717689 37728748606198006753288267)
                ·
                  refine ⟨56593122909297010129932401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37728748606198006753288267 56593122909297010129932401)
                  ·
                    refine ⟨42444842181972757597449301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56593122909297010129932401 42444842181972757597449301)
                    ·
                      refine ⟨497400494319993253095109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 42444842181972757597449301 497400494319993253095109)
                      ·
                        rfl

theorem cell23_968684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 8].length) (baseStart_968684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_968684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_968684 prefixEnd_968684 := by exact prefixLift 968684
  have htrace : WordTrace (prefixWord ++ tailWord_968684) baseStart_968684 baseEnd_968684 := by
    simpa [prefixWord, tailWord_968684, baseEnd_968684] using wordTrace_append hprefix tailTrace_968684
  have hstable : (prefixWord ++ tailWord_968684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968684).length < 2 ^ (prefixWord ++ tailWord_968684).sum := by decide
  have hdescent : baseEnd_968684 < baseStart_968684 := by decide
  rcases family_descends (prefixWord ++ tailWord_968684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968685 : List Nat := [1, 5, 1, 4, 2, 1, 9]
def baseStart_968685 : Nat := 118140960795 + 968685 * 2 ^ 59
def prefixEnd_968685 : Nat := 4983230072969 + 3 ^ 40 * 968685 * 2
def baseEnd_968685 : Nat := 6140753182724046286205

theorem tailTrace_968685 : CollatzResearch.WordTrace tailWord_968685 prefixEnd_968685 6140753182724046286205 := by
  unfold tailWord_968685
  simp only [CollatzResearch.WordTrace]
  refine ⟨35330844495627158071899509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23553896330418105381266339 35330844495627158071899509)
  ·
    refine ⟨3312266671465046069240579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35330844495627158071899509 3312266671465046069240579)
    ·
      refine ⟨4968400007197569103860869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3312266671465046069240579 4968400007197569103860869)
      ·
        refine ⟨931575001349544206973913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4968400007197569103860869 931575001349544206973913)
        ·
          refine ⟨698681251012158155230435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 931575001349544206973913 698681251012158155230435)
          ·
            refine ⟨1048021876518237232845653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 698681251012158155230435 1048021876518237232845653)
            ·
              refine ⟨6140753182724046286205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1048021876518237232845653 6140753182724046286205)
              ·
                rfl

theorem cell23_968685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 9].length) (baseStart_968685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_968685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_968685 prefixEnd_968685 := by exact prefixLift 968685
  have htrace : WordTrace (prefixWord ++ tailWord_968685) baseStart_968685 baseEnd_968685 := by
    simpa [prefixWord, tailWord_968685, baseEnd_968685] using wordTrace_append hprefix tailTrace_968685
  have hstable : (prefixWord ++ tailWord_968685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968685).length < 2 ^ (prefixWord ++ tailWord_968685).sum := by decide
  have hdescent : baseEnd_968685 < baseStart_968685 := by decide
  rcases family_descends (prefixWord ++ tailWord_968685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968752 : List Nat := [2, 1, 1, 1, 2, 6, 2, 2, 2, 2, 2]
def baseStart_968752 : Nat := 118140960795 + 968752 * 2 ^ 59
def prefixEnd_968752 : Nat := 4983230072969 + 3 ^ 40 * 968752 * 2
def baseEnd_968752 : Nat := 497435411004498987044797

theorem tailTrace_968752 : CollatzResearch.WordTrace tailWord_968752 prefixEnd_968752 497435411004498987044797 := by
  unfold tailWord_968752
  simp only [CollatzResearch.WordTrace]
  refine ⟨17666644093192214257294255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23555525457589619009725673 17666644093192214257294255)
  ·
    refine ⟨26499966139788321385941383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17666644093192214257294255 26499966139788321385941383)
    ·
      refine ⟨39749949209682482078912075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26499966139788321385941383 39749949209682482078912075)
      ·
        refine ⟨59624923814523723118368113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39749949209682482078912075 59624923814523723118368113)
        ·
          refine ⟨44718692860892792338776085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59624923814523723118368113 44718692860892792338776085)
          ·
            refine ⟨2096188727854349640880129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 44718692860892792338776085 2096188727854349640880129)
            ·
              refine ⟨1572141545890762230660097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2096188727854349640880129 1572141545890762230660097)
              ·
                refine ⟨1179106159418071672995073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1572141545890762230660097 1179106159418071672995073)
                ·
                  refine ⟨884329619563553754746305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1179106159418071672995073 884329619563553754746305)
                  ·
                    refine ⟨663247214672665316059729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 884329619563553754746305 663247214672665316059729)
                    ·
                      refine ⟨497435411004498987044797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 663247214672665316059729 497435411004498987044797)
                      ·
                        rfl

theorem cell23_968752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2, 2, 2, 2, 2].length) (baseStart_968752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_968752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_968752 prefixEnd_968752 := by exact prefixLift 968752
  have htrace : WordTrace (prefixWord ++ tailWord_968752) baseStart_968752 baseEnd_968752 := by
    simpa [prefixWord, tailWord_968752, baseEnd_968752] using wordTrace_append hprefix tailTrace_968752
  have hstable : (prefixWord ++ tailWord_968752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968752).length < 2 ^ (prefixWord ++ tailWord_968752).sum := by decide
  have hdescent : baseEnd_968752 < baseStart_968752 := by decide
  rcases family_descends (prefixWord ++ tailWord_968752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968758 : List Nat := [5, 1, 2, 1, 1, 1, 2, 3, 7]
def baseStart_968758 : Nat := 118140960795 + 968758 * 2 ^ 59
def prefixEnd_968758 : Nat := 4983230072969 + 3 ^ 40 * 968758 * 2
def baseEnd_968758 : Nat := 55270943543158440396641

theorem tailTrace_968758 : CollatzResearch.WordTrace tailWord_968758 prefixEnd_968758 55270943543158440396641 := by
  unfold tailWord_968758
  simp only [CollatzResearch.WordTrace]
  refine ⟨2208344189022668221206683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23555671349575127692871285 2208344189022668221206683)
  ·
    refine ⟨3312516283534002331810025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2208344189022668221206683 3312516283534002331810025)
    ·
      refine ⟨2484387212650501748857519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3312516283534002331810025 2484387212650501748857519)
      ·
        refine ⟨3726580818975752623286279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2484387212650501748857519 3726580818975752623286279)
        ·
          refine ⟨5589871228463628934929419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3726580818975752623286279 5589871228463628934929419)
          ·
            refine ⟨8384806842695443402394129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5589871228463628934929419 8384806842695443402394129)
            ·
              refine ⟨6288605132021582551795597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8384806842695443402394129 6288605132021582551795597)
              ·
                refine ⟨2358226924508093456923349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6288605132021582551795597 2358226924508093456923349)
                ·
                  refine ⟨55270943543158440396641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2358226924508093456923349 55270943543158440396641)
                  ·
                    rfl

theorem cell23_968758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 3, 7].length) (baseStart_968758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_968758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_968758 prefixEnd_968758 := by exact prefixLift 968758
  have htrace : WordTrace (prefixWord ++ tailWord_968758) baseStart_968758 baseEnd_968758 := by
    simpa [prefixWord, tailWord_968758, baseEnd_968758] using wordTrace_append hprefix tailTrace_968758
  have hstable : (prefixWord ++ tailWord_968758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968758).length < 2 ^ (prefixWord ++ tailWord_968758).sum := by decide
  have hdescent : baseEnd_968758 < baseStart_968758 := by decide
  rcases family_descends (prefixWord ++ tailWord_968758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968768 : List Nat := [2, 1, 1, 2, 2, 5, 1, 1, 2, 3, 3]
def baseStart_968768 : Nat := 118140960795 + 968768 * 2 ^ 59
def prefixEnd_968768 : Nat := 4983230072969 + 3 ^ 40 * 968768 * 2
def baseEnd_968768 : Nat := 497443626694970924444723

theorem tailTrace_968768 : CollatzResearch.WordTrace tailWord_968768 prefixEnd_968768 497443626694970924444723 := by
  unfold tailWord_968768
  simp only [CollatzResearch.WordTrace]
  refine ⟨17666935877163231623585479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23555914502884308831447305 17666935877163231623585479)
  ·
    refine ⟨26500403815744847435378219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17666935877163231623585479 26500403815744847435378219)
    ·
      refine ⟨39750605723617271153067329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26500403815744847435378219 39750605723617271153067329)
      ·
        refine ⟨29812954292712953364800497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39750605723617271153067329 29812954292712953364800497)
        ·
          refine ⟨22359715719534715023600373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29812954292712953364800497 22359715719534715023600373)
          ·
            refine ⟨2096223348706379533462535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22359715719534715023600373 2096223348706379533462535)
            ·
              refine ⟨3144335023059569300193803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2096223348706379533462535 3144335023059569300193803)
              ·
                refine ⟨4716502534589353950290705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3144335023059569300193803 4716502534589353950290705)
                ·
                  refine ⟨3537376900942015462718029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4716502534589353950290705 3537376900942015462718029)
                  ·
                    refine ⟨1326516337853255798519261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3537376900942015462718029 1326516337853255798519261)
                    ·
                      refine ⟨497443626694970924444723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1326516337853255798519261 497443626694970924444723)
                      ·
                        rfl

theorem cell23_968768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 1, 2, 3, 3].length) (baseStart_968768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_968768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_968768 prefixEnd_968768 := by exact prefixLift 968768
  have htrace : WordTrace (prefixWord ++ tailWord_968768) baseStart_968768 baseEnd_968768 := by
    simpa [prefixWord, tailWord_968768, baseEnd_968768] using wordTrace_append hprefix tailTrace_968768
  have hstable : (prefixWord ++ tailWord_968768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968768).length < 2 ^ (prefixWord ++ tailWord_968768).sum := by decide
  have hdescent : baseEnd_968768 < baseStart_968768 := by decide
  rcases family_descends (prefixWord ++ tailWord_968768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968778 : List Nat := [3, 1, 2, 1, 1, 2, 1, 1, 4, 5, 2]
def baseStart_968778 : Nat := 118140960795 + 968778 * 2 ^ 59
def prefixEnd_968778 : Nat := 4983230072969 + 3 ^ 40 * 968778 * 2
def baseEnd_968778 : Nat := 497448761501515885319677

theorem tailTrace_968778 : CollatzResearch.WordTrace tailWord_968778 prefixEnd_968778 497448761501515885319677 := by
  unfold tailWord_968778
  simp only [CollatzResearch.WordTrace]
  refine ⟨8833559121072558738758747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23556157656193489970023325 8833559121072558738758747)
  ·
    refine ⟨13250338681608838108138121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8833559121072558738758747 13250338681608838108138121)
    ·
      refine ⟨9937754011206628581103591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13250338681608838108138121 9937754011206628581103591)
      ·
        refine ⟨14906631016809942871655387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9937754011206628581103591 14906631016809942871655387)
        ·
          refine ⟨22359946525214914307483081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14906631016809942871655387 22359946525214914307483081)
          ·
            refine ⟨16769959893911185730612311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22359946525214914307483081 16769959893911185730612311)
            ·
              refine ⟨25154939840866778595918467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16769959893911185730612311 25154939840866778595918467)
              ·
                refine ⟨37732409761300167893877701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25154939840866778595918467 37732409761300167893877701)
                ·
                  refine ⟨7074826830243781480102069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37732409761300167893877701 7074826830243781480102069)
                  ·
                    refine ⟨663265015335354513759569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7074826830243781480102069 663265015335354513759569)
                    ·
                      refine ⟨497448761501515885319677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 663265015335354513759569 497448761501515885319677)
                      ·
                        rfl

theorem cell23_968778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 4, 5, 2].length) (baseStart_968778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_968778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_968778 prefixEnd_968778 := by exact prefixLift 968778
  have htrace : WordTrace (prefixWord ++ tailWord_968778) baseStart_968778 baseEnd_968778 := by
    simpa [prefixWord, tailWord_968778, baseEnd_968778] using wordTrace_append hprefix tailTrace_968778
  have hstable : (prefixWord ++ tailWord_968778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968778).length < 2 ^ (prefixWord ++ tailWord_968778).sum := by decide
  have hdescent : baseEnd_968778 < baseStart_968778 := by decide
  rcases family_descends (prefixWord ++ tailWord_968778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968825 : List Nat := [1, 2, 1, 3, 4, 1, 2, 1, 2, 4, 2]
def baseStart_968825 : Nat := 118140960795 + 968825 * 2 ^ 59
def prefixEnd_968825 : Nat := 4983230072969 + 3 ^ 40 * 968825 * 2
def baseEnd_968825 : Nat := 497472895092277201431961

theorem tailTrace_968825 : CollatzResearch.WordTrace tailWord_968825 prefixEnd_968825 497472895092277201431961 := by
  unfold tailWord_968825
  simp only [CollatzResearch.WordTrace]
  refine ⟨35335950715119961981995929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23557300476746641321330619 35335950715119961981995929)
  ·
    refine ⟨26501963036339971486496947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35335950715119961981995929 26501963036339971486496947)
    ·
      refine ⟨39752944554509957229745421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26501963036339971486496947 39752944554509957229745421)
      ·
        refine ⟨14907354207941233961154533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39752944554509957229745421 14907354207941233961154533)
        ·
          refine ⟨2795128913988981367716475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14907354207941233961154533 2795128913988981367716475)
          ·
            refine ⟨4192693370983472051574713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2795128913988981367716475 4192693370983472051574713)
            ·
              refine ⟨3144520028237604038681035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4192693370983472051574713 3144520028237604038681035)
              ·
                refine ⟨4716780042356406058021553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3144520028237604038681035 4716780042356406058021553)
                ·
                  refine ⟨3537585031767304543516165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4716780042356406058021553 3537585031767304543516165)
                  ·
                    refine ⟨663297193456369601909281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3537585031767304543516165 663297193456369601909281)
                    ·
                      refine ⟨497472895092277201431961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 663297193456369601909281 497472895092277201431961)
                      ·
                        rfl

theorem cell23_968825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 1, 2, 4, 2].length) (baseStart_968825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_968825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_968825 prefixEnd_968825 := by exact prefixLift 968825
  have htrace : WordTrace (prefixWord ++ tailWord_968825) baseStart_968825 baseEnd_968825 := by
    simpa [prefixWord, tailWord_968825, baseEnd_968825] using wordTrace_append hprefix tailTrace_968825
  have hstable : (prefixWord ++ tailWord_968825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968825).length < 2 ^ (prefixWord ++ tailWord_968825).sum := by decide
  have hdescent : baseEnd_968825 < baseStart_968825 := by decide
  rcases family_descends (prefixWord ++ tailWord_968825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968828 : List Nat := [2, 2, 2, 1, 1, 4, 1, 2, 1, 4, 3]
def baseStart_968828 : Nat := 118140960795 + 968828 * 2 ^ 59
def prefixEnd_968828 : Nat := 4983230072969 + 3 ^ 40 * 968828 * 2
def baseEnd_968828 : Nat := 497474435534240689694447

theorem tailTrace_968828 : CollatzResearch.WordTrace tailWord_968828 prefixEnd_968828 497474435534240689694447 := by
  unfold tailWord_968828
  simp only [CollatzResearch.WordTrace]
  refine ⟨17668030067054546747177569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23557373422739395662903425 17668030067054546747177569)
  ·
    refine ⟨13251022550290910060383177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17668030067054546747177569 13251022550290910060383177)
    ·
      refine ⟨9938266912718182545287383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13251022550290910060383177 9938266912718182545287383)
      ·
        refine ⟨14907400369077273817931075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9938266912718182545287383 14907400369077273817931075)
        ·
          refine ⟨22361100553615910726896613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14907400369077273817931075 22361100553615910726896613)
          ·
            refine ⟨4192706353802983261293115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22361100553615910726896613 4192706353802983261293115)
            ·
              refine ⟨6289059530704474891939673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4192706353802983261293115 6289059530704474891939673)
              ·
                refine ⟨4716794648028356168954755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6289059530704474891939673 4716794648028356168954755)
                ·
                  refine ⟨7075191972042534253432133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4716794648028356168954755 7075191972042534253432133)
                  ·
                    refine ⟨1326598494757975172518525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7075191972042534253432133 1326598494757975172518525)
                    ·
                      refine ⟨497474435534240689694447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1326598494757975172518525 497474435534240689694447)
                      ·
                        rfl

theorem cell23_968828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 2, 1, 4, 3].length) (baseStart_968828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_968828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_968828 prefixEnd_968828 := by exact prefixLift 968828
  have htrace : WordTrace (prefixWord ++ tailWord_968828) baseStart_968828 baseEnd_968828 := by
    simpa [prefixWord, tailWord_968828, baseEnd_968828] using wordTrace_append hprefix tailTrace_968828
  have hstable : (prefixWord ++ tailWord_968828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968828).length < 2 ^ (prefixWord ++ tailWord_968828).sum := by decide
  have hdescent : baseEnd_968828 < baseStart_968828 := by decide
  rcases family_descends (prefixWord ++ tailWord_968828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968928 : List Nat := [2, 1, 1, 3, 1, 3, 1, 2, 3, 2, 4]
def baseStart_968928 : Nat := 118140960795 + 968928 * 2 ^ 59
def prefixEnd_968928 : Nat := 4983230072969 + 3 ^ 40 * 968928 * 2
def baseEnd_968928 : Nat := 497525783599690298443987

theorem tailTrace_968928 : CollatzResearch.WordTrace tailWord_968928 prefixEnd_968928 497525783599690298443987 := by
  unfold tailWord_968928
  simp only [CollatzResearch.WordTrace]
  refine ⟨17669853716873405286497719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23559804955831207048663625 17669853716873405286497719)
  ·
    refine ⟨26504780575310107929746579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17669853716873405286497719 26504780575310107929746579)
    ·
      refine ⟨39757170862965161894619869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26504780575310107929746579 39757170862965161894619869)
      ·
        refine ⟨14908939073611935710482451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39757170862965161894619869 14908939073611935710482451)
        ·
          refine ⟨22363408610417903565723677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14908939073611935710482451 22363408610417903565723677)
          ·
            refine ⟨8386278228906713837146379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22363408610417903565723677 8386278228906713837146379)
            ·
              refine ⟨12579417343360070755719569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8386278228906713837146379 12579417343360070755719569)
              ·
                refine ⟨9434563007520053066789677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12579417343360070755719569 9434563007520053066789677)
                ·
                  refine ⟨3537961127820019900046129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9434563007520053066789677 3537961127820019900046129)
                  ·
                    refine ⟨2653470845865014925034597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3537961127820019900046129 2653470845865014925034597)
                    ·
                      refine ⟨497525783599690298443987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2653470845865014925034597 497525783599690298443987)
                      ·
                        rfl

theorem cell23_968928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2, 4].length) (baseStart_968928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_968928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_968928 prefixEnd_968928 := by exact prefixLift 968928
  have htrace : WordTrace (prefixWord ++ tailWord_968928) baseStart_968928 baseEnd_968928 := by
    simpa [prefixWord, tailWord_968928, baseEnd_968928] using wordTrace_append hprefix tailTrace_968928
  have hstable : (prefixWord ++ tailWord_968928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968928).length < 2 ^ (prefixWord ++ tailWord_968928).sum := by decide
  have hdescent : baseEnd_968928 < baseStart_968928 := by decide
  rcases family_descends (prefixWord ++ tailWord_968928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968932 : List Nat := [2, 3, 1, 1, 1, 2, 1, 5, 3, 2, 2]
def baseStart_968932 : Nat := 118140960795 + 968932 * 2 ^ 59
def prefixEnd_968932 : Nat := 4983230072969 + 3 ^ 40 * 968932 * 2
def baseEnd_968932 : Nat := 497527837522308282793969

theorem tailTrace_968932 : CollatzResearch.WordTrace tailWord_968932 prefixEnd_968932 497527837522308282793969 := by
  unfold tailWord_968932
  simp only [CollatzResearch.WordTrace]
  refine ⟨17669926662866159628070525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23559902217154879504094033 17669926662866159628070525)
  ·
    refine ⟨6626222498574809860526447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17669926662866159628070525 6626222498574809860526447)
    ·
      refine ⟨9939333747862214790789671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6626222498574809860526447 9939333747862214790789671)
      ·
        refine ⟨14909000621793322186184507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9939333747862214790789671 14909000621793322186184507)
        ·
          refine ⟨22363500932689983279276761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14909000621793322186184507 22363500932689983279276761)
          ·
            refine ⟨16772625699517487459457571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22363500932689983279276761 16772625699517487459457571)
            ·
              refine ⟨25158938549276231189186357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16772625699517487459457571 25158938549276231189186357)
              ·
                refine ⟨2358650488994646673986221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25158938549276231189186357 2358650488994646673986221)
                ·
                  refine ⟨884493933372992502744833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2358650488994646673986221 884493933372992502744833)
                  ·
                    refine ⟨663370450029744377058625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 884493933372992502744833 663370450029744377058625)
                    ·
                      refine ⟨497527837522308282793969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 663370450029744377058625 497527837522308282793969)
                      ·
                        rfl

theorem cell23_968932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 5, 3, 2, 2].length) (baseStart_968932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_968932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_968932 prefixEnd_968932 := by exact prefixLift 968932
  have htrace : WordTrace (prefixWord ++ tailWord_968932) baseStart_968932 baseEnd_968932 := by
    simpa [prefixWord, tailWord_968932, baseEnd_968932] using wordTrace_append hprefix tailTrace_968932
  have hstable : (prefixWord ++ tailWord_968932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968932).length < 2 ^ (prefixWord ++ tailWord_968932).sum := by decide
  have hdescent : baseEnd_968932 < baseStart_968932 := by decide
  rcases family_descends (prefixWord ++ tailWord_968932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968962 : List Nat := [3, 4, 1, 1, 2, 1, 2, 2, 1, 2, 4]
def baseStart_968962 : Nat := 118140960795 + 968962 * 2 ^ 59
def prefixEnd_968962 : Nat := 4983230072969 + 3 ^ 40 * 968962 * 2
def baseEnd_968962 : Nat := 497543241941943165418831

theorem tailTrace_968962 : CollatzResearch.WordTrace tailWord_968962 prefixEnd_968962 497543241941943165418831 := by
  unfold tailWord_968962
  simp only [CollatzResearch.WordTrace]
  refine ⟨8835236878905908594933285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23560631677082422919822093 8835236878905908594933285)
  ·
    refine ⟨1656606914794857861549991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8835236878905908594933285 1656606914794857861549991)
    ·
      refine ⟨2484910372192286792324987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1656606914794857861549991 2484910372192286792324987)
      ·
        refine ⟨3727365558288430188487481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2484910372192286792324987 3727365558288430188487481)
        ·
          refine ⟨2795524168716322641365611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3727365558288430188487481 2795524168716322641365611)
          ·
            refine ⟨4193286253074483962048417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2795524168716322641365611 4193286253074483962048417)
            ·
              refine ⟨3144964689805862971536313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4193286253074483962048417 3144964689805862971536313)
              ·
                refine ⟨2358723517354397228652235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3144964689805862971536313 2358723517354397228652235)
                ·
                  refine ⟨3538085276031595842978353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2358723517354397228652235 3538085276031595842978353)
                  ·
                    refine ⟨2653563957023696882233765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3538085276031595842978353 2653563957023696882233765)
                    ·
                      refine ⟨497543241941943165418831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2653563957023696882233765 497543241941943165418831)
                      ·
                        rfl

theorem cell23_968962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_968962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_968962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_968962 prefixEnd_968962 := by exact prefixLift 968962
  have htrace : WordTrace (prefixWord ++ tailWord_968962) baseStart_968962 baseEnd_968962 := by
    simpa [prefixWord, tailWord_968962, baseEnd_968962] using wordTrace_append hprefix tailTrace_968962
  have hstable : (prefixWord ++ tailWord_968962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968962).length < 2 ^ (prefixWord ++ tailWord_968962).sum := by decide
  have hdescent : baseEnd_968962 < baseStart_968962 := by decide
  rcases family_descends (prefixWord ++ tailWord_968962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968969 : List Nat := [1, 2, 1, 1, 3, 6, 2, 1, 1, 2, 3]
def baseStart_968969 : Nat := 118140960795 + 968969 * 2 ^ 59
def prefixEnd_968969 : Nat := 4983230072969 + 3 ^ 40 * 968969 * 2
def baseEnd_968969 : Nat := 497546836306524638031299

theorem tailTrace_968969 : CollatzResearch.WordTrace tailWord_968969 prefixEnd_968969 497546836306524638031299 := by
  unfold tailWord_968969
  simp only [CollatzResearch.WordTrace]
  refine ⟨35341202826598274575237961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23560801884398849716825307 35341202826598274575237961)
  ·
    refine ⟨26505902119948705931428471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35341202826598274575237961 26505902119948705931428471)
    ·
      refine ⟨39758853179923058897142707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26505902119948705931428471 39758853179923058897142707)
      ·
        refine ⟨59638279769884588345714061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39758853179923058897142707 59638279769884588345714061)
        ·
          refine ⟨22364354913706720629642773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59638279769884588345714061 22364354913706720629642773)
          ·
            refine ⟨1048329136580002529514505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 22364354913706720629642773 1048329136580002529514505)
            ·
              refine ⟨786246852435001897135879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1048329136580002529514505 786246852435001897135879)
              ·
                refine ⟨1179370278652502845703819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 786246852435001897135879 1179370278652502845703819)
                ·
                  refine ⟨1769055417978754268555729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1179370278652502845703819 1769055417978754268555729)
                  ·
                    refine ⟨1326791563484065701416797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1769055417978754268555729 1326791563484065701416797)
                    ·
                      refine ⟨497546836306524638031299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1326791563484065701416797 497546836306524638031299)
                      ·
                        rfl

theorem cell23_968969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 2, 1, 1, 2, 3].length) (baseStart_968969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_968969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_968969 prefixEnd_968969 := by exact prefixLift 968969
  have htrace : WordTrace (prefixWord ++ tailWord_968969) baseStart_968969 baseEnd_968969 := by
    simpa [prefixWord, tailWord_968969, baseEnd_968969] using wordTrace_append hprefix tailTrace_968969
  have hstable : (prefixWord ++ tailWord_968969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968969).length < 2 ^ (prefixWord ++ tailWord_968969).sum := by decide
  have hdescent : baseEnd_968969 < baseStart_968969 := by decide
  rcases family_descends (prefixWord ++ tailWord_968969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969006 : List Nat := [4, 1, 3, 3, 2, 1, 2, 7]
def baseStart_969006 : Nat := 118140960795 + 969006 * 2 ^ 59
def prefixEnd_969006 : Nat := 4983230072969 + 3 ^ 40 * 969006 * 2
def baseEnd_969006 : Nat := 18428364262620036787727

theorem tailTrace_969006 : CollatzResearch.WordTrace tailWord_969006 prefixEnd_969006 18428364262620036787727 := by
  unfold tailWord_969006
  simp only [CollatzResearch.WordTrace]
  refine ⟨4417819040933028736791859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23561701551642819929556581 4417819040933028736791859)
  ·
    refine ⟨6626728561399543105187789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4417819040933028736791859 6626728561399543105187789)
    ·
      refine ⟨2485023210524828664445421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6626728561399543105187789 2485023210524828664445421)
      ·
        refine ⟨931883703946810749167033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2485023210524828664445421 931883703946810749167033)
        ·
          refine ⟨698912777960108061875275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 931883703946810749167033 698912777960108061875275)
          ·
            refine ⟨1048369166940162092812913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 698912777960108061875275 1048369166940162092812913)
            ·
              refine ⟨786276875205121569609685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1048369166940162092812913 786276875205121569609685)
              ·
                refine ⟨18428364262620036787727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 786276875205121569609685 18428364262620036787727)
                ·
                  rfl

theorem cell23_969006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 2, 7].length) (baseStart_969006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_969006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_969006 prefixEnd_969006 := by exact prefixLift 969006
  have htrace : WordTrace (prefixWord ++ tailWord_969006) baseStart_969006 baseEnd_969006 := by
    simpa [prefixWord, tailWord_969006, baseEnd_969006] using wordTrace_append hprefix tailTrace_969006
  have hstable : (prefixWord ++ tailWord_969006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969006).length < 2 ^ (prefixWord ++ tailWord_969006).sum := by decide
  have hdescent : baseEnd_969006 < baseStart_969006 := by decide
  rcases family_descends (prefixWord ++ tailWord_969006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969048 : List Nat := [2, 1, 2, 2, 1, 1, 2, 1, 2, 1, 8]
def baseStart_969048 : Nat := 118140960795 + 969048 * 2 ^ 59
def prefixEnd_969048 : Nat := 4983230072969 + 3 ^ 40 * 969048 * 2
def baseEnd_969048 : Nat := 497587401278229828943435

theorem tailTrace_969048 : CollatzResearch.WordTrace tailWord_969048 prefixEnd_969048 497587401278229828943435 := by
  unfold tailWord_969048
  simp only [CollatzResearch.WordTrace]
  refine ⟨17672042096656035533681899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23562722795541380711575865 17672042096656035533681899)
  ·
    refine ⟨26508063144984053300522849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17672042096656035533681899 26508063144984053300522849)
    ·
      refine ⟨19881047358738039975392137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26508063144984053300522849 19881047358738039975392137)
      ·
        refine ⟨14910785519053529981544103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19881047358738039975392137 14910785519053529981544103)
        ·
          refine ⟨22366178278580294972316155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14910785519053529981544103 22366178278580294972316155)
          ·
            refine ⟨33549267417870442458474233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22366178278580294972316155 33549267417870442458474233)
            ·
              refine ⟨25161950563402831843855675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33549267417870442458474233 25161950563402831843855675)
              ·
                refine ⟨37742925845104247765783513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25161950563402831843855675 37742925845104247765783513)
                ·
                  refine ⟨28307194383828185824337635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37742925845104247765783513 28307194383828185824337635)
                  ·
                    refine ⟨42460791575742278736506453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28307194383828185824337635 42460791575742278736506453)
                    ·
                      refine ⟨497587401278229828943435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 42460791575742278736506453 497587401278229828943435)
                      ·
                        rfl

theorem cell23_969048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 2, 1, 8].length) (baseStart_969048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_969048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_969048 prefixEnd_969048 := by exact prefixLift 969048
  have htrace : WordTrace (prefixWord ++ tailWord_969048) baseStart_969048 baseEnd_969048 := by
    simpa [prefixWord, tailWord_969048, baseEnd_969048] using wordTrace_append hprefix tailTrace_969048
  have hstable : (prefixWord ++ tailWord_969048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969048).length < 2 ^ (prefixWord ++ tailWord_969048).sum := by decide
  have hdescent : baseEnd_969048 < baseStart_969048 := by decide
  rcases family_descends (prefixWord ++ tailWord_969048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969055 : List Nat := [1, 1, 2, 3, 1, 2, 2, 3, 2, 3, 3]
def baseStart_969055 : Nat := 118140960795 + 969055 * 2 ^ 59
def prefixEnd_969055 : Nat := 4983230072969 + 3 ^ 40 * 969055 * 2
def baseEnd_969055 : Nat := 497590995642811301555903

theorem tailTrace_969055 : CollatzResearch.WordTrace tailWord_969055 prefixEnd_969055 497590995642811301555903 := by
  unfold tailWord_969055
  simp only [CollatzResearch.WordTrace]
  refine ⟨35344339504286711262868619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23562893002857807508579079 35344339504286711262868619)
  ·
    refine ⟨53016509256430066894302929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35344339504286711262868619 53016509256430066894302929)
    ·
      refine ⟨39762381942322550170727197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53016509256430066894302929 39762381942322550170727197)
      ·
        refine ⟨14910893228370956314022699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39762381942322550170727197 14910893228370956314022699)
        ·
          refine ⟨22366339842556434471034049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14910893228370956314022699 22366339842556434471034049)
          ·
            refine ⟨16774754881917325853275537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22366339842556434471034049 16774754881917325853275537)
            ·
              refine ⟨12581066161437994389956653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16774754881917325853275537 12581066161437994389956653)
              ·
                refine ⟨4717899810539247896233745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12581066161437994389956653 4717899810539247896233745)
                ·
                  refine ⟨3538424857904435922175309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4717899810539247896233745 3538424857904435922175309)
                  ·
                    refine ⟨1326909321714163470815741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3538424857904435922175309 1326909321714163470815741)
                    ·
                      refine ⟨497590995642811301555903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1326909321714163470815741 497590995642811301555903)
                      ·
                        rfl

theorem cell23_969055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 3, 2, 3, 3].length) (baseStart_969055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_969055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_969055 prefixEnd_969055 := by exact prefixLift 969055
  have htrace : WordTrace (prefixWord ++ tailWord_969055) baseStart_969055 baseEnd_969055 := by
    simpa [prefixWord, tailWord_969055, baseEnd_969055] using wordTrace_append hprefix tailTrace_969055
  have hstable : (prefixWord ++ tailWord_969055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969055).length < 2 ^ (prefixWord ++ tailWord_969055).sum := by decide
  have hdescent : baseEnd_969055 < baseStart_969055 := by decide
  rcases family_descends (prefixWord ++ tailWord_969055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969056 : List Nat := [2, 1, 1, 3, 5, 1, 1, 3, 2, 2, 2]
def baseStart_969056 : Nat := 118140960795 + 969056 * 2 ^ 59
def prefixEnd_969056 : Nat := 4983230072969 + 3 ^ 40 * 969056 * 2
def baseEnd_969056 : Nat := 497591509123465797643399

theorem tailTrace_969056 : CollatzResearch.WordTrace tailWord_969056 prefixEnd_969056 497591509123465797643399 := by
  unfold tailWord_969056
  simp only [CollatzResearch.WordTrace]
  refine ⟨17672187988641544216827511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23562917318188725622436681 17672187988641544216827511)
  ·
    refine ⟨26508281982962316325241267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17672187988641544216827511 26508281982962316325241267)
    ·
      refine ⟨39762422974443474487861901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26508281982962316325241267 39762422974443474487861901)
      ·
        refine ⟨14910908615416302932948213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39762422974443474487861901 14910908615416302932948213)
        ·
          refine ⟨1397897682695278399963895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14910908615416302932948213 1397897682695278399963895)
          ·
            refine ⟨2096846524042917599945843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1397897682695278399963895 2096846524042917599945843)
            ·
              refine ⟨3145269786064376399918765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2096846524042917599945843 3145269786064376399918765)
              ·
                refine ⟨1179476169774141149969537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3145269786064376399918765 1179476169774141149969537)
                ·
                  refine ⟨884607127330605862477153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1179476169774141149969537 884607127330605862477153)
                  ·
                    refine ⟨663455345497954396857865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 884607127330605862477153 663455345497954396857865)
                    ·
                      refine ⟨497591509123465797643399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 663455345497954396857865 497591509123465797643399)
                      ·
                        rfl

theorem cell23_969056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 3, 2, 2, 2].length) (baseStart_969056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_969056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_969056 prefixEnd_969056 := by exact prefixLift 969056
  have htrace : WordTrace (prefixWord ++ tailWord_969056) baseStart_969056 baseEnd_969056 := by
    simpa [prefixWord, tailWord_969056, baseEnd_969056] using wordTrace_append hprefix tailTrace_969056
  have hstable : (prefixWord ++ tailWord_969056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969056).length < 2 ^ (prefixWord ++ tailWord_969056).sum := by decide
  have hdescent : baseEnd_969056 < baseStart_969056 := by decide
  rcases family_descends (prefixWord ++ tailWord_969056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969085 : List Nat := [1, 4, 1, 1, 2, 3, 1, 2, 1, 2, 5]
def baseStart_969085 : Nat := 118140960795 + 969085 * 2 ^ 59
def prefixEnd_969085 : Nat := 4983230072969 + 3 ^ 40 * 969085 * 2
def baseEnd_969085 : Nat := 497606400062446184180765

theorem tailTrace_969085 : CollatzResearch.WordTrace tailWord_969085 prefixEnd_969085 497606400062446184180765 := by
  unfold tailWord_969085
  simp only [CollatzResearch.WordTrace]
  refine ⟨35345433694178026386460709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23563622462785350924307139 35345433694178026386460709)
  ·
    refine ⟨6627268817658379947461383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35345433694178026386460709 6627268817658379947461383)
    ·
      refine ⟨9940903226487569921192075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6627268817658379947461383 9940903226487569921192075)
      ·
        refine ⟨14911354839731354881788113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9940903226487569921192075 14911354839731354881788113)
        ·
          refine ⟨11183516129798516161341085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14911354839731354881788113 11183516129798516161341085)
          ·
            refine ⟨4193818548674443560502907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11183516129798516161341085 4193818548674443560502907)
            ·
              refine ⟨6290727823011665340754361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4193818548674443560502907 6290727823011665340754361)
              ·
                refine ⟨4718045867258749005565771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6290727823011665340754361 4718045867258749005565771)
                ·
                  refine ⟨7077068800888123508348657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4718045867258749005565771 7077068800888123508348657)
                  ·
                    refine ⟨5307801600666092631261493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7077068800888123508348657 5307801600666092631261493)
                    ·
                      refine ⟨497606400062446184180765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5307801600666092631261493 497606400062446184180765)
                      ·
                        rfl

theorem cell23_969085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 2, 1, 2, 5].length) (baseStart_969085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_969085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_969085 prefixEnd_969085 := by exact prefixLift 969085
  have htrace : WordTrace (prefixWord ++ tailWord_969085) baseStart_969085 baseEnd_969085 := by
    simpa [prefixWord, tailWord_969085, baseEnd_969085] using wordTrace_append hprefix tailTrace_969085
  have hstable : (prefixWord ++ tailWord_969085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969085).length < 2 ^ (prefixWord ++ tailWord_969085).sum := by decide
  have hdescent : baseEnd_969085 < baseStart_969085 := by decide
  rcases family_descends (prefixWord ++ tailWord_969085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969090 : List Nat := [3, 4, 2, 1, 2, 1, 2, 2, 2, 2, 2]
def baseStart_969090 : Nat := 118140960795 + 969090 * 2 ^ 59
def prefixEnd_969090 : Nat := 4983230072969 + 3 ^ 40 * 969090 * 2
def baseEnd_969090 : Nat := 497608967465718664618243

theorem tailTrace_969090 : CollatzResearch.WordTrace tailWord_969090 prefixEnd_969090 497608967465718664618243 := by
  unfold tailWord_969090
  simp only [CollatzResearch.WordTrace]
  refine ⟨8836404014789978060098181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23563744039439941493595149 8836404014789978060098181)
  ·
    refine ⟨1656825752773120886268409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8836404014789978060098181 1656825752773120886268409)
    ·
      refine ⟨1242619314579840664701307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1656825752773120886268409 1242619314579840664701307)
      ·
        refine ⟨1863928971869760997051961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1242619314579840664701307 1863928971869760997051961)
        ·
          refine ⟨1397946728902320747788971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1863928971869760997051961 1397946728902320747788971)
          ·
            refine ⟨2096920093353481121683457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1397946728902320747788971 2096920093353481121683457)
            ·
              refine ⟨1572690070015110841262593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2096920093353481121683457 1572690070015110841262593)
              ·
                refine ⟨1179517552511333130946945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1572690070015110841262593 1179517552511333130946945)
                ·
                  refine ⟨884638164383499848210209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1179517552511333130946945 884638164383499848210209)
                  ·
                    refine ⟨663478623287624886157657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 884638164383499848210209 663478623287624886157657)
                    ·
                      refine ⟨497608967465718664618243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 663478623287624886157657 497608967465718664618243)
                      ·
                        rfl

theorem cell23_969090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 2, 2, 2, 2, 2].length) (baseStart_969090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_969090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_969090 prefixEnd_969090 := by exact prefixLift 969090
  have htrace : WordTrace (prefixWord ++ tailWord_969090) baseStart_969090 baseEnd_969090 := by
    simpa [prefixWord, tailWord_969090, baseEnd_969090] using wordTrace_append hprefix tailTrace_969090
  have hstable : (prefixWord ++ tailWord_969090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969090).length < 2 ^ (prefixWord ++ tailWord_969090).sum := by decide
  have hdescent : baseEnd_969090 < baseStart_969090 := by decide
  rcases family_descends (prefixWord ++ tailWord_969090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969102 : List Nat := [4, 1, 1, 4, 1, 1, 2, 1, 1, 2, 5]
def baseStart_969102 : Nat := 118140960795 + 969102 * 2 ^ 59
def prefixEnd_969102 : Nat := 4983230072969 + 3 ^ 40 * 969102 * 2
def baseEnd_969102 : Nat := 497615129233572617668187

theorem tailTrace_969102 : CollatzResearch.WordTrace tailWord_969102 prefixEnd_969102 497615129233572617668187 := by
  unfold tailWord_969102
  simp only [CollatzResearch.WordTrace]
  refine ⟨4418256716889554786228695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23564035823410958859886373 4418256716889554786228695)
  ·
    refine ⟨6627385075334332179343043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4418256716889554786228695 6627385075334332179343043)
    ·
      refine ⟨9941077613001498269014565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6627385075334332179343043 9941077613001498269014565)
      ·
        refine ⟨1863952052437780925440231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9941077613001498269014565 1863952052437780925440231)
        ·
          refine ⟨2795928078656671388160347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1863952052437780925440231 2795928078656671388160347)
          ·
            refine ⟨4193892117985007082240521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2795928078656671388160347 4193892117985007082240521)
            ·
              refine ⟨3145419088488755311680391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4193892117985007082240521 3145419088488755311680391)
              ·
                refine ⟨4718128632733132967520587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3145419088488755311680391 4718128632733132967520587)
                ·
                  refine ⟨7077192949099699451280881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4718128632733132967520587 7077192949099699451280881)
                  ·
                    refine ⟨5307894711824774588460661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7077192949099699451280881 5307894711824774588460661)
                    ·
                      refine ⟨497615129233572617668187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5307894711824774588460661 497615129233572617668187)
                      ·
                        rfl

theorem cell23_969102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_969102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_969102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_969102 prefixEnd_969102 := by exact prefixLift 969102
  have htrace : WordTrace (prefixWord ++ tailWord_969102) baseStart_969102 baseEnd_969102 := by
    simpa [prefixWord, tailWord_969102, baseEnd_969102] using wordTrace_append hprefix tailTrace_969102
  have hstable : (prefixWord ++ tailWord_969102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969102).length < 2 ^ (prefixWord ++ tailWord_969102).sum := by decide
  have hdescent : baseEnd_969102 < baseStart_969102 := by decide
  rcases family_descends (prefixWord ++ tailWord_969102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969156 : List Nat := [2, 3, 3, 2, 2, 1, 2, 1, 3, 4]
def baseStart_969156 : Nat := 118140960795 + 969156 * 2 ^ 59
def prefixEnd_969156 : Nat := 4983230072969 + 3 ^ 40 * 969156 * 2
def baseEnd_969156 : Nat := 165880952396305135464313

theorem tailTrace_969156 : CollatzResearch.WordTrace tailWord_969156 prefixEnd_969156 165880952396305135464313 := by
  unfold tailWord_969156
  simp only [CollatzResearch.WordTrace]
  refine ⟨17674011638460402756147661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23565348851280537008196881 17674011638460402756147661)
  ·
    refine ⟨6627754364422651033555373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17674011638460402756147661 6627754364422651033555373)
    ·
      refine ⟨2485407886658494137583265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6627754364422651033555373 2485407886658494137583265)
      ·
        refine ⟨1864055914993870603187449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2485407886658494137583265 1864055914993870603187449)
        ·
          refine ⟨1398041936245402952390587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1864055914993870603187449 1398041936245402952390587)
          ·
            refine ⟨2097062904368104428585881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1398041936245402952390587 2097062904368104428585881)
            ·
              refine ⟨1572797178276078321439411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2097062904368104428585881 1572797178276078321439411)
              ·
                refine ⟨2359195767414117482159117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1572797178276078321439411 2359195767414117482159117)
                ·
                  refine ⟨884698412780294055809669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2359195767414117482159117 884698412780294055809669)
                  ·
                    refine ⟨165880952396305135464313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 884698412780294055809669 165880952396305135464313)
                    ·
                      rfl

theorem cell23_969156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 2, 1, 3, 4].length) (baseStart_969156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_969156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_969156 prefixEnd_969156 := by exact prefixLift 969156
  have htrace : WordTrace (prefixWord ++ tailWord_969156) baseStart_969156 baseEnd_969156 := by
    simpa [prefixWord, tailWord_969156, baseEnd_969156] using wordTrace_append hprefix tailTrace_969156
  have hstable : (prefixWord ++ tailWord_969156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969156).length < 2 ^ (prefixWord ++ tailWord_969156).sum := by decide
  have hdescent : baseEnd_969156 < baseStart_969156 := by decide
  rcases family_descends (prefixWord ++ tailWord_969156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969195 : List Nat := [1, 1, 1, 1, 2, 3, 4, 1, 3, 6]
def baseStart_969195 : Nat := 118140960795 + 969195 * 2 ^ 59
def prefixEnd_969195 : Nat := 4983230072969 + 3 ^ 40 * 969195 * 2
def baseEnd_969195 : Nat := 165887627644813584601753

theorem tailTrace_969195 : CollatzResearch.WordTrace tailWord_969195 prefixEnd_969195 165887627644813584601753 := by
  unfold tailWord_969195
  simp only [CollatzResearch.WordTrace]
  refine ⟨35349445723779515172965039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23566297149186343448643359 35349445723779515172965039)
  ·
    refine ⟨53024168585669272759447559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35349445723779515172965039 53024168585669272759447559)
    ·
      refine ⟨79536252878503909139171339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53024168585669272759447559 79536252878503909139171339)
      ·
        refine ⟨119304379317755863708757009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79536252878503909139171339 119304379317755863708757009)
        ·
          refine ⟨89478284488316897781567757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119304379317755863708757009 89478284488316897781567757)
          ·
            refine ⟨33554356683118836668087909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89478284488316897781567757 33554356683118836668087909)
            ·
              refine ⟨6291441878084781875266483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33554356683118836668087909 6291441878084781875266483)
              ·
                refine ⟨9437162817127172812899725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6291441878084781875266483 9437162817127172812899725)
                ·
                  refine ⟨3538936056422689804837397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9437162817127172812899725 3538936056422689804837397)
                  ·
                    refine ⟨165887627644813584601753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3538936056422689804837397 165887627644813584601753)
                    ·
                      rfl

theorem cell23_969195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 1, 3, 6].length) (baseStart_969195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_969195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_969195 prefixEnd_969195 := by exact prefixLift 969195
  have htrace : WordTrace (prefixWord ++ tailWord_969195) baseStart_969195 baseEnd_969195 := by
    simpa [prefixWord, tailWord_969195, baseEnd_969195] using wordTrace_append hprefix tailTrace_969195
  have hstable : (prefixWord ++ tailWord_969195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969195).length < 2 ^ (prefixWord ++ tailWord_969195).sum := by decide
  have hdescent : baseEnd_969195 < baseStart_969195 := by decide
  rcases family_descends (prefixWord ++ tailWord_969195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969206 : List Nat := [5, 1, 1, 1, 2, 1, 3, 2, 2, 3, 2]
def baseStart_969206 : Nat := 118140960795 + 969206 * 2 ^ 59
def prefixEnd_969206 : Nat := 4983230072969 + 3 ^ 40 * 969206 * 2
def baseEnd_969206 : Nat := 497668531221640210767709

theorem tailTrace_969206 : CollatzResearch.WordTrace tailWord_969206 prefixEnd_969206 497668531221640210767709 := by
  unfold tailWord_969206
  simp only [CollatzResearch.WordTrace]
  refine ⟨2209365432921229003225967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23566564617826442701076981 2209365432921229003225967)
  ·
    refine ⟨3314048149381843504838951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2209365432921229003225967 3314048149381843504838951)
    ·
      refine ⟨4971072224072765257258427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3314048149381843504838951 4971072224072765257258427)
      ·
        refine ⟨7456608336109147885887641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4971072224072765257258427 7456608336109147885887641)
        ·
          refine ⟨5592456252081860914415731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7456608336109147885887641 5592456252081860914415731)
          ·
            refine ⟨8388684378122791371623597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5592456252081860914415731 8388684378122791371623597)
            ·
              refine ⟨3145756641796046764358849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8388684378122791371623597 3145756641796046764358849)
              ·
                refine ⟨2359317481347035073269137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3145756641796046764358849 2359317481347035073269137)
                ·
                  refine ⟨1769488111010276304951853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2359317481347035073269137 1769488111010276304951853)
                  ·
                    refine ⟨663558041628853614356945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1769488111010276304951853 663558041628853614356945)
                    ·
                      refine ⟨497668531221640210767709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 663558041628853614356945 497668531221640210767709)
                      ·
                        rfl

theorem cell23_969206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 2, 2, 3, 2].length) (baseStart_969206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_969206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_969206 prefixEnd_969206 := by exact prefixLift 969206
  have htrace : WordTrace (prefixWord ++ tailWord_969206) baseStart_969206 baseEnd_969206 := by
    simpa [prefixWord, tailWord_969206, baseEnd_969206] using wordTrace_append hprefix tailTrace_969206
  have hstable : (prefixWord ++ tailWord_969206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969206).length < 2 ^ (prefixWord ++ tailWord_969206).sum := by decide
  have hdescent : baseEnd_969206 < baseStart_969206 := by decide
  rcases family_descends (prefixWord ++ tailWord_969206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969213 : List Nat := [1, 4, 1, 1, 1, 3, 5, 2, 1, 1, 3]
def baseStart_969213 : Nat := 118140960795 + 969213 * 2 ^ 59
def prefixEnd_969213 : Nat := 4983230072969 + 3 ^ 40 * 969213 * 2
def baseEnd_969213 : Nat := 497672125586221683380177

theorem tailTrace_969213 : CollatzResearch.WordTrace tailWord_969213 prefixEnd_969213 497672125586221683380177 := by
  unfold tailWord_969213
  simp only [CollatzResearch.WordTrace]
  refine ⟨35350102237714304247120293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23566734825142869498080195 35350102237714304247120293)
  ·
    refine ⟨6628144169571432046335055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35350102237714304247120293 6628144169571432046335055)
    ·
      refine ⟨9942216254357148069502583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6628144169571432046335055 9942216254357148069502583)
      ·
        refine ⟨14913324381535722104253875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9942216254357148069502583 14913324381535722104253875)
        ·
          refine ⟨22369986572303583156380813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14913324381535722104253875 22369986572303583156380813)
          ·
            refine ⟨8388744964613843683642805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22369986572303583156380813 8388744964613843683642805)
            ·
              refine ⟨786444840432547845341513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8388744964613843683642805 786444840432547845341513)
              ·
                refine ⟨589833630324410884006135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 786444840432547845341513 589833630324410884006135)
                ·
                  refine ⟨884750445486616326009203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 589833630324410884006135 884750445486616326009203)
                  ·
                    refine ⟨1327125668229924489013805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 884750445486616326009203 1327125668229924489013805)
                    ·
                      refine ⟨497672125586221683380177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1327125668229924489013805 497672125586221683380177)
                      ·
                        rfl

theorem cell23_969213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 5, 2, 1, 1, 3].length) (baseStart_969213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_969213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_969213 prefixEnd_969213 := by exact prefixLift 969213
  have htrace : WordTrace (prefixWord ++ tailWord_969213) baseStart_969213 baseEnd_969213 := by
    simpa [prefixWord, tailWord_969213, baseEnd_969213] using wordTrace_append hprefix tailTrace_969213
  have hstable : (prefixWord ++ tailWord_969213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969213).length < 2 ^ (prefixWord ++ tailWord_969213).sum := by decide
  have hdescent : baseEnd_969213 < baseStart_969213 := by decide
  rcases family_descends (prefixWord ++ tailWord_969213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969215 : List Nat := [1, 1, 2, 2, 1, 2, 3, 1, 3, 1, 6]
def baseStart_969215 : Nat := 118140960795 + 969215 * 2 ^ 59
def prefixEnd_969215 : Nat := 4983230072969 + 3 ^ 40 * 969215 * 2
def baseEnd_969215 : Nat := 497673152547530675555167

theorem tailTrace_969215 : CollatzResearch.WordTrace tailWord_969215 prefixEnd_969215 497673152547530675555167 := by
  unfold tailWord_969215
  simp only [CollatzResearch.WordTrace]
  refine ⟨35350175183707058588693099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23566783455804705725795399 35350175183707058588693099)
  ·
    refine ⟨53025262775560587883039649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35350175183707058588693099 53025262775560587883039649)
    ·
      refine ⟨39768947081670440912279737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53025262775560587883039649 39768947081670440912279737)
      ·
        refine ⟨29826710311252830684209803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39768947081670440912279737 29826710311252830684209803)
        ·
          refine ⟨44740065466879246026314705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29826710311252830684209803 44740065466879246026314705)
          ·
            refine ⟨33555049100159434519736029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44740065466879246026314705 33555049100159434519736029)
            ·
              refine ⟨12583143412559787944901011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33555049100159434519736029 12583143412559787944901011)
              ·
                refine ⟨18874715118839681917351517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12583143412559787944901011 18874715118839681917351517)
                ·
                  refine ⟨7078018169564880719006819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18874715118839681917351517 7078018169564880719006819)
                  ·
                    refine ⟨10617027254347321078510229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7078018169564880719006819 10617027254347321078510229)
                    ·
                      refine ⟨497673152547530675555167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10617027254347321078510229 497673152547530675555167)
                      ·
                        rfl

theorem cell23_969215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 3, 1, 6].length) (baseStart_969215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_969215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_969215 prefixEnd_969215 := by exact prefixLift 969215
  have htrace : WordTrace (prefixWord ++ tailWord_969215) baseStart_969215 baseEnd_969215 := by
    simpa [prefixWord, tailWord_969215, baseEnd_969215] using wordTrace_append hprefix tailTrace_969215
  have hstable : (prefixWord ++ tailWord_969215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969215).length < 2 ^ (prefixWord ++ tailWord_969215).sum := by decide
  have hdescent : baseEnd_969215 < baseStart_969215 := by decide
  rcases family_descends (prefixWord ++ tailWord_969215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969236 : List Nat := [2, 4, 3, 1, 1, 2, 1, 1, 3, 1, 4]
def baseStart_969236 : Nat := 118140960795 + 969236 * 2 ^ 59
def prefixEnd_969236 : Nat := 4983230072969 + 3 ^ 40 * 969236 * 2
def baseEnd_969236 : Nat := 497683935641275093392571

theorem tailTrace_969236 : CollatzResearch.WordTrace tailWord_969236 prefixEnd_969236 497683935641275093392571 := by
  unfold tailWord_969236
  simp only [CollatzResearch.WordTrace]
  refine ⟨17675470558315489587603781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23567294077753986116805041 17675470558315489587603781)
  ·
    refine ⟨3314150729684154297675709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17675470558315489587603781 3314150729684154297675709)
    ·
      refine ⟨1242806523631557861628391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3314150729684154297675709 1242806523631557861628391)
      ·
        refine ⟨1864209785447336792442587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1242806523631557861628391 1864209785447336792442587)
        ·
          refine ⟨2796314678171005188663881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1864209785447336792442587 2796314678171005188663881)
          ·
            refine ⟨2097236008628253891497911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2796314678171005188663881 2097236008628253891497911)
            ·
              refine ⟨3145854012942380837246867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2097236008628253891497911 3145854012942380837246867)
              ·
                refine ⟨4718781019413571255870301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3145854012942380837246867 4718781019413571255870301)
                ·
                  refine ⟨1769542882280089220951363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4718781019413571255870301 1769542882280089220951363)
                  ·
                    refine ⟨2654314323420133831427045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1769542882280089220951363 2654314323420133831427045)
                    ·
                      refine ⟨497683935641275093392571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2654314323420133831427045 497683935641275093392571)
                      ·
                        rfl

theorem cell23_969236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_969236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_969236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_969236 prefixEnd_969236 := by exact prefixLift 969236
  have htrace : WordTrace (prefixWord ++ tailWord_969236) baseStart_969236 baseEnd_969236 := by
    simpa [prefixWord, tailWord_969236, baseEnd_969236] using wordTrace_append hprefix tailTrace_969236
  have hstable : (prefixWord ++ tailWord_969236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969236).length < 2 ^ (prefixWord ++ tailWord_969236).sum := by decide
  have hdescent : baseEnd_969236 < baseStart_969236 := by decide
  rcases family_descends (prefixWord ++ tailWord_969236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969256 : List Nat := [2, 1, 5, 2, 1, 3, 1, 1, 1, 1, 5]
def baseStart_969256 : Nat := 118140960795 + 969256 * 2 ^ 59
def prefixEnd_969256 : Nat := 4983230072969 + 3 ^ 40 * 969256 * 2
def baseEnd_969256 : Nat := 497694205254365015142479

theorem tailTrace_969256 : CollatzResearch.WordTrace tailWord_969256 prefixEnd_969256 497694205254365015142479 := by
  unfold tailWord_969256
  simp only [CollatzResearch.WordTrace]
  refine ⟨17675835288279261295467811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23567780384372348393957081 17675835288279261295467811)
  ·
    refine ⟨26513752932418891943201717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17675835288279261295467811 26513752932418891943201717)
    ·
      refine ⟨2485664337414271119675161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26513752932418891943201717 2485664337414271119675161)
      ·
        refine ⟨1864248253060703339756371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2485664337414271119675161 1864248253060703339756371)
        ·
          refine ⟨2796372379591055009634557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1864248253060703339756371 2796372379591055009634557)
          ·
            refine ⟨1048639642346645628612959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2796372379591055009634557 1048639642346645628612959)
            ·
              refine ⟨1572959463519968442919439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1048639642346645628612959 1572959463519968442919439)
              ·
                refine ⟨2359439195279952664379159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1572959463519968442919439 2359439195279952664379159)
                ·
                  refine ⟨3539158792919928996568739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2359439195279952664379159 3539158792919928996568739)
                  ·
                    refine ⟨5308738189379893494853109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3539158792919928996568739 5308738189379893494853109)
                    ·
                      refine ⟨497694205254365015142479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5308738189379893494853109 497694205254365015142479)
                      ·
                        rfl

theorem cell23_969256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_969256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_969256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_969256 prefixEnd_969256 := by exact prefixLift 969256
  have htrace : WordTrace (prefixWord ++ tailWord_969256) baseStart_969256 baseEnd_969256 := by
    simpa [prefixWord, tailWord_969256, baseEnd_969256] using wordTrace_append hprefix tailTrace_969256
  have hstable : (prefixWord ++ tailWord_969256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969256).length < 2 ^ (prefixWord ++ tailWord_969256).sum := by decide
  have hdescent : baseEnd_969256 < baseStart_969256 := by decide
  rcases family_descends (prefixWord ++ tailWord_969256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969275 : List Nat := [1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 8]
def baseStart_969275 : Nat := 118140960795 + 969275 * 2 ^ 59
def prefixEnd_969275 : Nat := 4983230072969 + 3 ^ 40 * 969275 * 2
def baseEnd_969275 : Nat := 497703961386800440804891

theorem tailTrace_969275 : CollatzResearch.WordTrace tailWord_969275 prefixEnd_969275 497703961386800440804891 := by
  unfold tailWord_969275
  simp only [CollatzResearch.WordTrace]
  refine ⟨35352363563489688835877279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23568242375659792557251519 35352363563489688835877279)
  ·
    refine ⟨53028545345234533253815919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35352363563489688835877279 53028545345234533253815919)
    ·
      refine ⟨79542818017851799880723879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53028545345234533253815919 79542818017851799880723879)
      ·
        refine ⟨119314227026777699821085819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79542818017851799880723879 119314227026777699821085819)
        ·
          refine ⟨178971340540166549731628729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119314227026777699821085819 178971340540166549731628729)
          ·
            refine ⟨134228505405124912298721547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178971340540166549731628729 134228505405124912298721547)
            ·
              refine ⟨201342758107687368448082321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134228505405124912298721547 201342758107687368448082321)
              ·
                refine ⟨151007068580765526336061741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 201342758107687368448082321 151007068580765526336061741)
                ·
                  refine ⟨56627650717787072376023153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 151007068580765526336061741 56627650717787072376023153)
                  ·
                    refine ⟨42470738038340304282017365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56627650717787072376023153 42470738038340304282017365)
                    ·
                      refine ⟨497703961386800440804891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 42470738038340304282017365 497703961386800440804891)
                      ·
                        rfl

theorem cell23_969275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 8].length) (baseStart_969275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_969275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_969275 prefixEnd_969275 := by exact prefixLift 969275
  have htrace : WordTrace (prefixWord ++ tailWord_969275) baseStart_969275 baseEnd_969275 := by
    simpa [prefixWord, tailWord_969275, baseEnd_969275] using wordTrace_append hprefix tailTrace_969275
  have hstable : (prefixWord ++ tailWord_969275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969275).length < 2 ^ (prefixWord ++ tailWord_969275).sum := by decide
  have hdescent : baseEnd_969275 < baseStart_969275 := by decide
  rcases family_descends (prefixWord ++ tailWord_969275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969279 : List Nat := [1, 1, 2, 2, 3, 2, 1, 1, 5, 3, 2]
def baseStart_969279 : Nat := 118140960795 + 969279 * 2 ^ 59
def prefixEnd_969279 : Nat := 4983230072969 + 3 ^ 40 * 969279 * 2
def baseEnd_969279 : Nat := 497706015309418425154873

theorem tailTrace_969279 : CollatzResearch.WordTrace tailWord_969279 prefixEnd_969279 497706015309418425154873 := by
  unfold tailWord_969279
  simp only [CollatzResearch.WordTrace]
  refine ⟨35352509455475197519022891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23568339636983465012681927 35352509455475197519022891)
  ·
    refine ⟨53028764183212796278534337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35352509455475197519022891 53028764183212796278534337)
    ·
      refine ⟨39771573137409597208900753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53028764183212796278534337 39771573137409597208900753)
      ·
        refine ⟨29828679853057197906675565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39771573137409597208900753 29828679853057197906675565)
        ·
          refine ⟨11185754944896449215003337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29828679853057197906675565 11185754944896449215003337)
          ·
            refine ⟨8389316208672336911252503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11185754944896449215003337 8389316208672336911252503)
            ·
              refine ⟨12583974313008505366878755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8389316208672336911252503 12583974313008505366878755)
              ·
                refine ⟨18875961469512758050318133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12583974313008505366878755 18875961469512758050318133)
                ·
                  refine ⟨1769621387766821067217325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18875961469512758050318133 1769621387766821067217325)
                  ·
                    refine ⟨663608020412557900206497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1769621387766821067217325 663608020412557900206497)
                    ·
                      refine ⟨497706015309418425154873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 663608020412557900206497 497706015309418425154873)
                      ·
                        rfl

theorem cell23_969279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 5, 3, 2].length) (baseStart_969279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_969279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_969279 prefixEnd_969279 := by exact prefixLift 969279
  have htrace : WordTrace (prefixWord ++ tailWord_969279) baseStart_969279 baseEnd_969279 := by
    simpa [prefixWord, tailWord_969279, baseEnd_969279] using wordTrace_append hprefix tailTrace_969279
  have hstable : (prefixWord ++ tailWord_969279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969279).length < 2 ^ (prefixWord ++ tailWord_969279).sum := by decide
  have hdescent : baseEnd_969279 < baseStart_969279 := by decide
  rcases family_descends (prefixWord ++ tailWord_969279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969292 : List Nat := [2, 2, 1, 3, 1, 2, 1, 2, 2, 3, 4]
def baseStart_969292 : Nat := 118140960795 + 969292 * 2 ^ 59
def prefixEnd_969292 : Nat := 4983230072969 + 3 ^ 40 * 969292 * 2
def baseEnd_969292 : Nat := 497712690557926874292313

theorem tailTrace_969292 : CollatzResearch.WordTrace tailWord_969292 prefixEnd_969292 497712690557926874292313 := by
  unfold tailWord_969292
  simp only [CollatzResearch.WordTrace]
  refine ⟨17676491802214050369623065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23568655736285400492830753 17676491802214050369623065)
  ·
    refine ⟨13257368851660537777217299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17676491802214050369623065 13257368851660537777217299)
    ·
      refine ⟨19886053277490806665825949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13257368851660537777217299 19886053277490806665825949)
      ·
        refine ⟨7457269979059052499684731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19886053277490806665825949 7457269979059052499684731)
        ·
          refine ⟨11185904968588578749527097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7457269979059052499684731 11185904968588578749527097)
          ·
            refine ⟨8389428726441434062145323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11185904968588578749527097 8389428726441434062145323)
            ·
              refine ⟨12584143089662151093217985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8389428726441434062145323 12584143089662151093217985)
              ·
                refine ⟨9438107317246613319913489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12584143089662151093217985 9438107317246613319913489)
                ·
                  refine ⟨7078580487934959989935117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9438107317246613319913489 7078580487934959989935117)
                  ·
                    refine ⟨2654467682975609996225669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7078580487934959989935117 2654467682975609996225669)
                    ·
                      refine ⟨497712690557926874292313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2654467682975609996225669 497712690557926874292313)
                      ·
                        rfl

theorem cell23_969292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 2, 2, 3, 4].length) (baseStart_969292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_969292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_969292 prefixEnd_969292 := by exact prefixLift 969292
  have htrace : WordTrace (prefixWord ++ tailWord_969292) baseStart_969292 baseEnd_969292 := by
    simpa [prefixWord, tailWord_969292, baseEnd_969292] using wordTrace_append hprefix tailTrace_969292
  have hstable : (prefixWord ++ tailWord_969292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969292).length < 2 ^ (prefixWord ++ tailWord_969292).sum := by decide
  have hdescent : baseEnd_969292 < baseStart_969292 := by decide
  rcases family_descends (prefixWord ++ tailWord_969292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969312 : List Nat := [2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 5]
def baseStart_969312 : Nat := 118140960795 + 969312 * 2 ^ 59
def prefixEnd_969312 : Nat := 4983230072969 + 3 ^ 40 * 969312 * 2
def baseEnd_969312 : Nat := 497722960171016796042221

theorem tailTrace_969312 : CollatzResearch.WordTrace tailWord_969312 prefixEnd_969312 497722960171016796042221 := by
  unfold tailWord_969312
  simp only [CollatzResearch.WordTrace]
  refine ⟨17676856532177822077487095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23569142042903762769982793 17676856532177822077487095)
  ·
    refine ⟨26515284798266733116230643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17676856532177822077487095 26515284798266733116230643)
    ·
      refine ⟨39772927197400099674345965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26515284798266733116230643 39772927197400099674345965)
      ·
        refine ⟨14914847699025037377879737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39772927197400099674345965 14914847699025037377879737)
        ·
          refine ⟨11186135774268778033409803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14914847699025037377879737 11186135774268778033409803)
          ·
            refine ⟨16779203661403167050114705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11186135774268778033409803 16779203661403167050114705)
            ·
              refine ⟨12584402746052375287586029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16779203661403167050114705 12584402746052375287586029)
              ·
                refine ⟨4719151029769640732844761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12584402746052375287586029 4719151029769640732844761)
                ·
                  refine ⟨3539363272327230549633571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4719151029769640732844761 3539363272327230549633571)
                  ·
                    refine ⟨5309044908490845824450357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3539363272327230549633571 5309044908490845824450357)
                    ·
                      refine ⟨497722960171016796042221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5309044908490845824450357 497722960171016796042221)
                      ·
                        rfl

theorem cell23_969312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 5].length) (baseStart_969312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_969312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_969312 prefixEnd_969312 := by exact prefixLift 969312
  have htrace : WordTrace (prefixWord ++ tailWord_969312) baseStart_969312 baseEnd_969312 := by
    simpa [prefixWord, tailWord_969312, baseEnd_969312] using wordTrace_append hprefix tailTrace_969312
  have hstable : (prefixWord ++ tailWord_969312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969312).length < 2 ^ (prefixWord ++ tailWord_969312).sum := by decide
  have hdescent : baseEnd_969312 < baseStart_969312 := by decide
  rcases family_descends (prefixWord ++ tailWord_969312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969313 : List Nat := [1, 2, 3, 1, 1, 4, 4, 1, 1, 3, 2]
def baseStart_969313 : Nat := 118140960795 + 969313 * 2 ^ 59
def prefixEnd_969313 : Nat := 4983230072969 + 3 ^ 40 * 969313 * 2
def baseEnd_969313 : Nat := 497723473651671292129717

theorem tailTrace_969313 : CollatzResearch.WordTrace tailWord_969313 prefixEnd_969313 497723473651671292129717 := by
  unfold tailWord_969313
  simp only [CollatzResearch.WordTrace]
  refine ⟨35353749537352021325760593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23569166358234680883840395 35353749537352021325760593)
  ·
    refine ⟨26515312153014015994320445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35353749537352021325760593 26515312153014015994320445)
    ·
      refine ⟨9943242057380255997870167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26515312153014015994320445 9943242057380255997870167)
      ·
        refine ⟨14914863086070383996805251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9943242057380255997870167 14914863086070383996805251)
        ·
          refine ⟨22372294629105575995207877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14914863086070383996805251 22372294629105575995207877)
          ·
            refine ⟨4194805242957295499101477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22372294629105575995207877 4194805242957295499101477)
            ·
              refine ⟨786525983054492906081527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4194805242957295499101477 786525983054492906081527)
              ·
                refine ⟨1179788974581739359122291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 786525983054492906081527 1179788974581739359122291)
                ·
                  refine ⟨1769683461872609038683437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1179788974581739359122291 1769683461872609038683437)
                  ·
                    refine ⟨663631298202228389506289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1769683461872609038683437 663631298202228389506289)
                    ·
                      refine ⟨497723473651671292129717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 663631298202228389506289 497723473651671292129717)
                      ·
                        rfl

theorem cell23_969313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 4, 1, 1, 3, 2].length) (baseStart_969313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_969313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_969313 prefixEnd_969313 := by exact prefixLift 969313
  have htrace : WordTrace (prefixWord ++ tailWord_969313) baseStart_969313 baseEnd_969313 := by
    simpa [prefixWord, tailWord_969313, baseEnd_969313] using wordTrace_append hprefix tailTrace_969313
  have hstable : (prefixWord ++ tailWord_969313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969313).length < 2 ^ (prefixWord ++ tailWord_969313).sum := by decide
  have hdescent : baseEnd_969313 < baseStart_969313 := by decide
  rcases family_descends (prefixWord ++ tailWord_969313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969320 : List Nat := [2, 1, 4, 3, 2, 2, 1, 2, 2, 1, 3]
def baseStart_969320 : Nat := 118140960795 + 969320 * 2 ^ 59
def prefixEnd_969320 : Nat := 4983230072969 + 3 ^ 40 * 969320 * 2
def baseEnd_969320 : Nat := 497727068016252764742185

theorem tailTrace_969320 : CollatzResearch.WordTrace tailWord_969320 prefixEnd_969320 497727068016252764742185 := by
  unfold tailWord_969320
  simp only [CollatzResearch.WordTrace]
  refine ⟨17677002424163330760632707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23569336565551107680843609 17677002424163330760632707)
  ·
    refine ⟨26515503636244996140949061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17677002424163330760632707 26515503636244996140949061)
    ·
      refine ⟨4971656931795936776427949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26515503636244996140949061 4971656931795936776427949)
      ·
        refine ⟨1864371349423476291160481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4971656931795936776427949 1864371349423476291160481)
        ·
          refine ⟨1398278512067607218370361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1864371349423476291160481 1398278512067607218370361)
          ·
            refine ⟨1048708884050705413777771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1398278512067607218370361 1048708884050705413777771)
            ·
              refine ⟨1573063326076058120666657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1048708884050705413777771 1573063326076058120666657)
              ·
                refine ⟨1179797494557043590499993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1573063326076058120666657 1179797494557043590499993)
                ·
                  refine ⟨884848120917782692874995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1179797494557043590499993 884848120917782692874995)
                  ·
                    refine ⟨1327272181376674039312493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 884848120917782692874995 1327272181376674039312493)
                    ·
                      refine ⟨497727068016252764742185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1327272181376674039312493 497727068016252764742185)
                      ·
                        rfl

theorem cell23_969320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_969320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_969320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_969320 prefixEnd_969320 := by exact prefixLift 969320
  have htrace : WordTrace (prefixWord ++ tailWord_969320) baseStart_969320 baseEnd_969320 := by
    simpa [prefixWord, tailWord_969320, baseEnd_969320] using wordTrace_append hprefix tailTrace_969320
  have hstable : (prefixWord ++ tailWord_969320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969320).length < 2 ^ (prefixWord ++ tailWord_969320).sum := by decide
  have hdescent : baseEnd_969320 < baseStart_969320 := by decide
  rcases family_descends (prefixWord ++ tailWord_969320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969383 : List Nat := [1, 1, 6, 3, 1, 2, 1, 1, 7]
def baseStart_969383 : Nat := 118140960795 + 969383 * 2 ^ 59
def prefixEnd_969383 : Nat := 4983230072969 + 3 ^ 40 * 969383 * 2
def baseEnd_969383 : Nat := 55306601921942890917155

theorem tailTrace_969383 : CollatzResearch.WordTrace tailWord_969383 prefixEnd_969383 55306601921942890917155 := by
  unfold tailWord_969383
  simp only [CollatzResearch.WordTrace]
  refine ⟨35356302647098423280808803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23570868431398948853872535 35356302647098423280808803)
  ·
    refine ⟨53034453970647634921213205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35356302647098423280808803 53034453970647634921213205)
    ·
      refine ⟨2485990029874107886931869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 53034453970647634921213205 2485990029874107886931869)
      ·
        refine ⟨932246261202790457599451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2485990029874107886931869 932246261202790457599451)
        ·
          refine ⟨1398369391804185686399177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 932246261202790457599451 1398369391804185686399177)
          ·
            refine ⟨1048777043853139264799383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1398369391804185686399177 1048777043853139264799383)
            ·
              refine ⟨1573165565779708897199075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1048777043853139264799383 1573165565779708897199075)
              ·
                refine ⟨2359748348669563345798613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1573165565779708897199075 2359748348669563345798613)
                ·
                  refine ⟨55306601921942890917155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2359748348669563345798613 55306601921942890917155)
                  ·
                    rfl

theorem cell23_969383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 1, 1, 7].length) (baseStart_969383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_969383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_969383 prefixEnd_969383 := by exact prefixLift 969383
  have htrace : WordTrace (prefixWord ++ tailWord_969383) baseStart_969383 baseEnd_969383 := by
    simpa [prefixWord, tailWord_969383, baseEnd_969383] using wordTrace_append hprefix tailTrace_969383
  have hstable : (prefixWord ++ tailWord_969383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969383).length < 2 ^ (prefixWord ++ tailWord_969383).sum := by decide
  have hdescent : baseEnd_969383 < baseStart_969383 := by decide
  rcases family_descends (prefixWord ++ tailWord_969383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969389 : List Nat := [1, 5, 2, 1, 1, 2, 1, 1, 1, 1, 7]
def baseStart_969389 : Nat := 118140960795 + 969389 * 2 ^ 59
def prefixEnd_969389 : Nat := 4983230072969 + 3 ^ 40 * 969389 * 2
def baseEnd_969389 : Nat := 497762498181412994779367

theorem tailTrace_969389 : CollatzResearch.WordTrace tailWord_969389 prefixEnd_969389 497762498181412994779367 := by
  unfold tailWord_969389
  simp only [CollatzResearch.WordTrace]
  refine ⟨35356521485076686305527221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23571014323384457537018147 35356521485076686305527221)
  ·
    refine ⟨3314673889225939341143177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35356521485076686305527221 3314673889225939341143177)
    ·
      refine ⟨2486005416919454505857383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3314673889225939341143177 2486005416919454505857383)
      ·
        refine ⟨3729008125379181758786075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2486005416919454505857383 3729008125379181758786075)
        ·
          refine ⟨5593512188068772638179113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3729008125379181758786075 5593512188068772638179113)
          ·
            refine ⟨4195134141051579478634335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5593512188068772638179113 4195134141051579478634335)
            ·
              refine ⟨6292701211577369217951503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4195134141051579478634335 6292701211577369217951503)
              ·
                refine ⟨9439051817366053826927255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6292701211577369217951503 9439051817366053826927255)
                ·
                  refine ⟨14158577726049080740390883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9439051817366053826927255 14158577726049080740390883)
                  ·
                    refine ⟨21237866589073621110586325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14158577726049080740390883 21237866589073621110586325)
                    ·
                      refine ⟨497762498181412994779367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 21237866589073621110586325 497762498181412994779367)
                      ·
                        rfl

theorem cell23_969389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_969389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_969389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_969389 prefixEnd_969389 := by exact prefixLift 969389
  have htrace : WordTrace (prefixWord ++ tailWord_969389) baseStart_969389 baseEnd_969389 := by
    simpa [prefixWord, tailWord_969389, baseEnd_969389] using wordTrace_append hprefix tailTrace_969389
  have hstable : (prefixWord ++ tailWord_969389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969389).length < 2 ^ (prefixWord ++ tailWord_969389).sum := by decide
  have hdescent : baseEnd_969389 < baseStart_969389 := by decide
  rcases family_descends (prefixWord ++ tailWord_969389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969416 : List Nat := [2, 1, 3, 1, 2, 4, 2, 1, 2, 1, 4]
def baseStart_969416 : Nat := 118140960795 + 969416 * 2 ^ 59
def prefixEnd_969416 : Nat := 4983230072969 + 3 ^ 40 * 969416 * 2
def baseEnd_969416 : Nat := 497776362159084389141743

theorem tailTrace_969416 : CollatzResearch.WordTrace tailWord_969416 prefixEnd_969416 497776362159084389141743 := by
  unfold tailWord_969416
  simp only [CollatzResearch.WordTrace]
  refine ⟨17678753127989434958380051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23571670837319246611173401 17678753127989434958380051)
  ·
    refine ⟨26518129691984152437570077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17678753127989434958380051 26518129691984152437570077)
    ·
      refine ⟨9944298634494057164088779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26518129691984152437570077 9944298634494057164088779)
      ·
        refine ⟨14916447951741085746133169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9944298634494057164088779 14916447951741085746133169)
        ·
          refine ⟨11187335963805814309599877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14916447951741085746133169 11187335963805814309599877)
          ·
            refine ⟨2097625493213590183049977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11187335963805814309599877 2097625493213590183049977)
            ·
              refine ⟨1573219119910192637287483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2097625493213590183049977 1573219119910192637287483)
              ·
                refine ⟨2359828679865288955931225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1573219119910192637287483 2359828679865288955931225)
                ·
                  refine ⟨1769871509898966716948419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2359828679865288955931225 1769871509898966716948419)
                  ·
                    refine ⟨2654807264848450075422629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1769871509898966716948419 2654807264848450075422629)
                    ·
                      refine ⟨497776362159084389141743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2654807264848450075422629 497776362159084389141743)
                      ·
                        rfl

theorem cell23_969416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2, 1, 2, 1, 4].length) (baseStart_969416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_969416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_969416 prefixEnd_969416 := by exact prefixLift 969416
  have htrace : WordTrace (prefixWord ++ tailWord_969416) baseStart_969416 baseEnd_969416 := by
    simpa [prefixWord, tailWord_969416, baseEnd_969416] using wordTrace_append hprefix tailTrace_969416
  have hstable : (prefixWord ++ tailWord_969416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969416).length < 2 ^ (prefixWord ++ tailWord_969416).sum := by decide
  have hdescent : baseEnd_969416 < baseStart_969416 := by decide
  rcases family_descends (prefixWord ++ tailWord_969416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969439 : List Nat := [1, 1, 2, 3, 2, 3, 1, 4, 6]
def baseStart_969439 : Nat := 118140960795 + 969439 * 2 ^ 59
def prefixEnd_969439 : Nat := 4983230072969 + 3 ^ 40 * 969439 * 2
def baseEnd_969439 : Nat := 55309796912681977683793

theorem tailTrace_969439 : CollatzResearch.WordTrace tailWord_969439 prefixEnd_969439 55309796912681977683793 := by
  unfold tailWord_969439
  simp only [CollatzResearch.WordTrace]
  refine ⟨35358345134895544844847371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23572230089930363229898247 35358345134895544844847371)
  ·
    refine ⟨53037517702343317267271057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35358345134895544844847371 53037517702343317267271057)
    ·
      refine ⟨39778138276757487950453293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53037517702343317267271057 39778138276757487950453293)
      ·
        refine ⟨14916801853784057981419985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39778138276757487950453293 14916801853784057981419985)
        ·
          refine ⟨11187601390338043486064989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14916801853784057981419985 11187601390338043486064989)
          ·
            refine ⟨4195350521376766307274371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11187601390338043486064989 4195350521376766307274371)
            ·
              refine ⟨6293025782065149460911557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4195350521376766307274371 6293025782065149460911557)
              ·
                refine ⟨1179942334137215523920917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6293025782065149460911557 1179942334137215523920917)
                ·
                  refine ⟨55309796912681977683793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1179942334137215523920917 55309796912681977683793)
                  ·
                    rfl

theorem cell23_969439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 4, 6].length) (baseStart_969439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_969439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_969439 prefixEnd_969439 := by exact prefixLift 969439
  have htrace : WordTrace (prefixWord ++ tailWord_969439) baseStart_969439 baseEnd_969439 := by
    simpa [prefixWord, tailWord_969439, baseEnd_969439] using wordTrace_append hprefix tailTrace_969439
  have hstable : (prefixWord ++ tailWord_969439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969439).length < 2 ^ (prefixWord ++ tailWord_969439).sum := by decide
  have hdescent : baseEnd_969439 < baseStart_969439 := by decide
  rcases family_descends (prefixWord ++ tailWord_969439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969466 : List Nat := [3, 1, 1, 1, 1, 3, 3, 1, 5, 1, 3]
def baseStart_969466 : Nat := 118140960795 + 969466 * 2 ^ 59
def prefixEnd_969466 : Nat := 4983230072969 + 3 ^ 40 * 969466 * 2
def baseEnd_969466 : Nat := 497802036191809193516513

theorem tailTrace_969466 : CollatzResearch.WordTrace tailWord_969466 prefixEnd_969466 497802036191809193516513 := by
  unfold tailWord_969466
  simp only [CollatzResearch.WordTrace]
  refine ⟨8839832476449432114020063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23572886603865152304053501 8839832476449432114020063)
  ·
    refine ⟨13259748714674148171030095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8839832476449432114020063 13259748714674148171030095)
    ·
      refine ⟨19889623072011222256545143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13259748714674148171030095 19889623072011222256545143)
      ·
        refine ⟨29834434608016833384817715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19889623072011222256545143 29834434608016833384817715)
        ·
          refine ⟨44751651912025250077226573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29834434608016833384817715 44751651912025250077226573)
          ·
            refine ⟨16781869467009468778959965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44751651912025250077226573 16781869467009468778959965)
            ·
              refine ⟨6293201050128550792109987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16781869467009468778959965 6293201050128550792109987)
              ·
                refine ⟨9439801575192826188164981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6293201050128550792109987 9439801575192826188164981)
                ·
                  refine ⟨884981397674327455140467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9439801575192826188164981 884981397674327455140467)
                  ·
                    refine ⟨1327472096511491182710701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 884981397674327455140467 1327472096511491182710701)
                    ·
                      refine ⟨497802036191809193516513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1327472096511491182710701 497802036191809193516513)
                      ·
                        rfl

theorem cell23_969466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 1, 5, 1, 3].length) (baseStart_969466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_969466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_969466 prefixEnd_969466 := by exact prefixLift 969466
  have htrace : WordTrace (prefixWord ++ tailWord_969466) baseStart_969466 baseEnd_969466 := by
    simpa [prefixWord, tailWord_969466, baseEnd_969466] using wordTrace_append hprefix tailTrace_969466
  have hstable : (prefixWord ++ tailWord_969466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969466).length < 2 ^ (prefixWord ++ tailWord_969466).sum := by decide
  have hdescent : baseEnd_969466 < baseStart_969466 := by decide
  rcases family_descends (prefixWord ++ tailWord_969466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969469 : List Nat := [1, 4, 1, 1, 1, 1, 3, 3, 3, 5]
def baseStart_969469 : Nat := 118140960795 + 969469 * 2 ^ 59
def prefixEnd_969469 : Nat := 4983230072969 + 3 ^ 40 * 969469 * 2
def baseEnd_969469 : Nat := 165934525544590893926333

theorem tailTrace_969469 : CollatzResearch.WordTrace tailWord_969469 prefixEnd_969469 165934525544590893926333 := by
  unfold tailWord_969469
  simp only [CollatzResearch.WordTrace]
  refine ⟨35359439324786859968439461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23572959549857906645626307 35359439324786859968439461)
  ·
    refine ⟨6629894873397536244082399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35359439324786859968439461 6629894873397536244082399)
    ·
      refine ⟨9944842310096304366123599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6629894873397536244082399 9944842310096304366123599)
      ·
        refine ⟨14917263465144456549185399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9944842310096304366123599 14917263465144456549185399)
        ·
          refine ⟨22375895197716684823778099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14917263465144456549185399 22375895197716684823778099)
          ·
            refine ⟨33563842796575027235667149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22375895197716684823778099 33563842796575027235667149)
            ·
              refine ⟨12586441048715635213375181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33563842796575027235667149 12586441048715635213375181)
              ·
                refine ⟨4719915393268363205015693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12586441048715635213375181 4719915393268363205015693)
                ·
                  refine ⟨1769968272475636201880885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4719915393268363205015693 1769968272475636201880885)
                  ·
                    refine ⟨165934525544590893926333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1769968272475636201880885 165934525544590893926333)
                    ·
                      rfl

theorem cell23_969469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 3, 3, 5].length) (baseStart_969469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_969469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_969469 prefixEnd_969469 := by exact prefixLift 969469
  have htrace : WordTrace (prefixWord ++ tailWord_969469) baseStart_969469 baseEnd_969469 := by
    simpa [prefixWord, tailWord_969469, baseEnd_969469] using wordTrace_append hprefix tailTrace_969469
  have hstable : (prefixWord ++ tailWord_969469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969469).length < 2 ^ (prefixWord ++ tailWord_969469).sum := by decide
  have hdescent : baseEnd_969469 < baseStart_969469 := by decide
  rcases family_descends (prefixWord ++ tailWord_969469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969470 : List Nat := [4, 2, 2, 1, 2, 3, 1, 1, 2, 2, 3]
def baseStart_969470 : Nat := 118140960795 + 969470 * 2 ^ 59
def prefixEnd_969470 : Nat := 4983230072969 + 3 ^ 40 * 969470 * 2
def baseEnd_969470 : Nat := 497804090114427177866495

theorem tailTrace_969470 : CollatzResearch.WordTrace tailWord_969470 prefixEnd_969470 497804090114427177866495 := by
  unfold tailWord_969470
  simp only [CollatzResearch.WordTrace]
  refine ⟨4419934474722904642403233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23572983865188824759483909 4419934474722904642403233)
  ·
    refine ⟨3314950856042178481802425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4419934474722904642403233 3314950856042178481802425)
    ·
      refine ⟨2486213142031633861351819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3314950856042178481802425 2486213142031633861351819)
      ·
        refine ⟨3729319713047450792027729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2486213142031633861351819 3729319713047450792027729)
        ·
          refine ⟨2796989784785588094020797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3729319713047450792027729 2796989784785588094020797)
          ·
            refine ⟨1048871169294595535257799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2796989784785588094020797 1048871169294595535257799)
            ·
              refine ⟨1573306753941893302886699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1048871169294595535257799 1573306753941893302886699)
              ·
                refine ⟨2359960130912839954330049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1573306753941893302886699 2359960130912839954330049)
                ·
                  refine ⟨1769970098184629965747537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2359960130912839954330049 1769970098184629965747537)
                  ·
                    refine ⟨1327477573638472474310653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1769970098184629965747537 1327477573638472474310653)
                    ·
                      refine ⟨497804090114427177866495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1327477573638472474310653 497804090114427177866495)
                      ·
                        rfl

theorem cell23_969470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 1, 1, 2, 2, 3].length) (baseStart_969470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_969470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_969470 prefixEnd_969470 := by exact prefixLift 969470
  have htrace : WordTrace (prefixWord ++ tailWord_969470) baseStart_969470 baseEnd_969470 := by
    simpa [prefixWord, tailWord_969470, baseEnd_969470] using wordTrace_append hprefix tailTrace_969470
  have hstable : (prefixWord ++ tailWord_969470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969470).length < 2 ^ (prefixWord ++ tailWord_969470).sum := by decide
  have hdescent : baseEnd_969470 < baseStart_969470 := by decide
  rcases family_descends (prefixWord ++ tailWord_969470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969490 : List Nat := [3, 2, 4, 1, 2, 2, 1, 2, 6]
def baseStart_969490 : Nat := 118140960795 + 969490 * 2 ^ 59
def prefixEnd_969490 : Nat := 4983230072969 + 3 ^ 40 * 969490 * 2
def baseEnd_969490 : Nat := 55312706636390788846267

theorem tailTrace_969490 : CollatzResearch.WordTrace tailWord_969490 prefixEnd_969490 55312706636390788846267 := by
  unfold tailWord_969490
  simp only [CollatzResearch.WordTrace]
  refine ⟨8840051314427695138738481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23573470171807187036635949 8840051314427695138738481)
  ·
    refine ⟨6630038485820771354053861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8840051314427695138738481 6630038485820771354053861)
    ·
      refine ⟨1243132216091394628885099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6630038485820771354053861 1243132216091394628885099)
      ·
        refine ⟨1864698324137091943327649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1243132216091394628885099 1864698324137091943327649)
        ·
          refine ⟨1398523743102818957495737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1864698324137091943327649 1398523743102818957495737)
          ·
            refine ⟨1048892807327114218121803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1398523743102818957495737 1048892807327114218121803)
            ·
              refine ⟨1573339210990671327182705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1048892807327114218121803 1573339210990671327182705)
              ·
                refine ⟨1180004408243003495387029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1573339210990671327182705 1180004408243003495387029)
                ·
                  refine ⟨55312706636390788846267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1180004408243003495387029 55312706636390788846267)
                  ·
                    rfl

theorem cell23_969490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 1, 2, 6].length) (baseStart_969490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_969490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_969490 prefixEnd_969490 := by exact prefixLift 969490
  have htrace : WordTrace (prefixWord ++ tailWord_969490) baseStart_969490 baseEnd_969490 := by
    simpa [prefixWord, tailWord_969490, baseEnd_969490] using wordTrace_append hprefix tailTrace_969490
  have hstable : (prefixWord ++ tailWord_969490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969490).length < 2 ^ (prefixWord ++ tailWord_969490).sum := by decide
  have hdescent : baseEnd_969490 < baseStart_969490 := by decide
  rcases family_descends (prefixWord ++ tailWord_969490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969500 : List Nat := [2, 2, 3, 1, 1, 3, 2, 4, 1, 1, 3]
def baseStart_969500 : Nat := 118140960795 + 969500 * 2 ^ 59
def prefixEnd_969500 : Nat := 4983230072969 + 3 ^ 40 * 969500 * 2
def baseEnd_969500 : Nat := 497819494534062060491357

theorem tailTrace_969500 : CollatzResearch.WordTrace tailWord_969500 prefixEnd_969500 497819494534062060491357 := by
  unfold tailWord_969500
  simp only [CollatzResearch.WordTrace]
  refine ⟨17680284993837276131408977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23573713325116368175211969 17680284993837276131408977)
  ·
    refine ⟨13260213745377957098556733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17680284993837276131408977 13260213745377957098556733)
    ·
      refine ⟨4972580154516733911958775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13260213745377957098556733 4972580154516733911958775)
      ·
        refine ⟨7458870231775100867938163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4972580154516733911958775 7458870231775100867938163)
        ·
          refine ⟨11188305347662651301907245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7458870231775100867938163 11188305347662651301907245)
          ·
            refine ⟨4195614505373494238215217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11188305347662651301907245 4195614505373494238215217)
            ·
              refine ⟨3146710879030120678661413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4195614505373494238215217 3146710879030120678661413)
              ·
                refine ⟨590008289818147627249015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3146710879030120678661413 590008289818147627249015)
                ·
                  refine ⟨885012434727221440873523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 590008289818147627249015 885012434727221440873523)
                  ·
                    refine ⟨1327518652090832161310285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 885012434727221440873523 1327518652090832161310285)
                    ·
                      refine ⟨497819494534062060491357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1327518652090832161310285 497819494534062060491357)
                      ·
                        rfl

theorem cell23_969500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 4, 1, 1, 3].length) (baseStart_969500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_969500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_969500 prefixEnd_969500 := by exact prefixLift 969500
  have htrace : WordTrace (prefixWord ++ tailWord_969500) baseStart_969500 baseEnd_969500 := by
    simpa [prefixWord, tailWord_969500, baseEnd_969500] using wordTrace_append hprefix tailTrace_969500
  have hstable : (prefixWord ++ tailWord_969500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969500).length < 2 ^ (prefixWord ++ tailWord_969500).sum := by decide
  have hdescent : baseEnd_969500 < baseStart_969500 := by decide
  rcases family_descends (prefixWord ++ tailWord_969500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969523 : List Nat := [1, 1, 1, 2, 6, 2, 2, 2, 1, 1, 4]
def baseStart_969523 : Nat := 118140960795 + 969523 * 2 ^ 59
def prefixEnd_969523 : Nat := 4983230072969 + 3 ^ 40 * 969523 * 2
def baseEnd_969523 : Nat := 497831304589115470503751

theorem tailTrace_969523 : CollatzResearch.WordTrace tailWord_969523 prefixEnd_969523 497831304589115470503751 := by
  unfold tailWord_969523
  simp only [CollatzResearch.WordTrace]
  refine ⟨35361408866591227190905223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23574272577727484793936815 35361408866591227190905223)
  ·
    refine ⟨53042113299886840786357835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35361408866591227190905223 53042113299886840786357835)
    ·
      refine ⟨79563169949830261179536753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53042113299886840786357835 79563169949830261179536753)
      ·
        refine ⟨59672377462372695884652565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79563169949830261179536753 59672377462372695884652565)
        ·
          refine ⟨2797142693548720119593089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 59672377462372695884652565 2797142693548720119593089)
          ·
            refine ⟨2097857020161540089694817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2797142693548720119593089 2097857020161540089694817)
            ·
              refine ⟨1573392765121155067271113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2097857020161540089694817 1573392765121155067271113)
              ·
                refine ⟨1180044573840866300453335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1573392765121155067271113 1180044573840866300453335)
                ·
                  refine ⟨1770066860761299450680003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1180044573840866300453335 1770066860761299450680003)
                  ·
                    refine ⟨2655100291141949176020005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1770066860761299450680003 2655100291141949176020005)
                    ·
                      refine ⟨497831304589115470503751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2655100291141949176020005 497831304589115470503751)
                      ·
                        rfl

theorem cell23_969523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2, 2, 1, 1, 4].length) (baseStart_969523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_969523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_969523 prefixEnd_969523 := by exact prefixLift 969523
  have htrace : WordTrace (prefixWord ++ tailWord_969523) baseStart_969523 baseEnd_969523 := by
    simpa [prefixWord, tailWord_969523, baseEnd_969523] using wordTrace_append hprefix tailTrace_969523
  have hstable : (prefixWord ++ tailWord_969523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969523).length < 2 ^ (prefixWord ++ tailWord_969523).sum := by decide
  have hdescent : baseEnd_969523 < baseStart_969523 := by decide
  rcases family_descends (prefixWord ++ tailWord_969523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969534 : List Nat := [4, 2, 1, 2, 3, 2, 1, 3, 1, 1, 3]
def baseStart_969534 : Nat := 118140960795 + 969534 * 2 ^ 59
def prefixEnd_969534 : Nat := 4983230072969 + 3 ^ 40 * 969534 * 2
def baseEnd_969534 : Nat := 497836952876314927466201

theorem tailTrace_969534 : CollatzResearch.WordTrace tailWord_969534 prefixEnd_969534 497836952876314927466201 := by
  unfold tailWord_969534
  simp only [CollatzResearch.WordTrace]
  refine ⟨4420226258693922008694457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23574540046367584046370437 4420226258693922008694457)
  ·
    refine ⟨3315169694020441506520843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4420226258693922008694457 3315169694020441506520843)
    ·
      refine ⟨4972754541030662259781265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3315169694020441506520843 4972754541030662259781265)
      ·
        refine ⟨3729565905772996694835949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4972754541030662259781265 3729565905772996694835949)
        ·
          refine ⟨1398587214664873760563481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3729565905772996694835949 1398587214664873760563481)
          ·
            refine ⟨1048940410998655320422611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1398587214664873760563481 1048940410998655320422611)
            ·
              refine ⟨1573410616497982980633917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1048940410998655320422611 1573410616497982980633917)
              ·
                refine ⟨590028981186743617737719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1573410616497982980633917 590028981186743617737719)
                ·
                  refine ⟨885043471780115426606579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 590028981186743617737719 885043471780115426606579)
                  ·
                    refine ⟨1327565207670173139909869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 885043471780115426606579 1327565207670173139909869)
                    ·
                      refine ⟨497836952876314927466201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1327565207670173139909869 497836952876314927466201)
                      ·
                        rfl

theorem cell23_969534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 1, 3, 1, 1, 3].length) (baseStart_969534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_969534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_969534 prefixEnd_969534 := by exact prefixLift 969534
  have htrace : WordTrace (prefixWord ++ tailWord_969534) baseStart_969534 baseEnd_969534 := by
    simpa [prefixWord, tailWord_969534, baseEnd_969534] using wordTrace_append hprefix tailTrace_969534
  have hstable : (prefixWord ++ tailWord_969534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969534).length < 2 ^ (prefixWord ++ tailWord_969534).sum := by decide
  have hdescent : baseEnd_969534 < baseStart_969534 := by decide
  rcases family_descends (prefixWord ++ tailWord_969534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969569 : List Nat := [1, 2, 3, 1, 1, 1, 2, 2, 1, 4, 5]
def baseStart_969569 : Nat := 118140960795 + 969569 * 2 ^ 59
def prefixEnd_969569 : Nat := 4983230072969 + 3 ^ 40 * 969569 * 2
def baseEnd_969569 : Nat := 497854924699222290528539

theorem tailTrace_969569 : CollatzResearch.WordTrace tailWord_969569 prefixEnd_969569 497854924699222290528539 := by
  unfold tailWord_969569
  simp only [CollatzResearch.WordTrace]
  refine ⟨35363086624424577047079761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23575391082949718031386507 35363086624424577047079761)
  ·
    refine ⟨26522314968318432785309821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35363086624424577047079761 26522314968318432785309821)
    ·
      refine ⟨9945868113119412294491183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26522314968318432785309821 9945868113119412294491183)
      ·
        refine ⟨14918802169679118441736775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9945868113119412294491183 14918802169679118441736775)
        ·
          refine ⟨22378203254518677662605163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14918802169679118441736775 22378203254518677662605163)
          ·
            refine ⟨33567304881778016493907745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22378203254518677662605163 33567304881778016493907745)
            ·
              refine ⟨25175478661333512370430809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33567304881778016493907745 25175478661333512370430809)
              ·
                refine ⟨18881608996000134277823107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25175478661333512370430809 18881608996000134277823107)
                ·
                  refine ⟨28322413494000201416734661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18881608996000134277823107 28322413494000201416734661)
                  ·
                    refine ⟨5310452530125037765637749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28322413494000201416734661 5310452530125037765637749)
                    ·
                      refine ⟨497854924699222290528539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5310452530125037765637749 497854924699222290528539)
                      ·
                        rfl

theorem cell23_969569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 4, 5].length) (baseStart_969569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_969569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_969569 prefixEnd_969569 := by exact prefixLift 969569
  have htrace : WordTrace (prefixWord ++ tailWord_969569) baseStart_969569 baseEnd_969569 := by
    simpa [prefixWord, tailWord_969569, baseEnd_969569] using wordTrace_append hprefix tailTrace_969569
  have hstable : (prefixWord ++ tailWord_969569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969569).length < 2 ^ (prefixWord ++ tailWord_969569).sum := by decide
  have hdescent : baseEnd_969569 < baseStart_969569 := by decide
  rcases family_descends (prefixWord ++ tailWord_969569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969590 : List Nat := [5, 1, 1, 3, 1, 2, 1, 2, 1, 3, 3]
def baseStart_969590 : Nat := 118140960795 + 969590 * 2 ^ 59
def prefixEnd_969590 : Nat := 4983230072969 + 3 ^ 40 * 969590 * 2
def baseEnd_969590 : Nat := 497865707792966708365943

theorem tailTrace_969590 : CollatzResearch.WordTrace tailWord_969590 prefixEnd_969590 497865707792966708365943 := by
  unfold tailWord_969590
  simp only [CollatzResearch.WordTrace]
  refine ⟨2210240784834281102099639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23575901704898998422396149 2210240784834281102099639)
  ·
    refine ⟨3315361177251421653149459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2210240784834281102099639 3315361177251421653149459)
    ·
      refine ⟨4973041765877132479724189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3315361177251421653149459 4973041765877132479724189)
      ·
        refine ⟨1864890662203924679896571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4973041765877132479724189 1864890662203924679896571)
        ·
          refine ⟨2797335993305887019844857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1864890662203924679896571 2797335993305887019844857)
          ·
            refine ⟨2098001994979415264883643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2797335993305887019844857 2098001994979415264883643)
            ·
              refine ⟨3147002992469122897325465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2098001994979415264883643 3147002992469122897325465)
              ·
                refine ⟨2360252244351842172994099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3147002992469122897325465 2360252244351842172994099)
                ·
                  refine ⟨3540378366527763259491149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2360252244351842172994099 3540378366527763259491149)
                  ·
                    refine ⟨1327641887447911222309181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3540378366527763259491149 1327641887447911222309181)
                    ·
                      refine ⟨497865707792966708365943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1327641887447911222309181 497865707792966708365943)
                      ·
                        rfl

theorem cell23_969590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_969590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_969590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_969590 prefixEnd_969590 := by exact prefixLift 969590
  have htrace : WordTrace (prefixWord ++ tailWord_969590) baseStart_969590 baseEnd_969590 := by
    simpa [prefixWord, tailWord_969590, baseEnd_969590] using wordTrace_append hprefix tailTrace_969590
  have hstable : (prefixWord ++ tailWord_969590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969590).length < 2 ^ (prefixWord ++ tailWord_969590).sum := by decide
  have hdescent : baseEnd_969590 < baseStart_969590 := by decide
  rcases family_descends (prefixWord ++ tailWord_969590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969636 : List Nat := [2, 3, 1, 2, 1, 2, 3, 2, 7]
def baseStart_969636 : Nat := 118140960795 + 969636 * 2 ^ 59
def prefixEnd_969636 : Nat := 4983230072969 + 3 ^ 40 * 969636 * 2
def baseEnd_969636 : Nat := 55321036433674836487859

theorem tailTrace_969636 : CollatzResearch.WordTrace tailWord_969636 prefixEnd_969636 55321036433674836487859 := by
  unfold tailWord_969636
  simp only [CollatzResearch.WordTrace]
  refine ⟨17682765157590923744884381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23577020210121231659845841 17682765157590923744884381)
  ·
    refine ⟨6631036934096596404331643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17682765157590923744884381 6631036934096596404331643)
    ·
      refine ⟨9946555401144894606497465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6631036934096596404331643 9946555401144894606497465)
      ·
        refine ⟨7459916550858670954873099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9946555401144894606497465 7459916550858670954873099)
        ·
          refine ⟨11189874826288006432309649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7459916550858670954873099 11189874826288006432309649)
          ·
            refine ⟨8392406119716004824232237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11189874826288006432309649 8392406119716004824232237)
            ·
              refine ⟨3147152294893501809087089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8392406119716004824232237 3147152294893501809087089)
              ·
                refine ⟨2360364221170126356815317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3147152294893501809087089 2360364221170126356815317)
                ·
                  refine ⟨55321036433674836487859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2360364221170126356815317 55321036433674836487859)
                  ·
                    rfl

theorem cell23_969636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 2, 7].length) (baseStart_969636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_969636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_969636 prefixEnd_969636 := by exact prefixLift 969636
  have htrace : WordTrace (prefixWord ++ tailWord_969636) baseStart_969636 baseEnd_969636 := by
    simpa [prefixWord, tailWord_969636, baseEnd_969636] using wordTrace_append hprefix tailTrace_969636
  have hstable : (prefixWord ++ tailWord_969636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969636).length < 2 ^ (prefixWord ++ tailWord_969636).sum := by decide
  have hdescent : baseEnd_969636 < baseStart_969636 := by decide
  rcases family_descends (prefixWord ++ tailWord_969636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969676 : List Nat := [2, 2, 1, 4, 1, 1, 2, 1, 1, 1, 7]
def baseStart_969676 : Nat := 118140960795 + 969676 * 2 ^ 59
def prefixEnd_969676 : Nat := 4983230072969 + 3 ^ 40 * 969676 * 2
def baseEnd_969676 : Nat := 497909867129253371890547

theorem tailTrace_969676 : CollatzResearch.WordTrace tailWord_969676 prefixEnd_969676 497909867129253371890547 := by
  unfold tailWord_969676
  simp only [CollatzResearch.WordTrace]
  refine ⟨17683494617518467160612441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23577992823357956214149921 17683494617518467160612441)
  ·
    refine ⟨13262620963138850370459331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17683494617518467160612441 13262620963138850370459331)
    ·
      refine ⟨19893931444708275555688997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13262620963138850370459331 19893931444708275555688997)
      ·
        refine ⟨3730112145882801666691687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19893931444708275555688997 3730112145882801666691687)
        ·
          refine ⟨5595168218824202500037531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3730112145882801666691687 5595168218824202500037531)
          ·
            refine ⟨8392752328236303750056297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5595168218824202500037531 8392752328236303750056297)
            ·
              refine ⟨6294564246177227812542223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8392752328236303750056297 6294564246177227812542223)
              ·
                refine ⟨9441846369265841718813335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6294564246177227812542223 9441846369265841718813335)
                ·
                  refine ⟨14162769553898762578220003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9441846369265841718813335 14162769553898762578220003)
                  ·
                    refine ⟨21244154330848143867330005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14162769553898762578220003 21244154330848143867330005)
                    ·
                      refine ⟨497909867129253371890547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 21244154330848143867330005 497909867129253371890547)
                      ·
                        rfl

theorem cell23_969676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_969676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_969676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_969676 prefixEnd_969676 := by exact prefixLift 969676
  have htrace : WordTrace (prefixWord ++ tailWord_969676) baseStart_969676 baseEnd_969676 := by
    simpa [prefixWord, tailWord_969676, baseEnd_969676] using wordTrace_append hprefix tailTrace_969676
  have hstable : (prefixWord ++ tailWord_969676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969676).length < 2 ^ (prefixWord ++ tailWord_969676).sum := by decide
  have hdescent : baseEnd_969676 < baseStart_969676 := by decide
  rcases family_descends (prefixWord ++ tailWord_969676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969703 : List Nat := [1, 1, 5, 2, 2, 1, 2, 1, 1, 3, 4]
def baseStart_969703 : Nat := 118140960795 + 969703 * 2 ^ 59
def prefixEnd_969703 : Nat := 4983230072969 + 3 ^ 40 * 969703 * 2
def baseEnd_969703 : Nat := 497923731106924766252923

theorem tailTrace_969703 : CollatzResearch.WordTrace tailWord_969703 prefixEnd_969703 497923731106924766252923 := by
  unfold tailWord_969703
  simp only [CollatzResearch.WordTrace]
  refine ⟨35367974005939117932457763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23578649337292745288305175 35367974005939117932457763)
  ·
    refine ⟨53051961008908676898686645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35367974005939117932457763 53051961008908676898686645)
    ·
      refine ⟨4973621344585188459251873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53051961008908676898686645 4973621344585188459251873)
      ·
        refine ⟨3730216008438891344438905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4973621344585188459251873 3730216008438891344438905)
        ·
          refine ⟨2797662006329168508329179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3730216008438891344438905 2797662006329168508329179)
          ·
            refine ⟨4196493009493752762493769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2797662006329168508329179 4196493009493752762493769)
            ·
              refine ⟨3147369757120314571870327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4196493009493752762493769 3147369757120314571870327)
              ·
                refine ⟨4721054635680471857805491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3147369757120314571870327 4721054635680471857805491)
                ·
                  refine ⟨7081581953520707786708237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4721054635680471857805491 7081581953520707786708237)
                  ·
                    refine ⟨2655593232570265420015589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7081581953520707786708237 2655593232570265420015589)
                    ·
                      refine ⟨497923731106924766252923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2655593232570265420015589 497923731106924766252923)
                      ·
                        rfl

theorem cell23_969703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_969703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_969703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_969703 prefixEnd_969703 := by exact prefixLift 969703
  have htrace : WordTrace (prefixWord ++ tailWord_969703) baseStart_969703 baseEnd_969703 := by
    simpa [prefixWord, tailWord_969703, baseEnd_969703] using wordTrace_append hprefix tailTrace_969703
  have hstable : (prefixWord ++ tailWord_969703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969703).length < 2 ^ (prefixWord ++ tailWord_969703).sum := by decide
  have hdescent : baseEnd_969703 < baseStart_969703 := by decide
  rcases family_descends (prefixWord ++ tailWord_969703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969717 : List Nat := [1, 3, 5, 2, 1, 1, 1, 2, 2, 5]
def baseStart_969717 : Nat := 118140960795 + 969717 * 2 ^ 59
def prefixEnd_969717 : Nat := 4983230072969 + 3 ^ 40 * 969717 * 2
def baseEnd_969717 : Nat := 165976973278695903825953

theorem tailTrace_969717 : CollatzResearch.WordTrace tailWord_969717 prefixEnd_969717 165976973278695903825953 := by
  unfold tailWord_969717
  simp only [CollatzResearch.WordTrace]
  refine ⟨35368484627888398323467405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23578989751925598882311603 35368484627888398323467405)
  ·
    refine ⟨13263181735458149371300277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35368484627888398323467405 13263181735458149371300277)
    ·
      refine ⟨1243423287699201503559401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13263181735458149371300277 1243423287699201503559401)
      ·
        refine ⟨932567465774401127669551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1243423287699201503559401 932567465774401127669551)
        ·
          refine ⟨1398851198661601691504327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 932567465774401127669551 1398851198661601691504327)
          ·
            refine ⟨2098276797992402537256491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1398851198661601691504327 2098276797992402537256491)
            ·
              refine ⟨3147415196988603805884737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2098276797992402537256491 3147415196988603805884737)
              ·
                refine ⟨2360561397741452854413553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3147415196988603805884737 2360561397741452854413553)
                ·
                  refine ⟨1770421048306089640810165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2360561397741452854413553 1770421048306089640810165)
                  ·
                    refine ⟨165976973278695903825953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1770421048306089640810165 165976973278695903825953)
                    ·
                      rfl

theorem cell23_969717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_969717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_969717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_969717 prefixEnd_969717 := by exact prefixLift 969717
  have htrace : WordTrace (prefixWord ++ tailWord_969717) baseStart_969717 baseEnd_969717 := by
    simpa [prefixWord, tailWord_969717, baseEnd_969717] using wordTrace_append hprefix tailTrace_969717
  have hstable : (prefixWord ++ tailWord_969717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969717).length < 2 ^ (prefixWord ++ tailWord_969717).sum := by decide
  have hdescent : baseEnd_969717 < baseStart_969717 := by decide
  rcases family_descends (prefixWord ++ tailWord_969717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969757 : List Nat := [1, 4, 2, 2, 3, 1, 2, 1, 2, 2, 3]
def baseStart_969757 : Nat := 118140960795 + 969757 * 2 ^ 59
def prefixEnd_969757 : Nat := 4983230072969 + 3 ^ 40 * 969757 * 2
def baseEnd_969757 : Nat := 497951459062267554977675

theorem tailTrace_969757 : CollatzResearch.WordTrace tailWord_969757 prefixEnd_969757 497951459062267554977675 := by
  unfold tailWord_969757
  simp only [CollatzResearch.WordTrace]
  refine ⟨35369943547743485154923525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23579962365162323436615683 35369943547743485154923525)
  ·
    refine ⟨6631864415201903466548161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35369943547743485154923525 6631864415201903466548161)
    ·
      refine ⟨4973898311401427599911121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6631864415201903466548161 4973898311401427599911121)
      ·
        refine ⟨3730423733551070699933341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4973898311401427599911121 3730423733551070699933341)
        ·
          refine ⟨1398908900081651512475003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3730423733551070699933341 1398908900081651512475003)
          ·
            refine ⟨2098363350122477268712505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1398908900081651512475003 2098363350122477268712505)
            ·
              refine ⟨1573772512591857951534379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2098363350122477268712505 1573772512591857951534379)
              ·
                refine ⟨2360658768887786927301569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1573772512591857951534379 2360658768887786927301569)
                ·
                  refine ⟨1770494076665840195476177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2360658768887786927301569 1770494076665840195476177)
                  ·
                    refine ⟨1327870557499380146607133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1770494076665840195476177 1327870557499380146607133)
                    ·
                      refine ⟨497951459062267554977675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1327870557499380146607133 497951459062267554977675)
                      ·
                        rfl

theorem cell23_969757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 2, 1, 2, 2, 3].length) (baseStart_969757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_969757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_969757 prefixEnd_969757 := by exact prefixLift 969757
  have htrace : WordTrace (prefixWord ++ tailWord_969757) baseStart_969757 baseEnd_969757 := by
    simpa [prefixWord, tailWord_969757, baseEnd_969757] using wordTrace_append hprefix tailTrace_969757
  have hstable : (prefixWord ++ tailWord_969757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969757).length < 2 ^ (prefixWord ++ tailWord_969757).sum := by decide
  have hdescent : baseEnd_969757 < baseStart_969757 := by decide
  rcases family_descends (prefixWord ++ tailWord_969757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969790 : List Nat := [4, 2, 1, 3, 1, 1, 1, 2, 3, 5]
def baseStart_969790 : Nat := 118140960795 + 969790 * 2 ^ 59
def prefixEnd_969790 : Nat := 4983230072969 + 3 ^ 40 * 969790 * 2
def baseEnd_969790 : Nat := 165989467974621975288341

theorem tailTrace_969790 : CollatzResearch.WordTrace tailWord_969790 prefixEnd_969790 165989467974621975288341 := by
  unfold tailWord_969790
  simp only [CollatzResearch.WordTrace]
  refine ⟨4421393394577991473859353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23580764771082621193916549 4421393394577991473859353)
  ·
    refine ⟨3316045045933493605394515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4421393394577991473859353 3316045045933493605394515)
    ·
      refine ⟨4974067568900240408091773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3316045045933493605394515 4974067568900240408091773)
      ·
        refine ⟨1865275338337590153034415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4974067568900240408091773 1865275338337590153034415)
        ·
          refine ⟨2797913007506385229551623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1865275338337590153034415 2797913007506385229551623)
          ·
            refine ⟨4196869511259577844327435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2797913007506385229551623 4196869511259577844327435)
            ·
              refine ⟨6295304266889366766491153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4196869511259577844327435 6295304266889366766491153)
              ·
                refine ⟨4721478200167025074868365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6295304266889366766491153 4721478200167025074868365)
                ·
                  refine ⟨1770554325062634403075637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4721478200167025074868365 1770554325062634403075637)
                  ·
                    refine ⟨165989467974621975288341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1770554325062634403075637 165989467974621975288341)
                    ·
                      rfl

theorem cell23_969790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 2, 3, 5].length) (baseStart_969790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_969790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_969790 prefixEnd_969790 := by exact prefixLift 969790
  have htrace : WordTrace (prefixWord ++ tailWord_969790) baseStart_969790 baseEnd_969790 := by
    simpa [prefixWord, tailWord_969790, baseEnd_969790] using wordTrace_append hprefix tailTrace_969790
  have hstable : (prefixWord ++ tailWord_969790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969790).length < 2 ^ (prefixWord ++ tailWord_969790).sum := by decide
  have hdescent : baseEnd_969790 < baseStart_969790 := by decide
  rcases family_descends (prefixWord ++ tailWord_969790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969810 : List Nat := [3, 2, 2, 1, 3, 1, 2, 1, 3, 1, 4]
def baseStart_969810 : Nat := 118140960795 + 969810 * 2 ^ 59
def prefixEnd_969810 : Nat := 4983230072969 + 3 ^ 40 * 969810 * 2
def baseEnd_969810 : Nat := 497978673536955847614931

theorem tailTrace_969810 : CollatzResearch.WordTrace tailWord_969810 prefixEnd_969810 497978673536955847614931 := by
  unfold tailWord_969810
  simp only [CollatzResearch.WordTrace]
  refine ⟨8842969154137868801650721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23581251077700983471068589 8842969154137868801650721)
  ·
    refine ⟨6632226865603401601238041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8842969154137868801650721 6632226865603401601238041)
    ·
      refine ⟨4974170149202551200928531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6632226865603401601238041 4974170149202551200928531)
      ·
        refine ⟨7461255223803826801392797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4974170149202551200928531 7461255223803826801392797)
        ·
          refine ⟨2797970708926435050522299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7461255223803826801392797 2797970708926435050522299)
          ·
            refine ⟨4196956063389652575783449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2797970708926435050522299 4196956063389652575783449)
            ·
              refine ⟨3147717047542239431837587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4196956063389652575783449 3147717047542239431837587)
              ·
                refine ⟨4721575571313359147756381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3147717047542239431837587 4721575571313359147756381)
                ·
                  refine ⟨1770590839242509680408643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4721575571313359147756381 1770590839242509680408643)
                  ·
                    refine ⟨2655886258863764520612965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1770590839242509680408643 2655886258863764520612965)
                    ·
                      refine ⟨497978673536955847614931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2655886258863764520612965 497978673536955847614931)
                      ·
                        rfl

theorem cell23_969810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 1, 3, 1, 4].length) (baseStart_969810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_969810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_969810 prefixEnd_969810 := by exact prefixLift 969810
  have htrace : WordTrace (prefixWord ++ tailWord_969810) baseStart_969810 baseEnd_969810 := by
    simpa [prefixWord, tailWord_969810, baseEnd_969810] using wordTrace_append hprefix tailTrace_969810
  have hstable : (prefixWord ++ tailWord_969810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969810).length < 2 ^ (prefixWord ++ tailWord_969810).sum := by decide
  have hdescent : baseEnd_969810 < baseStart_969810 := by decide
  rcases family_descends (prefixWord ++ tailWord_969810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969820 : List Nat := [2, 2, 4, 1, 1, 1, 2, 2, 4, 4]
def baseStart_969820 : Nat := 118140960795 + 969820 * 2 ^ 59
def prefixEnd_969820 : Nat := 4983230072969 + 3 ^ 40 * 969820 * 2
def baseEnd_969820 : Nat := 165994602781166936163295

theorem tailTrace_969820 : CollatzResearch.WordTrace tailWord_969820 prefixEnd_969820 165994602781166936163295 := by
  unfold tailWord_969820
  simp only [CollatzResearch.WordTrace]
  refine ⟨17686120673257623457233457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23581494231010164609644609 17686120673257623457233457)
  ·
    refine ⟨13264590504943217592925093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17686120673257623457233457 13264590504943217592925093)
    ·
      refine ⟨2487110719676853298673455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13264590504943217592925093 2487110719676853298673455)
      ·
        refine ⟨3730666079515279948010183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2487110719676853298673455 3730666079515279948010183)
        ·
          refine ⟨5595999119272919922015275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3730666079515279948010183 5595999119272919922015275)
          ·
            refine ⟨8393998678909379883022913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5595999119272919922015275 8393998678909379883022913)
            ·
              refine ⟨6295499009182034912267185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8393998678909379883022913 6295499009182034912267185)
              ·
                refine ⟨4721624256886526184200389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6295499009182034912267185 4721624256886526184200389)
                ·
                  refine ⟨885304548166223659537573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4721624256886526184200389 885304548166223659537573)
                  ·
                    refine ⟨165994602781166936163295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 885304548166223659537573 165994602781166936163295)
                    ·
                      rfl

theorem cell23_969820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 2, 4, 4].length) (baseStart_969820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_969820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_969820 prefixEnd_969820 := by exact prefixLift 969820
  have htrace : WordTrace (prefixWord ++ tailWord_969820) baseStart_969820 baseEnd_969820 := by
    simpa [prefixWord, tailWord_969820, baseEnd_969820] using wordTrace_append hprefix tailTrace_969820
  have hstable : (prefixWord ++ tailWord_969820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969820).length < 2 ^ (prefixWord ++ tailWord_969820).sum := by decide
  have hdescent : baseEnd_969820 < baseStart_969820 := by decide
  rcases family_descends (prefixWord ++ tailWord_969820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969823 : List Nat := [1, 1, 2, 3, 1, 1, 3, 4, 1, 2, 4]
def baseStart_969823 : Nat := 118140960795 + 969823 * 2 ^ 59
def prefixEnd_969823 : Nat := 4983230072969 + 3 ^ 40 * 969823 * 2
def baseEnd_969823 : Nat := 497985348785464296752371

theorem tailTrace_969823 : CollatzResearch.WordTrace tailWord_969823 prefixEnd_969823 497985348785464296752371 := by
  unfold tailWord_969823
  simp only [CollatzResearch.WordTrace]
  refine ⟨35372350765504378426826123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23581567177002918951217415 35372350765504378426826123)
  ·
    refine ⟨53058526148256567640239185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35372350765504378426826123 53058526148256567640239185)
    ·
      refine ⟨39793894611192425730179389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53058526148256567640239185 39793894611192425730179389)
      ·
        refine ⟨14922710479197159648817271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39793894611192425730179389 14922710479197159648817271)
        ·
          refine ⟨22384065718795739473225907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14922710479197159648817271 22384065718795739473225907)
          ·
            refine ⟨33576098578193609209838861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22384065718795739473225907 33576098578193609209838861)
            ·
              refine ⟨12591036966822603453689573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33576098578193609209838861 12591036966822603453689573)
              ·
                refine ⟨2360819431279238147566795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12591036966822603453689573 2360819431279238147566795)
                ·
                  refine ⟨3541229146918857221350193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2360819431279238147566795 3541229146918857221350193)
                  ·
                    refine ⟨2655921860189142916012645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3541229146918857221350193 2655921860189142916012645)
                    ·
                      refine ⟨497985348785464296752371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2655921860189142916012645 497985348785464296752371)
                      ·
                        rfl

theorem cell23_969823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 4, 1, 2, 4].length) (baseStart_969823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_969823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_969823 prefixEnd_969823 := by exact prefixLift 969823
  have htrace : WordTrace (prefixWord ++ tailWord_969823) baseStart_969823 baseEnd_969823 := by
    simpa [prefixWord, tailWord_969823, baseEnd_969823] using wordTrace_append hprefix tailTrace_969823
  have hstable : (prefixWord ++ tailWord_969823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969823).length < 2 ^ (prefixWord ++ tailWord_969823).sum := by decide
  have hdescent : baseEnd_969823 < baseStart_969823 := by decide
  rcases family_descends (prefixWord ++ tailWord_969823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969837 : List Nat := [1, 5, 1, 1, 2, 2, 3, 2, 2, 4]
def baseStart_969837 : Nat := 118140960795 + 969837 * 2 ^ 59
def prefixEnd_969837 : Nat := 4983230072969 + 3 ^ 40 * 969837 * 2
def baseEnd_969837 : Nat := 165997512504875747325769

theorem tailTrace_969837 : CollatzResearch.WordTrace tailWord_969837 prefixEnd_969837 165997512504875747325769 := by
  unfold tailWord_969837
  simp only [CollatzResearch.WordTrace]
  refine ⟨35372861387453658817835765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23581907591635772545223843 35372861387453658817835765)
  ·
    refine ⟨3316205755073780514172103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35372861387453658817835765 3316205755073780514172103)
    ·
      refine ⟨4974308632610670771258155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3316205755073780514172103 4974308632610670771258155)
      ·
        refine ⟨7461462948916006156887233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4974308632610670771258155 7461462948916006156887233)
        ·
          refine ⟨5596097211687004617665425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7461462948916006156887233 5596097211687004617665425)
          ·
            refine ⟨4197072908765253463249069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5596097211687004617665425 4197072908765253463249069)
            ·
              refine ⟨1573902340786970048718401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4197072908765253463249069 1573902340786970048718401)
              ·
                refine ⟨1180426755590227536538801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1573902340786970048718401 1180426755590227536538801)
                ·
                  refine ⟨885320066692670652404101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1180426755590227536538801 885320066692670652404101)
                  ·
                    refine ⟨165997512504875747325769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 885320066692670652404101 165997512504875747325769)
                    ·
                      rfl

theorem cell23_969837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3, 2, 2, 4].length) (baseStart_969837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_969837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_969837 prefixEnd_969837 := by exact prefixLift 969837
  have htrace : WordTrace (prefixWord ++ tailWord_969837) baseStart_969837 baseEnd_969837 := by
    simpa [prefixWord, tailWord_969837, baseEnd_969837] using wordTrace_append hprefix tailTrace_969837
  have hstable : (prefixWord ++ tailWord_969837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969837).length < 2 ^ (prefixWord ++ tailWord_969837).sum := by decide
  have hdescent : baseEnd_969837 < baseStart_969837 := by decide
  rcases family_descends (prefixWord ++ tailWord_969837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969857 : List Nat := [1, 2, 4, 2, 2, 3, 1, 1, 1, 2, 4]
def baseStart_969857 : Nat := 118140960795 + 969857 * 2 ^ 59
def prefixEnd_969857 : Nat := 4983230072969 + 3 ^ 40 * 969857 * 2
def baseEnd_969857 : Nat := 498002807127717163727215

theorem tailTrace_969857 : CollatzResearch.WordTrace tailWord_969857 prefixEnd_969857 498002807127717163727215 := by
  unfold tailWord_969857
  simp only [CollatzResearch.WordTrace]
  refine ⟨35373590847381202233563825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23582393898254134822375883 35373590847381202233563825)
  ·
    refine ⟨26530193135535901675172869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35373590847381202233563825 26530193135535901675172869)
    ·
      refine ⟨4974411212912981564094913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26530193135535901675172869 4974411212912981564094913)
      ·
        refine ⟨3730808409684736173071185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4974411212912981564094913 3730808409684736173071185)
        ·
          refine ⟨2798106307263552129803389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3730808409684736173071185 2798106307263552129803389)
          ·
            refine ⟨1049289865223832048676271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2798106307263552129803389 1049289865223832048676271)
            ·
              refine ⟨1573934797835748073014407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1049289865223832048676271 1573934797835748073014407)
              ·
                refine ⟨2360902196753622109521611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1573934797835748073014407 2360902196753622109521611)
                ·
                  refine ⟨3541353295130433164282417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2360902196753622109521611 3541353295130433164282417)
                  ·
                    refine ⟨2656014971347824873211813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3541353295130433164282417 2656014971347824873211813)
                    ·
                      refine ⟨498002807127717163727215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2656014971347824873211813 498002807127717163727215)
                      ·
                        rfl

theorem cell23_969857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 1, 1, 1, 2, 4].length) (baseStart_969857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_969857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_969857 prefixEnd_969857 := by exact prefixLift 969857
  have htrace : WordTrace (prefixWord ++ tailWord_969857) baseStart_969857 baseEnd_969857 := by
    simpa [prefixWord, tailWord_969857, baseEnd_969857] using wordTrace_append hprefix tailTrace_969857
  have hstable : (prefixWord ++ tailWord_969857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969857).length < 2 ^ (prefixWord ++ tailWord_969857).sum := by decide
  have hdescent : baseEnd_969857 < baseStart_969857 := by decide
  rcases family_descends (prefixWord ++ tailWord_969857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969864 : List Nat := [2, 1, 3, 4, 2, 1, 2, 2, 1, 2, 3]
def baseStart_969864 : Nat := 118140960795 + 969864 * 2 ^ 59
def prefixEnd_969864 : Nat := 4983230072969 + 3 ^ 40 * 969864 * 2
def baseEnd_969864 : Nat := 498006401492298636339683

theorem tailTrace_969864 : CollatzResearch.WordTrace tailWord_969864 prefixEnd_969864 498006401492298636339683 := by
  unfold tailWord_969864
  simp only [CollatzResearch.WordTrace]
  refine ⟨17686923079177921214534323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23582564105570561619379097 17686923079177921214534323)
  ·
    refine ⟨26530384618766881821801485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17686923079177921214534323 26530384618766881821801485)
    ·
      refine ⟨9948894232037580683175557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26530384618766881821801485 9948894232037580683175557)
      ·
        refine ⟨1865417668507046378095417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9948894232037580683175557 1865417668507046378095417)
        ·
          refine ⟨1399063251380284783571563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1865417668507046378095417 1399063251380284783571563)
          ·
            refine ⟨2098594877070427175357345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1399063251380284783571563 2098594877070427175357345)
            ·
              refine ⟨1573946157802820381518009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2098594877070427175357345 1573946157802820381518009)
              ·
                refine ⟨1180459618352115286138507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1573946157802820381518009 1180459618352115286138507)
                ·
                  refine ⟨1770689427528172929207761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1180459618352115286138507 1770689427528172929207761)
                  ·
                    refine ⟨1328017070646129696905821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1770689427528172929207761 1328017070646129696905821)
                    ·
                      refine ⟨498006401492298636339683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1328017070646129696905821 498006401492298636339683)
                      ·
                        rfl

theorem cell23_969864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_969864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_969864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_969864 prefixEnd_969864 := by exact prefixLift 969864
  have htrace : WordTrace (prefixWord ++ tailWord_969864) baseStart_969864 baseEnd_969864 := by
    simpa [prefixWord, tailWord_969864, baseEnd_969864] using wordTrace_append hprefix tailTrace_969864
  have hstable : (prefixWord ++ tailWord_969864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969864).length < 2 ^ (prefixWord ++ tailWord_969864).sum := by decide
  have hdescent : baseEnd_969864 < baseStart_969864 := by decide
  rcases family_descends (prefixWord ++ tailWord_969864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969900 : List Nat := [2, 2, 1, 1, 1, 1, 1, 3, 5, 4, 2]
def baseStart_969900 : Nat := 118140960795 + 969900 * 2 ^ 59
def prefixEnd_969900 : Nat := 4983230072969 + 3 ^ 40 * 969900 * 2
def baseEnd_969900 : Nat := 498024886795860495489517

theorem tailTrace_969900 : CollatzResearch.WordTrace tailWord_969900 prefixEnd_969900 498024886795860495489517 := by
  unfold tailWord_969900
  simp only [CollatzResearch.WordTrace]
  refine ⟨17687579593112710288689577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23583439457483613718252769 17687579593112710288689577)
  ·
    refine ⟨13265684694834532716517183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17687579593112710288689577 13265684694834532716517183)
    ·
      refine ⟨19898527042251799074775775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13265684694834532716517183 19898527042251799074775775)
      ·
        refine ⟨29847790563377698612163663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19898527042251799074775775 29847790563377698612163663)
        ·
          refine ⟨44771685845066547918245495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29847790563377698612163663 44771685845066547918245495)
          ·
            refine ⟨67157528767599821877368243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44771685845066547918245495 67157528767599821877368243)
            ·
              refine ⟨100736293151399732816052365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67157528767599821877368243 100736293151399732816052365)
              ·
                refine ⟨37776109931774899806019637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100736293151399732816052365 37776109931774899806019637)
                ·
                  refine ⟨3541510306103896856814341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37776109931774899806019637 3541510306103896856814341)
                  ·
                    refine ⟨664033182394480660652689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3541510306103896856814341 664033182394480660652689)
                    ·
                      refine ⟨498024886795860495489517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 664033182394480660652689 498024886795860495489517)
                      ·
                        rfl

theorem cell23_969900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 4, 2].length) (baseStart_969900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_969900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_969900 prefixEnd_969900 := by exact prefixLift 969900
  have htrace : WordTrace (prefixWord ++ tailWord_969900) baseStart_969900 baseEnd_969900 := by
    simpa [prefixWord, tailWord_969900, baseEnd_969900] using wordTrace_append hprefix tailTrace_969900
  have hstable : (prefixWord ++ tailWord_969900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969900).length < 2 ^ (prefixWord ++ tailWord_969900).sum := by decide
  have hdescent : baseEnd_969900 < baseStart_969900 := by decide
  rcases family_descends (prefixWord ++ tailWord_969900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969921 : List Nat := [1, 2, 6, 1, 1, 1, 3, 2, 1, 3, 2]
def baseStart_969921 : Nat := 118140960795 + 969921 * 2 ^ 59
def prefixEnd_969921 : Nat := 4983230072969 + 3 ^ 40 * 969921 * 2
def baseEnd_969921 : Nat := 498035669889604913326921

theorem tailTrace_969921 : CollatzResearch.WordTrace tailWord_969921 prefixEnd_969921 498035669889604913326921 := by
  unfold tailWord_969921
  simp only [CollatzResearch.WordTrace]
  refine ⟨35375925119149341163893617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23583950079432894109262411 35375925119149341163893617)
  ·
    refine ⟨26531943839362005872920213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35375925119149341163893617 26531943839362005872920213)
    ·
      refine ⟨1243684867470094025293135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 26531943839362005872920213 1243684867470094025293135)
      ·
        refine ⟨1865527301205141037939703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1243684867470094025293135 1865527301205141037939703)
        ·
          refine ⟨2798290951807711556909555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1865527301205141037939703 2798290951807711556909555)
          ·
            refine ⟨4197436427711567335364333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2798290951807711556909555 4197436427711567335364333)
            ·
              refine ⟨1574038660391837750761625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4197436427711567335364333 1574038660391837750761625)
              ·
                refine ⟨1180528995293878313071219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1574038660391837750761625 1180528995293878313071219)
                ·
                  refine ⟨1770793492940817469606829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1180528995293878313071219 1770793492940817469606829)
                  ·
                    refine ⟨664047559852806551102561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1770793492940817469606829 664047559852806551102561)
                    ·
                      refine ⟨498035669889604913326921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 664047559852806551102561 498035669889604913326921)
                      ·
                        rfl

theorem cell23_969921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 3, 2, 1, 3, 2].length) (baseStart_969921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_969921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_969921 prefixEnd_969921 := by exact prefixLift 969921
  have htrace : WordTrace (prefixWord ++ tailWord_969921) baseStart_969921 baseEnd_969921 := by
    simpa [prefixWord, tailWord_969921, baseEnd_969921] using wordTrace_append hprefix tailTrace_969921
  have hstable : (prefixWord ++ tailWord_969921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969921).length < 2 ^ (prefixWord ++ tailWord_969921).sum := by decide
  have hdescent : baseEnd_969921 < baseStart_969921 := by decide
  rcases family_descends (prefixWord ++ tailWord_969921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969934 : List Nat := [4, 1, 1, 1, 5, 1, 1, 2, 1, 4, 2]
def baseStart_969934 : Nat := 118140960795 + 969934 * 2 ^ 59
def prefixEnd_969934 : Nat := 4983230072969 + 3 ^ 40 * 969934 * 2
def baseEnd_969934 : Nat := 498042345138113362464361

theorem tailTrace_969934 : CollatzResearch.WordTrace tailWord_969934 prefixEnd_969934 498042345138113362464361 := by
  unfold tailWord_969934
  simp only [CollatzResearch.WordTrace]
  refine ⟨4422049908512780548014607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23584266178734829589411237 4422049908512780548014607)
  ·
    refine ⟨6633074862769170822021911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4422049908512780548014607 6633074862769170822021911)
    ·
      refine ⟨9949612294153756233032867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6633074862769170822021911 9949612294153756233032867)
      ·
        refine ⟨14924418441230634349549301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9949612294153756233032867 14924418441230634349549301)
        ·
          refine ⟨1399164228865371970270247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14924418441230634349549301 1399164228865371970270247)
          ·
            refine ⟨2098746343298057955405371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1399164228865371970270247 2098746343298057955405371)
            ·
              refine ⟨3148119514947086933108057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2098746343298057955405371 3148119514947086933108057)
              ·
                refine ⟨2361089636210315199831043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3148119514947086933108057 2361089636210315199831043)
                ·
                  refine ⟨3541634454315472799746565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2361089636210315199831043 3541634454315472799746565)
                  ·
                    refine ⟨664056460184151149952481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3541634454315472799746565 664056460184151149952481)
                    ·
                      refine ⟨498042345138113362464361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 664056460184151149952481 498042345138113362464361)
                      ·
                        rfl

theorem cell23_969934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 2, 1, 4, 2].length) (baseStart_969934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_969934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_969934 prefixEnd_969934 := by exact prefixLift 969934
  have htrace : WordTrace (prefixWord ++ tailWord_969934) baseStart_969934 baseEnd_969934 := by
    simpa [prefixWord, tailWord_969934, baseEnd_969934] using wordTrace_append hprefix tailTrace_969934
  have hstable : (prefixWord ++ tailWord_969934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969934).length < 2 ^ (prefixWord ++ tailWord_969934).sum := by decide
  have hdescent : baseEnd_969934 < baseStart_969934 := by decide
  rcases family_descends (prefixWord ++ tailWord_969934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969967 : List Nat := [1, 1, 2, 1, 7, 1, 1, 1, 2, 3, 3]
def baseStart_969967 : Nat := 118140960795 + 969967 * 2 ^ 59
def prefixEnd_969967 : Nat := 4983230072969 + 3 ^ 40 * 969967 * 2
def baseEnd_969967 : Nat := 498059289999711733351709

theorem tailTrace_969967 : CollatzResearch.WordTrace tailWord_969967 prefixEnd_969967 498059289999711733351709 := by
  unfold tailWord_969967
  simp only [CollatzResearch.WordTrace]
  refine ⟨35377602876982691020068155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23585068584655127346712103 35377602876982691020068155)
  ·
    refine ⟨53066404315474036530102233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35377602876982691020068155 53066404315474036530102233)
    ·
      refine ⟨39799803236605527397576675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53066404315474036530102233 39799803236605527397576675)
      ·
        refine ⟨59699704854908291096365013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39799803236605527397576675 59699704854908291096365013)
        ·
          refine ⟨1399211832536913072571055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 59699704854908291096365013 1399211832536913072571055)
          ·
            refine ⟨2098817748805369608856583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1399211832536913072571055 2098817748805369608856583)
            ·
              refine ⟨3148226623208054413284875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2098817748805369608856583 3148226623208054413284875)
              ·
                refine ⟨4722339934812081619927313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3148226623208054413284875 4722339934812081619927313)
                ·
                  refine ⟨3541754951109061214945485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4722339934812081619927313 3541754951109061214945485)
                  ·
                    refine ⟨1328158106665897955604557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3541754951109061214945485 1328158106665897955604557)
                    ·
                      refine ⟨498059289999711733351709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1328158106665897955604557 498059289999711733351709)
                      ·
                        rfl

theorem cell23_969967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 1, 2, 3, 3].length) (baseStart_969967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_969967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_969967 prefixEnd_969967 := by exact prefixLift 969967
  have htrace : WordTrace (prefixWord ++ tailWord_969967) baseStart_969967 baseEnd_969967 := by
    simpa [prefixWord, tailWord_969967, baseEnd_969967] using wordTrace_append hprefix tailTrace_969967
  have hstable : (prefixWord ++ tailWord_969967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969967).length < 2 ^ (prefixWord ++ tailWord_969967).sum := by decide
  have hdescent : baseEnd_969967 < baseStart_969967 := by decide
  rcases family_descends (prefixWord ++ tailWord_969967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969987 : List Nat := [1, 1, 1, 3, 2, 6, 1, 1, 2, 5]
def baseStart_969987 : Nat := 118140960795 + 969987 * 2 ^ 59
def prefixEnd_969987 : Nat := 4983230072969 + 3 ^ 40 * 969987 * 2
def baseEnd_969987 : Nat := 166023186537600551700539

theorem tailTrace_969987 : CollatzResearch.WordTrace tailWord_969987 prefixEnd_969987 166023186537600551700539 := by
  unfold tailWord_969987
  simp only [CollatzResearch.WordTrace]
  refine ⟨35378332336910234435796215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23585554891273489623864143 35378332336910234435796215)
  ·
    refine ⟨53067498505365351653694323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35378332336910234435796215 53067498505365351653694323)
    ·
      refine ⟨79601247758048027480541485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53067498505365351653694323 79601247758048027480541485)
      ·
        refine ⟨29850467909268010305203057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79601247758048027480541485 29850467909268010305203057)
        ·
          refine ⟨22387850931951007728902293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29850467909268010305203057 22387850931951007728902293)
          ·
            refine ⟨1049430512435203487292295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 22387850931951007728902293 1049430512435203487292295)
            ·
              refine ⟨1574145768652805230938443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1049430512435203487292295 1574145768652805230938443)
              ·
                refine ⟨2361218652979207846407665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1574145768652805230938443 2361218652979207846407665)
                ·
                  refine ⟨1770913989734405884805749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2361218652979207846407665 1770913989734405884805749)
                  ·
                    refine ⟨166023186537600551700539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1770913989734405884805749 166023186537600551700539)
                    ·
                      rfl

theorem cell23_969987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 1, 1, 2, 5].length) (baseStart_969987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_969987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_969987 prefixEnd_969987 := by exact prefixLift 969987
  have htrace : WordTrace (prefixWord ++ tailWord_969987) baseStart_969987 baseEnd_969987 := by
    simpa [prefixWord, tailWord_969987, baseEnd_969987] using wordTrace_append hprefix tailTrace_969987
  have hstable : (prefixWord ++ tailWord_969987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969987).length < 2 ^ (prefixWord ++ tailWord_969987).sum := by decide
  have hdescent : baseEnd_969987 < baseStart_969987 := by decide
  rcases family_descends (prefixWord ++ tailWord_969987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970002 : List Nat := [3, 2, 4, 2, 2, 1, 1, 2, 2, 2, 2]
def baseStart_970002 : Nat := 118140960795 + 970002 * 2 ^ 59
def prefixEnd_970002 : Nat := 4983230072969 + 3 ^ 40 * 970002 * 2
def baseEnd_970002 : Nat := 498077261822619096414049

theorem tailTrace_970002 : CollatzResearch.WordTrace tailWord_970002 prefixEnd_970002 498077261822619096414049 := by
  unfold tailWord_970002
  simp only [CollatzResearch.WordTrace]
  refine ⟨8844719857963972999398065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23585919621237261331728173 8844719857963972999398065)
  ·
    refine ⟨6633539893472979749548549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8844719857963972999398065 6633539893472979749548549)
    ·
      refine ⟨1243788730026183703040353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6633539893472979749548549 1243788730026183703040353)
      ·
        refine ⟨932841547519637777280265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1243788730026183703040353 932841547519637777280265)
        ·
          refine ⟨699631160639728332960199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 932841547519637777280265 699631160639728332960199)
          ·
            refine ⟨1049446740959592499440299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 699631160639728332960199 1049446740959592499440299)
            ·
              refine ⟨1574170111439388749160449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1049446740959592499440299 1574170111439388749160449)
              ·
                refine ⟨1180627583579541561870337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1574170111439388749160449 1180627583579541561870337)
                ·
                  refine ⟨885470687684656171402753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1180627583579541561870337 885470687684656171402753)
                  ·
                    refine ⟨664103015763492128552065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 885470687684656171402753 664103015763492128552065)
                    ·
                      refine ⟨498077261822619096414049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 664103015763492128552065 498077261822619096414049)
                      ·
                        rfl

theorem cell23_970002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_970002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_970002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_970002 prefixEnd_970002 := by exact prefixLift 970002
  have htrace : WordTrace (prefixWord ++ tailWord_970002) baseStart_970002 baseEnd_970002 := by
    simpa [prefixWord, tailWord_970002, baseEnd_970002] using wordTrace_append hprefix tailTrace_970002
  have hstable : (prefixWord ++ tailWord_970002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970002).length < 2 ^ (prefixWord ++ tailWord_970002).sum := by decide
  have hdescent : baseEnd_970002 < baseStart_970002 := by decide
  rcases family_descends (prefixWord ++ tailWord_970002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970007 : List Nat := [1, 1, 3, 4, 1, 1, 1, 1, 4, 4, 2]
def baseStart_970007 : Nat := 118140960795 + 970007 * 2 ^ 59
def prefixEnd_970007 : Nat := 4983230072969 + 3 ^ 40 * 970007 * 2
def baseEnd_970007 : Nat := 498079829225891576851525

theorem tailTrace_970007 : CollatzResearch.WordTrace tailWord_970007 prefixEnd_970007 498079829225891576851525 := by
  unfold tailWord_970007
  simp only [CollatzResearch.WordTrace]
  refine ⟨35379061796837777851524275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23586041197891851901016183 35379061796837777851524275)
  ·
    refine ⟨53068592695256666777286413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35379061796837777851524275 53068592695256666777286413)
    ·
      refine ⟨19900722260721250041482405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53068592695256666777286413 19900722260721250041482405)
      ·
        refine ⟨3731385423885234382777951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19900722260721250041482405 3731385423885234382777951)
        ·
          refine ⟨5597078135827851574166927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3731385423885234382777951 5597078135827851574166927)
          ·
            refine ⟨8395617203741777361250391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5597078135827851574166927 8395617203741777361250391)
            ·
              refine ⟨12593425805612666041875587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8395617203741777361250391 12593425805612666041875587)
              ·
                refine ⟨18890138708418999062813381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12593425805612666041875587 18890138708418999062813381)
                ·
                  refine ⟨3541901007828562324277509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18890138708418999062813381 3541901007828562324277509)
                  ·
                    refine ⟨664106438967855435802033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3541901007828562324277509 664106438967855435802033)
                    ·
                      refine ⟨498079829225891576851525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 664106438967855435802033 498079829225891576851525)
                      ·
                        rfl

theorem cell23_970007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 4, 4, 2].length) (baseStart_970007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_970007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_970007 prefixEnd_970007 := by exact prefixLift 970007
  have htrace : WordTrace (prefixWord ++ tailWord_970007) baseStart_970007 baseEnd_970007 := by
    simpa [prefixWord, tailWord_970007, baseEnd_970007] using wordTrace_append hprefix tailTrace_970007
  have hstable : (prefixWord ++ tailWord_970007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970007).length < 2 ^ (prefixWord ++ tailWord_970007).sum := by decide
  have hdescent : baseEnd_970007 < baseStart_970007 := by decide
  rcases family_descends (prefixWord ++ tailWord_970007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970020 : List Nat := [2, 3, 1, 3, 1, 1, 1, 2, 2, 1, 6]
def baseStart_970020 : Nat := 118140960795 + 970020 * 2 ^ 59
def prefixEnd_970020 : Nat := 4983230072969 + 3 ^ 40 * 970020 * 2
def baseEnd_970020 : Nat := 498086504474400025988965

theorem tailTrace_970020 : CollatzResearch.WordTrace tailWord_970020 prefixEnd_970020 498086504474400025988965 := by
  unfold tailWord_970020
  simp only [CollatzResearch.WordTrace]
  refine ⟨17689767972895340535873757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23586357297193787381165009 17689767972895340535873757)
  ·
    refine ⟨6633662989835752700952659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17689767972895340535873757 6633662989835752700952659)
    ·
      refine ⟨9950494484753629051428989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6633662989835752700952659 9950494484753629051428989)
      ·
        refine ⟨3731435431782610894285871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9950494484753629051428989 3731435431782610894285871)
        ·
          refine ⟨5597153147673916341428807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3731435431782610894285871 5597153147673916341428807)
          ·
            refine ⟨8395729721510874512143211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5597153147673916341428807 8395729721510874512143211)
            ·
              refine ⟨12593594582266311768214817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8395729721510874512143211 12593594582266311768214817)
              ·
                refine ⟨9445195936699733826161113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12593594582266311768214817 9445195936699733826161113)
                ·
                  refine ⟨7083896952524800369620835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9445195936699733826161113 7083896952524800369620835)
                  ·
                    refine ⟨10625845428787200554431253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7083896952524800369620835 10625845428787200554431253)
                    ·
                      refine ⟨498086504474400025988965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10625845428787200554431253 498086504474400025988965)
                      ·
                        rfl

theorem cell23_970020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_970020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_970020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_970020 prefixEnd_970020 := by exact prefixLift 970020
  have htrace : WordTrace (prefixWord ++ tailWord_970020) baseStart_970020 baseEnd_970020 := by
    simpa [prefixWord, tailWord_970020, baseEnd_970020] using wordTrace_append hprefix tailTrace_970020
  have hstable : (prefixWord ++ tailWord_970020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970020).length < 2 ^ (prefixWord ++ tailWord_970020).sum := by decide
  have hdescent : baseEnd_970020 < baseStart_970020 := by decide
  rcases family_descends (prefixWord ++ tailWord_970020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970024 : List Nat := [2, 1, 5, 1, 2, 1, 2, 1, 2, 4, 2]
def baseStart_970024 : Nat := 118140960795 + 970024 * 2 ^ 59
def prefixEnd_970024 : Nat := 4983230072969 + 3 ^ 40 * 970024 * 2
def baseEnd_970024 : Nat := 498088558397018010338947

theorem tailTrace_970024 : CollatzResearch.WordTrace tailWord_970024 prefixEnd_970024 498088558397018010338947 := by
  unfold tailWord_970024
  simp only [CollatzResearch.WordTrace]
  refine ⟨17689840918888094877446563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23586454558517459836595417 17689840918888094877446563)
  ·
    refine ⟨26534761378332142316169845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17689840918888094877446563 26534761378332142316169845)
    ·
      refine ⟨2487633879218638342140923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26534761378332142316169845 2487633879218638342140923)
      ·
        refine ⟨3731450818827957513211385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2487633879218638342140923 3731450818827957513211385)
        ·
          refine ⟨2798588114120968134908539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3731450818827957513211385 2798588114120968134908539)
          ·
            refine ⟨4197882171181452202362809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2798588114120968134908539 4197882171181452202362809)
            ·
              refine ⟨3148411628386089151772107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4197882171181452202362809 3148411628386089151772107)
              ·
                refine ⟨4722617442579133727658161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3148411628386089151772107 4722617442579133727658161)
                ·
                  refine ⟨3541963081934350295743621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4722617442579133727658161 3541963081934350295743621)
                  ·
                    refine ⟨664118077862690680451929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3541963081934350295743621 664118077862690680451929)
                    ·
                      refine ⟨498088558397018010338947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 664118077862690680451929 498088558397018010338947)
                      ·
                        rfl

theorem cell23_970024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 1, 2, 4, 2].length) (baseStart_970024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_970024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_970024 prefixEnd_970024 := by exact prefixLift 970024
  have htrace : WordTrace (prefixWord ++ tailWord_970024) baseStart_970024 baseEnd_970024 := by
    simpa [prefixWord, tailWord_970024, baseEnd_970024] using wordTrace_append hprefix tailTrace_970024
  have hstable : (prefixWord ++ tailWord_970024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970024).length < 2 ^ (prefixWord ++ tailWord_970024).sum := by decide
  have hdescent : baseEnd_970024 < baseStart_970024 := by decide
  rcases family_descends (prefixWord ++ tailWord_970024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970040 : List Nat := [2, 1, 2, 1, 3, 1, 1, 1, 1, 7, 3]
def baseStart_970040 : Nat := 118140960795 + 970040 * 2 ^ 59
def prefixEnd_970040 : Nat := 4983230072969 + 3 ^ 40 * 970040 * 2
def baseEnd_970040 : Nat := 498096774087489947738873

theorem tailTrace_970040 : CollatzResearch.WordTrace tailWord_970040 prefixEnd_970040 498096774087489947738873 := by
  unfold tailWord_970040
  simp only [CollatzResearch.WordTrace]
  refine ⟨17690132702859112243737787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23586843603812149658317049 17690132702859112243737787)
  ·
    refine ⟨26535199054288668365606681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17690132702859112243737787 26535199054288668365606681)
    ·
      refine ⟨19901399290716501274205011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26535199054288668365606681 19901399290716501274205011)
      ·
        refine ⟨29852098936074751911307517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19901399290716501274205011 29852098936074751911307517)
        ·
          refine ⟨11194537101028031966740319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29852098936074751911307517 11194537101028031966740319)
          ·
            refine ⟨16791805651542047950110479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11194537101028031966740319 16791805651542047950110479)
            ·
              refine ⟨25187708477313071925165719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16791805651542047950110479 25187708477313071925165719)
              ·
                refine ⟨37781562715969607887748579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25187708477313071925165719 37781562715969607887748579)
                ·
                  refine ⟨56672344073954411831622869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37781562715969607887748579 56672344073954411831622869)
                  ·
                    refine ⟨1328258064233306527303661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56672344073954411831622869 1328258064233306527303661)
                    ·
                      refine ⟨498096774087489947738873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1328258064233306527303661 498096774087489947738873)
                      ·
                        rfl

theorem cell23_970040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 1, 7, 3].length) (baseStart_970040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_970040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_970040 prefixEnd_970040 := by exact prefixLift 970040
  have htrace : WordTrace (prefixWord ++ tailWord_970040) baseStart_970040 baseEnd_970040 := by
    simpa [prefixWord, tailWord_970040, baseEnd_970040] using wordTrace_append hprefix tailTrace_970040
  have hstable : (prefixWord ++ tailWord_970040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970040).length < 2 ^ (prefixWord ++ tailWord_970040).sum := by decide
  have hdescent : baseEnd_970040 < baseStart_970040 := by decide
  rcases family_descends (prefixWord ++ tailWord_970040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970057 : List Nat := [1, 2, 1, 1, 2, 3, 2, 2, 5, 1, 3]
def baseStart_970057 : Nat := 118140960795 + 970057 * 2 ^ 59
def prefixEnd_970057 : Nat := 4983230072969 + 3 ^ 40 * 970057 * 2
def baseEnd_970057 : Nat := 498105503258616381226295

theorem tailTrace_970057 : CollatzResearch.WordTrace tailWord_970057 prefixEnd_970057 498105503258616381226295 := by
  unfold tailWord_970057
  simp only [CollatzResearch.WordTrace]
  refine ⟨35380885446656636390844425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23587256964437757593896283 35380885446656636390844425)
  ·
    refine ⟨26535664084992477293133319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35380885446656636390844425 26535664084992477293133319)
    ·
      refine ⟨39803496127488715939699979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26535664084992477293133319 39803496127488715939699979)
      ·
        refine ⟨59705244191233073909549969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39803496127488715939699979 59705244191233073909549969)
        ·
          refine ⟨44778933143424805432162477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59705244191233073909549969 44778933143424805432162477)
          ·
            refine ⟨16792099928784302037060929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44778933143424805432162477 16792099928784302037060929)
            ·
              refine ⟨12594074946588226527795697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16792099928784302037060929 12594074946588226527795697)
              ·
                refine ⟨9445556209941169895846773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12594074946588226527795697 9445556209941169895846773)
                ·
                  refine ⟨885520894681984677735635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9445556209941169895846773 885520894681984677735635)
                  ·
                    refine ⟨1328281342022977016603453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 885520894681984677735635 1328281342022977016603453)
                    ·
                      refine ⟨498105503258616381226295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1328281342022977016603453 498105503258616381226295)
                      ·
                        rfl

theorem cell23_970057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 2, 5, 1, 3].length) (baseStart_970057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_970057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_970057 prefixEnd_970057 := by exact prefixLift 970057
  have htrace : WordTrace (prefixWord ++ tailWord_970057) baseStart_970057 baseEnd_970057 := by
    simpa [prefixWord, tailWord_970057, baseEnd_970057] using wordTrace_append hprefix tailTrace_970057
  have hstable : (prefixWord ++ tailWord_970057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970057).length < 2 ^ (prefixWord ++ tailWord_970057).sum := by decide
  have hdescent : baseEnd_970057 < baseStart_970057 := by decide
  rcases family_descends (prefixWord ++ tailWord_970057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970074 : List Nat := [3, 1, 1, 2, 1, 2, 5, 1, 3, 1, 3]
def baseStart_970074 : Nat := 118140960795 + 970074 * 2 ^ 59
def prefixEnd_970074 : Nat := 4983230072969 + 3 ^ 40 * 970074 * 2
def baseEnd_970074 : Nat := 498114232429742814713717

theorem tailTrace_970074 : CollatzResearch.WordTrace tailWord_970074 prefixEnd_970074 498114232429742814713717 := by
  unfold tailWord_970074
  simp only [CollatzResearch.WordTrace]
  refine ⟨8845376371898762073553319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23587670325063365529475517 8845376371898762073553319)
  ·
    refine ⟨13268064557848143110329979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8845376371898762073553319 13268064557848143110329979)
    ·
      refine ⟨19902096836772214665494969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13268064557848143110329979 19902096836772214665494969)
      ·
        refine ⟨14926572627579160999121227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19902096836772214665494969 14926572627579160999121227)
        ·
          refine ⟨22389858941368741498681841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14926572627579160999121227 22389858941368741498681841)
          ·
            refine ⟨16792394206026556124011381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22389858941368741498681841 16792394206026556124011381)
            ·
              refine ⟨1574286956814989636626067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16792394206026556124011381 1574286956814989636626067)
              ·
                refine ⟨2361430435222484454939101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1574286956814989636626067 2361430435222484454939101)
                ·
                  refine ⟨885536413208431670602163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2361430435222484454939101 885536413208431670602163)
                  ·
                    refine ⟨1328304619812647505903245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 885536413208431670602163 1328304619812647505903245)
                    ·
                      refine ⟨498114232429742814713717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1328304619812647505903245 498114232429742814713717)
                      ·
                        rfl

theorem cell23_970074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5, 1, 3, 1, 3].length) (baseStart_970074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_970074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_970074 prefixEnd_970074 := by exact prefixLift 970074
  have htrace : WordTrace (prefixWord ++ tailWord_970074) baseStart_970074 baseEnd_970074 := by
    simpa [prefixWord, tailWord_970074, baseEnd_970074] using wordTrace_append hprefix tailTrace_970074
  have hstable : (prefixWord ++ tailWord_970074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970074).length < 2 ^ (prefixWord ++ tailWord_970074).sum := by decide
  have hdescent : baseEnd_970074 < baseStart_970074 := by decide
  rcases family_descends (prefixWord ++ tailWord_970074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970097 : List Nat := [1, 2, 2, 2, 1, 2, 2, 1, 2, 6, 2]
def baseStart_970097 : Nat := 118140960795 + 970097 * 2 ^ 59
def prefixEnd_970097 : Nat := 4983230072969 + 3 ^ 40 * 970097 * 2
def baseEnd_970097 : Nat := 498126042484796224726111

theorem tailTrace_970097 : CollatzResearch.WordTrace tailWord_970097 prefixEnd_970097 498126042484796224726111 := by
  unfold tailWord_970097
  simp only [CollatzResearch.WordTrace]
  refine ⟨35382344366511723222300545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23588229577674482148200363 35382344366511723222300545)
  ·
    refine ⟨26536758274883792416725409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35382344366511723222300545 26536758274883792416725409)
    ·
      refine ⟨19902568706162844312544057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26536758274883792416725409 19902568706162844312544057)
      ·
        refine ⟨14926926529622133234408043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19902568706162844312544057 14926926529622133234408043)
        ·
          refine ⟨22390389794433199851612065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14926926529622133234408043 22390389794433199851612065)
          ·
            refine ⟨16792792345824899888709049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22390389794433199851612065 16792792345824899888709049)
            ·
              refine ⟨12594594259368674916531787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16792792345824899888709049 12594594259368674916531787)
              ·
                refine ⟨18891891389053012374797681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12594594259368674916531787 18891891389053012374797681)
                ·
                  refine ⟨14168918541789759281098261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18891891389053012374797681 14168918541789759281098261)
                  ·
                    refine ⟨664168056646394966301481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14168918541789759281098261 664168056646394966301481)
                    ·
                      refine ⟨498126042484796224726111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 664168056646394966301481 498126042484796224726111)
                      ·
                        rfl

theorem cell23_970097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 6, 2].length) (baseStart_970097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_970097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_970097 prefixEnd_970097 := by exact prefixLift 970097
  have htrace : WordTrace (prefixWord ++ tailWord_970097) baseStart_970097 baseEnd_970097 := by
    simpa [prefixWord, tailWord_970097, baseEnd_970097] using wordTrace_append hprefix tailTrace_970097
  have hstable : (prefixWord ++ tailWord_970097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970097).length < 2 ^ (prefixWord ++ tailWord_970097).sum := by decide
  have hdescent : baseEnd_970097 < baseStart_970097 := by decide
  rcases family_descends (prefixWord ++ tailWord_970097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970117 : List Nat := [1, 3, 1, 1, 3, 1, 5, 1, 1, 1, 5]
def baseStart_970117 : Nat := 118140960795 + 970117 * 2 ^ 59
def prefixEnd_970117 : Nat := 4983230072969 + 3 ^ 40 * 970117 * 2
def baseEnd_970117 : Nat := 498136312097886146476019

theorem tailTrace_970117 : CollatzResearch.WordTrace tailWord_970117 prefixEnd_970117 498136312097886146476019 := by
  unfold tailWord_970117
  simp only [CollatzResearch.WordTrace]
  refine ⟨35383073826439266638028605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23588715884292844425352403 35383073826439266638028605)
  ·
    refine ⟨13268652684914724989260727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35383073826439266638028605 13268652684914724989260727)
    ·
      refine ⟨19902979027372087483891091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13268652684914724989260727 19902979027372087483891091)
      ·
        refine ⟨29854468541058131225836637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19902979027372087483891091 29854468541058131225836637)
        ·
          refine ⟨11195425702896799209688739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29854468541058131225836637 11195425702896799209688739)
          ·
            refine ⟨16793138554345198814533109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11195425702896799209688739 16793138554345198814533109)
            ·
              refine ⟨1574356739469862388862479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16793138554345198814533109 1574356739469862388862479)
              ·
                refine ⟨2361535109204793583293719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1574356739469862388862479 2361535109204793583293719)
                ·
                  refine ⟨3542302663807190374940579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2361535109204793583293719 3542302663807190374940579)
                  ·
                    refine ⟨5313453995710785562410869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3542302663807190374940579 5313453995710785562410869)
                    ·
                      refine ⟨498136312097886146476019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5313453995710785562410869 498136312097886146476019)
                      ·
                        rfl

theorem cell23_970117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5, 1, 1, 1, 5].length) (baseStart_970117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_970117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_970117 prefixEnd_970117 := by exact prefixLift 970117
  have htrace : WordTrace (prefixWord ++ tailWord_970117) baseStart_970117 baseEnd_970117 := by
    simpa [prefixWord, tailWord_970117, baseEnd_970117] using wordTrace_append hprefix tailTrace_970117
  have hstable : (prefixWord ++ tailWord_970117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970117).length < 2 ^ (prefixWord ++ tailWord_970117).sum := by decide
  have hdescent : baseEnd_970117 < baseStart_970117 := by decide
  rcases family_descends (prefixWord ++ tailWord_970117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970120 : List Nat := [2, 1, 3, 3, 1, 13]
def baseStart_970120 : Nat := 118140960795 + 970120 * 2 ^ 59
def prefixEnd_970120 : Nat := 4983230072969 + 3 ^ 40 * 970120 * 2
def baseEnd_970120 : Nat := 2049950010452056110035

theorem tailTrace_970120 : CollatzResearch.WordTrace tailWord_970120 prefixEnd_970120 2049950010452056110035 := by
  unfold tailWord_970120
  simp only [CollatzResearch.WordTrace]
  refine ⟨17691591622714199075193907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23588788830285598766925209 17691591622714199075193907)
  ·
    refine ⟨26537387434071298612790861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17691591622714199075193907 26537387434071298612790861)
    ·
      refine ⟨9951520287776736979796573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26537387434071298612790861 9951520287776736979796573)
      ·
        refine ⟨3731820107916276367423715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9951520287776736979796573 3731820107916276367423715)
        ·
          refine ⟨5597730161874414551135573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3731820107916276367423715 5597730161874414551135573)
          ·
            refine ⟨2049950010452056110035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 5597730161874414551135573 2049950010452056110035)
            ·
              rfl

theorem cell23_970120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 13].length) (baseStart_970120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_970120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_970120 prefixEnd_970120 := by exact prefixLift 970120
  have htrace : WordTrace (prefixWord ++ tailWord_970120) baseStart_970120 baseEnd_970120 := by
    simpa [prefixWord, tailWord_970120, baseEnd_970120] using wordTrace_append hprefix tailTrace_970120
  have hstable : (prefixWord ++ tailWord_970120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970120).length < 2 ^ (prefixWord ++ tailWord_970120).sum := by decide
  have hdescent : baseEnd_970120 < baseStart_970120 := by decide
  rcases family_descends (prefixWord ++ tailWord_970120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970124 : List Nat := [2, 2, 1, 2, 1, 3, 4, 2, 2, 4]
def baseStart_970124 : Nat := 118140960795 + 970124 * 2 ^ 59
def prefixEnd_970124 : Nat := 4983230072969 + 3 ^ 40 * 970124 * 2
def baseEnd_970124 : Nat := 166046635487489206362829

theorem tailTrace_970124 : CollatzResearch.WordTrace tailWord_970124 prefixEnd_970124 166046635487489206362829 := by
  unfold tailWord_970124
  simp only [CollatzResearch.WordTrace]
  refine ⟨17691664568706953416766713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23588886091609271222355617 17691664568706953416766713)
  ·
    refine ⟨13268748426530215062575035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17691664568706953416766713 13268748426530215062575035)
    ·
      refine ⟨19903122639795322593862553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13268748426530215062575035 19903122639795322593862553)
      ·
        refine ⟨14927341979846491945396915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19903122639795322593862553 14927341979846491945396915)
        ·
          refine ⟨22391012969769737918095373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14927341979846491945396915 22391012969769737918095373)
          ·
            refine ⟨8396629863663651719285765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22391012969769737918095373 8396629863663651719285765)
            ·
              refine ⟨1574368099436934697366081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8396629863663651719285765 1574368099436934697366081)
              ·
                refine ⟨1180776074577701023024561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1574368099436934697366081 1180776074577701023024561)
                ·
                  refine ⟨885582055933275767268421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1180776074577701023024561 885582055933275767268421)
                  ·
                    refine ⟨166046635487489206362829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 885582055933275767268421 166046635487489206362829)
                    ·
                      rfl

theorem cell23_970124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4, 2, 2, 4].length) (baseStart_970124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_970124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_970124 prefixEnd_970124 := by exact prefixLift 970124
  have htrace : WordTrace (prefixWord ++ tailWord_970124) baseStart_970124 baseEnd_970124 := by
    simpa [prefixWord, tailWord_970124, baseEnd_970124] using wordTrace_append hprefix tailTrace_970124
  have hstable : (prefixWord ++ tailWord_970124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970124).length < 2 ^ (prefixWord ++ tailWord_970124).sum := by decide
  have hdescent : baseEnd_970124 < baseStart_970124 := by decide
  rcases family_descends (prefixWord ++ tailWord_970124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970137 : List Nat := [1, 2, 1, 2, 1, 7, 1, 8]
def baseStart_970137 : Nat := 118140960795 + 970137 * 2 ^ 59
def prefixEnd_970137 : Nat := 4983230072969 + 3 ^ 40 * 970137 * 2
def baseEnd_970137 : Nat := 18449873396702817341701

theorem tailTrace_970137 : CollatzResearch.WordTrace tailWord_970137 prefixEnd_970137 18449873396702817341701 := by
  unfold tailWord_970137
  simp only [CollatzResearch.WordTrace]
  refine ⟨35383803286366810053756665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23589202190911206702504443 35383803286366810053756665)
  ·
    refine ⟨26537852464775107540317499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35383803286366810053756665 26537852464775107540317499)
    ·
      refine ⟨39806778697162661310476249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26537852464775107540317499 39806778697162661310476249)
      ·
        refine ⟨29855084022871995982857187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39806778697162661310476249 29855084022871995982857187)
        ·
          refine ⟨44782626034307993974285781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29855084022871995982857187 44782626034307993974285781)
          ·
            refine ⟨1049592797679093608772323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 44782626034307993974285781 1049592797679093608772323)
            ·
              refine ⟨1574389196518640413158485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1049592797679093608772323 1574389196518640413158485)
              ·
                refine ⟨18449873396702817341701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1574389196518640413158485 18449873396702817341701)
                ·
                  rfl

theorem cell23_970137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 1, 8].length) (baseStart_970137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_970137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_970137 prefixEnd_970137 := by exact prefixLift 970137
  have htrace : WordTrace (prefixWord ++ tailWord_970137) baseStart_970137 baseEnd_970137 := by
    simpa [prefixWord, tailWord_970137, baseEnd_970137] using wordTrace_append hprefix tailTrace_970137
  have hstable : (prefixWord ++ tailWord_970137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970137).length < 2 ^ (prefixWord ++ tailWord_970137).sum := by decide
  have hdescent : baseEnd_970137 < baseStart_970137 := by decide
  rcases family_descends (prefixWord ++ tailWord_970137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
