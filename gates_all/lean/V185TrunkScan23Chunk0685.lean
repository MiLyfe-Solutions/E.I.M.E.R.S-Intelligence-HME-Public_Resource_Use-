import V185TrunkScan23Chunk0684

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4050845 : List Nat := [1, 4, 2, 1, 2, 3, 1, 1, 3, 2, 3]
def baseStart_4050845 : Nat := 118140960795 + 4050845 * 2 ^ 59
def prefixEnd_4050845 : Nat := 4983230072969 + 3 ^ 40 * 4050845 * 2
def baseEnd_4050845 : Nat := 2080030541862308784008009

theorem tailTrace_4050845 : CollatzResearch.WordTrace tailWord_4050845 prefixEnd_4050845 2080030541862308784008009 := by
  unfold tailWord_4050845
  simp only [CollatzResearch.WordTrace]
  refine ⟨147746455009487869091769989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98497636672991912727846659 147746455009487869091769989)
  ·
    refine ⟨27702460314278975454706873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147746455009487869091769989 27702460314278975454706873)
    ·
      refine ⟨20776845235709231591030155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27702460314278975454706873 20776845235709231591030155)
      ·
        refine ⟨31165267853563847386545233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20776845235709231591030155 31165267853563847386545233)
        ·
          refine ⟨23373950890172885539908925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31165267853563847386545233 23373950890172885539908925)
          ·
            refine ⟨8765231583814832077465847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23373950890172885539908925 8765231583814832077465847)
            ·
              refine ⟨13147847375722248116198771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8765231583814832077465847 13147847375722248116198771)
              ·
                refine ⟨19721771063583372174298157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13147847375722248116198771 19721771063583372174298157)
                ·
                  refine ⟨7395664148843764565361809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19721771063583372174298157 7395664148843764565361809)
                  ·
                    refine ⟨5546748111632823424021357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7395664148843764565361809 5546748111632823424021357)
                    ·
                      refine ⟨2080030541862308784008009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5546748111632823424021357 2080030541862308784008009)
                      ·
                        rfl

theorem cell23_4050845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 1, 3, 2, 3].length) (baseStart_4050845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4050845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4050845 prefixEnd_4050845 := by exact prefixLift 4050845
  have htrace : WordTrace (prefixWord ++ tailWord_4050845) baseStart_4050845 baseEnd_4050845 := by
    simpa [prefixWord, tailWord_4050845, baseEnd_4050845] using wordTrace_append hprefix tailTrace_4050845
  have hstable : (prefixWord ++ tailWord_4050845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4050845).length < 2 ^ (prefixWord ++ tailWord_4050845).sum := by decide
  have hdescent : baseEnd_4050845 < baseStart_4050845 := by decide
  rcases family_descends (prefixWord ++ tailWord_4050845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4050846 : List Nat := [4, 3, 1, 3, 1, 1, 2, 1, 2, 3, 2]
def baseStart_4050846 : Nat := 118140960795 + 4050846 * 2 ^ 59
def prefixEnd_4050846 : Nat := 4983230072969 + 3 ^ 40 * 4050846 * 2
def baseEnd_4050846 : Nat := 2080031055342963280095505

theorem tailTrace_4050846 : CollatzResearch.WordTrace tailWord_4050846 prefixEnd_4050846 2080031055342963280095505 := by
  unfold tailWord_4050846
  simp only [CollatzResearch.WordTrace]
  refine ⟨18468311435310530782819549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98497660988322830841704261 18468311435310530782819549)
  ·
    refine ⟨6925616788241449043557331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18468311435310530782819549 6925616788241449043557331)
    ·
      refine ⟨10388425182362173565335997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6925616788241449043557331 10388425182362173565335997)
      ·
        refine ⟨3895659443385815087000999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10388425182362173565335997 3895659443385815087000999)
        ·
          refine ⟨5843489165078722630501499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3895659443385815087000999 5843489165078722630501499)
          ·
            refine ⟨8765233747618083945752249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5843489165078722630501499 8765233747618083945752249)
            ·
              refine ⟨6573925310713562959314187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8765233747618083945752249 6573925310713562959314187)
              ·
                refine ⟨9860887966070344438971281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6573925310713562959314187 9860887966070344438971281)
                ·
                  refine ⟨7395665974552758329228461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9860887966070344438971281 7395665974552758329228461)
                  ·
                    refine ⟨2773374740457284373460673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7395665974552758329228461 2773374740457284373460673)
                    ·
                      refine ⟨2080031055342963280095505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2773374740457284373460673 2080031055342963280095505)
                      ·
                        rfl

theorem cell23_4050846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_4050846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4050846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4050846 prefixEnd_4050846 := by exact prefixLift 4050846
  have htrace : WordTrace (prefixWord ++ tailWord_4050846) baseStart_4050846 baseEnd_4050846 := by
    simpa [prefixWord, tailWord_4050846, baseEnd_4050846] using wordTrace_append hprefix tailTrace_4050846
  have hstable : (prefixWord ++ tailWord_4050846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4050846).length < 2 ^ (prefixWord ++ tailWord_4050846).sum := by decide
  have hdescent : baseEnd_4050846 < baseStart_4050846 := by decide
  rcases family_descends (prefixWord ++ tailWord_4050846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4050855 : List Nat := [1, 1, 6, 1, 2, 2, 1, 2, 1, 2, 4]
def baseStart_4050855 : Nat := 118140960795 + 4050855 * 2 ^ 59
def prefixEnd_4050855 : Nat := 4983230072969 + 3 ^ 40 * 4050855 * 2
def baseEnd_4050855 : Nat := 2080035676668853744882963

theorem tailTrace_4050855 : CollatzResearch.WordTrace tailWord_4050855 prefixEnd_4050855 2080035676668853744882963 := by
  unfold tailWord_4050855
  simp only [CollatzResearch.WordTrace]
  refine ⟨147746819739451640799634019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98497879826301093866422679 147746819739451640799634019)
  ·
    refine ⟨221620229609177461199451029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147746819739451640799634019 221620229609177461199451029)
    ·
      refine ⟨10388448262930193493724267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 221620229609177461199451029 10388448262930193493724267)
      ·
        refine ⟨15582672394395290240586401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10388448262930193493724267 15582672394395290240586401)
        ·
          refine ⟨11687004295796467680439801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15582672394395290240586401 11687004295796467680439801)
          ·
            refine ⟨8765253221847350760329851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11687004295796467680439801 8765253221847350760329851)
            ·
              refine ⟨13147879832771026140494777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8765253221847350760329851 13147879832771026140494777)
              ·
                refine ⟨9860909874578269605371083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13147879832771026140494777 9860909874578269605371083)
                ·
                  refine ⟨14791364811867404408056625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9860909874578269605371083 14791364811867404408056625)
                  ·
                    refine ⟨11093523608900553306042469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14791364811867404408056625 11093523608900553306042469)
                    ·
                      refine ⟨2080035676668853744882963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11093523608900553306042469 2080035676668853744882963)
                      ·
                        rfl

theorem cell23_4050855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_4050855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4050855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4050855 prefixEnd_4050855 := by exact prefixLift 4050855
  have htrace : WordTrace (prefixWord ++ tailWord_4050855) baseStart_4050855 baseEnd_4050855 := by
    simpa [prefixWord, tailWord_4050855, baseEnd_4050855] using wordTrace_append hprefix tailTrace_4050855
  have hstable : (prefixWord ++ tailWord_4050855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4050855).length < 2 ^ (prefixWord ++ tailWord_4050855).sum := by decide
  have hdescent : baseEnd_4050855 < baseStart_4050855 := by decide
  rcases family_descends (prefixWord ++ tailWord_4050855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4050875 : List Nat := [1, 1, 1, 1, 1, 2, 2, 8, 2, 1, 3]
def baseStart_4050875 : Nat := 118140960795 + 4050875 * 2 ^ 59
def prefixEnd_4050875 : Nat := 4983230072969 + 3 ^ 40 * 4050875 * 2
def baseEnd_4050875 : Nat := 2080045946281943666632871

theorem tailTrace_4050875 : CollatzResearch.WordTrace tailWord_4050875 prefixEnd_4050875 2080045946281943666632871 := by
  unfold tailWord_4050875
  simp only [CollatzResearch.WordTrace]
  refine ⟨147747549199379184215362079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98498366132919456143574719 147747549199379184215362079)
  ·
    refine ⟨221621323799068776323043119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147747549199379184215362079 221621323799068776323043119)
    ·
      refine ⟨332431985698603164484564679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221621323799068776323043119 332431985698603164484564679)
      ·
        refine ⟨498647978547904746726847019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332431985698603164484564679 498647978547904746726847019)
        ·
          refine ⟨747971967821857120090270529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 498647978547904746726847019 747971967821857120090270529)
          ·
            refine ⟨560978975866392840067702897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 747971967821857120090270529 560978975866392840067702897)
            ·
              refine ⟨420734231899794630050777173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 560978975866392840067702897 420734231899794630050777173)
              ·
                refine ⟨4930479280075718320907545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 420734231899794630050777173 4930479280075718320907545)
                ·
                  refine ⟨3697859460056788740680659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4930479280075718320907545 3697859460056788740680659)
                  ·
                    refine ⟨5546789190085183111020989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3697859460056788740680659 5546789190085183111020989)
                    ·
                      refine ⟨2080045946281943666632871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5546789190085183111020989 2080045946281943666632871)
                      ·
                        rfl

theorem cell23_4050875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 8, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 8, 2, 1, 3].length) (baseStart_4050875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4050875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4050875 prefixEnd_4050875 := by exact prefixLift 4050875
  have htrace : WordTrace (prefixWord ++ tailWord_4050875) baseStart_4050875 baseEnd_4050875 := by
    simpa [prefixWord, tailWord_4050875, baseEnd_4050875] using wordTrace_append hprefix tailTrace_4050875
  have hstable : (prefixWord ++ tailWord_4050875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4050875).length < 2 ^ (prefixWord ++ tailWord_4050875).sum := by decide
  have hdescent : baseEnd_4050875 < baseStart_4050875 := by decide
  rcases family_descends (prefixWord ++ tailWord_4050875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4050878 : List Nat := [4, 2, 1, 1, 1, 3, 1, 1, 2, 7]
def baseStart_4050878 : Nat := 118140960795 + 4050878 * 2 ^ 59
def prefixEnd_4050878 : Nat := 4983230072969 + 3 ^ 40 * 4050878 * 2
def baseEnd_4050878 : Nat := 693349162241302384965119

theorem tailTrace_4050878 : CollatzResearch.WordTrace tailWord_4050878 prefixEnd_4050878 693349162241302384965119 := by
  unfold tailWord_4050878
  simp only [CollatzResearch.WordTrace]
  refine ⟨18468457327296039465965161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98498439078912210485147525 18468457327296039465965161)
  ·
    refine ⟨13851342995472029599473871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18468457327296039465965161 13851342995472029599473871)
    ·
      refine ⟨20777014493208044399210807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13851342995472029599473871 20777014493208044399210807)
      ·
        refine ⟨31165521739812066598816211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20777014493208044399210807 31165521739812066598816211)
        ·
          refine ⟨46748282609718099898224317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31165521739812066598816211 46748282609718099898224317)
          ·
            refine ⟨17530605978644287461834119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46748282609718099898224317 17530605978644287461834119)
            ·
              refine ⟨26295908967966431192751179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17530605978644287461834119 26295908967966431192751179)
              ·
                refine ⟨39443863451949646789126769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26295908967966431192751179 39443863451949646789126769)
                ·
                  refine ⟨29582897588962235091845077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39443863451949646789126769 29582897588962235091845077)
                  ·
                    refine ⟨693349162241302384965119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29582897588962235091845077 693349162241302384965119)
                    ·
                      rfl

theorem cell23_4050878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 1, 2, 7].length) (baseStart_4050878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4050878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4050878 prefixEnd_4050878 := by exact prefixLift 4050878
  have htrace : WordTrace (prefixWord ++ tailWord_4050878) baseStart_4050878 baseEnd_4050878 := by
    simpa [prefixWord, tailWord_4050878, baseEnd_4050878] using wordTrace_append hprefix tailTrace_4050878
  have hstable : (prefixWord ++ tailWord_4050878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4050878).length < 2 ^ (prefixWord ++ tailWord_4050878).sum := by decide
  have hdescent : baseEnd_4050878 < baseStart_4050878 := by decide
  rcases family_descends (prefixWord ++ tailWord_4050878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4050892 : List Nat := [2, 2, 1, 4, 1, 2, 2, 3, 2, 1, 3]
def baseStart_4050892 : Nat := 118140960795 + 4050892 * 2 ^ 59
def prefixEnd_4050892 : Nat := 4983230072969 + 3 ^ 40 * 4050892 * 2
def baseEnd_4050892 : Nat := 2080054675453070100120293

theorem tailTrace_4050892 : CollatzResearch.WordTrace tailWord_4050892 prefixEnd_4050892 2080054675453070100120293 := by
  unfold tailWord_4050892
  simp only [CollatzResearch.WordTrace]
  refine ⟨73874084620158798059365465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98498779493545064079153953 73874084620158798059365465)
  ·
    refine ⟨55405563465119098544524099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73874084620158798059365465 55405563465119098544524099)
    ·
      refine ⟨83108345197678647816786149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55405563465119098544524099 83108345197678647816786149)
      ·
        refine ⟨15582814724564746465647403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83108345197678647816786149 15582814724564746465647403)
        ·
          refine ⟨23374222086847119698471105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15582814724564746465647403 23374222086847119698471105)
          ·
            refine ⟨17530666565135339773853329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23374222086847119698471105 17530666565135339773853329)
            ·
              refine ⟨13147999923851504830389997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17530666565135339773853329 13147999923851504830389997)
              ·
                refine ⟨4930499971444314311396249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13147999923851504830389997 4930499971444314311396249)
                ·
                  refine ⟨3697874978583235733547187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4930499971444314311396249 3697874978583235733547187)
                  ·
                    refine ⟨5546812467874853600320781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3697874978583235733547187 5546812467874853600320781)
                    ·
                      refine ⟨2080054675453070100120293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5546812467874853600320781 2080054675453070100120293)
                      ·
                        rfl

theorem cell23_4050892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 3, 2, 1, 3].length) (baseStart_4050892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4050892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4050892 prefixEnd_4050892 := by exact prefixLift 4050892
  have htrace : WordTrace (prefixWord ++ tailWord_4050892) baseStart_4050892 baseEnd_4050892 := by
    simpa [prefixWord, tailWord_4050892, baseEnd_4050892] using wordTrace_append hprefix tailTrace_4050892
  have hstable : (prefixWord ++ tailWord_4050892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4050892).length < 2 ^ (prefixWord ++ tailWord_4050892).sum := by decide
  have hdescent : baseEnd_4050892 < baseStart_4050892 := by decide
  rcases family_descends (prefixWord ++ tailWord_4050892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4050919 : List Nat := [1, 1, 5, 2, 3, 1, 1, 3, 1, 3, 2]
def baseStart_4050919 : Nat := 118140960795 + 4050919 * 2 ^ 59
def prefixEnd_4050919 : Nat := 4983230072969 + 3 ^ 40 * 4050919 * 2
def baseEnd_4050919 : Nat := 2080068539430741494482669

theorem tailTrace_4050919 : CollatzResearch.WordTrace tailWord_4050919 prefixEnd_4050919 2080068539430741494482669 := by
  unfold tailWord_4050919
  simp only [CollatzResearch.WordTrace]
  refine ⟨147749154011219779729963811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98499436007479853153309207 147749154011219779729963811)
  ·
    refine ⟨221623731016829669594945717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147749154011219779729963811 221623731016829669594945717)
    ·
      refine ⟨20777224782827781524526161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 221623731016829669594945717 20777224782827781524526161)
      ·
        refine ⟨15582918587120836143394621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20777224782827781524526161 15582918587120836143394621)
        ·
          refine ⟨5843594470170313553772983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15582918587120836143394621 5843594470170313553772983)
          ·
            refine ⟨8765391705255470330659475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5843594470170313553772983 8765391705255470330659475)
            ·
              refine ⟨13148087557883205495989213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8765391705255470330659475 13148087557883205495989213)
              ·
                refine ⟨4930532834206202060995955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13148087557883205495989213 4930532834206202060995955)
                ·
                  refine ⟨7395799251309303091493933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4930532834206202060995955 7395799251309303091493933)
                  ·
                    refine ⟨2773424719240988659310225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7395799251309303091493933 2773424719240988659310225)
                    ·
                      refine ⟨2080068539430741494482669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2773424719240988659310225 2080068539430741494482669)
                      ·
                        rfl

theorem cell23_4050919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 3, 1, 3, 2].length) (baseStart_4050919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4050919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4050919 prefixEnd_4050919 := by exact prefixLift 4050919
  have htrace : WordTrace (prefixWord ++ tailWord_4050919) baseStart_4050919 baseEnd_4050919 := by
    simpa [prefixWord, tailWord_4050919, baseEnd_4050919] using wordTrace_append hprefix tailTrace_4050919
  have hstable : (prefixWord ++ tailWord_4050919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4050919).length < 2 ^ (prefixWord ++ tailWord_4050919).sum := by decide
  have hdescent : baseEnd_4050919 < baseStart_4050919 := by decide
  rcases family_descends (prefixWord ++ tailWord_4050919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4050928 : List Nat := [2, 1, 1, 1, 3, 2, 3, 2, 2, 2, 4]
def baseStart_4050928 : Nat := 118140960795 + 4050928 * 2 ^ 59
def prefixEnd_4050928 : Nat := 4983230072969 + 3 ^ 40 * 4050928 * 2
def baseEnd_4050928 : Nat := 2080073160756631959270127

theorem tailTrace_4050928 : CollatzResearch.WordTrace tailWord_4050928 prefixEnd_4050928 2080073160756631959270127 := by
  unfold tailWord_4050928
  simp only [CollatzResearch.WordTrace]
  refine ⟨73874741134093587133520719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98499654845458116178027625 73874741134093587133520719)
  ·
    refine ⟨110812111701140380700281079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73874741134093587133520719 110812111701140380700281079)
    ·
      refine ⟨166218167551710571050421619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110812111701140380700281079 166218167551710571050421619)
      ·
        refine ⟨249327251327565856575632429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166218167551710571050421619 249327251327565856575632429)
        ·
          refine ⟨93497719247837196215862161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 249327251327565856575632429 93497719247837196215862161)
          ·
            refine ⟨70123289435877897161896621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93497719247837196215862161 70123289435877897161896621)
            ·
              refine ⟨26296233538454211435711233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70123289435877897161896621 26296233538454211435711233)
              ·
                refine ⟨19722175153840658576783425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26296233538454211435711233 19722175153840658576783425)
                ·
                  refine ⟨14791631365380493932587569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19722175153840658576783425 14791631365380493932587569)
                  ·
                    refine ⟨11093723524035370449440677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14791631365380493932587569 11093723524035370449440677)
                    ·
                      refine ⟨2080073160756631959270127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11093723524035370449440677 2080073160756631959270127)
                      ·
                        rfl

theorem cell23_4050928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2, 4].length) (baseStart_4050928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4050928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4050928 prefixEnd_4050928 := by exact prefixLift 4050928
  have htrace : WordTrace (prefixWord ++ tailWord_4050928) baseStart_4050928 baseEnd_4050928 := by
    simpa [prefixWord, tailWord_4050928, baseEnd_4050928] using wordTrace_append hprefix tailTrace_4050928
  have hstable : (prefixWord ++ tailWord_4050928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4050928).length < 2 ^ (prefixWord ++ tailWord_4050928).sum := by decide
  have hdescent : baseEnd_4050928 < baseStart_4050928 := by decide
  rcases family_descends (prefixWord ++ tailWord_4050928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4050968 : List Nat := [2, 1, 2, 3, 2, 1, 1, 3, 1, 7]
def baseStart_4050968 : Nat := 118140960795 + 4050968 * 2 ^ 59
def prefixEnd_4050968 : Nat := 4983230072969 + 3 ^ 40 * 4050968 * 2
def baseEnd_4050968 : Nat := 693364566660937267589981

theorem tailTrace_4050968 : CollatzResearch.WordTrace tailWord_4050968 prefixEnd_4050968 693364566660937267589981 := by
  unfold tailWord_4050968
  simp only [CollatzResearch.WordTrace]
  refine ⟨73875470594021130549248779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98500627458694840732331705 73875470594021130549248779)
  ·
    refine ⟨110813205891031695823873169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73875470594021130549248779 110813205891031695823873169)
    ·
      refine ⟨83109904418273771867904877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110813205891031695823873169 83109904418273771867904877)
      ·
        refine ⟨31166214156852664450464329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83109904418273771867904877 31166214156852664450464329)
        ·
          refine ⟨23374660617639498337848247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31166214156852664450464329 23374660617639498337848247)
          ·
            refine ⟨35061990926459247506772371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23374660617639498337848247 35061990926459247506772371)
            ·
              refine ⟨52592986389688871260158557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35061990926459247506772371 52592986389688871260158557)
              ·
                refine ⟨19722369896133326722559459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52592986389688871260158557 19722369896133326722559459)
                ·
                  refine ⟨29583554844199990083839189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19722369896133326722559459 29583554844199990083839189)
                  ·
                    refine ⟨693364566660937267589981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29583554844199990083839189 693364566660937267589981)
                    ·
                      rfl

theorem cell23_4050968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 3, 1, 7].length) (baseStart_4050968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4050968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4050968 prefixEnd_4050968 := by exact prefixLift 4050968
  have htrace : WordTrace (prefixWord ++ tailWord_4050968) baseStart_4050968 baseEnd_4050968 := by
    simpa [prefixWord, tailWord_4050968, baseEnd_4050968] using wordTrace_append hprefix tailTrace_4050968
  have hstable : (prefixWord ++ tailWord_4050968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4050968).length < 2 ^ (prefixWord ++ tailWord_4050968).sum := by decide
  have hdescent : baseEnd_4050968 < baseStart_4050968 := by decide
  rcases family_descends (prefixWord ++ tailWord_4050968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4050972 : List Nat := [2, 2, 3, 1, 3, 1, 3, 3, 5]
def baseStart_4050972 : Nat := 118140960795 + 4050972 * 2 ^ 59
def prefixEnd_4050972 : Nat := 4983230072969 + 3 ^ 40 * 4050972 * 2
def baseEnd_4050972 : Nat := 231121750433936643013325

theorem tailTrace_4050972 : CollatzResearch.WordTrace tailWord_4050972 prefixEnd_4050972 231121750433936643013325 := by
  unfold tailWord_4050972
  simp only [CollatzResearch.WordTrace]
  refine ⟨73875543540013884890821585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98500724720018513187762113 73875543540013884890821585)
  ·
    refine ⟨55406657655010413668116189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73875543540013884890821585 55406657655010413668116189)
    ·
      refine ⟨20777496620628905125543571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55406657655010413668116189 20777496620628905125543571)
      ·
        refine ⟨31166244930943357688315357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20777496620628905125543571 31166244930943357688315357)
        ·
          refine ⟨11687341849103759133118259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31166244930943357688315357 11687341849103759133118259)
          ·
            refine ⟨17531012773655638699677389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11687341849103759133118259 17531012773655638699677389)
            ·
              refine ⟨6574129790120864512379021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17531012773655638699677389 6574129790120864512379021)
              ·
                refine ⟨2465298671295324192142133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6574129790120864512379021 2465298671295324192142133)
                ·
                  refine ⟨231121750433936643013325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2465298671295324192142133 231121750433936643013325)
                  ·
                    rfl

theorem cell23_4050972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3, 3, 5].length) (baseStart_4050972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4050972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4050972 prefixEnd_4050972 := by exact prefixLift 4050972
  have htrace : WordTrace (prefixWord ++ tailWord_4050972) baseStart_4050972 baseEnd_4050972 := by
    simpa [prefixWord, tailWord_4050972, baseEnd_4050972] using wordTrace_append hprefix tailTrace_4050972
  have hstable : (prefixWord ++ tailWord_4050972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4050972).length < 2 ^ (prefixWord ++ tailWord_4050972).sum := by decide
  have hdescent : baseEnd_4050972 < baseStart_4050972 := by decide
  rcases family_descends (prefixWord ++ tailWord_4050972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4050988 : List Nat := [2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 4]
def baseStart_4050988 : Nat := 118140960795 + 4050988 * 2 ^ 59
def prefixEnd_4050988 : Nat := 4983230072969 + 3 ^ 40 * 4050988 * 2
def baseEnd_4050988 : Nat := 2080103969595901724519851

theorem tailTrace_4050988 : CollatzResearch.WordTrace tailWord_4050988 prefixEnd_4050988 2080103969595901724519851 := by
  unfold tailWord_4050988
  simp only [CollatzResearch.WordTrace]
  refine ⟨73875835323984902257112809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98501113765313203009483745 73875835323984902257112809)
  ·
    refine ⟨55406876492988676692834607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73875835323984902257112809 55406876492988676692834607)
    ·
      refine ⟨83110314739483015039251911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55406876492988676692834607 83110314739483015039251911)
      ·
        refine ⟨124665472109224522558877867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83110314739483015039251911 124665472109224522558877867)
        ·
          refine ⟨186998208163836783838316801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124665472109224522558877867 186998208163836783838316801)
          ·
            refine ⟨140248656122877587878737601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186998208163836783838316801 140248656122877587878737601)
            ·
              refine ⟨105186492092158190909053201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140248656122877587878737601 105186492092158190909053201)
              ·
                refine ⟨78889869069118643181789901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105186492092158190909053201 78889869069118643181789901)
                ·
                  refine ⟨29583700900919491193171213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78889869069118643181789901 29583700900919491193171213)
                  ·
                    refine ⟨11093887837844809197439205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29583700900919491193171213 11093887837844809197439205)
                    ·
                      refine ⟨2080103969595901724519851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11093887837844809197439205 2080103969595901724519851)
                      ·
                        rfl

theorem cell23_4050988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 4].length) (baseStart_4050988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4050988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4050988 prefixEnd_4050988 := by exact prefixLift 4050988
  have htrace : WordTrace (prefixWord ++ tailWord_4050988) baseStart_4050988 baseEnd_4050988 := by
    simpa [prefixWord, tailWord_4050988, baseEnd_4050988] using wordTrace_append hprefix tailTrace_4050988
  have hstable : (prefixWord ++ tailWord_4050988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4050988).length < 2 ^ (prefixWord ++ tailWord_4050988).sum := by decide
  have hdescent : baseEnd_4050988 < baseStart_4050988 := by decide
  rcases family_descends (prefixWord ++ tailWord_4050988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4051005 : List Nat := [1, 4, 1, 3, 1, 1, 1, 2, 4, 1, 4]
def baseStart_4051005 : Nat := 118140960795 + 4051005 * 2 ^ 59
def prefixEnd_4051005 : Nat := 4983230072969 + 3 ^ 40 * 4051005 * 2
def baseEnd_4051005 : Nat := 2080112698767028158007273

theorem tailTrace_4051005 : CollatzResearch.WordTrace tailWord_4051005 prefixEnd_4051005 2080112698767028158007273 := by
  unfold tailWord_4051005
  simp only [CollatzResearch.WordTrace]
  refine ⟨147752290688908216417594469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98501527125938810945062979 147752290688908216417594469)
  ·
    refine ⟨27703554504170290578298963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147752290688908216417594469 27703554504170290578298963)
    ·
      refine ⟨41555331756255435867448445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27703554504170290578298963 41555331756255435867448445)
      ·
        refine ⟨15583249408595788450293167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41555331756255435867448445 15583249408595788450293167)
        ·
          refine ⟨23374874112893682675439751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15583249408595788450293167 23374874112893682675439751)
          ·
            refine ⟨35062311169340524013159627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23374874112893682675439751 35062311169340524013159627)
            ·
              refine ⟨52593466754010786019739441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35062311169340524013159627 52593466754010786019739441)
              ·
                refine ⟨39445100065508089514804581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52593466754010786019739441 39445100065508089514804581)
                ·
                  refine ⟨7395956262282766784025859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39445100065508089514804581 7395956262282766784025859)
                  ·
                    refine ⟨11093934393424150176038789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7395956262282766784025859 11093934393424150176038789)
                    ·
                      refine ⟨2080112698767028158007273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11093934393424150176038789 2080112698767028158007273)
                      ·
                        rfl

theorem cell23_4051005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_4051005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4051005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4051005 prefixEnd_4051005 := by exact prefixLift 4051005
  have htrace : WordTrace (prefixWord ++ tailWord_4051005) baseStart_4051005 baseEnd_4051005 := by
    simpa [prefixWord, tailWord_4051005, baseEnd_4051005] using wordTrace_append hprefix tailTrace_4051005
  have hstable : (prefixWord ++ tailWord_4051005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4051005).length < 2 ^ (prefixWord ++ tailWord_4051005).sum := by decide
  have hdescent : baseEnd_4051005 < baseStart_4051005 := by decide
  rcases family_descends (prefixWord ++ tailWord_4051005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4051015 : List Nat := [1, 1, 4, 1, 3, 1, 2, 1, 5, 4]
def baseStart_4051015 : Nat := 118140960795 + 4051015 * 2 ^ 59
def prefixEnd_4051015 : Nat := 4983230072969 + 3 ^ 40 * 4051015 * 2
def baseEnd_4051015 : Nat := 693372611191191039627409

theorem tailTrace_4051015 : CollatzResearch.WordTrace tailWord_4051015 prefixEnd_4051015 693372611191191039627409 := by
  unfold tailWord_4051015
  simp only [CollatzResearch.WordTrace]
  refine ⟨147752655418871988125458499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98501770279247992083638999 147752655418871988125458499)
  ·
    refine ⟨221628983128307982188187749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147752655418871988125458499 221628983128307982188187749)
    ·
      refine ⟨41555434336557746660285203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 221628983128307982188187749 41555434336557746660285203)
      ·
        refine ⟨62333151504836619990427805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41555434336557746660285203 62333151504836619990427805)
        ·
          refine ⟨23374931814313732496410427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62333151504836619990427805 23374931814313732496410427)
          ·
            refine ⟨35062397721470598744615641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23374931814313732496410427 35062397721470598744615641)
            ·
              refine ⟨26296798291102949058461731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35062397721470598744615641 26296798291102949058461731)
              ·
                refine ⟨39445197436654423587692597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26296798291102949058461731 39445197436654423587692597)
                ·
                  refine ⟨3697987259686352211346181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39445197436654423587692597 3697987259686352211346181)
                  ·
                    refine ⟨693372611191191039627409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3697987259686352211346181 693372611191191039627409)
                    ·
                      rfl

theorem cell23_4051015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 1, 5, 4].length) (baseStart_4051015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4051015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4051015 prefixEnd_4051015 := by exact prefixLift 4051015
  have htrace : WordTrace (prefixWord ++ tailWord_4051015) baseStart_4051015 baseEnd_4051015 := by
    simpa [prefixWord, tailWord_4051015, baseEnd_4051015] using wordTrace_append hprefix tailTrace_4051015
  have hstable : (prefixWord ++ tailWord_4051015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4051015).length < 2 ^ (prefixWord ++ tailWord_4051015).sum := by decide
  have hdescent : baseEnd_4051015 < baseStart_4051015 := by decide
  rcases family_descends (prefixWord ++ tailWord_4051015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4051018 : List Nat := [3, 1, 2, 1, 1, 2, 1, 2, 1, 3, 6]
def baseStart_4051018 : Nat := 118140960795 + 4051018 * 2 ^ 59
def prefixEnd_4051018 : Nat := 4983230072969 + 3 ^ 40 * 4051018 * 2
def baseEnd_4051018 : Nat := 2080119374015536607144713

theorem tailTrace_4051018 : CollatzResearch.WordTrace tailWord_4051018 prefixEnd_4051018 2080119374015536607144713 := by
  unfold tailWord_4051018
  simp only [CollatzResearch.WordTrace]
  refine ⟨36938191209465279909454427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98501843225240746425211805 36938191209465279909454427)
  ·
    refine ⟨55407286814197919864181641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36938191209465279909454427 55407286814197919864181641)
    ·
      refine ⟨41555465110648439898136231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55407286814197919864181641 41555465110648439898136231)
      ·
        refine ⟨62333197665972659847204347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41555465110648439898136231 62333197665972659847204347)
        ·
          refine ⟨93499796498958989770806521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62333197665972659847204347 93499796498958989770806521)
          ·
            refine ⟨70124847374219242328104891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93499796498958989770806521 70124847374219242328104891)
            ·
              refine ⟨105187271061328863492157337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70124847374219242328104891 105187271061328863492157337)
              ·
                refine ⟨78890453295996647619118003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105187271061328863492157337 78890453295996647619118003)
                ·
                  refine ⟨118335679943994971428677005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78890453295996647619118003 118335679943994971428677005)
                  ·
                    refine ⟨44375879978998114285753877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 118335679943994971428677005 44375879978998114285753877)
                    ·
                      refine ⟨2080119374015536607144713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44375879978998114285753877 2080119374015536607144713)
                      ·
                        rfl

theorem cell23_4051018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 1, 3, 6].length) (baseStart_4051018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4051018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4051018 prefixEnd_4051018 := by exact prefixLift 4051018
  have htrace : WordTrace (prefixWord ++ tailWord_4051018) baseStart_4051018 baseEnd_4051018 := by
    simpa [prefixWord, tailWord_4051018, baseEnd_4051018] using wordTrace_append hprefix tailTrace_4051018
  have hstable : (prefixWord ++ tailWord_4051018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4051018).length < 2 ^ (prefixWord ++ tailWord_4051018).sum := by decide
  have hdescent : baseEnd_4051018 < baseStart_4051018 := by decide
  rcases family_descends (prefixWord ++ tailWord_4051018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4051022 : List Nat := [4, 1, 1, 1, 1, 5, 2, 1, 2, 1, 4]
def baseStart_4051022 : Nat := 118140960795 + 4051022 * 2 ^ 59
def prefixEnd_4051022 : Nat := 4983230072969 + 3 ^ 40 * 4051022 * 2
def baseEnd_4051022 : Nat := 2080121427938154591494695

theorem tailTrace_4051022 : CollatzResearch.WordTrace tailWord_4051022 prefixEnd_4051022 2080121427938154591494695 := by
  unfold tailWord_4051022
  simp only [CollatzResearch.WordTrace]
  refine ⟨18469113841230828540120415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98501940486564418880642213 18469113841230828540120415)
  ·
    refine ⟨27703670761846242810180623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18469113841230828540120415 27703670761846242810180623)
    ·
      refine ⟨41555506142769364215270935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27703670761846242810180623 41555506142769364215270935)
      ·
        refine ⟨62333259214154046322906403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41555506142769364215270935 62333259214154046322906403)
        ·
          refine ⟨93499888821231069484359605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62333259214154046322906403 93499888821231069484359605)
          ·
            refine ⟨8765614576990412764158713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 93499888821231069484359605 8765614576990412764158713)
            ·
              refine ⟨6574210932742809573119035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8765614576990412764158713 6574210932742809573119035)
              ·
                refine ⟨9861316399114214359678553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6574210932742809573119035 9861316399114214359678553)
                ·
                  refine ⟨7395987299335660769758915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9861316399114214359678553 7395987299335660769758915)
                  ·
                    refine ⟨11093980949003491154638373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7395987299335660769758915 11093980949003491154638373)
                    ·
                      refine ⟨2080121427938154591494695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11093980949003491154638373 2080121427938154591494695)
                      ·
                        rfl

theorem cell23_4051022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2, 1, 2, 1, 4].length) (baseStart_4051022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4051022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4051022 prefixEnd_4051022 := by exact prefixLift 4051022
  have htrace : WordTrace (prefixWord ++ tailWord_4051022) baseStart_4051022 baseEnd_4051022 := by
    simpa [prefixWord, tailWord_4051022, baseEnd_4051022] using wordTrace_append hprefix tailTrace_4051022
  have hstable : (prefixWord ++ tailWord_4051022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4051022).length < 2 ^ (prefixWord ++ tailWord_4051022).sum := by decide
  have hdescent : baseEnd_4051022 < baseStart_4051022 := by decide
  rcases family_descends (prefixWord ++ tailWord_4051022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4051045 : List Nat := [1, 3, 1, 3, 2, 2, 1, 4, 6]
def baseStart_4051045 : Nat := 118140960795 + 4051045 * 2 ^ 59
def prefixEnd_4051045 : Nat := 4983230072969 + 3 ^ 40 * 4051045 * 2
def baseEnd_4051045 : Nat := 231125915332578666834121

theorem tailTrace_4051045 : CollatzResearch.WordTrace tailWord_4051045 prefixEnd_4051045 231125915332578666834121 := by
  unfold tailWord_4051045
  simp only [CollatzResearch.WordTrace]
  refine ⟨147753749608763303249050589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98502499739175535499367059 147753749608763303249050589)
  ·
    refine ⟨55407656103286238718393971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147753749608763303249050589 55407656103286238718393971)
    ·
      refine ⟨83111484154929358077590957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55407656103286238718393971 83111484154929358077590957)
      ·
        refine ⟨31166806558098509279096609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83111484154929358077590957 31166806558098509279096609)
        ·
          refine ⟨23375104918573881959322457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31166806558098509279096609 23375104918573881959322457)
          ·
            refine ⟨17531328688930411469491843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23375104918573881959322457 17531328688930411469491843)
            ·
              refine ⟨26296993033395617204237765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17531328688930411469491843 26296993033395617204237765)
              ·
                refine ⟨4930686193761678225794581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26296993033395617204237765 4930686193761678225794581)
                ·
                  refine ⟨231125915332578666834121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4930686193761678225794581 231125915332578666834121)
                  ·
                    rfl

theorem cell23_4051045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 4, 6].length) (baseStart_4051045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4051045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4051045 prefixEnd_4051045 := by exact prefixLift 4051045
  have htrace : WordTrace (prefixWord ++ tailWord_4051045) baseStart_4051045 baseEnd_4051045 := by
    simpa [prefixWord, tailWord_4051045, baseEnd_4051045] using wordTrace_append hprefix tailTrace_4051045
  have hstable : (prefixWord ++ tailWord_4051045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4051045).length < 2 ^ (prefixWord ++ tailWord_4051045).sum := by decide
  have hdescent : baseEnd_4051045 < baseStart_4051045 := by decide
  rcases family_descends (prefixWord ++ tailWord_4051045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4051062 : List Nat := [5, 1, 1, 2, 1, 2, 2, 3, 6]
def baseStart_4051062 : Nat := 118140960795 + 4051062 * 2 ^ 59
def prefixEnd_4051062 : Nat := 4983230072969 + 3 ^ 40 * 4051062 * 2
def baseEnd_4051062 : Nat := 231126885240481603888279

theorem tailTrace_4051062 : CollatzResearch.WordTrace tailWord_4051062 prefixEnd_4051062 231126885240481603888279 := by
  unfold tailWord_4051062
  simp only [CollatzResearch.WordTrace]
  refine ⟨9234648103106357197026215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 98502913099801143434946293 9234648103106357197026215)
  ·
    refine ⟨13851972154659535795539323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9234648103106357197026215 13851972154659535795539323)
    ·
      refine ⟨20777958231989303693308985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13851972154659535795539323 20777958231989303693308985)
      ·
        refine ⟨15583468673991977769981739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20777958231989303693308985 15583468673991977769981739)
        ·
          refine ⟨23375203010987966654972609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15583468673991977769981739 23375203010987966654972609)
          ·
            refine ⟨17531402258240974991229457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23375203010987966654972609 17531402258240974991229457)
            ·
              refine ⟨13148551693680731243422093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17531402258240974991229457 13148551693680731243422093)
              ·
                refine ⟨4930706885130274216283285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13148551693680731243422093 4930706885130274216283285)
                ·
                  refine ⟨231126885240481603888279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4930706885130274216283285 231126885240481603888279)
                  ·
                    rfl

theorem cell23_4051062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 3, 6].length) (baseStart_4051062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4051062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4051062 prefixEnd_4051062 := by exact prefixLift 4051062
  have htrace : WordTrace (prefixWord ++ tailWord_4051062) baseStart_4051062 baseEnd_4051062 := by
    simpa [prefixWord, tailWord_4051062, baseEnd_4051062] using wordTrace_append hprefix tailTrace_4051062
  have hstable : (prefixWord ++ tailWord_4051062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4051062).length < 2 ^ (prefixWord ++ tailWord_4051062).sum := by decide
  have hdescent : baseEnd_4051062 < baseStart_4051062 := by decide
  rcases family_descends (prefixWord ++ tailWord_4051062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4051075 : List Nat := [1, 1, 1, 3, 3, 3, 2, 1, 3, 5]
def baseStart_4051075 : Nat := 118140960795 + 4051075 * 2 ^ 59
def prefixEnd_4051075 : Nat := 4983230072969 + 3 ^ 40 * 4051075 * 2
def baseEnd_4051075 : Nat := 693382880804280961377317

theorem tailTrace_4051075 : CollatzResearch.WordTrace tailWord_4051075 prefixEnd_4051075 693382880804280961377317 := by
  unfold tailWord_4051075
  simp only [CollatzResearch.WordTrace]
  refine ⟨147754843798654618372642679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98503229199103078915095119 147754843798654618372642679)
  ·
    refine ⟨221632265697981927558964019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147754843798654618372642679 221632265697981927558964019)
    ·
      refine ⟨332448398546972891338446029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221632265697981927558964019 332448398546972891338446029)
      ·
        refine ⟨124668149455114834251917261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 332448398546972891338446029 124668149455114834251917261)
        ·
          refine ⟨46750556045668062844468973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124668149455114834251917261 46750556045668062844468973)
          ·
            refine ⟨17531458517125523566675865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46750556045668062844468973 17531458517125523566675865)
            ·
              refine ⟨13148593887844142675006899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17531458517125523566675865 13148593887844142675006899)
              ·
                refine ⟨19722890831766214012510349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13148593887844142675006899 19722890831766214012510349)
                ·
                  refine ⟨7396084061912330254691381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19722890831766214012510349 7396084061912330254691381)
                  ·
                    refine ⟨693382880804280961377317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7396084061912330254691381 693382880804280961377317)
                    ·
                      rfl

theorem cell23_4051075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 1, 3, 5].length) (baseStart_4051075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4051075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4051075 prefixEnd_4051075 := by exact prefixLift 4051075
  have htrace : WordTrace (prefixWord ++ tailWord_4051075) baseStart_4051075 baseEnd_4051075 := by
    simpa [prefixWord, tailWord_4051075, baseEnd_4051075] using wordTrace_append hprefix tailTrace_4051075
  have hstable : (prefixWord ++ tailWord_4051075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4051075).length < 2 ^ (prefixWord ++ tailWord_4051075).sum := by decide
  have hdescent : baseEnd_4051075 < baseStart_4051075 := by decide
  rcases family_descends (prefixWord ++ tailWord_4051075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4051106 : List Nat := [3, 3, 1, 3, 1, 2, 2, 1, 3, 1, 3]
def baseStart_4051106 : Nat := 118140960795 + 4051106 * 2 ^ 59
def prefixEnd_4051106 : Nat := 4983230072969 + 3 ^ 40 * 4051106 * 2
def baseEnd_4051106 : Nat := 2080164560313132262844309

theorem tailTrace_4051106 : CollatzResearch.WordTrace tailWord_4051106 prefixEnd_4051106 2080164560313132262844309 := by
  unfold tailWord_4051106
  simp only [CollatzResearch.WordTrace]
  refine ⟨36938993615385577666755293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98503982974361540444680781 36938993615385577666755293)
  ·
    refine ⟨13852122605769591625033235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36938993615385577666755293 13852122605769591625033235)
    ·
      refine ⟨20778183908654387437549853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13852122605769591625033235 20778183908654387437549853)
      ·
        refine ⟨7791818965745395289081195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20778183908654387437549853 7791818965745395289081195)
        ·
          refine ⟨11687728448618092933621793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7791818965745395289081195 11687728448618092933621793)
          ·
            refine ⟨8765796336463569700216345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11687728448618092933621793 8765796336463569700216345)
            ·
              refine ⟨6574347252347677275162259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8765796336463569700216345 6574347252347677275162259)
              ·
                refine ⟨9861520878521515912743389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6574347252347677275162259 9861520878521515912743389)
                ·
                  refine ⟨3698070329445568467278771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9861520878521515912743389 3698070329445568467278771)
                  ·
                    refine ⟨5547105494168352700918157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3698070329445568467278771 5547105494168352700918157)
                    ·
                      refine ⟨2080164560313132262844309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5547105494168352700918157 2080164560313132262844309)
                      ·
                        rfl

theorem cell23_4051106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_4051106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4051106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4051106 prefixEnd_4051106 := by exact prefixLift 4051106
  have htrace : WordTrace (prefixWord ++ tailWord_4051106) baseStart_4051106 baseEnd_4051106 := by
    simpa [prefixWord, tailWord_4051106, baseEnd_4051106] using wordTrace_append hprefix tailTrace_4051106
  have hstable : (prefixWord ++ tailWord_4051106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4051106).length < 2 ^ (prefixWord ++ tailWord_4051106).sum := by decide
  have hdescent : baseEnd_4051106 < baseStart_4051106 := by decide
  rcases family_descends (prefixWord ++ tailWord_4051106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4051129 : List Nat := [1, 2, 1, 4, 1, 2, 1, 4, 3, 2, 2]
def baseStart_4051129 : Nat := 118140960795 + 4051129 * 2 ^ 59
def prefixEnd_4051129 : Nat := 4983230072969 + 3 ^ 40 * 4051129 * 2
def baseEnd_4051129 : Nat := 2080176370368185672856703

theorem tailTrace_4051129 : CollatzResearch.WordTrace tailWord_4051129 prefixEnd_4051129 2080176370368185672856703 := by
  unfold tailWord_4051129
  simp only [CollatzResearch.WordTrace]
  refine ⟨147756813340458985595108441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98504542226972657063405627 147756813340458985595108441)
  ·
    refine ⟨110817610005344239196331331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147756813340458985595108441 110817610005344239196331331)
    ·
      refine ⟨166226415008016358794496997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110817610005344239196331331 166226415008016358794496997)
      ·
        refine ⟨31167452814003067273968187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 166226415008016358794496997 31167452814003067273968187)
        ·
          refine ⟨46751179221004600910952281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31167452814003067273968187 46751179221004600910952281)
          ·
            refine ⟨35063384415753450683214211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46751179221004600910952281 35063384415753450683214211)
            ·
              refine ⟨52595076623630176024821317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35063384415753450683214211 52595076623630176024821317)
              ·
                refine ⟨9861576866930658004653997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52595076623630176024821317 9861576866930658004653997)
                ·
                  refine ⟨3698091325098996751745249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9861576866930658004653997 3698091325098996751745249)
                  ·
                    refine ⟨2773568493824247563808937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3698091325098996751745249 2773568493824247563808937)
                    ·
                      refine ⟨2080176370368185672856703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2773568493824247563808937 2080176370368185672856703)
                      ·
                        rfl

theorem cell23_4051129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 4, 3, 2, 2].length) (baseStart_4051129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4051129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4051129 prefixEnd_4051129 := by exact prefixLift 4051129
  have htrace : WordTrace (prefixWord ++ tailWord_4051129) baseStart_4051129 baseEnd_4051129 := by
    simpa [prefixWord, tailWord_4051129, baseEnd_4051129] using wordTrace_append hprefix tailTrace_4051129
  have hstable : (prefixWord ++ tailWord_4051129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4051129).length < 2 ^ (prefixWord ++ tailWord_4051129).sum := by decide
  have hdescent : baseEnd_4051129 < baseStart_4051129 := by decide
  rcases family_descends (prefixWord ++ tailWord_4051129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4051172 : List Nat := [2, 3, 1, 1, 1, 2, 1, 1, 2, 7, 2]
def baseStart_4051172 : Nat := 118140960795 + 4051172 * 2 ^ 59
def prefixEnd_4051172 : Nat := 4983230072969 + 3 ^ 40 * 4051172 * 2
def baseEnd_4051172 : Nat := 2080198450036329004619005

theorem tailTrace_4051172 : CollatzResearch.WordTrace tailWord_4051172 prefixEnd_4051172 2080198450036329004619005 := by
  unfold tailWord_4051172
  simp only [CollatzResearch.WordTrace]
  refine ⟨73879190839651601969461885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98505587786202135959282513 73879190839651601969461885)
  ·
    refine ⟨27704696564869350738548207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73879190839651601969461885 27704696564869350738548207)
    ·
      refine ⟨41557044847304026107822311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27704696564869350738548207 41557044847304026107822311)
      ·
        refine ⟨62335567270956039161733467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41557044847304026107822311 62335567270956039161733467)
        ·
          refine ⟨93503350906434058742600201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62335567270956039161733467 93503350906434058742600201)
          ·
            refine ⟨70127513179825544056950151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93503350906434058742600201 70127513179825544056950151)
            ·
              refine ⟨105191269769738316085425227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70127513179825544056950151 105191269769738316085425227)
              ·
                refine ⟨157786904654607474128137841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105191269769738316085425227 157786904654607474128137841)
                ·
                  refine ⟨118340178490955605596103381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 157786904654607474128137841 118340178490955605596103381)
                  ·
                    refine ⟨2773597933381772006158673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 118340178490955605596103381 2773597933381772006158673)
                    ·
                      refine ⟨2080198450036329004619005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2773597933381772006158673 2080198450036329004619005)
                      ·
                        rfl

theorem cell23_4051172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 2, 7, 2].length) (baseStart_4051172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4051172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4051172 prefixEnd_4051172 := by exact prefixLift 4051172
  have htrace : WordTrace (prefixWord ++ tailWord_4051172) baseStart_4051172 baseEnd_4051172 := by
    simpa [prefixWord, tailWord_4051172, baseEnd_4051172] using wordTrace_append hprefix tailTrace_4051172
  have hstable : (prefixWord ++ tailWord_4051172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4051172).length < 2 ^ (prefixWord ++ tailWord_4051172).sum := by decide
  have hdescent : baseEnd_4051172 < baseStart_4051172 := by decide
  rcases family_descends (prefixWord ++ tailWord_4051172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4051179 : List Nat := [1, 1, 1, 1, 2, 5, 3, 3, 2, 1, 3]
def baseStart_4051179 : Nat := 118140960795 + 4051179 * 2 ^ 59
def prefixEnd_4051179 : Nat := 4983230072969 + 3 ^ 40 * 4051179 * 2
def baseEnd_4051179 : Nat := 2080202044400910477231473

theorem tailTrace_4051179 : CollatzResearch.WordTrace tailWord_4051179 prefixEnd_4051179 2080202044400910477231473 := by
  unfold tailWord_4051179
  simp only [CollatzResearch.WordTrace]
  refine ⟨147758636990277844134428591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98505757993518562756285727 147758636990277844134428591)
  ·
    refine ⟨221637955485416766201642887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147758636990277844134428591 221637955485416766201642887)
    ·
      refine ⟨332456933228125149302464331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221637955485416766201642887 332456933228125149302464331)
      ·
        refine ⟨498685399842187723953696497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332456933228125149302464331 498685399842187723953696497)
        ·
          refine ⟨374014049881640792965272373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 498685399842187723953696497 374014049881640792965272373)
          ·
            refine ⟨35063817176403824340494285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 374014049881640792965272373 35063817176403824340494285)
            ·
              refine ⟨13148931441151434127685357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35063817176403824340494285 13148931441151434127685357)
              ·
                refine ⟨4930849290431787797882009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13148931441151434127685357 4930849290431787797882009)
                ·
                  refine ⟨3698136967823840848411507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4930849290431787797882009 3698136967823840848411507)
                  ·
                    refine ⟨5547205451735761272617261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3698136967823840848411507 5547205451735761272617261)
                    ·
                      refine ⟨2080202044400910477231473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5547205451735761272617261 2080202044400910477231473)
                      ·
                        rfl

theorem cell23_4051179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 3, 2, 1, 3].length) (baseStart_4051179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4051179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4051179 prefixEnd_4051179 := by exact prefixLift 4051179
  have htrace : WordTrace (prefixWord ++ tailWord_4051179) baseStart_4051179 baseEnd_4051179 := by
    simpa [prefixWord, tailWord_4051179, baseEnd_4051179] using wordTrace_append hprefix tailTrace_4051179
  have hstable : (prefixWord ++ tailWord_4051179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4051179).length < 2 ^ (prefixWord ++ tailWord_4051179).sum := by decide
  have hdescent : baseEnd_4051179 < baseStart_4051179 := by decide
  rcases family_descends (prefixWord ++ tailWord_4051179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4051205 : List Nat := [1, 3, 1, 1, 2, 1, 2, 3, 1, 3, 5]
def baseStart_4051205 : Nat := 118140960795 + 4051205 * 2 ^ 59
def prefixEnd_4051205 : Nat := 4983230072969 + 3 ^ 40 * 4051205 * 2
def baseEnd_4051205 : Nat := 2080215394897927375506353

theorem tailTrace_4051205 : CollatzResearch.WordTrace tailWord_4051205 prefixEnd_4051205 2080215394897927375506353 := by
  unfold tailWord_4051205
  simp only [CollatzResearch.WordTrace]
  refine ⟨147759585288183650574875069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98506390192122433716583379 147759585288183650574875069)
  ·
    refine ⟨55409844483068868965578151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147759585288183650574875069 55409844483068868965578151)
    ·
      refine ⟨83114766724603303448367227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55409844483068868965578151 83114766724603303448367227)
      ·
        refine ⟨124672150086904955172550841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83114766724603303448367227 124672150086904955172550841)
        ·
          refine ⟨93504112565178716379413131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124672150086904955172550841 93504112565178716379413131)
          ·
            refine ⟨140256168847768074569119697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93504112565178716379413131 140256168847768074569119697)
            ·
              refine ⟨105192126635826055926839773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140256168847768074569119697 105192126635826055926839773)
              ·
                refine ⟨39447047488434770972564915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105192126635826055926839773 39447047488434770972564915)
                ·
                  refine ⟨59170571232652156458847373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39447047488434770972564915 59170571232652156458847373)
                  ·
                    refine ⟨22188964212244558672067765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59170571232652156458847373 22188964212244558672067765)
                    ·
                      refine ⟨2080215394897927375506353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22188964212244558672067765 2080215394897927375506353)
                      ·
                        rfl

theorem cell23_4051205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 3, 1, 3, 5].length) (baseStart_4051205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4051205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4051205 prefixEnd_4051205 := by exact prefixLift 4051205
  have htrace : WordTrace (prefixWord ++ tailWord_4051205) baseStart_4051205 baseEnd_4051205 := by
    simpa [prefixWord, tailWord_4051205, baseEnd_4051205] using wordTrace_append hprefix tailTrace_4051205
  have hstable : (prefixWord ++ tailWord_4051205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4051205).length < 2 ^ (prefixWord ++ tailWord_4051205).sum := by decide
  have hdescent : baseEnd_4051205 < baseStart_4051205 := by decide
  rcases family_descends (prefixWord ++ tailWord_4051205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4051215 : List Nat := [1, 1, 2, 1, 1, 1, 3, 2, 3, 4, 4]
def baseStart_4051215 : Nat := 118140960795 + 4051215 * 2 ^ 59
def prefixEnd_4051215 : Nat := 4983230072969 + 3 ^ 40 * 4051215 * 2
def baseEnd_4051215 : Nat := 2080220529704472336381307

theorem tailTrace_4051215 : CollatzResearch.WordTrace tailWord_4051215 prefixEnd_4051215 2080220529704472336381307 := by
  unfold tailWord_4051215
  simp only [CollatzResearch.WordTrace]
  refine ⟨147759950018147422282739099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98506633345431614855159399 147759950018147422282739099)
  ·
    refine ⟨221639925027221133424108649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147759950018147422282739099 221639925027221133424108649)
    ·
      refine ⟨166229943770415850068081487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221639925027221133424108649 166229943770415850068081487)
      ·
        refine ⟨249344915655623775102122231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166229943770415850068081487 249344915655623775102122231)
        ·
          refine ⟨374017373483435662653183347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249344915655623775102122231 374017373483435662653183347)
          ·
            refine ⟨561026060225153493979775021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 374017373483435662653183347 561026060225153493979775021)
            ·
              refine ⟨210384772584432560242415633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 561026060225153493979775021 210384772584432560242415633)
              ·
                refine ⟨157788579438324420181811725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 210384772584432560242415633 157788579438324420181811725)
                ·
                  refine ⟨59170717289371657568179397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 157788579438324420181811725 59170717289371657568179397)
                  ·
                    refine ⟨11094509491757185794033637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59170717289371657568179397 11094509491757185794033637)
                    ·
                      refine ⟨2080220529704472336381307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11094509491757185794033637 2080220529704472336381307)
                      ·
                        rfl

theorem cell23_4051215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 3, 4, 4].length) (baseStart_4051215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4051215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4051215 prefixEnd_4051215 := by exact prefixLift 4051215
  have htrace : WordTrace (prefixWord ++ tailWord_4051215) baseStart_4051215 baseEnd_4051215 := by
    simpa [prefixWord, tailWord_4051215, baseEnd_4051215] using wordTrace_append hprefix tailTrace_4051215
  have hstable : (prefixWord ++ tailWord_4051215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4051215).length < 2 ^ (prefixWord ++ tailWord_4051215).sum := by decide
  have hdescent : baseEnd_4051215 < baseStart_4051215 := by decide
  rcases family_descends (prefixWord ++ tailWord_4051215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4051219 : List Nat := [1, 1, 1, 2, 1, 3, 1, 5, 4, 2, 2]
def baseStart_4051219 : Nat := 118140960795 + 4051219 * 2 ^ 59
def prefixEnd_4051219 : Nat := 4983230072969 + 3 ^ 40 * 4051219 * 2
def baseEnd_4051219 : Nat := 2080222583627090320731289

theorem tailTrace_4051219 : CollatzResearch.WordTrace tailWord_4051219 prefixEnd_4051219 2080222583627090320731289 := by
  unfold tailWord_4051219
  simp only [CollatzResearch.WordTrace]
  refine ⟨147760095910132930965884711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98506730606755287310589807 147760095910132930965884711)
  ·
    refine ⟨221640143865199396448827067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147760095910132930965884711 221640143865199396448827067)
    ·
      refine ⟨332460215797799094673240601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221640143865199396448827067 332460215797799094673240601)
      ·
        refine ⟨249345161848349321004930451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 332460215797799094673240601 249345161848349321004930451)
        ·
          refine ⟨374017742772523981507395677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249345161848349321004930451 374017742772523981507395677)
          ·
            refine ⟨140256653539696493065273379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 374017742772523981507395677 140256653539696493065273379)
            ·
              refine ⟨210384980309544739597910069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140256653539696493065273379 210384980309544739597910069)
              ·
                refine ⟨19723591904019819337304069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 210384980309544739597910069 19723591904019819337304069)
                ·
                  refine ⟨3698173482003716125744513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19723591904019819337304069 3698173482003716125744513)
                  ·
                    refine ⟨2773630111502787094308385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3698173482003716125744513 2773630111502787094308385)
                    ·
                      refine ⟨2080222583627090320731289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2773630111502787094308385 2080222583627090320731289)
                      ·
                        rfl

theorem cell23_4051219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 5, 4, 2, 2].length) (baseStart_4051219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4051219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4051219 prefixEnd_4051219 := by exact prefixLift 4051219
  have htrace : WordTrace (prefixWord ++ tailWord_4051219) baseStart_4051219 baseEnd_4051219 := by
    simpa [prefixWord, tailWord_4051219, baseEnd_4051219] using wordTrace_append hprefix tailTrace_4051219
  have hstable : (prefixWord ++ tailWord_4051219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4051219).length < 2 ^ (prefixWord ++ tailWord_4051219).sum := by decide
  have hdescent : baseEnd_4051219 < baseStart_4051219 := by decide
  rcases family_descends (prefixWord ++ tailWord_4051219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4051229 : List Nat := [1, 4, 2, 3, 2, 1, 1, 1, 2, 6]
def baseStart_4051229 : Nat := 118140960795 + 4051229 * 2 ^ 59
def prefixEnd_4051229 : Nat := 4983230072969 + 3 ^ 40 * 4051229 * 2
def baseEnd_4051229 : Nat := 693409239477878427202081

theorem tailTrace_4051229 : CollatzResearch.WordTrace tailWord_4051229 prefixEnd_4051229 693409239477878427202081 := by
  unfold tailWord_4051229
  simp only [CollatzResearch.WordTrace]
  refine ⟨147760460640096702673748741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98506973760064468449165827 147760460640096702673748741)
  ·
    refine ⟨27705086370018131751327889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147760460640096702673748741 27705086370018131751327889)
    ·
      refine ⟨20778814777513598813495917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27705086370018131751327889 20778814777513598813495917)
      ·
        refine ⟨7792055541567599555060969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20778814777513598813495917 7792055541567599555060969)
        ·
          refine ⟨5844041656175699666295727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7792055541567599555060969 5844041656175699666295727)
          ·
            refine ⟨8766062484263549499443591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5844041656175699666295727 8766062484263549499443591)
            ·
              refine ⟨13149093726395324249165387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8766062484263549499443591 13149093726395324249165387)
              ·
                refine ⟨19723640589592986373748081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13149093726395324249165387 19723640589592986373748081)
                ·
                  refine ⟨14792730442194739780311061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19723640589592986373748081 14792730442194739780311061)
                  ·
                    refine ⟨693409239477878427202081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14792730442194739780311061 693409239477878427202081)
                    ·
                      rfl

theorem cell23_4051229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 1, 2, 6].length) (baseStart_4051229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4051229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4051229 prefixEnd_4051229 := by exact prefixLift 4051229
  have htrace : WordTrace (prefixWord ++ tailWord_4051229) baseStart_4051229 baseEnd_4051229 := by
    simpa [prefixWord, tailWord_4051229, baseEnd_4051229] using wordTrace_append hprefix tailTrace_4051229
  have hstable : (prefixWord ++ tailWord_4051229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4051229).length < 2 ^ (prefixWord ++ tailWord_4051229).sum := by decide
  have hdescent : baseEnd_4051229 < baseStart_4051229 := by decide
  rcases family_descends (prefixWord ++ tailWord_4051229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4051232 : List Nat := [2, 1, 1, 5, 2, 1, 1, 1, 1, 4, 4]
def baseStart_4051232 : Nat := 118140960795 + 4051232 * 2 ^ 59
def prefixEnd_4051232 : Nat := 4983230072969 + 3 ^ 40 * 4051232 * 2
def baseEnd_4051232 : Nat := 2080229258875598769868729

theorem tailTrace_4051232 : CollatzResearch.WordTrace tailWord_4051232 prefixEnd_4051232 2080229258875598769868729 := by
  unfold tailWord_4051232
  simp only [CollatzResearch.WordTrace]
  refine ⟨73880285029542917093053975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98507046706057222790738633 73880285029542917093053975)
  ·
    refine ⟨110820427544314375639580963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73880285029542917093053975 110820427544314375639580963)
    ·
      refine ⟨166230641316471563459371445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110820427544314375639580963 166230641316471563459371445)
      ·
        refine ⟨15584122623419209074316073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 166230641316471563459371445 15584122623419209074316073)
        ·
          refine ⟨11688091967564406805737055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15584122623419209074316073 11688091967564406805737055)
          ·
            refine ⟨17532137951346610208605583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11688091967564406805737055 17532137951346610208605583)
            ·
              refine ⟨26298206927019915312908375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17532137951346610208605583 26298206927019915312908375)
              ·
                refine ⟨39447310390529872969362563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26298206927019915312908375 39447310390529872969362563)
                ·
                  refine ⟨59170965585794809454043845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39447310390529872969362563 59170965585794809454043845)
                  ·
                    refine ⟨11094556047336526772633221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59170965585794809454043845 11094556047336526772633221)
                    ·
                      refine ⟨2080229258875598769868729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11094556047336526772633221 2080229258875598769868729)
                      ·
                        rfl

theorem cell23_4051232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_4051232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4051232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4051232 prefixEnd_4051232 := by exact prefixLift 4051232
  have htrace : WordTrace (prefixWord ++ tailWord_4051232) baseStart_4051232 baseEnd_4051232 := by
    simpa [prefixWord, tailWord_4051232, baseEnd_4051232] using wordTrace_append hprefix tailTrace_4051232
  have hstable : (prefixWord ++ tailWord_4051232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4051232).length < 2 ^ (prefixWord ++ tailWord_4051232).sum := by decide
  have hdescent : baseEnd_4051232 < baseStart_4051232 := by decide
  rcases family_descends (prefixWord ++ tailWord_4051232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4051236 : List Nat := [2, 3, 1, 3, 1, 3, 2, 1, 1, 4, 2]
def baseStart_4051236 : Nat := 118140960795 + 4051236 * 2 ^ 59
def prefixEnd_4051236 : Nat := 4983230072969 + 3 ^ 40 * 4051236 * 2
def baseEnd_4051236 : Nat := 2080231312798216754218711

theorem tailTrace_4051236 : CollatzResearch.WordTrace tailWord_4051236 prefixEnd_4051236 2080231312798216754218711 := by
  unfold tailWord_4051236
  simp only [CollatzResearch.WordTrace]
  refine ⟨73880357975535671434626781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98507143967380895246169041 73880357975535671434626781)
  ·
    refine ⟨27705134240825876787985043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73880357975535671434626781 27705134240825876787985043)
    ·
      refine ⟨41557701361238815181977565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27705134240825876787985043 41557701361238815181977565)
      ·
        refine ⟨15584138010464555693241587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41557701361238815181977565 15584138010464555693241587)
        ·
          refine ⟨23376207015696833539862381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15584138010464555693241587 23376207015696833539862381)
          ·
            refine ⟨8766077630886312577448393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23376207015696833539862381 8766077630886312577448393)
            ·
              refine ⟨6574558223164734433086295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8766077630886312577448393 6574558223164734433086295)
              ·
                refine ⟨9861837334747101649629443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6574558223164734433086295 9861837334747101649629443)
                ·
                  refine ⟨14792756002120652474444165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9861837334747101649629443 14792756002120652474444165)
                  ·
                    refine ⟨2773641750397622338958281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14792756002120652474444165 2773641750397622338958281)
                    ·
                      refine ⟨2080231312798216754218711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2773641750397622338958281 2080231312798216754218711)
                      ·
                        rfl

theorem cell23_4051236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2, 1, 1, 4, 2].length) (baseStart_4051236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4051236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4051236 prefixEnd_4051236 := by exact prefixLift 4051236
  have htrace : WordTrace (prefixWord ++ tailWord_4051236) baseStart_4051236 baseEnd_4051236 := by
    simpa [prefixWord, tailWord_4051236, baseEnd_4051236] using wordTrace_append hprefix tailTrace_4051236
  have hstable : (prefixWord ++ tailWord_4051236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4051236).length < 2 ^ (prefixWord ++ tailWord_4051236).sum := by decide
  have hdescent : baseEnd_4051236 < baseStart_4051236 := by decide
  rcases family_descends (prefixWord ++ tailWord_4051236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4051272 : List Nat := [2, 1, 3, 1, 1, 2, 2, 4, 2, 5]
def baseStart_4051272 : Nat := 118140960795 + 4051272 * 2 ^ 59
def prefixEnd_4051272 : Nat := 4983230072969 + 3 ^ 40 * 4051272 * 2
def baseEnd_4051272 : Nat := 693416599367259537789515

theorem tailTrace_4051272 : CollatzResearch.WordTrace tailWord_4051272 prefixEnd_4051272 693416599367259537789515 := by
  unfold tailWord_4051272
  simp only [CollatzResearch.WordTrace]
  refine ⟨73881014489470460508782035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98508019319293947345042713 73881014489470460508782035)
  ·
    refine ⟨110821521734205690763173053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73881014489470460508782035 110821521734205690763173053)
    ·
      refine ⟨41558070650327134036189895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110821521734205690763173053 41558070650327134036189895)
      ·
        refine ⟨62337105975490701054284843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41558070650327134036189895 62337105975490701054284843)
        ·
          refine ⟨93505658963236051581427265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62337105975490701054284843 93505658963236051581427265)
          ·
            refine ⟨70129244222427038686070449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93505658963236051581427265 70129244222427038686070449)
            ·
              refine ⟨52596933166820279014552837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70129244222427038686070449 52596933166820279014552837)
              ·
                refine ⟨9861924968778802315228657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52596933166820279014552837 9861924968778802315228657)
                ·
                  refine ⟨7396443726584101736421493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9861924968778802315228657 7396443726584101736421493)
                  ·
                    refine ⟨693416599367259537789515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7396443726584101736421493 693416599367259537789515)
                    ·
                      rfl

theorem cell23_4051272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 4, 2, 5].length) (baseStart_4051272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4051272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4051272 prefixEnd_4051272 := by exact prefixLift 4051272
  have htrace : WordTrace (prefixWord ++ tailWord_4051272) baseStart_4051272 baseEnd_4051272 := by
    simpa [prefixWord, tailWord_4051272, baseEnd_4051272] using wordTrace_append hprefix tailTrace_4051272
  have hstable : (prefixWord ++ tailWord_4051272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4051272).length < 2 ^ (prefixWord ++ tailWord_4051272).sum := by decide
  have hdescent : baseEnd_4051272 < baseStart_4051272 := by decide
  rcases family_descends (prefixWord ++ tailWord_4051272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4051282 : List Nat := [3, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5]
def baseStart_4051282 : Nat := 118140960795 + 4051282 * 2 ^ 59
def prefixEnd_4051282 : Nat := 4983230072969 + 3 ^ 40 * 4051282 * 2
def baseEnd_4051282 : Nat := 2080254932908323574243499

theorem tailTrace_4051282 : CollatzResearch.WordTrace tailWord_4051282 prefixEnd_4051282 2080254932908323574243499 := by
  unfold tailWord_4051282
  simp only [CollatzResearch.WordTrace]
  refine ⟨36940598427226173181357025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98508262472603128483618733 36940598427226173181357025)
  ·
    refine ⟨27705448820419629886017769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36940598427226173181357025 27705448820419629886017769)
    ·
      refine ⟨20779086615314722414513327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27705448820419629886017769 20779086615314722414513327)
      ·
        refine ⟨31168629922972083621769991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20779086615314722414513327 31168629922972083621769991)
        ·
          refine ⟨46752944884458125432654987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31168629922972083621769991 46752944884458125432654987)
          ·
            refine ⟨70129417326687188148982481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46752944884458125432654987 70129417326687188148982481)
            ·
              refine ⟨52597062995015391111736861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70129417326687188148982481 52597062995015391111736861)
              ·
                refine ⟨19723898623130771666901323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52597062995015391111736861 19723898623130771666901323)
                ·
                  refine ⟨29585847934696157500351985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19723898623130771666901323 29585847934696157500351985)
                  ·
                    refine ⟨22189385951022118125263989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29585847934696157500351985 22189385951022118125263989)
                    ·
                      refine ⟨2080254932908323574243499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22189385951022118125263989 2080254932908323574243499)
                      ·
                        rfl

theorem cell23_4051282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5].length) (baseStart_4051282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4051282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4051282 prefixEnd_4051282 := by exact prefixLift 4051282
  have htrace : WordTrace (prefixWord ++ tailWord_4051282) baseStart_4051282 baseEnd_4051282 := by
    simpa [prefixWord, tailWord_4051282, baseEnd_4051282] using wordTrace_append hprefix tailTrace_4051282
  have hstable : (prefixWord ++ tailWord_4051282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4051282).length < 2 ^ (prefixWord ++ tailWord_4051282).sum := by decide
  have hdescent : baseEnd_4051282 < baseStart_4051282 := by decide
  rcases family_descends (prefixWord ++ tailWord_4051282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4051309 : List Nat := [1, 5, 1, 1, 1, 2, 2, 3, 2, 1, 4]
def baseStart_4051309 : Nat := 118140960795 + 4051309 * 2 ^ 59
def prefixEnd_4051309 : Nat := 4983230072969 + 3 ^ 40 * 4051309 * 2
def baseEnd_4051309 : Nat := 2080268796885994968605875

theorem tailTrace_4051309 : CollatzResearch.WordTrace tailWord_4051309 prefixEnd_4051309 2080268796885994968605875 := by
  unfold tailWord_4051309
  simp only [CollatzResearch.WordTrace]
  refine ⟨147763378479806876336660981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98508918986537917557773987 147763378479806876336660981)
  ·
    refine ⟨13852816732481894656561967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 147763378479806876336660981 13852816732481894656561967)
    ·
      refine ⟨20779225098722841984842951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13852816732481894656561967 20779225098722841984842951)
      ·
        refine ⟨31168837648084262977264427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20779225098722841984842951 31168837648084262977264427)
        ·
          refine ⟨46753256472126394465896641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31168837648084262977264427 46753256472126394465896641)
          ·
            refine ⟨35064942354094795849422481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46753256472126394465896641 35064942354094795849422481)
            ·
              refine ⟨26298706765571096887066861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35064942354094795849422481 26298706765571096887066861)
              ·
                refine ⟨9862015037089161332650073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26298706765571096887066861 9862015037089161332650073)
                ·
                  refine ⟨7396511277816870999487555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9862015037089161332650073 7396511277816870999487555)
                  ·
                    refine ⟨11094766916725306499231333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7396511277816870999487555 11094766916725306499231333)
                    ·
                      refine ⟨2080268796885994968605875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11094766916725306499231333 2080268796885994968605875)
                      ·
                        rfl

theorem cell23_4051309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 3, 2, 1, 4].length) (baseStart_4051309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4051309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4051309 prefixEnd_4051309 := by exact prefixLift 4051309
  have htrace : WordTrace (prefixWord ++ tailWord_4051309) baseStart_4051309 baseEnd_4051309 := by
    simpa [prefixWord, tailWord_4051309, baseEnd_4051309] using wordTrace_append hprefix tailTrace_4051309
  have hstable : (prefixWord ++ tailWord_4051309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4051309).length < 2 ^ (prefixWord ++ tailWord_4051309).sum := by decide
  have hdescent : baseEnd_4051309 < baseStart_4051309 := by decide
  rcases family_descends (prefixWord ++ tailWord_4051309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4051332 : List Nat := [2, 3, 2, 1, 1, 2, 1, 3, 8]
def baseStart_4051332 : Nat := 118140960795 + 4051332 * 2 ^ 59
def prefixEnd_4051332 : Nat := 4983230072969 + 3 ^ 40 * 4051332 * 2
def baseEnd_4051332 : Nat := 231142289660116486513141

theorem tailTrace_4051332 : CollatzResearch.WordTrace tailWord_4051332 prefixEnd_4051332 231142289660116486513141 := by
  unfold tailWord_4051332
  simp only [CollatzResearch.WordTrace]
  refine ⟨73882108679361775632374125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98509478239149034176498833 73882108679361775632374125)
  ·
    refine ⟨27705790754760665862140297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73882108679361775632374125 27705790754760665862140297)
    ·
      refine ⟨20779343066070499396605223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27705790754760665862140297 20779343066070499396605223)
      ·
        refine ⟨31169014599105749094907835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20779343066070499396605223 31169014599105749094907835)
        ·
          refine ⟨46753521898658623642361753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31169014599105749094907835 46753521898658623642361753)
          ·
            refine ⟨35065141423993967731771315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46753521898658623642361753 35065141423993967731771315)
            ·
              refine ⟨52597712135990951597656973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35065141423993967731771315 52597712135990951597656973)
              ·
                refine ⟨19724142050996606849121365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52597712135990951597656973 19724142050996606849121365)
                ·
                  refine ⟨231142289660116486513141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19724142050996606849121365 231142289660116486513141)
                  ·
                    rfl

theorem cell23_4051332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 3, 8].length) (baseStart_4051332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4051332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4051332 prefixEnd_4051332 := by exact prefixLift 4051332
  have htrace : WordTrace (prefixWord ++ tailWord_4051332) baseStart_4051332 baseEnd_4051332 := by
    simpa [prefixWord, tailWord_4051332, baseEnd_4051332] using wordTrace_append hprefix tailTrace_4051332
  have hstable : (prefixWord ++ tailWord_4051332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4051332).length < 2 ^ (prefixWord ++ tailWord_4051332).sum := by decide
  have hdescent : baseEnd_4051332 < baseStart_4051332 := by decide
  rcases family_descends (prefixWord ++ tailWord_4051332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4051369 : List Nat := [1, 2, 1, 1, 1, 1, 3, 5, 1, 5, 2]
def baseStart_4051369 : Nat := 118140960795 + 4051369 * 2 ^ 59
def prefixEnd_4051369 : Nat := 4983230072969 + 3 ^ 40 * 4051369 * 2
def baseEnd_4051369 : Nat := 2080299605725264733855599

theorem tailTrace_4051369 : CollatzResearch.WordTrace tailWord_4051369 prefixEnd_4051369 2080299605725264733855599 := by
  unfold tailWord_4051369
  simp only [CollatzResearch.WordTrace]
  refine ⟨147765566859589506583845161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98510377906393004389230107 147765566859589506583845161)
  ·
    refine ⟨110824175144692129937883871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147765566859589506583845161 110824175144692129937883871)
    ·
      refine ⟨166236262717038194906825807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110824175144692129937883871 166236262717038194906825807)
      ·
        refine ⟨249354394075557292360238711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166236262717038194906825807 249354394075557292360238711)
        ·
          refine ⟨374031591113335938540358067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249354394075557292360238711 374031591113335938540358067)
          ·
            refine ⟨561047386670003907810537101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 374031591113335938540358067 561047386670003907810537101)
            ·
              refine ⟨210392770001251465428951413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 561047386670003907810537101 210392770001251465428951413)
              ·
                refine ⟨19724322187617324883964195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 210392770001251465428951413 19724322187617324883964195)
                ·
                  refine ⟨29586483281425987325946293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19724322187617324883964195 29586483281425987325946293)
                  ·
                    refine ⟨2773732807633686311807465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29586483281425987325946293 2773732807633686311807465)
                    ·
                      refine ⟨2080299605725264733855599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2773732807633686311807465 2080299605725264733855599)
                      ·
                        rfl

theorem cell23_4051369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 5, 1, 5, 2].length) (baseStart_4051369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4051369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4051369 prefixEnd_4051369 := by exact prefixLift 4051369
  have htrace : WordTrace (prefixWord ++ tailWord_4051369) baseStart_4051369 baseEnd_4051369 := by
    simpa [prefixWord, tailWord_4051369, baseEnd_4051369] using wordTrace_append hprefix tailTrace_4051369
  have hstable : (prefixWord ++ tailWord_4051369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4051369).length < 2 ^ (prefixWord ++ tailWord_4051369).sum := by decide
  have hdescent : baseEnd_4051369 < baseStart_4051369 := by decide
  rcases family_descends (prefixWord ++ tailWord_4051369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4051392 : List Nat := [2, 1, 1, 2, 3, 1, 1, 1, 5, 6]
def baseStart_4051392 : Nat := 118140960795 + 4051392 * 2 ^ 59
def prefixEnd_4051392 : Nat := 4983230072969 + 3 ^ 40 * 4051392 * 2
def baseEnd_4051392 : Nat := 693437138593439381289331

theorem tailTrace_4051392 : CollatzResearch.WordTrace tailWord_4051392 prefixEnd_4051392 693437138593439381289331 := by
  unfold tailWord_4051392
  simp only [CollatzResearch.WordTrace]
  refine ⟨73883202869253090755966215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98510937159004121007954953 73883202869253090755966215)
  ·
    refine ⟨110824804303879636133949323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73883202869253090755966215 110824804303879636133949323)
    ·
      refine ⟨166237206455819454200923985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110824804303879636133949323 166237206455819454200923985)
      ·
        refine ⟨124677904841864590650692989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166237206455819454200923985 124677904841864590650692989)
        ·
          refine ⟨46754214315699221494009871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124677904841864590650692989 46754214315699221494009871)
          ·
            refine ⟨70131321473548832241014807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46754214315699221494009871 70131321473548832241014807)
            ·
              refine ⟨105196982210323248361522211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70131321473548832241014807 105196982210323248361522211)
              ·
                refine ⟨157795473315484872542283317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105196982210323248361522211 157795473315484872542283317)
                ·
                  refine ⟨14793325623326706800839061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 157795473315484872542283317 14793325623326706800839061)
                  ·
                    refine ⟨693437138593439381289331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14793325623326706800839061 693437138593439381289331)
                    ·
                      rfl

theorem cell23_4051392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 5, 6].length) (baseStart_4051392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4051392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4051392 prefixEnd_4051392 := by exact prefixLift 4051392
  have htrace : WordTrace (prefixWord ++ tailWord_4051392) baseStart_4051392 baseEnd_4051392 := by
    simpa [prefixWord, tailWord_4051392, baseEnd_4051392] using wordTrace_append hprefix tailTrace_4051392
  have hstable : (prefixWord ++ tailWord_4051392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4051392).length < 2 ^ (prefixWord ++ tailWord_4051392).sum := by decide
  have hdescent : baseEnd_4051392 < baseStart_4051392 := by decide
  rcases family_descends (prefixWord ++ tailWord_4051392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4051399 : List Nat := [1, 1, 4, 1, 1, 4, 1, 2, 3, 1, 4]
def baseStart_4051399 : Nat := 118140960795 + 4051399 * 2 ^ 59
def prefixEnd_4051399 : Nat := 4983230072969 + 3 ^ 40 * 4051399 * 2
def baseEnd_4051399 : Nat := 2080315010144899616480461

theorem tailTrace_4051399 : CollatzResearch.WordTrace tailWord_4051399 prefixEnd_4051399 2080315010144899616480461 := by
  unfold tailWord_4051399
  simp only [CollatzResearch.WordTrace]
  refine ⟨147766661049480821707437251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98511107366320547804958167 147766661049480821707437251)
  ·
    refine ⟨221649991574221232561155877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147766661049480821707437251 221649991574221232561155877)
    ·
      refine ⟨41559373420166481105216727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 221649991574221232561155877 41559373420166481105216727)
      ·
        refine ⟨62339060130249721657825091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41559373420166481105216727 62339060130249721657825091)
        ·
          refine ⟨93508590195374582486737637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62339060130249721657825091 93508590195374582486737637)
          ·
            refine ⟨17532860661632734216263307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93508590195374582486737637 17532860661632734216263307)
            ·
              refine ⟨26299290992449101324394961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17532860661632734216263307 26299290992449101324394961)
              ·
                refine ⟨19724468244336825993296221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26299290992449101324394961 19724468244336825993296221)
                ·
                  refine ⟨7396675591626309747486083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19724468244336825993296221 7396675591626309747486083)
                  ·
                    refine ⟨11095013387439464621229125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7396675591626309747486083 11095013387439464621229125)
                    ·
                      refine ⟨2080315010144899616480461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11095013387439464621229125 2080315010144899616480461)
                      ·
                        rfl

theorem cell23_4051399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 2, 3, 1, 4].length) (baseStart_4051399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4051399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4051399 prefixEnd_4051399 := by exact prefixLift 4051399
  have htrace : WordTrace (prefixWord ++ tailWord_4051399) baseStart_4051399 baseEnd_4051399 := by
    simpa [prefixWord, tailWord_4051399, baseEnd_4051399] using wordTrace_append hprefix tailTrace_4051399
  have hstable : (prefixWord ++ tailWord_4051399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4051399).length < 2 ^ (prefixWord ++ tailWord_4051399).sum := by decide
  have hdescent : baseEnd_4051399 < baseStart_4051399 := by decide
  rcases family_descends (prefixWord ++ tailWord_4051399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4051410 : List Nat := [3, 2, 2, 4, 1, 1, 1, 2, 3, 1, 3]
def baseStart_4051410 : Nat := 118140960795 + 4051410 * 2 ^ 59
def prefixEnd_4051410 : Nat := 4983230072969 + 3 ^ 40 * 4051410 * 2
def baseEnd_4051410 : Nat := 2080320658432099073442911

theorem tailTrace_4051410 : CollatzResearch.WordTrace tailWord_4051410 prefixEnd_4051410 2080320658432099073442911 := by
  unfold tailWord_4051410
  simp only [CollatzResearch.WordTrace]
  refine ⟨36941765563110242646521921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98511374834960647057391789 36941765563110242646521921)
  ·
    refine ⟨27706324172332681984891441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36941765563110242646521921 27706324172332681984891441)
    ·
      refine ⟨20779743129249511488668581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27706324172332681984891441 20779743129249511488668581)
      ·
        refine ⟨3896201836734283404125359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20779743129249511488668581 3896201836734283404125359)
        ·
          refine ⟨5844302755101425106188039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3896201836734283404125359 5844302755101425106188039)
          ·
            refine ⟨8766454132652137659282059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5844302755101425106188039 8766454132652137659282059)
            ·
              refine ⟨13149681198978206488923089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8766454132652137659282059 13149681198978206488923089)
              ·
                refine ⟨9862260899233654866692317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13149681198978206488923089 9862260899233654866692317)
                ·
                  refine ⟨3698347837212620575009619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9862260899233654866692317 3698347837212620575009619)
                  ·
                    refine ⟨5547521755818930862514429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3698347837212620575009619 5547521755818930862514429)
                    ·
                      refine ⟨2080320658432099073442911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5547521755818930862514429 2080320658432099073442911)
                      ·
                        rfl

theorem cell23_4051410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_4051410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4051410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4051410 prefixEnd_4051410 := by exact prefixLift 4051410
  have htrace : WordTrace (prefixWord ++ tailWord_4051410) baseStart_4051410 baseEnd_4051410 := by
    simpa [prefixWord, tailWord_4051410, baseEnd_4051410] using wordTrace_append hprefix tailTrace_4051410
  have hstable : (prefixWord ++ tailWord_4051410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4051410).length < 2 ^ (prefixWord ++ tailWord_4051410).sum := by decide
  have hdescent : baseEnd_4051410 < baseStart_4051410 := by decide
  rcases family_descends (prefixWord ++ tailWord_4051410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4051436 : List Nat := [2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 3]
def baseStart_4051436 : Nat := 118140960795 + 4051436 * 2 ^ 59
def prefixEnd_4051436 : Nat := 4983230072969 + 3 ^ 40 * 4051436 * 2
def baseEnd_4051436 : Nat := 2080334008929115971717791

theorem tailTrace_4051436 : CollatzResearch.WordTrace tailWord_4051436 prefixEnd_4051436 2080334008929115971717791 := by
  unfold tailWord_4051436
  simp only [CollatzResearch.WordTrace]
  refine ⟨73884005275173388513267081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98512007033564518017689441 73884005275173388513267081)
  ·
    refine ⟨55413003956380041384950311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73884005275173388513267081 55413003956380041384950311)
    ·
      refine ⟨83119505934570062077425467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55413003956380041384950311 83119505934570062077425467)
      ·
        refine ⟨124679258901855093116138201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83119505934570062077425467 124679258901855093116138201)
        ·
          refine ⟨93509444176391319837103651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124679258901855093116138201 93509444176391319837103651)
          ·
            refine ⟨140264166264586979755655477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93509444176391319837103651 140264166264586979755655477)
            ·
              refine ⟨13149765587305029352092701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 140264166264586979755655477 13149765587305029352092701)
              ·
                refine ⟨4931162095239386007034763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13149765587305029352092701 4931162095239386007034763)
                ·
                  refine ⟨7396743142859079010552145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4931162095239386007034763 7396743142859079010552145)
                  ·
                    refine ⟨5547557357144309257914109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7396743142859079010552145 5547557357144309257914109)
                    ·
                      refine ⟨2080334008929115971717791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5547557357144309257914109 2080334008929115971717791)
                      ·
                        rfl

theorem cell23_4051436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 3].length) (baseStart_4051436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4051436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4051436 prefixEnd_4051436 := by exact prefixLift 4051436
  have htrace : WordTrace (prefixWord ++ tailWord_4051436) baseStart_4051436 baseEnd_4051436 := by
    simpa [prefixWord, tailWord_4051436, baseEnd_4051436] using wordTrace_append hprefix tailTrace_4051436
  have hstable : (prefixWord ++ tailWord_4051436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4051436).length < 2 ^ (prefixWord ++ tailWord_4051436).sum := by decide
  have hdescent : baseEnd_4051436 < baseStart_4051436 := by decide
  rcases family_descends (prefixWord ++ tailWord_4051436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4051449 : List Nat := [1, 2, 1, 3, 1, 2, 2, 2, 3, 3, 3]
def baseStart_4051449 : Nat := 118140960795 + 4051449 * 2 ^ 59
def prefixEnd_4051449 : Nat := 4983230072969 + 3 ^ 40 * 4051449 * 2
def baseEnd_4051449 : Nat := 2080340684177624420855231

theorem tailTrace_4051449 : CollatzResearch.WordTrace tailWord_4051449 prefixEnd_4051449 2080340684177624420855231 := by
  unfold tailWord_4051449
  simp only [CollatzResearch.WordTrace]
  refine ⟨147768484699299680246757401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98512323132866453497838267 147768484699299680246757401)
  ·
    refine ⟨110826363524474760185068051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147768484699299680246757401 110826363524474760185068051)
    ·
      refine ⟨166239545286712140277602077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110826363524474760185068051 166239545286712140277602077)
      ·
        refine ⟨62339829482517052604100779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166239545286712140277602077 62339829482517052604100779)
        ·
          refine ⟨93509744223775578906151169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62339829482517052604100779 93509744223775578906151169)
          ·
            refine ⟨70132308167831684179613377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93509744223775578906151169 70132308167831684179613377)
            ·
              refine ⟨52599231125873763134710033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70132308167831684179613377 52599231125873763134710033)
              ·
                refine ⟨39449423344405322351032525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52599231125873763134710033 39449423344405322351032525)
                ·
                  refine ⟨14793533754151995881637197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39449423344405322351032525 14793533754151995881637197)
                  ·
                    refine ⟨5547575157806998455613949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14793533754151995881637197 5547575157806998455613949)
                    ·
                      refine ⟨2080340684177624420855231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5547575157806998455613949 2080340684177624420855231)
                      ·
                        rfl

theorem cell23_4051449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 2, 3, 3, 3].length) (baseStart_4051449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4051449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4051449 prefixEnd_4051449 := by exact prefixLift 4051449
  have htrace : WordTrace (prefixWord ++ tailWord_4051449) baseStart_4051449 baseEnd_4051449 := by
    simpa [prefixWord, tailWord_4051449, baseEnd_4051449] using wordTrace_append hprefix tailTrace_4051449
  have hstable : (prefixWord ++ tailWord_4051449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4051449).length < 2 ^ (prefixWord ++ tailWord_4051449).sum := by decide
  have hdescent : baseEnd_4051449 < baseStart_4051449 := by decide
  rcases family_descends (prefixWord ++ tailWord_4051449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4051460 : List Nat := [2, 3, 2, 3, 1, 2, 3, 1, 2, 4]
def baseStart_4051460 : Nat := 118140960795 + 4051460 * 2 ^ 59
def prefixEnd_4051460 : Nat := 4983230072969 + 3 ^ 40 * 4051460 * 2
def baseEnd_4051460 : Nat := 693448777488274625939227

theorem tailTrace_4051460 : CollatzResearch.WordTrace tailWord_4051460 prefixEnd_4051460 693448777488274625939227 := by
  unfold tailWord_4051460
  simp only [CollatzResearch.WordTrace]
  refine ⟨73884442951129914562703917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98512590601506552750271889 73884442951129914562703917)
  ·
    refine ⟨27706666106673717961013969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73884442951129914562703917 27706666106673717961013969)
    ·
      refine ⟨20779999580005288470760477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27706666106673717961013969 20779999580005288470760477)
      ·
        refine ⟨7792499842501983176535179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20779999580005288470760477 7792499842501983176535179)
        ·
          refine ⟨11688749763752974764802769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7792499842501983176535179 11688749763752974764802769)
          ·
            refine ⟨8766562322814731073602077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11688749763752974764802769 8766562322814731073602077)
            ·
              refine ⟨3287460871055524152600779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8766562322814731073602077 3287460871055524152600779)
              ·
                refine ⟨4931191306583286228901169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3287460871055524152600779 4931191306583286228901169)
                ·
                  refine ⟨3698393479937464671675877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4931191306583286228901169 3698393479937464671675877)
                  ·
                    refine ⟨693448777488274625939227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3698393479937464671675877 693448777488274625939227)
                    ·
                      rfl

theorem cell23_4051460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 3, 1, 2, 4].length) (baseStart_4051460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4051460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4051460 prefixEnd_4051460 := by exact prefixLift 4051460
  have htrace : WordTrace (prefixWord ++ tailWord_4051460) baseStart_4051460 baseEnd_4051460 := by
    simpa [prefixWord, tailWord_4051460, baseEnd_4051460] using wordTrace_append hprefix tailTrace_4051460
  have hstable : (prefixWord ++ tailWord_4051460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4051460).length < 2 ^ (prefixWord ++ tailWord_4051460).sum := by decide
  have hdescent : baseEnd_4051460 < baseStart_4051460 := by decide
  rcases family_descends (prefixWord ++ tailWord_4051460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4051463 : List Nat := [1, 1, 4, 3, 3, 2, 1, 1, 1, 2, 4]
def baseStart_4051463 : Nat := 118140960795 + 4051463 * 2 ^ 59
def prefixEnd_4051463 : Nat := 4983230072969 + 3 ^ 40 * 4051463 * 2
def baseEnd_4051463 : Nat := 2080347872906787366080167

theorem tailTrace_4051463 : CollatzResearch.WordTrace tailWord_4051463 prefixEnd_4051463 2080347872906787366080167 := by
  unfold tailWord_4051463
  simp only [CollatzResearch.WordTrace]
  refine ⟨147768995321248960637767043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98512663547499307091844695 147768995321248960637767043)
  ·
    refine ⟨221653492981873440956650565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147768995321248960637767043 221653492981873440956650565)
    ·
      refine ⟨41560029934101270179371981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 221653492981873440956650565 41560029934101270179371981)
      ·
        refine ⟨15585011225287976317264493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41560029934101270179371981 15585011225287976317264493)
        ·
          refine ⟨5844379209482991118974185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15585011225287976317264493 5844379209482991118974185)
          ·
            refine ⟨4383284407112243339230639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5844379209482991118974185 4383284407112243339230639)
            ·
              refine ⟨6574926610668365008845959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4383284407112243339230639 6574926610668365008845959)
              ·
                refine ⟨9862389916002547513268939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6574926610668365008845959 9862389916002547513268939)
                ·
                  refine ⟨14793584874003821269903409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9862389916002547513268939 14793584874003821269903409)
                  ·
                    refine ⟨11095188655502865952427557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14793584874003821269903409 11095188655502865952427557)
                    ·
                      refine ⟨2080347872906787366080167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11095188655502865952427557 2080347872906787366080167)
                      ·
                        rfl

theorem cell23_4051463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 1, 1, 1, 2, 4].length) (baseStart_4051463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4051463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4051463 prefixEnd_4051463 := by exact prefixLift 4051463
  have htrace : WordTrace (prefixWord ++ tailWord_4051463) baseStart_4051463 baseEnd_4051463 := by
    simpa [prefixWord, tailWord_4051463, baseEnd_4051463] using wordTrace_append hprefix tailTrace_4051463
  have hstable : (prefixWord ++ tailWord_4051463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4051463).length < 2 ^ (prefixWord ++ tailWord_4051463).sum := by decide
  have hdescent : baseEnd_4051463 < baseStart_4051463 := by decide
  rcases family_descends (prefixWord ++ tailWord_4051463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4051493 : List Nat := [1, 3, 1, 2, 2, 1, 4, 3, 1, 3, 2]
def baseStart_4051493 : Nat := 118140960795 + 4051493 * 2 ^ 59
def prefixEnd_4051493 : Nat := 4983230072969 + 3 ^ 40 * 4051493 * 2
def baseEnd_4051493 : Nat := 2080363277326422248705029

theorem tailTrace_4051493 : CollatzResearch.WordTrace tailWord_4051493 prefixEnd_4051493 2080363277326422248705029 := by
  unfold tailWord_4051493
  simp only [CollatzResearch.WordTrace]
  refine ⟨147770089511140275761359133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98513393007426850507572755 147770089511140275761359133)
  ·
    refine ⟨55413783566677603410509675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147770089511140275761359133 55413783566677603410509675)
    ·
      refine ⟨83120675350016405115764513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55413783566677603410509675 83120675350016405115764513)
      ·
        refine ⟨62340506512512303836823385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83120675350016405115764513 62340506512512303836823385)
        ·
          refine ⟨46755379884384227877617539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62340506512512303836823385 46755379884384227877617539)
          ·
            refine ⟨70133069826576341816426309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46755379884384227877617539 70133069826576341816426309)
            ·
              refine ⟨13149950592483064090579933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70133069826576341816426309 13149950592483064090579933)
              ·
                refine ⟨4931231472181149033967475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13149950592483064090579933 4931231472181149033967475)
                ·
                  refine ⟨7396847208271723550951213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4931231472181149033967475 7396847208271723550951213)
                  ·
                    refine ⟨2773817703101896331606705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7396847208271723550951213 2773817703101896331606705)
                    ·
                      refine ⟨2080363277326422248705029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2773817703101896331606705 2080363277326422248705029)
                      ·
                        rfl

theorem cell23_4051493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 3, 1, 3, 2].length) (baseStart_4051493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4051493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4051493 prefixEnd_4051493 := by exact prefixLift 4051493
  have htrace : WordTrace (prefixWord ++ tailWord_4051493) baseStart_4051493 baseEnd_4051493 := by
    simpa [prefixWord, tailWord_4051493, baseEnd_4051493] using wordTrace_append hprefix tailTrace_4051493
  have hstable : (prefixWord ++ tailWord_4051493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4051493).length < 2 ^ (prefixWord ++ tailWord_4051493).sum := by decide
  have hdescent : baseEnd_4051493 < baseStart_4051493 := by decide
  rcases family_descends (prefixWord ++ tailWord_4051493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4051501 : List Nat := [1, 5, 4, 1, 1, 2, 1, 1, 3, 2, 2]
def baseStart_4051501 : Nat := 118140960795 + 4051501 * 2 ^ 59
def prefixEnd_4051501 : Nat := 4983230072969 + 3 ^ 40 * 4051501 * 2
def baseEnd_4051501 : Nat := 2080367385171658217404993

theorem tailTrace_4051501 : CollatzResearch.WordTrace tailWord_4051501 prefixEnd_4051501 2080367385171658217404993 := by
  unfold tailWord_4051501
  simp only [CollatzResearch.WordTrace]
  refine ⟨147770381295111293127650357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98513587530074195418433571 147770381295111293127650357)
  ·
    refine ⟨13853473246416683730717221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 147770381295111293127650357 13853473246416683730717221)
    ·
      refine ⟨2597526233703128199509479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13853473246416683730717221 2597526233703128199509479)
      ·
        refine ⟨3896289350554692299264219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2597526233703128199509479 3896289350554692299264219)
        ·
          refine ⟨5844434025832038448896329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3896289350554692299264219 5844434025832038448896329)
          ·
            refine ⟨4383325519374028836672247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5844434025832038448896329 4383325519374028836672247)
            ·
              refine ⟨6574988279061043255008371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4383325519374028836672247 6574988279061043255008371)
              ·
                refine ⟨9862482418591564882512557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6574988279061043255008371 9862482418591564882512557)
                ·
                  refine ⟨3698430906971836830942209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9862482418591564882512557 3698430906971836830942209)
                  ·
                    refine ⟨2773823180228877623206657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3698430906971836830942209 2773823180228877623206657)
                    ·
                      refine ⟨2080367385171658217404993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2773823180228877623206657 2080367385171658217404993)
                      ·
                        rfl

theorem cell23_4051501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_4051501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4051501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4051501 prefixEnd_4051501 := by exact prefixLift 4051501
  have htrace : WordTrace (prefixWord ++ tailWord_4051501) baseStart_4051501 baseEnd_4051501 := by
    simpa [prefixWord, tailWord_4051501, baseEnd_4051501] using wordTrace_append hprefix tailTrace_4051501
  have hstable : (prefixWord ++ tailWord_4051501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4051501).length < 2 ^ (prefixWord ++ tailWord_4051501).sum := by decide
  have hdescent : baseEnd_4051501 < baseStart_4051501 := by decide
  rcases family_descends (prefixWord ++ tailWord_4051501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4051509 : List Nat := [1, 3, 3, 1, 1, 2, 1, 2, 1, 3, 5]
def baseStart_4051509 : Nat := 118140960795 + 4051509 * 2 ^ 59
def prefixEnd_4051509 : Nat := 4983230072969 + 3 ^ 40 * 4051509 * 2
def baseEnd_4051509 : Nat := 2080371493016894186104955

theorem tailTrace_4051509 : CollatzResearch.WordTrace tailWord_4051509 prefixEnd_4051509 2080371493016894186104955 := by
  unfold tailWord_4051509
  simp only [CollatzResearch.WordTrace]
  refine ⟨147770673079082310493941581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98513782052721540329294387 147770673079082310493941581)
  ·
    refine ⟨55414002404655866435228093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147770673079082310493941581 55414002404655866435228093)
    ·
      refine ⟨20780250901745949913210535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55414002404655866435228093 20780250901745949913210535)
      ·
        refine ⟨31170376352618924869815803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20780250901745949913210535 31170376352618924869815803)
        ·
          refine ⟨46755564528928387304723705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31170376352618924869815803 46755564528928387304723705)
          ·
            refine ⟨35066673396696290478542779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46755564528928387304723705 35066673396696290478542779)
            ·
              refine ⟨52600010095044435717814169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35066673396696290478542779 52600010095044435717814169)
              ·
                refine ⟨39450007571283326788360627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52600010095044435717814169 39450007571283326788360627)
                ·
                  refine ⟨59175011356924990182540941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39450007571283326788360627 59175011356924990182540941)
                  ·
                    refine ⟨22190629258846871318452853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59175011356924990182540941 22190629258846871318452853)
                    ·
                      refine ⟨2080371493016894186104955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22190629258846871318452853 2080371493016894186104955)
                      ·
                        rfl

theorem cell23_4051509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_4051509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4051509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4051509 prefixEnd_4051509 := by exact prefixLift 4051509
  have htrace : WordTrace (prefixWord ++ tailWord_4051509) baseStart_4051509 baseEnd_4051509 := by
    simpa [prefixWord, tailWord_4051509, baseEnd_4051509] using wordTrace_append hprefix tailTrace_4051509
  have hstable : (prefixWord ++ tailWord_4051509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4051509).length < 2 ^ (prefixWord ++ tailWord_4051509).sum := by decide
  have hdescent : baseEnd_4051509 < baseStart_4051509 := by decide
  rcases family_descends (prefixWord ++ tailWord_4051509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4051517 : List Nat := [1, 4, 1, 3, 2, 3, 2, 1, 2, 1, 3]
def baseStart_4051517 : Nat := 118140960795 + 4051517 * 2 ^ 59
def prefixEnd_4051517 : Nat := 4983230072969 + 3 ^ 40 * 4051517 * 2
def baseEnd_4051517 : Nat := 2080375600862130154804919

theorem tailTrace_4051517 : CollatzResearch.WordTrace tailWord_4051517 prefixEnd_4051517 2080375600862130154804919 := by
  unfold tailWord_4051517
  simp only [CollatzResearch.WordTrace]
  refine ⟨147770964863053327860232805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98513976575368885240155203 147770964863053327860232805)
  ·
    refine ⟨27707055911822498973793651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147770964863053327860232805 27707055911822498973793651)
    ·
      refine ⟨41560583867733748460690477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27707055911822498973793651 41560583867733748460690477)
      ·
        refine ⟨15585218950400155672758929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41560583867733748460690477 15585218950400155672758929)
        ·
          refine ⟨11688914212800116754569197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15585218950400155672758929 11688914212800116754569197)
          ·
            refine ⟨4383342829800043782963449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11688914212800116754569197 4383342829800043782963449)
            ·
              refine ⟨3287507122350032837222587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4383342829800043782963449 3287507122350032837222587)
              ·
                refine ⟨4931260683525049255833881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3287507122350032837222587 4931260683525049255833881)
                ·
                  refine ⟨3698445512643786941875411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4931260683525049255833881 3698445512643786941875411)
                  ·
                    refine ⟨5547668268965680412813117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3698445512643786941875411 5547668268965680412813117)
                    ·
                      refine ⟨2080375600862130154804919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5547668268965680412813117 2080375600862130154804919)
                      ·
                        rfl

theorem cell23_4051517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 2, 1, 2, 1, 3].length) (baseStart_4051517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4051517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4051517 prefixEnd_4051517 := by exact prefixLift 4051517
  have htrace : WordTrace (prefixWord ++ tailWord_4051517) baseStart_4051517 baseEnd_4051517 := by
    simpa [prefixWord, tailWord_4051517, baseEnd_4051517] using wordTrace_append hprefix tailTrace_4051517
  have hstable : (prefixWord ++ tailWord_4051517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4051517).length < 2 ^ (prefixWord ++ tailWord_4051517).sum := by decide
  have hdescent : baseEnd_4051517 < baseStart_4051517 := by decide
  rcases family_descends (prefixWord ++ tailWord_4051517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4051519 : List Nat := [1, 1, 2, 2, 3, 2, 2, 1, 1, 4, 4]
def baseStart_4051519 : Nat := 118140960795 + 4051519 * 2 ^ 59
def prefixEnd_4051519 : Nat := 4983230072969 + 3 ^ 40 * 4051519 * 2
def baseEnd_4051519 : Nat := 2080376627823439146979909

theorem tailTrace_4051519 : CollatzResearch.WordTrace tailWord_4051519 prefixEnd_4051519 2080376627823439146979909 := by
  unfold tailWord_4051519
  simp only [CollatzResearch.WordTrace]
  refine ⟨147771037809046082201805611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98514025206030721467870407 147771037809046082201805611)
  ·
    refine ⟨221656556713569123302708417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147771037809046082201805611 221656556713569123302708417)
    ·
      refine ⟨166242417535176842477031313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221656556713569123302708417 166242417535176842477031313)
      ·
        refine ⟨124681813151382631857773485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166242417535176842477031313 124681813151382631857773485)
        ·
          refine ⟨46755679931768486946665057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124681813151382631857773485 46755679931768486946665057)
          ·
            refine ⟨35066759948826365209998793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46755679931768486946665057 35066759948826365209998793)
            ·
              refine ⟨26300069961619773907499095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35066759948826365209998793 26300069961619773907499095)
              ·
                refine ⟨39450104942429660861248643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26300069961619773907499095 39450104942429660861248643)
                ·
                  refine ⟨59175157413644491291872965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39450104942429660861248643 59175157413644491291872965)
                  ·
                    refine ⟨11095342015058342117226181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59175157413644491291872965 11095342015058342117226181)
                    ·
                      refine ⟨2080376627823439146979909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11095342015058342117226181 2080376627823439146979909)
                      ·
                        rfl

theorem cell23_4051519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 1, 1, 4, 4].length) (baseStart_4051519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4051519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4051519 prefixEnd_4051519 := by exact prefixLift 4051519
  have htrace : WordTrace (prefixWord ++ tailWord_4051519) baseStart_4051519 baseEnd_4051519 := by
    simpa [prefixWord, tailWord_4051519, baseEnd_4051519] using wordTrace_append hprefix tailTrace_4051519
  have hstable : (prefixWord ++ tailWord_4051519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4051519).length < 2 ^ (prefixWord ++ tailWord_4051519).sum := by decide
  have hdescent : baseEnd_4051519 < baseStart_4051519 := by decide
  rcases family_descends (prefixWord ++ tailWord_4051519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4051556 : List Nat := [2, 3, 1, 1, 2, 2, 2, 2, 2, 3, 3]
def baseStart_4051556 : Nat := 118140960795 + 4051556 * 2 ^ 59
def prefixEnd_4051556 : Nat := 4983230072969 + 3 ^ 40 * 4051556 * 2
def baseEnd_4051556 : Nat := 2080395626607655502217239

theorem tailTrace_4051556 : CollatzResearch.WordTrace tailWord_4051556 prefixEnd_4051556 2080395626607655502217239 := by
  unfold tailWord_4051556
  simp only [CollatzResearch.WordTrace]
  refine ⟨73886193654956018760451261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98514924873274691680601681 73886193654956018760451261)
  ·
    refine ⟨27707322620608507035169223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73886193654956018760451261 27707322620608507035169223)
    ·
      refine ⟨41560983930912760552753835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27707322620608507035169223 41560983930912760552753835)
      ·
        refine ⟨62341475896369140829130753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41560983930912760552753835 62341475896369140829130753)
        ·
          refine ⟨46756106922276855621848065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62341475896369140829130753 46756106922276855621848065)
          ·
            refine ⟨35067080191707641716386049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46756106922276855621848065 35067080191707641716386049)
            ·
              refine ⟨26300310143780731287289537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35067080191707641716386049 26300310143780731287289537)
              ·
                refine ⟨19725232607835548465467153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26300310143780731287289537 19725232607835548465467153)
                ·
                  refine ⟨14793924455876661349100365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19725232607835548465467153 14793924455876661349100365)
                  ·
                    refine ⟨5547721670953748005912637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14793924455876661349100365 5547721670953748005912637)
                    ·
                      refine ⟨2080395626607655502217239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5547721670953748005912637 2080395626607655502217239)
                      ·
                        rfl

theorem cell23_4051556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 2, 2, 3, 3].length) (baseStart_4051556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4051556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4051556 prefixEnd_4051556 := by exact prefixLift 4051556
  have htrace : WordTrace (prefixWord ++ tailWord_4051556) baseStart_4051556 baseEnd_4051556 := by
    simpa [prefixWord, tailWord_4051556, baseEnd_4051556] using wordTrace_append hprefix tailTrace_4051556
  have hstable : (prefixWord ++ tailWord_4051556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4051556).length < 2 ^ (prefixWord ++ tailWord_4051556).sum := by decide
  have hdescent : baseEnd_4051556 < baseStart_4051556 := by decide
  rcases family_descends (prefixWord ++ tailWord_4051556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4051557 : List Nat := [1, 3, 1, 3, 4, 1, 2, 2, 2, 2, 2]
def baseStart_4051557 : Nat := 118140960795 + 4051557 * 2 ^ 59
def prefixEnd_4051557 : Nat := 4983230072969 + 3 ^ 40 * 4051557 * 2
def baseEnd_4051557 : Nat := 2080396140088309998304735

theorem tailTrace_4051557 : CollatzResearch.WordTrace tailWord_4051557 prefixEnd_4051557 2080396140088309998304735 := by
  unfold tailWord_4051557
  simp only [CollatzResearch.WordTrace]
  refine ⟨147772423782908414691688925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98514949188605609794459283 147772423782908414691688925)
  ·
    refine ⟨55414658918590655509383347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147772423782908414691688925 55414658918590655509383347)
    ·
      refine ⟨83121988377885983264075021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55414658918590655509383347 83121988377885983264075021)
      ·
        refine ⟨31170745641707243724028133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83121988377885983264075021 31170745641707243724028133)
        ·
          refine ⟨5844514807820108198255275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31170745641707243724028133 5844514807820108198255275)
          ·
            refine ⟨8766772211730162297382913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5844514807820108198255275 8766772211730162297382913)
            ·
              refine ⟨6575079158797621723037185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8766772211730162297382913 6575079158797621723037185)
              ·
                refine ⟨4931309369098216292277889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6575079158797621723037185 4931309369098216292277889)
                ·
                  refine ⟨3698482026823662219208417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4931309369098216292277889 3698482026823662219208417)
                  ·
                    refine ⟨2773861520117746664406313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3698482026823662219208417 2773861520117746664406313)
                    ·
                      refine ⟨2080396140088309998304735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2773861520117746664406313 2080396140088309998304735)
                      ·
                        rfl

theorem cell23_4051557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 2, 2, 2, 2, 2].length) (baseStart_4051557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4051557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4051557 prefixEnd_4051557 := by exact prefixLift 4051557
  have htrace : WordTrace (prefixWord ++ tailWord_4051557) baseStart_4051557 baseEnd_4051557 := by
    simpa [prefixWord, tailWord_4051557, baseEnd_4051557] using wordTrace_append hprefix tailTrace_4051557
  have hstable : (prefixWord ++ tailWord_4051557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4051557).length < 2 ^ (prefixWord ++ tailWord_4051557).sum := by decide
  have hdescent : baseEnd_4051557 < baseStart_4051557 := by decide
  rcases family_descends (prefixWord ++ tailWord_4051557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4051559 : List Nat := [1, 1, 5, 1, 1, 1, 1, 2, 3, 7]
def baseStart_4051559 : Nat := 118140960795 + 4051559 * 2 ^ 59
def prefixEnd_4051559 : Nat := 4983230072969 + 3 ^ 40 * 4051559 * 2
def baseEnd_4051559 : Nat := 693465722349872996826575

theorem tailTrace_4051559 : CollatzResearch.WordTrace tailWord_4051559 prefixEnd_4051559 693465722349872996826575 := by
  unfold tailWord_4051559
  simp only [CollatzResearch.WordTrace]
  refine ⟨147772496728901169033261731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98514997819267446022174487 147772496728901169033261731)
  ·
    refine ⟨221658745093351753549892597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147772496728901169033261731 221658745093351753549892597)
    ·
      refine ⟨20780507352501726895302431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 221658745093351753549892597 20780507352501726895302431)
      ·
        refine ⟨31170761028752590342953647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20780507352501726895302431 31170761028752590342953647)
        ·
          refine ⟨46756141543128885514430471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31170761028752590342953647 46756141543128885514430471)
          ·
            refine ⟨70134212314693328271645707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46756141543128885514430471 70134212314693328271645707)
            ·
              refine ⟨105201318472039992407468561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70134212314693328271645707 105201318472039992407468561)
              ·
                refine ⟨78900988854029994305601421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105201318472039992407468561 78900988854029994305601421)
                ·
                  refine ⟨29587870820261247864600533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78900988854029994305601421 29587870820261247864600533)
                  ·
                    refine ⟨693465722349872996826575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29587870820261247864600533 693465722349872996826575)
                    ·
                      rfl

theorem cell23_4051559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 3, 7].length) (baseStart_4051559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4051559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4051559 prefixEnd_4051559 := by exact prefixLift 4051559
  have htrace : WordTrace (prefixWord ++ tailWord_4051559) baseStart_4051559 baseEnd_4051559 := by
    simpa [prefixWord, tailWord_4051559, baseEnd_4051559] using wordTrace_append hprefix tailTrace_4051559
  have hstable : (prefixWord ++ tailWord_4051559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4051559).length < 2 ^ (prefixWord ++ tailWord_4051559).sum := by decide
  have hdescent : baseEnd_4051559 < baseStart_4051559 := by decide
  rcases family_descends (prefixWord ++ tailWord_4051559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4051596 : List Nat := [2, 2, 1, 2, 1, 1, 2, 5, 2, 1, 4]
def baseStart_4051596 : Nat := 118140960795 + 4051596 * 2 ^ 59
def prefixEnd_4051596 : Nat := 4983230072969 + 3 ^ 40 * 4051596 * 2
def baseEnd_4051596 : Nat := 2080416165833835345717055

theorem tailTrace_4051596 : CollatzResearch.WordTrace tailWord_4051596 prefixEnd_4051596 2080416165833835345717055 := by
  unfold tailWord_4051596
  simp only [CollatzResearch.WordTrace]
  refine ⟨73886923114883562176179321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98515897486511416234905761 73886923114883562176179321)
  ·
    refine ⟨55415192336162671632134491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73886923114883562176179321 55415192336162671632134491)
    ·
      refine ⟨83122788504244007448201737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55415192336162671632134491 83122788504244007448201737)
      ·
        refine ⟨62342091378183005586151303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83122788504244007448201737 62342091378183005586151303)
        ·
          refine ⟨93513137067274508379226955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62342091378183005586151303 93513137067274508379226955)
          ·
            refine ⟨140269705600911762568840433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93513137067274508379226955 140269705600911762568840433)
            ·
              refine ⟨105202279200683821926630325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140269705600911762568840433 105202279200683821926630325)
              ·
                refine ⟨9862713675064108305621593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 105202279200683821926630325 9862713675064108305621593)
                ·
                  refine ⟨7397035256298081229216195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9862713675064108305621593 7397035256298081229216195)
                  ·
                    refine ⟨11095552884447121843824293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7397035256298081229216195 11095552884447121843824293)
                    ·
                      refine ⟨2080416165833835345717055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11095552884447121843824293 2080416165833835345717055)
                      ·
                        rfl

theorem cell23_4051596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 5, 2, 1, 4].length) (baseStart_4051596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4051596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4051596 prefixEnd_4051596 := by exact prefixLift 4051596
  have htrace : WordTrace (prefixWord ++ tailWord_4051596) baseStart_4051596 baseEnd_4051596 := by
    simpa [prefixWord, tailWord_4051596, baseEnd_4051596] using wordTrace_append hprefix tailTrace_4051596
  have hstable : (prefixWord ++ tailWord_4051596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4051596).length < 2 ^ (prefixWord ++ tailWord_4051596).sum := by decide
  have hdescent : baseEnd_4051596 < baseStart_4051596 := by decide
  rcases family_descends (prefixWord ++ tailWord_4051596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4051609 : List Nat := [1, 2, 1, 2, 1, 2, 3, 1, 1, 3, 6]
def baseStart_4051609 : Nat := 118140960795 + 4051609 * 2 ^ 59
def prefixEnd_4051609 : Nat := 4983230072969 + 3 ^ 40 * 4051609 * 2
def baseEnd_4051609 : Nat := 2080422841082343794854495

theorem tailTrace_4051609 : CollatzResearch.WordTrace tailWord_4051609 prefixEnd_4051609 2080422841082343794854495 := by
  unfold tailWord_4051609
  simp only [CollatzResearch.WordTrace]
  refine ⟨147774320378720027572581881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98516213585813351715054587 147774320378720027572581881)
  ·
    refine ⟨110830740284040020679436411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147774320378720027572581881 110830740284040020679436411)
    ·
      refine ⟨166246110426060031019154617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110830740284040020679436411 166246110426060031019154617)
      ·
        refine ⟨124684582819545023264365963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166246110426060031019154617 124684582819545023264365963)
        ·
          refine ⟨187026874229317534896548945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124684582819545023264365963 187026874229317534896548945)
          ·
            refine ⟨140270155671988151172411709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187026874229317534896548945 140270155671988151172411709)
            ·
              refine ⟨52601308376995556689654391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140270155671988151172411709 52601308376995556689654391)
              ·
                refine ⟨78901962565493335034481587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52601308376995556689654391 78901962565493335034481587)
                ·
                  refine ⟨118352943848240002551722381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78901962565493335034481587 118352943848240002551722381)
                  ·
                    refine ⟨44382353943090000956895893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 118352943848240002551722381 44382353943090000956895893)
                    ·
                      refine ⟨2080422841082343794854495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44382353943090000956895893 2080422841082343794854495)
                      ·
                        rfl

theorem cell23_4051609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 3, 6].length) (baseStart_4051609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4051609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4051609 prefixEnd_4051609 := by exact prefixLift 4051609
  have htrace : WordTrace (prefixWord ++ tailWord_4051609) baseStart_4051609 baseEnd_4051609 := by
    simpa [prefixWord, tailWord_4051609, baseEnd_4051609] using wordTrace_append hprefix tailTrace_4051609
  have hstable : (prefixWord ++ tailWord_4051609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4051609).length < 2 ^ (prefixWord ++ tailWord_4051609).sum := by decide
  have hdescent : baseEnd_4051609 < baseStart_4051609 := by decide
  rcases family_descends (prefixWord ++ tailWord_4051609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4051613 : List Nat := [1, 4, 2, 1, 1, 1, 3, 2, 2, 4, 2]
def baseStart_4051613 : Nat := 118140960795 + 4051613 * 2 ^ 59
def prefixEnd_4051613 : Nat := 4983230072969 + 3 ^ 40 * 4051613 * 2
def baseEnd_4051613 : Nat := 2080424895004961779204477

theorem tailTrace_4051613 : CollatzResearch.WordTrace tailWord_4051613 prefixEnd_4051613 2080424895004961779204477 := by
  unfold tailWord_4051613
  simp only [CollatzResearch.WordTrace]
  refine ⟨147774466270705536255727493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98516310847137024170484995 147774466270705536255727493)
  ·
    refine ⟨27707712425757288047948905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147774466270705536255727493 27707712425757288047948905)
    ·
      refine ⟨20780784319317966035961679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27707712425757288047948905 20780784319317966035961679)
      ·
        refine ⟨31171176478976949053942519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20780784319317966035961679 31171176478976949053942519)
        ·
          refine ⟨46756764718465423580913779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31171176478976949053942519 46756764718465423580913779)
          ·
            refine ⟨70135147077698135371370669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46756764718465423580913779 70135147077698135371370669)
            ·
              refine ⟨26300680154136800764264001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70135147077698135371370669 26300680154136800764264001)
              ·
                refine ⟨19725510115602600573198001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26300680154136800764264001 19725510115602600573198001)
                ·
                  refine ⟨14794132586701950429898501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19725510115602600573198001 14794132586701950429898501)
                  ·
                    refine ⟨2773899860006615705605969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14794132586701950429898501 2773899860006615705605969)
                    ·
                      refine ⟨2080424895004961779204477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2773899860006615705605969 2080424895004961779204477)
                      ·
                        rfl

theorem cell23_4051613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 2, 2, 4, 2].length) (baseStart_4051613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4051613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4051613 prefixEnd_4051613 := by exact prefixLift 4051613
  have htrace : WordTrace (prefixWord ++ tailWord_4051613) baseStart_4051613 baseEnd_4051613 := by
    simpa [prefixWord, tailWord_4051613, baseEnd_4051613] using wordTrace_append hprefix tailTrace_4051613
  have hstable : (prefixWord ++ tailWord_4051613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4051613).length < 2 ^ (prefixWord ++ tailWord_4051613).sum := by decide
  have hdescent : baseEnd_4051613 < baseStart_4051613 := by decide
  rcases family_descends (prefixWord ++ tailWord_4051613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4051696 : List Nat := [2, 1, 1, 1, 3, 1, 4, 3, 1, 6]
def baseStart_4051696 : Nat := 118140960795 + 4051696 * 2 ^ 59
def prefixEnd_4051696 : Nat := 4983230072969 + 3 ^ 40 * 4051696 * 2
def baseEnd_4051696 : Nat := 693489171299761651488865

theorem tailTrace_4051696 : CollatzResearch.WordTrace tailWord_4051696 prefixEnd_4051696 693489171299761651488865 := by
  unfold tailWord_4051696
  simp only [CollatzResearch.WordTrace]
  refine ⟨73888746764702420715499471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98518329019603227620665961 73888746764702420715499471)
  ·
    refine ⟨110833120147053631073249207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73888746764702420715499471 110833120147053631073249207)
    ·
      refine ⟨166249680220580446609873811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110833120147053631073249207 166249680220580446609873811)
      ·
        refine ⟨249374520330870669914810717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166249680220580446609873811 249374520330870669914810717)
        ·
          refine ⟨93515445124076501218054019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 249374520330870669914810717 93515445124076501218054019)
          ·
            refine ⟨140273167686114751827081029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93515445124076501218054019 140273167686114751827081029)
            ·
              refine ⟨26301218941146515967577693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 140273167686114751827081029 26301218941146515967577693)
              ·
                refine ⟨9862957102929943487841635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26301218941146515967577693 9862957102929943487841635)
                ·
                  refine ⟨14794435654394915231762453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9862957102929943487841635 14794435654394915231762453)
                  ·
                    refine ⟨693489171299761651488865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14794435654394915231762453 693489171299761651488865)
                    ·
                      rfl

theorem cell23_4051696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 3, 1, 6].length) (baseStart_4051696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4051696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4051696 prefixEnd_4051696 := by exact prefixLift 4051696
  have htrace : WordTrace (prefixWord ++ tailWord_4051696) baseStart_4051696 baseEnd_4051696 := by
    simpa [prefixWord, tailWord_4051696, baseEnd_4051696] using wordTrace_append hprefix tailTrace_4051696
  have hstable : (prefixWord ++ tailWord_4051696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4051696).length < 2 ^ (prefixWord ++ tailWord_4051696).sum := by decide
  have hdescent : baseEnd_4051696 < baseStart_4051696 := by decide
  rcases family_descends (prefixWord ++ tailWord_4051696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4051706 : List Nat := [3, 1, 1, 1, 1, 3, 2, 2, 3, 1, 5]
def baseStart_4051706 : Nat := 118140960795 + 4051706 * 2 ^ 59
def prefixEnd_4051706 : Nat := 4983230072969 + 3 ^ 40 * 4051706 * 2
def baseEnd_4051706 : Nat := 2080472648705829915341549

theorem tailTrace_4051706 : CollatzResearch.WordTrace tailWord_4051706 prefixEnd_4051706 2080472648705829915341549 := by
  unfold tailWord_4051706
  simp only [CollatzResearch.WordTrace]
  refine ⟨36944464564842153284715743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98518572172912408759241981 36944464564842153284715743)
  ·
    refine ⟨55416696847263229927073615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36944464564842153284715743 55416696847263229927073615)
    ·
      refine ⟨83125045270894844890610423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55416696847263229927073615 83125045270894844890610423)
      ·
        refine ⟨124687567906342267335915635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83125045270894844890610423 124687567906342267335915635)
        ·
          refine ⟨187031351859513401003873453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124687567906342267335915635 187031351859513401003873453)
          ·
            refine ⟨70136756947317525376452545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 187031351859513401003873453 70136756947317525376452545)
            ·
              refine ⟨52602567710488144032339409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70136756947317525376452545 52602567710488144032339409)
              ·
                refine ⟨39451925782866108024254557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52602567710488144032339409 39451925782866108024254557)
                ·
                  refine ⟨14794472168574790509095459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39451925782866108024254557 14794472168574790509095459)
                  ·
                    refine ⟨22191708252862185763643189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14794472168574790509095459 22191708252862185763643189)
                    ·
                      refine ⟨2080472648705829915341549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22191708252862185763643189 2080472648705829915341549)
                      ·
                        rfl

theorem cell23_4051706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 2, 3, 1, 5].length) (baseStart_4051706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4051706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4051706 prefixEnd_4051706 := by exact prefixLift 4051706
  have htrace : WordTrace (prefixWord ++ tailWord_4051706) baseStart_4051706 baseEnd_4051706 := by
    simpa [prefixWord, tailWord_4051706, baseEnd_4051706] using wordTrace_append hprefix tailTrace_4051706
  have hstable : (prefixWord ++ tailWord_4051706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4051706).length < 2 ^ (prefixWord ++ tailWord_4051706).sum := by decide
  have hdescent : baseEnd_4051706 < baseStart_4051706 := by decide
  rcases family_descends (prefixWord ++ tailWord_4051706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4051743 : List Nat := [1, 1, 2, 4, 2, 4, 1, 8]
def baseStart_4051743 : Nat := 118140960795 + 4051743 * 2 ^ 59
def prefixEnd_4051743 : Nat := 4983230072969 + 3 ^ 40 * 4051743 * 2
def baseEnd_4051743 : Nat := 77055246203335047058477

theorem tailTrace_4051743 : CollatzResearch.WordTrace tailWord_4051743 prefixEnd_4051743 77055246203335047058477 := by
  unfold tailWord_4051743
  simp only [CollatzResearch.WordTrace]
  refine ⟨147779207760234568457959883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98519471840156378971973255 147779207760234568457959883)
  ·
    refine ⟨221668811640351852686939825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147779207760234568457959883 221668811640351852686939825)
    ·
      refine ⟨166251608730263889515204869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221668811640351852686939825 166251608730263889515204869)
      ·
        refine ⟨31172176636924479284100913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 166251608730263889515204869 31172176636924479284100913)
        ·
          refine ⟨23379132477693359463075685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31172176636924479284100913 23379132477693359463075685)
          ·
            refine ⟨4383587339567504899326691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23379132477693359463075685 4383587339567504899326691)
            ·
              refine ⟨6575381009351257348990037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4383587339567504899326691 6575381009351257348990037)
              ·
                refine ⟨77055246203335047058477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6575381009351257348990037 77055246203335047058477)
                ·
                  rfl

theorem cell23_4051743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 1, 8].length) (baseStart_4051743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4051743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4051743 prefixEnd_4051743 := by exact prefixLift 4051743
  have htrace : WordTrace (prefixWord ++ tailWord_4051743) baseStart_4051743 baseEnd_4051743 := by
    simpa [prefixWord, tailWord_4051743, baseEnd_4051743] using wordTrace_append hprefix tailTrace_4051743
  have hstable : (prefixWord ++ tailWord_4051743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4051743).length < 2 ^ (prefixWord ++ tailWord_4051743).sum := by decide
  have hdescent : baseEnd_4051743 < baseStart_4051743 := by decide
  rcases family_descends (prefixWord ++ tailWord_4051743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4051756 : List Nat := [2, 2, 1, 1, 1, 4, 1, 2, 2, 7]
def baseStart_4051756 : Nat := 118140960795 + 4051756 * 2 ^ 59
def prefixEnd_4051756 : Nat := 4983230072969 + 3 ^ 40 * 4051756 * 2
def baseEnd_4051756 : Nat := 693499440912851573238773

theorem tailTrace_4051756 : CollatzResearch.WordTrace tailWord_4051756 prefixEnd_4051756 693499440912851573238773 := by
  unfold tailWord_4051756
  simp only [CollatzResearch.WordTrace]
  refine ⟨73889840954593735839091561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98519787939458314452122081 73889840954593735839091561)
  ·
    refine ⟨55417380715945301879318671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73889840954593735839091561 55417380715945301879318671)
    ·
      refine ⟨83126071073917952818978007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55417380715945301879318671 83126071073917952818978007)
      ·
        refine ⟨124689106610876929228467011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83126071073917952818978007 124689106610876929228467011)
        ·
          refine ⟨187033659916315393842700517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124689106610876929228467011 187033659916315393842700517)
          ·
            refine ⟨35068811234309136345506347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 187033659916315393842700517 35068811234309136345506347)
            ·
              refine ⟨52603216851463704518259521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35068811234309136345506347 52603216851463704518259521)
              ·
                refine ⟨39452412638597778388694641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52603216851463704518259521 39452412638597778388694641)
                ·
                  refine ⟨29589309478948333791520981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39452412638597778388694641 29589309478948333791520981)
                  ·
                    refine ⟨693499440912851573238773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29589309478948333791520981 693499440912851573238773)
                    ·
                      rfl

theorem cell23_4051756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 7].length) (baseStart_4051756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4051756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4051756 prefixEnd_4051756 := by exact prefixLift 4051756
  have htrace : WordTrace (prefixWord ++ tailWord_4051756) baseStart_4051756 baseEnd_4051756 := by
    simpa [prefixWord, tailWord_4051756, baseEnd_4051756] using wordTrace_append hprefix tailTrace_4051756
  have hstable : (prefixWord ++ tailWord_4051756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4051756).length < 2 ^ (prefixWord ++ tailWord_4051756).sum := by decide
  have hdescent : baseEnd_4051756 < baseStart_4051756 := by decide
  rcases family_descends (prefixWord ++ tailWord_4051756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4051813 : List Nat := [1, 3, 1, 3, 1, 1, 2, 2, 2, 4, 3]
def baseStart_4051813 : Nat := 118140960795 + 4051813 * 2 ^ 59
def prefixEnd_4051813 : Nat := 4983230072969 + 3 ^ 40 * 4051813 * 2
def baseEnd_4051813 : Nat := 2080527591135860996703557

theorem tailTrace_4051813 : CollatzResearch.WordTrace tailWord_4051813 prefixEnd_4051813 2080527591135860996703557 := by
  unfold tailWord_4051813
  simp only [CollatzResearch.WordTrace]
  refine ⟨147781760869980970413008093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98521173913320646942005395 147781760869980970413008093)
  ·
    refine ⟨55418160326242863904878035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147781760869980970413008093 55418160326242863904878035)
    ·
      refine ⟨83127240489364295857317053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55418160326242863904878035 83127240489364295857317053)
      ·
        refine ⟨31172715183511610946493895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83127240489364295857317053 31172715183511610946493895)
        ·
          refine ⟨46759072775267416419740843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31172715183511610946493895 46759072775267416419740843)
          ·
            refine ⟨70138609162901124629611265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46759072775267416419740843 70138609162901124629611265)
            ·
              refine ⟨52603956872175843472208449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70138609162901124629611265 52603956872175843472208449)
              ·
                refine ⟨39452967654131882604156337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52603956872175843472208449 39452967654131882604156337)
                ·
                  refine ⟨29589725740598911953117253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39452967654131882604156337 29589725740598911953117253)
                  ·
                    refine ⟨5548073576362295991209485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29589725740598911953117253 5548073576362295991209485)
                    ·
                      refine ⟨2080527591135860996703557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5548073576362295991209485 2080527591135860996703557)
                      ·
                        rfl

theorem cell23_4051813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 2, 2, 4, 3].length) (baseStart_4051813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4051813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4051813 prefixEnd_4051813 := by exact prefixLift 4051813
  have htrace : WordTrace (prefixWord ++ tailWord_4051813) baseStart_4051813 baseEnd_4051813 := by
    simpa [prefixWord, tailWord_4051813, baseEnd_4051813] using wordTrace_append hprefix tailTrace_4051813
  have hstable : (prefixWord ++ tailWord_4051813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4051813).length < 2 ^ (prefixWord ++ tailWord_4051813).sum := by decide
  have hdescent : baseEnd_4051813 < baseStart_4051813 := by decide
  rcases family_descends (prefixWord ++ tailWord_4051813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4051830 : List Nat := [5, 1, 1, 3, 1, 1, 1, 1, 1, 3, 5]
def baseStart_4051830 : Nat := 118140960795 + 4051830 * 2 ^ 59
def prefixEnd_4051830 : Nat := 4983230072969 + 3 ^ 40 * 4051830 * 2
def baseEnd_4051830 : Nat := 2080536320306987430190979

theorem tailTrace_4051830 : CollatzResearch.WordTrace tailWord_4051830 prefixEnd_4051830 2080536320306987430190979 := by
  unfold tailWord_4051830
  simp only [CollatzResearch.WordTrace]
  refine ⟨9236398806932461394773559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 98521587273946254877584629 9236398806932461394773559)
  ·
    refine ⟨13854598210398692092160339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9236398806932461394773559 13854598210398692092160339)
    ·
      refine ⟨20781897315598038138240509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13854598210398692092160339 20781897315598038138240509)
      ·
        refine ⟨7793211493349264301840191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20781897315598038138240509 7793211493349264301840191)
        ·
          refine ⟨11689817240023896452760287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7793211493349264301840191 11689817240023896452760287)
          ·
            refine ⟨17534725860035844679140431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11689817240023896452760287 17534725860035844679140431)
            ·
              refine ⟨26302088790053767018710647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17534725860035844679140431 26302088790053767018710647)
              ·
                refine ⟨39453133185080650528065971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26302088790053767018710647 39453133185080650528065971)
                ·
                  refine ⟨59179699777620975792098957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39453133185080650528065971 59179699777620975792098957)
                  ·
                    refine ⟨22192387416607865922037109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59179699777620975792098957 22192387416607865922037109)
                    ·
                      refine ⟨2080536320306987430190979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22192387416607865922037109 2080536320306987430190979)
                      ·
                        rfl

theorem cell23_4051830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_4051830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4051830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4051830 prefixEnd_4051830 := by exact prefixLift 4051830
  have htrace : WordTrace (prefixWord ++ tailWord_4051830) baseStart_4051830 baseEnd_4051830 := by
    simpa [prefixWord, tailWord_4051830, baseEnd_4051830] using wordTrace_append hprefix tailTrace_4051830
  have hstable : (prefixWord ++ tailWord_4051830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4051830).length < 2 ^ (prefixWord ++ tailWord_4051830).sum := by decide
  have hdescent : baseEnd_4051830 < baseStart_4051830 := by decide
  rcases family_descends (prefixWord ++ tailWord_4051830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4051850 : List Nat := [3, 1, 2, 4, 1, 1, 3, 1, 7]
def baseStart_4051850 : Nat := 118140960795 + 4051850 * 2 ^ 59
def prefixEnd_4051850 : Nat := 4983230072969 + 3 ^ 40 * 4051850 * 2
def baseEnd_4051850 : Nat := 231171843324453039104543

theorem tailTrace_4051850 : CollatzResearch.WordTrace tailWord_4051850 prefixEnd_4051850 231171843324453039104543 := by
  unfold tailWord_4051850
  simp only [CollatzResearch.WordTrace]
  refine ⟨36945777592711731433026251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98522073580564617154736669 36945777592711731433026251)
  ·
    refine ⟨55418666389067597149539377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36945777592711731433026251 55418666389067597149539377)
    ·
      refine ⟨41563999791800697862154533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55418666389067597149539377 41563999791800697862154533)
      ·
        refine ⟨7793249960962630849153975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41563999791800697862154533 7793249960962630849153975)
        ·
          refine ⟨11689874941443946273730963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7793249960962630849153975 11689874941443946273730963)
          ·
            refine ⟨17534812412165919410596445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11689874941443946273730963 17534812412165919410596445)
            ·
              refine ⟨6575554654562219778973667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17534812412165919410596445 6575554654562219778973667)
              ·
                refine ⟨9863331981843329668460501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6575554654562219778973667 9863331981843329668460501)
                ·
                  refine ⟨231171843324453039104543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9863331981843329668460501 231171843324453039104543)
                  ·
                    rfl

theorem cell23_4051850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3, 1, 7].length) (baseStart_4051850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4051850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4051850 prefixEnd_4051850 := by exact prefixLift 4051850
  have htrace : WordTrace (prefixWord ++ tailWord_4051850) baseStart_4051850 baseEnd_4051850 := by
    simpa [prefixWord, tailWord_4051850, baseEnd_4051850] using wordTrace_append hprefix tailTrace_4051850
  have hstable : (prefixWord ++ tailWord_4051850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4051850).length < 2 ^ (prefixWord ++ tailWord_4051850).sum := by decide
  have hdescent : baseEnd_4051850 < baseStart_4051850 := by decide
  rcases family_descends (prefixWord ++ tailWord_4051850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4051860 : List Nat := [2, 4, 2, 1, 1, 1, 2, 1, 1, 5, 3]
def baseStart_4051860 : Nat := 118140960795 + 4051860 * 2 ^ 59
def prefixEnd_4051860 : Nat := 4983230072969 + 3 ^ 40 * 4051860 * 2
def baseEnd_4051860 : Nat := 2080551724726622312815841

theorem tailTrace_4051860 : CollatzResearch.WordTrace tailWord_4051860 prefixEnd_4051860 2080551724726622312815841 := by
  unfold tailWord_4051860
  simp only [CollatzResearch.WordTrace]
  refine ⟨73891737550405348719984517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98522316733873798293312689 73891737550405348719984517)
  ·
    refine ⟨13854700790701002884997097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73891737550405348719984517 13854700790701002884997097)
    ·
      refine ⟨10391025593025752163747823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13854700790701002884997097 10391025593025752163747823)
      ·
        refine ⟨15586538389538628245621735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10391025593025752163747823 15586538389538628245621735)
        ·
          refine ⟨23379807584307942368432603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15586538389538628245621735 23379807584307942368432603)
          ·
            refine ⟨35069711376461913552648905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23379807584307942368432603 35069711376461913552648905)
            ·
              refine ⟨26302283532346435164486679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35069711376461913552648905 26302283532346435164486679)
              ·
                refine ⟨39453425298519652746730019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26302283532346435164486679 39453425298519652746730019)
                ·
                  refine ⟨59180137947779479120095029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39453425298519652746730019 59180137947779479120095029)
                  ·
                    refine ⟨5548137932604326167508909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59180137947779479120095029 5548137932604326167508909)
                    ·
                      refine ⟨2080551724726622312815841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5548137932604326167508909 2080551724726622312815841)
                      ·
                        rfl

theorem cell23_4051860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 1, 1, 5, 3].length) (baseStart_4051860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4051860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4051860 prefixEnd_4051860 := by exact prefixLift 4051860
  have htrace : WordTrace (prefixWord ++ tailWord_4051860) baseStart_4051860 baseEnd_4051860 := by
    simpa [prefixWord, tailWord_4051860, baseEnd_4051860] using wordTrace_append hprefix tailTrace_4051860
  have hstable : (prefixWord ++ tailWord_4051860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4051860).length < 2 ^ (prefixWord ++ tailWord_4051860).sum := by decide
  have hdescent : baseEnd_4051860 < baseStart_4051860 := by decide
  rcases family_descends (prefixWord ++ tailWord_4051860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4051861 : List Nat := [1, 3, 2, 1, 1, 6, 2, 1, 2, 2, 2]
def baseStart_4051861 : Nat := 118140960795 + 4051861 * 2 ^ 59
def prefixEnd_4051861 : Nat := 4983230072969 + 3 ^ 40 * 4051861 * 2
def baseEnd_4051861 : Nat := 2080552238207276808903337

theorem tailTrace_4051861 : CollatzResearch.WordTrace tailWord_4051861 prefixEnd_4051861 2080552238207276808903337 := by
  unfold tailWord_4051861
  simp only [CollatzResearch.WordTrace]
  refine ⟨147783511573807074610755437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98522341049204716407170291 147783511573807074610755437)
  ·
    refine ⟨55418816840177652979033289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147783511573807074610755437 55418816840177652979033289)
    ·
      refine ⟨41564112630133239734274967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55418816840177652979033289 41564112630133239734274967)
      ·
        refine ⟨62346168945199859601412451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41564112630133239734274967 62346168945199859601412451)
        ·
          refine ⟨93519253417799789402118677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62346168945199859601412451 93519253417799789402118677)
          ·
            refine ⟨4383715003959365128224313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 93519253417799789402118677 4383715003959365128224313)
            ·
              refine ⟨3287786252969523846168235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4383715003959365128224313 3287786252969523846168235)
              ·
                refine ⟨4931679379454285769252353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3287786252969523846168235 4931679379454285769252353)
                ·
                  refine ⟨3698759534590714326939265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4931679379454285769252353 3698759534590714326939265)
                  ·
                    refine ⟨2774069650943035745204449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3698759534590714326939265 2774069650943035745204449)
                    ·
                      refine ⟨2080552238207276808903337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2774069650943035745204449 2080552238207276808903337)
                      ·
                        rfl

theorem cell23_4051861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 2, 1, 2, 2, 2].length) (baseStart_4051861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4051861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4051861 prefixEnd_4051861 := by exact prefixLift 4051861
  have htrace : WordTrace (prefixWord ++ tailWord_4051861) baseStart_4051861 baseEnd_4051861 := by
    simpa [prefixWord, tailWord_4051861, baseEnd_4051861] using wordTrace_append hprefix tailTrace_4051861
  have hstable : (prefixWord ++ tailWord_4051861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4051861).length < 2 ^ (prefixWord ++ tailWord_4051861).sum := by decide
  have hdescent : baseEnd_4051861 < baseStart_4051861 := by decide
  rcases family_descends (prefixWord ++ tailWord_4051861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4051863 : List Nat := [1, 1, 3, 3, 1, 2, 1, 2, 4, 5]
def baseStart_4051863 : Nat := 118140960795 + 4051863 * 2 ^ 59
def prefixEnd_4051863 : Nat := 4983230072969 + 3 ^ 40 * 4051863 * 2
def baseEnd_4051863 : Nat := 693517755056195267026109

theorem tailTrace_4051863 : CollatzResearch.WordTrace tailWord_4051863 prefixEnd_4051863 693517755056195267026109 := by
  unfold tailWord_4051863
  simp only [CollatzResearch.WordTrace]
  refine ⟨147783584519799828952328243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98522389679866552634885495 147783584519799828952328243)
  ·
    refine ⟨221675376779699743428492365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147783584519799828952328243 221675376779699743428492365)
    ·
      refine ⟨83128266292387403785684637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221675376779699743428492365 83128266292387403785684637)
      ·
        refine ⟨31173099859645276419631739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83128266292387403785684637 31173099859645276419631739)
        ·
          refine ⟨46759649789467914629447609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31173099859645276419631739 46759649789467914629447609)
          ·
            refine ⟨35069737342100935972085707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46759649789467914629447609 35069737342100935972085707)
            ·
              refine ⟨52604606013151403958128561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35069737342100935972085707 52604606013151403958128561)
              ·
                refine ⟨39453454509863552968596421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52604606013151403958128561 39453454509863552968596421)
                ·
                  refine ⟨7397522720599416181611829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39453454509863552968596421 7397522720599416181611829)
                  ·
                    refine ⟨693517755056195267026109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7397522720599416181611829 693517755056195267026109)
                    ·
                      rfl

theorem cell23_4051863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 2, 4, 5].length) (baseStart_4051863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4051863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4051863 prefixEnd_4051863 := by exact prefixLift 4051863
  have htrace : WordTrace (prefixWord ++ tailWord_4051863) baseStart_4051863 baseEnd_4051863 := by
    simpa [prefixWord, tailWord_4051863, baseEnd_4051863] using wordTrace_append hprefix tailTrace_4051863
  have hstable : (prefixWord ++ tailWord_4051863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4051863).length < 2 ^ (prefixWord ++ tailWord_4051863).sum := by decide
  have hdescent : baseEnd_4051863 < baseStart_4051863 := by decide
  rcases family_descends (prefixWord ++ tailWord_4051863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4051883 : List Nat := [1, 1, 1, 1, 2, 1, 1, 4, 6, 1, 4]
def baseStart_4051883 : Nat := 118140960795 + 4051883 * 2 ^ 59
def prefixEnd_4051883 : Nat := 4983230072969 + 3 ^ 40 * 4051883 * 2
def baseEnd_4051883 : Nat := 2080563534781675722828235

theorem tailTrace_4051883 : CollatzResearch.WordTrace tailWord_4051883 prefixEnd_4051883 2080563534781675722828235 := by
  unfold tailWord_4051883
  simp only [CollatzResearch.WordTrace]
  refine ⟨147784313979727372368056303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98522875986484914912037535 147784313979727372368056303)
  ·
    refine ⟨221676470969591058552084455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147784313979727372368056303 221676470969591058552084455)
    ·
      refine ⟨332514706454386587828126683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221676470969591058552084455 332514706454386587828126683)
      ·
        refine ⟨498772059681579881742190025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332514706454386587828126683 498772059681579881742190025)
        ·
          refine ⟨374079044761184911306642519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 498772059681579881742190025 374079044761184911306642519)
          ·
            refine ⟨561118567141777366959963779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 374079044761184911306642519 561118567141777366959963779)
            ·
              refine ⟨841677850712666050439945669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 561118567141777366959963779 841677850712666050439945669)
              ·
                refine ⟨157814597008624884457489813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 841677850712666050439945669 157814597008624884457489813)
                ·
                  refine ⟨7397559234779291458944835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 157814597008624884457489813 7397559234779291458944835)
                  ·
                    refine ⟨11096338852168937188417253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7397559234779291458944835 11096338852168937188417253)
                    ·
                      refine ⟨2080563534781675722828235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11096338852168937188417253 2080563534781675722828235)
                      ·
                        rfl

theorem cell23_4051883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 6, 1, 4].length) (baseStart_4051883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4051883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4051883 prefixEnd_4051883 := by exact prefixLift 4051883
  have htrace : WordTrace (prefixWord ++ tailWord_4051883) baseStart_4051883 baseEnd_4051883 := by
    simpa [prefixWord, tailWord_4051883, baseEnd_4051883] using wordTrace_append hprefix tailTrace_4051883
  have hstable : (prefixWord ++ tailWord_4051883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4051883).length < 2 ^ (prefixWord ++ tailWord_4051883).sum := by decide
  have hdescent : baseEnd_4051883 < baseStart_4051883 := by decide
  rcases family_descends (prefixWord ++ tailWord_4051883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4051901 : List Nat := [1, 4, 1, 2, 5, 1, 2, 2, 5]
def baseStart_4051901 : Nat := 118140960795 + 4051901 * 2 ^ 59
def prefixEnd_4051901 : Nat := 4983230072969 + 3 ^ 40 * 4051901 * 2
def baseEnd_4051901 : Nat := 231174753048161850267017

theorem tailTrace_4051901 : CollatzResearch.WordTrace tailWord_4051901 prefixEnd_4051901 231174753048161850267017 := by
  unfold tailWord_4051901
  simp only [CollatzResearch.WordTrace]
  refine ⟨147784970493662161442211557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98523313662441440961474371 147784970493662161442211557)
  ·
    refine ⟨27709681967561655270414667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147784970493662161442211557 27709681967561655270414667)
    ·
      refine ⟨41564522951342482905622001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27709681967561655270414667 41564522951342482905622001)
      ·
        refine ⟨31173392213506862179216501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41564522951342482905622001 31173392213506862179216501)
        ·
          refine ⟨2922505520016268329301547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31173392213506862179216501 2922505520016268329301547)
          ·
            refine ⟨4383758280024402493952321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2922505520016268329301547 4383758280024402493952321)
            ·
              refine ⟨3287818710018301870464241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4383758280024402493952321 3287818710018301870464241)
              ·
                refine ⟨2465864032513726402848181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3287818710018301870464241 2465864032513726402848181)
                ·
                  refine ⟨231174753048161850267017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2465864032513726402848181 231174753048161850267017)
                  ·
                    rfl

theorem cell23_4051901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 2, 2, 5].length) (baseStart_4051901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4051901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4051901 prefixEnd_4051901 := by exact prefixLift 4051901
  have htrace : WordTrace (prefixWord ++ tailWord_4051901) baseStart_4051901 baseEnd_4051901 := by
    simpa [prefixWord, tailWord_4051901, baseEnd_4051901] using wordTrace_append hprefix tailTrace_4051901
  have hstable : (prefixWord ++ tailWord_4051901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4051901).length < 2 ^ (prefixWord ++ tailWord_4051901).sum := by decide
  have hdescent : baseEnd_4051901 < baseStart_4051901 := by decide
  rcases family_descends (prefixWord ++ tailWord_4051901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4051983 : List Nat := [1, 1, 2, 1, 1, 1, 2, 1, 7, 6]
def baseStart_4051983 : Nat := 118140960795 + 4051983 * 2 ^ 59
def prefixEnd_4051983 : Nat := 4983230072969 + 3 ^ 40 * 4051983 * 2
def baseEnd_4051983 : Nat := 693538294282375110525925

theorem tailTrace_4051983 : CollatzResearch.WordTrace tailWord_4051983 prefixEnd_4051983 693538294282375110525925 := by
  unfold tailWord_4051983
  simp only [CollatzResearch.WordTrace]
  refine ⟨147787961279365089446696603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98525307519576726297797735 147787961279365089446696603)
  ·
    refine ⟨221681941919047634170044905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147787961279365089446696603 221681941919047634170044905)
    ·
      refine ⟨166261456439285725627533679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221681941919047634170044905 166261456439285725627533679)
      ·
        refine ⟨249392184658928588441300519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166261456439285725627533679 249392184658928588441300519)
        ·
          refine ⟨374088276988392882661950779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249392184658928588441300519 374088276988392882661950779)
          ·
            refine ⟨561132415482589323992926169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 374088276988392882661950779 561132415482589323992926169)
            ·
              refine ⟨420849311611941992994694627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 561132415482589323992926169 420849311611941992994694627)
              ·
                refine ⟨631273967417912989492041941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 420849311611941992994694627 631273967417912989492041941)
                ·
                  refine ⟨14795483611357335691219733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 631273967417912989492041941 14795483611357335691219733)
                  ·
                    refine ⟨693538294282375110525925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14795483611357335691219733 693538294282375110525925)
                    ·
                      rfl

theorem cell23_4051983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 7, 6].length) (baseStart_4051983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4051983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4051983 prefixEnd_4051983 := by exact prefixLift 4051983
  have htrace : WordTrace (prefixWord ++ tailWord_4051983) baseStart_4051983 baseEnd_4051983 := by
    simpa [prefixWord, tailWord_4051983, baseEnd_4051983] using wordTrace_append hprefix tailTrace_4051983
  have hstable : (prefixWord ++ tailWord_4051983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4051983).length < 2 ^ (prefixWord ++ tailWord_4051983).sum := by decide
  have hdescent : baseEnd_4051983 < baseStart_4051983 := by decide
  rcases family_descends (prefixWord ++ tailWord_4051983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4052001 : List Nat := [1, 2, 3, 2, 3, 1, 3, 3, 1, 1, 3]
def baseStart_4052001 : Nat := 118140960795 + 4052001 * 2 ^ 59
def prefixEnd_4052001 : Nat := 4983230072969 + 3 ^ 40 * 4052001 * 2
def baseEnd_4052001 : Nat := 2080624125498906261152693

theorem tailTrace_4052001 : CollatzResearch.WordTrace tailWord_4052001 prefixEnd_4052001 2080624125498906261152693 := by
  unfold tailWord_4052001
  simp only [CollatzResearch.WordTrace]
  refine ⟨147788617793299878520851857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98525745195533252347234571 147788617793299878520851857)
  ·
    refine ⟨110841463344974908890638893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147788617793299878520851857 110841463344974908890638893)
    ·
      refine ⟨41565548754365590833989585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110841463344974908890638893 41565548754365590833989585)
      ·
        refine ⟨31174161565774193125492189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41565548754365590833989585 31174161565774193125492189)
        ·
          refine ⟨11690310587165322422059571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31174161565774193125492189 11690310587165322422059571)
          ·
            refine ⟨17535465880747983633089357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11690310587165322422059571 17535465880747983633089357)
            ·
              refine ⟨6575799705280493862408509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17535465880747983633089357 6575799705280493862408509)
              ·
                refine ⟨2465924889480185198403191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6575799705280493862408509 2465924889480185198403191)
                ·
                  refine ⟨3698887334220277797604787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2465924889480185198403191 3698887334220277797604787)
                  ·
                    refine ⟨5548331001330416696407181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3698887334220277797604787 5548331001330416696407181)
                    ·
                      refine ⟨2080624125498906261152693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5548331001330416696407181 2080624125498906261152693)
                      ·
                        rfl

theorem cell23_4052001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3, 3, 1, 1, 3].length) (baseStart_4052001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4052001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4052001 prefixEnd_4052001 := by exact prefixLift 4052001
  have htrace : WordTrace (prefixWord ++ tailWord_4052001) baseStart_4052001 baseEnd_4052001 := by
    simpa [prefixWord, tailWord_4052001, baseEnd_4052001] using wordTrace_append hprefix tailTrace_4052001
  have hstable : (prefixWord ++ tailWord_4052001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4052001).length < 2 ^ (prefixWord ++ tailWord_4052001).sum := by decide
  have hdescent : baseEnd_4052001 < baseStart_4052001 := by decide
  rcases family_descends (prefixWord ++ tailWord_4052001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4052017 : List Nat := [1, 2, 2, 3, 1, 2, 2, 4, 2, 4]
def baseStart_4052017 : Nat := 118140960795 + 4052017 * 2 ^ 59
def prefixEnd_4052017 : Nat := 4983230072969 + 3 ^ 40 * 4052017 * 2
def baseEnd_4052017 : Nat := 693544113729792732850873

theorem tailTrace_4052017 : CollatzResearch.WordTrace tailWord_4052017 prefixEnd_4052017 693544113729792732850873 := by
  unfold tailWord_4052017
  simp only [CollatzResearch.WordTrace]
  refine ⟨147789201361241913253434305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98526134240827942168956203 147789201361241913253434305)
  ·
    refine ⟨110841901020931434940075729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147789201361241913253434305 110841901020931434940075729)
    ·
      refine ⟨83131425765698576205056797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110841901020931434940075729 83131425765698576205056797)
      ·
        refine ⟨31174284662136966076896299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83131425765698576205056797 31174284662136966076896299)
        ·
          refine ⟨46761426993205449115344449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31174284662136966076896299 46761426993205449115344449)
          ·
            refine ⟨35071070244904086836508337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46761426993205449115344449 35071070244904086836508337)
            ·
              refine ⟨26303302683678065127381253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35071070244904086836508337 26303302683678065127381253)
              ·
                refine ⟨4931869253189637211383985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26303302683678065127381253 4931869253189637211383985)
                ·
                  refine ⟨3698901939892227908537989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4931869253189637211383985 3698901939892227908537989)
                  ·
                    refine ⟨693544113729792732850873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3698901939892227908537989 693544113729792732850873)
                    ·
                      rfl

theorem cell23_4052017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 4, 2, 4].length) (baseStart_4052017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4052017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4052017 prefixEnd_4052017 := by exact prefixLift 4052017
  have htrace : WordTrace (prefixWord ++ tailWord_4052017) baseStart_4052017 baseEnd_4052017 := by
    simpa [prefixWord, tailWord_4052017, baseEnd_4052017] using wordTrace_append hprefix tailTrace_4052017
  have hstable : (prefixWord ++ tailWord_4052017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4052017).length < 2 ^ (prefixWord ++ tailWord_4052017).sum := by decide
  have hdescent : baseEnd_4052017 < baseStart_4052017 := by decide
  rcases family_descends (prefixWord ++ tailWord_4052017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4052057 : List Nat := [1, 2, 1, 2, 2, 1, 2, 4, 4, 1, 3]
def baseStart_4052057 : Nat := 118140960795 + 4052057 * 2 ^ 59
def prefixEnd_4052057 : Nat := 4983230072969 + 3 ^ 40 * 4052057 * 2
def baseEnd_4052057 : Nat := 2080652880415558042052435

theorem tailTrace_4052057 : CollatzResearch.WordTrace tailWord_4052057 prefixEnd_4052057 2080652880415558042052435 := by
  unfold tailWord_4052057
  simp only [CollatzResearch.WordTrace]
  refine ⟨147790660281097000084890425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98527106854064666723260283 147790660281097000084890425)
  ·
    refine ⟨110842995210822750063667819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147790660281097000084890425 110842995210822750063667819)
    ·
      refine ⟨166264492816234125095501729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110842995210822750063667819 166264492816234125095501729)
      ·
        refine ⟨124698369612175593821626297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166264492816234125095501729 124698369612175593821626297)
        ·
          refine ⟨93523777209131695366219723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124698369612175593821626297 93523777209131695366219723)
          ·
            refine ⟨140285665813697543049329585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93523777209131695366219723 140285665813697543049329585)
            ·
              refine ⟨105214249360273157286997189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140285665813697543049329585 105214249360273157286997189)
              ·
                refine ⟨19727671755051216991311973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105214249360273157286997189 19727671755051216991311973)
                ·
                  refine ⟨3698938454072103185870995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19727671755051216991311973 3698938454072103185870995)
                  ·
                    refine ⟨5548407681108154778806493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3698938454072103185870995 5548407681108154778806493)
                    ·
                      refine ⟨2080652880415558042052435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5548407681108154778806493 2080652880415558042052435)
                      ·
                        rfl

theorem cell23_4052057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 4, 4, 1, 3].length) (baseStart_4052057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4052057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4052057 prefixEnd_4052057 := by exact prefixLift 4052057
  have htrace : WordTrace (prefixWord ++ tailWord_4052057) baseStart_4052057 baseEnd_4052057 := by
    simpa [prefixWord, tailWord_4052057, baseEnd_4052057] using wordTrace_append hprefix tailTrace_4052057
  have hstable : (prefixWord ++ tailWord_4052057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4052057).length < 2 ^ (prefixWord ++ tailWord_4052057).sum := by decide
  have hdescent : baseEnd_4052057 < baseStart_4052057 := by decide
  rcases family_descends (prefixWord ++ tailWord_4052057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4052061 : List Nat := [1, 4, 4, 1, 2, 2, 1, 1, 1, 1, 5]
def baseStart_4052061 : Nat := 118140960795 + 4052061 * 2 ^ 59
def prefixEnd_4052061 : Nat := 4983230072969 + 3 ^ 40 * 4052061 * 2
def baseEnd_4052061 : Nat := 2080654934338176026402417

theorem tailTrace_4052061 : CollatzResearch.WordTrace tailWord_4052061 prefixEnd_4052061 2080654934338176026402417 := by
  unfold tailWord_4052061
  simp only [CollatzResearch.WordTrace]
  refine ⟨147790806173082508768036037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98527204115388339178690691 147790806173082508768036037)
  ·
    refine ⟨27710776157452970394006757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147790806173082508768036037 27710776157452970394006757)
    ·
      refine ⟨5195770529522431948876267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27710776157452970394006757 5195770529522431948876267)
      ·
        refine ⟨7793655794283647923314401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5195770529522431948876267 7793655794283647923314401)
        ·
          refine ⟨5845241845712735942485801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7793655794283647923314401 5845241845712735942485801)
          ·
            refine ⟨4383931384284551956864351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5845241845712735942485801 4383931384284551956864351)
            ·
              refine ⟨6575897076426827935296527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4383931384284551956864351 6575897076426827935296527)
              ·
                refine ⟨9863845614640241902944791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6575897076426827935296527 9863845614640241902944791)
                ·
                  refine ⟨14795768421960362854417187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9863845614640241902944791 14795768421960362854417187)
                  ·
                    refine ⟨22193652632940544281625781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14795768421960362854417187 22193652632940544281625781)
                    ·
                      refine ⟨2080654934338176026402417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22193652632940544281625781 2080654934338176026402417)
                      ·
                        rfl

theorem cell23_4052061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_4052061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4052061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4052061 prefixEnd_4052061 := by exact prefixLift 4052061
  have htrace : WordTrace (prefixWord ++ tailWord_4052061) baseStart_4052061 baseEnd_4052061 := by
    simpa [prefixWord, tailWord_4052061, baseEnd_4052061] using wordTrace_append hprefix tailTrace_4052061
  have hstable : (prefixWord ++ tailWord_4052061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4052061).length < 2 ^ (prefixWord ++ tailWord_4052061).sum := by decide
  have hdescent : baseEnd_4052061 < baseStart_4052061 := by decide
  rcases family_descends (prefixWord ++ tailWord_4052061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4052080 : List Nat := [2, 1, 1, 1, 5, 1, 1, 1, 1, 5, 4]
def baseStart_4052080 : Nat := 118140960795 + 4052080 * 2 ^ 59
def prefixEnd_4052080 : Nat := 4983230072969 + 3 ^ 40 * 4052080 * 2
def baseEnd_4052080 : Nat := 2080664690470611452064829

theorem tailTrace_4052080 : CollatzResearch.WordTrace tailWord_4052080 prefixEnd_4052080 2080664690470611452064829 := by
  unfold tailWord_4052080
  simp only [CollatzResearch.WordTrace]
  refine ⟨73895749580006837506488847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98527666106675783341985129 73895749580006837506488847)
  ·
    refine ⟨110843624370010256259733271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73895749580006837506488847 110843624370010256259733271)
    ·
      refine ⟨166265436555015384389599907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110843624370010256259733271 166265436555015384389599907)
      ·
        refine ⟨249398154832523076584399861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166265436555015384389599907 249398154832523076584399861)
        ·
          refine ⟨23381077015549038429787487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 249398154832523076584399861 23381077015549038429787487)
          ·
            refine ⟨35071615523323557644681231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23381077015549038429787487 35071615523323557644681231)
            ·
              refine ⟨52607423284985336467021847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35071615523323557644681231 52607423284985336467021847)
              ·
                refine ⟨78911134927478004700532771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52607423284985336467021847 78911134927478004700532771)
                ·
                  refine ⟨118366702391217007050799157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78911134927478004700532771 118366702391217007050799157)
                  ·
                    refine ⟨11096878349176594411012421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 118366702391217007050799157 11096878349176594411012421)
                    ·
                      refine ⟨2080664690470611452064829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11096878349176594411012421 2080664690470611452064829)
                      ·
                        rfl

theorem cell23_4052080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5, 4].length) (baseStart_4052080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4052080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4052080 prefixEnd_4052080 := by exact prefixLift 4052080
  have htrace : WordTrace (prefixWord ++ tailWord_4052080) baseStart_4052080 baseEnd_4052080 := by
    simpa [prefixWord, tailWord_4052080, baseEnd_4052080] using wordTrace_append hprefix tailTrace_4052080
  have hstable : (prefixWord ++ tailWord_4052080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4052080).length < 2 ^ (prefixWord ++ tailWord_4052080).sum := by decide
  have hdescent : baseEnd_4052080 < baseStart_4052080 := by decide
  rcases family_descends (prefixWord ++ tailWord_4052080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4052147 : List Nat := [1, 1, 1, 2, 3, 2, 4, 1, 2, 3, 3]
def baseStart_4052147 : Nat := 118140960795 + 4052147 * 2 ^ 59
def prefixEnd_4052147 : Nat := 4983230072969 + 3 ^ 40 * 4052147 * 2
def baseEnd_4052147 : Nat := 2080699093674462689927021

theorem tailTrace_4052147 : CollatzResearch.WordTrace tailWord_4052147 prefixEnd_4052147 2080699093674462689927021 := by
  unfold tailWord_4052147
  simp only [CollatzResearch.WordTrace]
  refine ⟨147793942850770945455666695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98529295233847296970444463 147793942850770945455666695)
  ·
    refine ⟨221690914276156418183500043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147793942850770945455666695 221690914276156418183500043)
    ·
      refine ⟨332536371414234627275250065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221690914276156418183500043 332536371414234627275250065)
      ·
        refine ⟨249402278560675970456437549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 332536371414234627275250065 249402278560675970456437549)
        ·
          refine ⟨93525854460253488921164081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 249402278560675970456437549 93525854460253488921164081)
          ·
            refine ⟨70144390845190116690873061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93525854460253488921164081 70144390845190116690873061)
            ·
              refine ⟨13152073283473146879538699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70144390845190116690873061 13152073283473146879538699)
              ·
                refine ⟨19728109925209720319308049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13152073283473146879538699 19728109925209720319308049)
                ·
                  refine ⟨14796082443907290239481037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19728109925209720319308049 14796082443907290239481037)
                  ·
                    refine ⟨5548530916465233839805389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14796082443907290239481037 5548530916465233839805389)
                    ·
                      refine ⟨2080699093674462689927021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5548530916465233839805389 2080699093674462689927021)
                      ·
                        rfl

theorem cell23_4052147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 1, 2, 3, 3].length) (baseStart_4052147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4052147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4052147 prefixEnd_4052147 := by exact prefixLift 4052147
  have htrace : WordTrace (prefixWord ++ tailWord_4052147) baseStart_4052147 baseEnd_4052147 := by
    simpa [prefixWord, tailWord_4052147, baseEnd_4052147] using wordTrace_append hprefix tailTrace_4052147
  have hstable : (prefixWord ++ tailWord_4052147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4052147).length < 2 ^ (prefixWord ++ tailWord_4052147).sum := by decide
  have hdescent : baseEnd_4052147 < baseStart_4052147 := by decide
  rcases family_descends (prefixWord ++ tailWord_4052147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4052184 : List Nat := [2, 1, 2, 2, 5, 1, 1, 2, 2, 5]
def baseStart_4052184 : Nat := 118140960795 + 4052184 * 2 ^ 59
def prefixEnd_4052184 : Nat := 4983230072969 + 3 ^ 40 * 4052184 * 2
def baseEnd_4052184 : Nat := 693572697486226348388117

theorem tailTrace_4052184 : CollatzResearch.WordTrace tailWord_4052184 prefixEnd_4052184 693572697486226348388117 := by
  unfold tailWord_4052184
  simp only [CollatzResearch.WordTrace]
  refine ⟨73897646175818450387381803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98530194901091267183175737 73897646175818450387381803)
  ·
    refine ⟨110846469263727675581072705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73897646175818450387381803 110846469263727675581072705)
    ·
      refine ⟨83134851947795756685804529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110846469263727675581072705 83134851947795756685804529)
      ·
        refine ⟨62351138960846817514353397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83134851947795756685804529 62351138960846817514353397)
        ·
          refine ⟨5845419277579389141970631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62351138960846817514353397 5845419277579389141970631)
          ·
            refine ⟨8768128916369083712955947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5845419277579389141970631 8768128916369083712955947)
            ·
              refine ⟨13152193374553625569433921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8768128916369083712955947 13152193374553625569433921)
              ·
                refine ⟨9864145030915219177075441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13152193374553625569433921 9864145030915219177075441)
                ·
                  refine ⟨7398108773186414382806581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9864145030915219177075441 7398108773186414382806581)
                  ·
                    refine ⟨693572697486226348388117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7398108773186414382806581 693572697486226348388117)
                    ·
                      rfl

theorem cell23_4052184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 2, 2, 5].length) (baseStart_4052184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4052184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4052184 prefixEnd_4052184 := by exact prefixLift 4052184
  have htrace : WordTrace (prefixWord ++ tailWord_4052184) baseStart_4052184 baseEnd_4052184 := by
    simpa [prefixWord, tailWord_4052184, baseEnd_4052184] using wordTrace_append hprefix tailTrace_4052184
  have hstable : (prefixWord ++ tailWord_4052184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4052184).length < 2 ^ (prefixWord ++ tailWord_4052184).sum := by decide
  have hdescent : baseEnd_4052184 < baseStart_4052184 := by decide
  rcases family_descends (prefixWord ++ tailWord_4052184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4052214 : List Nat := [5, 1, 1, 1, 1, 1, 1, 3, 5, 4]
def baseStart_4052214 : Nat := 118140960795 + 4052214 * 2 ^ 59
def prefixEnd_4052214 : Nat := 4983230072969 + 3 ^ 40 * 4052214 * 2
def baseEnd_4052214 : Nat := 693577832292771309263071

theorem tailTrace_4052214 : CollatzResearch.WordTrace tailWord_4052214 prefixEnd_4052214 693577832292771309263071 := by
  unfold tailWord_4052214
  simp only [CollatzResearch.WordTrace]
  refine ⟨9237274158845513493647231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 98530924361018810598903797 9237274158845513493647231)
  ·
    refine ⟨13855911238268270240470847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9237274158845513493647231 13855911238268270240470847)
    ·
      refine ⟨20783866857402405360706271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13855911238268270240470847 20783866857402405360706271)
      ·
        refine ⟨31175800286103608041059407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20783866857402405360706271 31175800286103608041059407)
        ·
          refine ⟨46763700429155412061589111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31175800286103608041059407 46763700429155412061589111)
          ·
            refine ⟨70145550643733118092383667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46763700429155412061589111 70145550643733118092383667)
            ·
              refine ⟨105218325965599677138575501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70145550643733118092383667 105218325965599677138575501)
              ·
                refine ⟨39456872237099878926965813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105218325965599677138575501 39456872237099878926965813)
                ·
                  refine ⟨3699081772228113649403045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39456872237099878926965813 3699081772228113649403045)
                  ·
                    refine ⟨693577832292771309263071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3699081772228113649403045 693577832292771309263071)
                    ·
                      rfl

theorem cell23_4052214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 3, 5, 4].length) (baseStart_4052214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4052214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4052214 prefixEnd_4052214 := by exact prefixLift 4052214
  have htrace : WordTrace (prefixWord ++ tailWord_4052214) baseStart_4052214 baseEnd_4052214 := by
    simpa [prefixWord, tailWord_4052214, baseEnd_4052214] using wordTrace_append hprefix tailTrace_4052214
  have hstable : (prefixWord ++ tailWord_4052214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4052214).length < 2 ^ (prefixWord ++ tailWord_4052214).sum := by decide
  have hdescent : baseEnd_4052214 < baseStart_4052214 := by decide
  rcases family_descends (prefixWord ++ tailWord_4052214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4052247 : List Nat := [1, 1, 3, 4, 1, 1, 2, 1, 1, 2, 6]
def baseStart_4052247 : Nat := 118140960795 + 4052247 * 2 ^ 59
def prefixEnd_4052247 : Nat := 4983230072969 + 3 ^ 40 * 4052247 * 2
def baseEnd_4052247 : Nat := 2080750441739912298676561

theorem tailTrace_4052247 : CollatzResearch.WordTrace tailWord_4052247 prefixEnd_4052247 2080750441739912298676561 := by
  unfold tailWord_4052247
  simp only [CollatzResearch.WordTrace]
  refine ⟨147797590150408662534306995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98531726766939108356204663 147797590150408662534306995)
  ·
    refine ⟨221696385225612993801460493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147797590150408662534306995 221696385225612993801460493)
    ·
      refine ⟨83136144459604872675547685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221696385225612993801460493 83136144459604872675547685)
      ·
        refine ⟨15588027086175913626665191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83136144459604872675547685 15588027086175913626665191)
        ·
          refine ⟨23382040629263870439997787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15588027086175913626665191 23382040629263870439997787)
          ·
            refine ⟨35073060943895805659996681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23382040629263870439997787 35073060943895805659996681)
            ·
              refine ⟨26304795707921854244997511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35073060943895805659996681 26304795707921854244997511)
              ·
                refine ⟨39457193561882781367496267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26304795707921854244997511 39457193561882781367496267)
                ·
                  refine ⟨59185790342824172051244401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39457193561882781367496267 59185790342824172051244401)
                  ·
                    refine ⟨44389342757118129038433301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59185790342824172051244401 44389342757118129038433301)
                    ·
                      refine ⟨2080750441739912298676561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44389342757118129038433301 2080750441739912298676561)
                      ·
                        rfl

theorem cell23_4052247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_4052247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4052247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4052247 prefixEnd_4052247 := by exact prefixLift 4052247
  have htrace : WordTrace (prefixWord ++ tailWord_4052247) baseStart_4052247 baseEnd_4052247 := by
    simpa [prefixWord, tailWord_4052247, baseEnd_4052247] using wordTrace_append hprefix tailTrace_4052247
  have hstable : (prefixWord ++ tailWord_4052247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4052247).length < 2 ^ (prefixWord ++ tailWord_4052247).sum := by decide
  have hdescent : baseEnd_4052247 < baseStart_4052247 := by decide
  rcases family_descends (prefixWord ++ tailWord_4052247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4052248 : List Nat := [2, 1, 2, 3, 1, 3, 4, 2, 1, 4]
def baseStart_4052248 : Nat := 118140960795 + 4052248 * 2 ^ 59
def prefixEnd_4052248 : Nat := 4983230072969 + 3 ^ 40 * 4052248 * 2
def baseEnd_4052248 : Nat := 693583651740188931588019

theorem tailTrace_4052248 : CollatzResearch.WordTrace tailWord_4052248 prefixEnd_4052248 693583651740188931588019 := by
  unfold tailWord_4052248
  simp only [CollatzResearch.WordTrace]
  refine ⟨73898813311702519852546699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98531751082270026470062265 73898813311702519852546699)
  ·
    refine ⟨110848219967553779778820049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73898813311702519852546699 110848219967553779778820049)
    ·
      refine ⟨83136164975665334834115037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110848219967553779778820049 83136164975665334834115037)
      ·
        refine ⟨31176061865874500562793139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83136164975665334834115037 31176061865874500562793139)
        ·
          refine ⟨46764092798811750844189709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31176061865874500562793139 46764092798811750844189709)
          ·
            refine ⟨17536534799554406566571141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46764092798811750844189709 17536534799554406566571141)
            ·
              refine ⟨3288100274916451231232089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17536534799554406566571141 3288100274916451231232089)
              ·
                refine ⟨2466075206187338423424067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3288100274916451231232089 2466075206187338423424067)
                ·
                  refine ⟨3699112809281007635136101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2466075206187338423424067 3699112809281007635136101)
                  ·
                    refine ⟨693583651740188931588019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3699112809281007635136101 693583651740188931588019)
                    ·
                      rfl

theorem cell23_4052248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 4, 2, 1, 4].length) (baseStart_4052248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4052248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4052248 prefixEnd_4052248 := by exact prefixLift 4052248
  have htrace : WordTrace (prefixWord ++ tailWord_4052248) baseStart_4052248 baseEnd_4052248 := by
    simpa [prefixWord, tailWord_4052248, baseEnd_4052248] using wordTrace_append hprefix tailTrace_4052248
  have hstable : (prefixWord ++ tailWord_4052248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4052248).length < 2 ^ (prefixWord ++ tailWord_4052248).sum := by decide
  have hdescent : baseEnd_4052248 < baseStart_4052248 := by decide
  rcases family_descends (prefixWord ++ tailWord_4052248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4052274 : List Nat := [3, 2, 1, 1, 4, 1, 2, 1, 3, 5]
def baseStart_4052274 : Nat := 118140960795 + 4052274 * 2 ^ 59
def prefixEnd_4052274 : Nat := 4983230072969 + 3 ^ 40 * 4052274 * 2
def baseEnd_4052274 : Nat := 693588101905861231012979

theorem tailTrace_4052274 : CollatzResearch.WordTrace tailWord_4052274 prefixEnd_4052274 693588101905861231012979 := by
  unfold tailWord_4052274
  simp only [CollatzResearch.WordTrace]
  refine ⟨36949643730327711536384969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98532383280873897430359917 36949643730327711536384969)
  ·
    refine ⟨27712232797745783652288727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36949643730327711536384969 27712232797745783652288727)
    ·
      refine ⟨41568349196618675478433091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27712232797745783652288727 41568349196618675478433091)
      ·
        refine ⟨62352523794928013217649637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41568349196618675478433091 62352523794928013217649637)
        ·
          refine ⟨11691098211549002478309307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62352523794928013217649637 11691098211549002478309307)
          ·
            refine ⟨17536647317323503717463961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11691098211549002478309307 17536647317323503717463961)
            ·
              refine ⟨13152485487992627788097971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17536647317323503717463961 13152485487992627788097971)
              ·
                refine ⟨19728728231988941682146957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13152485487992627788097971 19728728231988941682146957)
                ·
                  refine ⟨7398273086995853130805109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19728728231988941682146957 7398273086995853130805109)
                  ·
                    refine ⟨693588101905861231012979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7398273086995853130805109 693588101905861231012979)
                    ·
                      rfl

theorem cell23_4052274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 1, 3, 5].length) (baseStart_4052274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4052274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4052274 prefixEnd_4052274 := by exact prefixLift 4052274
  have htrace : WordTrace (prefixWord ++ tailWord_4052274) baseStart_4052274 baseEnd_4052274 := by
    simpa [prefixWord, tailWord_4052274, baseEnd_4052274] using wordTrace_append hprefix tailTrace_4052274
  have hstable : (prefixWord ++ tailWord_4052274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4052274).length < 2 ^ (prefixWord ++ tailWord_4052274).sum := by decide
  have hdescent : baseEnd_4052274 < baseStart_4052274 := by decide
  rcases family_descends (prefixWord ++ tailWord_4052274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4052288 : List Nat := [2, 1, 1, 2, 2, 1, 6, 3, 1, 1, 3]
def baseStart_4052288 : Nat := 118140960795 + 4052288 * 2 ^ 59
def prefixEnd_4052288 : Nat := 4983230072969 + 3 ^ 40 * 4052288 * 2
def baseEnd_4052288 : Nat := 2080771494446746638263873

theorem tailTrace_4052288 : CollatzResearch.WordTrace tailWord_4052288 prefixEnd_4052288 2080771494446746638263873 := by
  unfold tailWord_4052288
  simp only [CollatzResearch.WordTrace]
  refine ⟨73899542771630063268274759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98532723695506751024366345 73899542771630063268274759)
  ·
    refine ⟨110849314157445094902412139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73899542771630063268274759 110849314157445094902412139)
    ·
      refine ⟨166273971236167642353618209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110849314157445094902412139 166273971236167642353618209)
      ·
        refine ⟨124705478427125731765213657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166273971236167642353618209 124705478427125731765213657)
        ·
          refine ⟨93529108820344298823910243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124705478427125731765213657 93529108820344298823910243)
          ·
            refine ⟨140293663230516448235865365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93529108820344298823910243 140293663230516448235865365)
            ·
              refine ⟨6576265463930458511056189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 140293663230516448235865365 6576265463930458511056189)
              ·
                refine ⟨2466099548973921941646071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6576265463930458511056189 2466099548973921941646071)
                ·
                  refine ⟨3699149323460882912469107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2466099548973921941646071 3699149323460882912469107)
                  ·
                    refine ⟨5548723985191324368703661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3699149323460882912469107 5548723985191324368703661)
                    ·
                      refine ⟨2080771494446746638263873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5548723985191324368703661 2080771494446746638263873)
                      ·
                        rfl

theorem cell23_4052288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6, 3, 1, 1, 3].length) (baseStart_4052288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4052288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4052288 prefixEnd_4052288 := by exact prefixLift 4052288
  have htrace : WordTrace (prefixWord ++ tailWord_4052288) baseStart_4052288 baseEnd_4052288 := by
    simpa [prefixWord, tailWord_4052288, baseEnd_4052288] using wordTrace_append hprefix tailTrace_4052288
  have hstable : (prefixWord ++ tailWord_4052288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4052288).length < 2 ^ (prefixWord ++ tailWord_4052288).sum := by decide
  have hdescent : baseEnd_4052288 < baseStart_4052288 := by decide
  rcases family_descends (prefixWord ++ tailWord_4052288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4052304 : List Nat := [2, 1, 1, 1, 1, 5, 3, 1, 4, 4]
def baseStart_4052304 : Nat := 118140960795 + 4052304 * 2 ^ 59
def prefixEnd_4052304 : Nat := 4983230072969 + 3 ^ 40 * 4052304 * 2
def baseEnd_4052304 : Nat := 693593236712406191887933

theorem tailTrace_4052304 : CollatzResearch.WordTrace tailWord_4052304 prefixEnd_4052304 693593236712406191887933 := by
  unfold tailWord_4052304
  simp only [CollatzResearch.WordTrace]
  refine ⟨73899834555601080634565983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98533112740801440846087977 73899834555601080634565983)
  ·
    refine ⟨110849751833401620951848975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73899834555601080634565983 110849751833401620951848975)
    ·
      refine ⟨166274627750102431427773463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110849751833401620951848975 166274627750102431427773463)
      ·
        refine ⟨249411941625153647141660195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166274627750102431427773463 249411941625153647141660195)
        ·
          refine ⟨374117912437730470712490293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249411941625153647141660195 374117912437730470712490293)
          ·
            refine ⟨35073554291037231629295965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 374117912437730470712490293 35073554291037231629295965)
            ·
              refine ⟨13152582859138961860985987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35073554291037231629295965 13152582859138961860985987)
              ·
                refine ⟨19728874288708442791478981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13152582859138961860985987 19728874288708442791478981)
                ·
                  refine ⟨3699163929132833023402309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19728874288708442791478981 3699163929132833023402309)
                  ·
                    refine ⟨693593236712406191887933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3699163929132833023402309 693593236712406191887933)
                    ·
                      rfl

theorem cell23_4052304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 1, 4, 4].length) (baseStart_4052304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4052304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4052304 prefixEnd_4052304 := by exact prefixLift 4052304
  have htrace : WordTrace (prefixWord ++ tailWord_4052304) baseStart_4052304 baseEnd_4052304 := by
    simpa [prefixWord, tailWord_4052304, baseEnd_4052304] using wordTrace_append hprefix tailTrace_4052304
  have hstable : (prefixWord ++ tailWord_4052304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4052304).length < 2 ^ (prefixWord ++ tailWord_4052304).sum := by decide
  have hdescent : baseEnd_4052304 < baseStart_4052304 := by decide
  rcases family_descends (prefixWord ++ tailWord_4052304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4052307 : List Nat := [1, 1, 1, 2, 1, 1, 6, 2, 1, 1, 6]
def baseStart_4052307 : Nat := 118140960795 + 4052307 * 2 ^ 59
def prefixEnd_4052307 : Nat := 4983230072969 + 3 ^ 40 * 4052307 * 2
def baseEnd_4052307 : Nat := 2080781250579182063926285

theorem tailTrace_4052307 : CollatzResearch.WordTrace tailWord_4052307 prefixEnd_4052307 2080781250579182063926285 := by
  unfold tailWord_4052307
  simp only [CollatzResearch.WordTrace]
  refine ⟨147799778530191292781491175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98533185686794195187660783 147799778530191292781491175)
  ·
    refine ⟨221699667795286939172236763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147799778530191292781491175 221699667795286939172236763)
    ·
      refine ⟨332549501692930408758355145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221699667795286939172236763 332549501692930408758355145)
      ·
        refine ⟨249412126269697806568766359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 332549501692930408758355145 249412126269697806568766359)
        ·
          refine ⟨374118189404546709853149539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249412126269697806568766359 374118189404546709853149539)
          ·
            refine ⟨561177284106820064779724309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 374118189404546709853149539 561177284106820064779724309)
            ·
              refine ⟨26305185192507190536549577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 561177284106820064779724309 26305185192507190536549577)
              ·
                refine ⟨19728888894380392902412183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26305185192507190536549577 19728888894380392902412183)
                ·
                  refine ⟨29593333341570589353618275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19728888894380392902412183 29593333341570589353618275)
                  ·
                    refine ⟨44390000012355884030427413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29593333341570589353618275 44390000012355884030427413)
                    ·
                      refine ⟨2080781250579182063926285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44390000012355884030427413 2080781250579182063926285)
                      ·
                        rfl

theorem cell23_4052307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 2, 1, 1, 6].length) (baseStart_4052307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4052307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4052307 prefixEnd_4052307 := by exact prefixLift 4052307
  have htrace : WordTrace (prefixWord ++ tailWord_4052307) baseStart_4052307 baseEnd_4052307 := by
    simpa [prefixWord, tailWord_4052307, baseEnd_4052307] using wordTrace_append hprefix tailTrace_4052307
  have hstable : (prefixWord ++ tailWord_4052307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4052307).length < 2 ^ (prefixWord ++ tailWord_4052307).sum := by decide
  have hdescent : baseEnd_4052307 < baseStart_4052307 := by decide
  rcases family_descends (prefixWord ++ tailWord_4052307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4052314 : List Nat := [3, 1, 1, 2, 1, 2, 2, 1, 5, 2, 3]
def baseStart_4052314 : Nat := 118140960795 + 4052314 * 2 ^ 59
def prefixEnd_4052314 : Nat := 4983230072969 + 3 ^ 40 * 4052314 * 2
def baseEnd_4052314 : Nat := 2080784844943763536538753

theorem tailTrace_4052314 : CollatzResearch.WordTrace tailWord_4052314 prefixEnd_4052314 2080784844943763536538753 := by
  unfold tailWord_4052314
  simp only [CollatzResearch.WordTrace]
  refine ⟨36950008460291483244248999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98533355894110621984663997 36950008460291483244248999)
  ·
    refine ⟨55425012690437224866373499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36950008460291483244248999 55425012690437224866373499)
    ·
      refine ⟨83137519035655837299560249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55425012690437224866373499 83137519035655837299560249)
      ·
        refine ⟨62353139276741877974670187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83137519035655837299560249 62353139276741877974670187)
        ·
          refine ⟨93529708915112816962005281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62353139276741877974670187 93529708915112816962005281)
          ·
            refine ⟨70147281686334612721503961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93529708915112816962005281 70147281686334612721503961)
            ·
              refine ⟨52610461264750959541127971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70147281686334612721503961 52610461264750959541127971)
              ·
                refine ⟨78915691897126439311691957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52610461264750959541127971 78915691897126439311691957)
                ·
                  refine ⟨7398346115355603685471121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78915691897126439311691957 7398346115355603685471121)
                  ·
                    refine ⟨5548759586516702764103341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7398346115355603685471121 5548759586516702764103341)
                    ·
                      refine ⟨2080784844943763536538753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5548759586516702764103341 2080784844943763536538753)
                      ·
                        rfl

theorem cell23_4052314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 5, 2, 3].length) (baseStart_4052314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4052314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4052314 prefixEnd_4052314 := by exact prefixLift 4052314
  have htrace : WordTrace (prefixWord ++ tailWord_4052314) baseStart_4052314 baseEnd_4052314 := by
    simpa [prefixWord, tailWord_4052314, baseEnd_4052314] using wordTrace_append hprefix tailTrace_4052314
  have hstable : (prefixWord ++ tailWord_4052314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4052314).length < 2 ^ (prefixWord ++ tailWord_4052314).sum := by decide
  have hdescent : baseEnd_4052314 < baseStart_4052314 := by decide
  rcases family_descends (prefixWord ++ tailWord_4052314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4052324 : List Nat := [2, 3, 1, 1, 3, 3, 1, 1, 1, 1, 6]
def baseStart_4052324 : Nat := 118140960795 + 4052324 * 2 ^ 59
def prefixEnd_4052324 : Nat := 4983230072969 + 3 ^ 40 * 4052324 * 2
def baseEnd_4052324 : Nat := 2080789979750308497413707

theorem tailTrace_4052324 : CollatzResearch.WordTrace tailWord_4052324 prefixEnd_4052324 2080789979750308497413707 := by
  unfold tailWord_4052324
  simp only [CollatzResearch.WordTrace]
  refine ⟨73900199285564852342430013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98533599047419803123240017 73900199285564852342430013)
  ·
    refine ⟨27712574732086819628411255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73900199285564852342430013 27712574732086819628411255)
    ·
      refine ⟨41568862098130229442616883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27712574732086819628411255 41568862098130229442616883)
      ·
        refine ⟨62353293147195344163925325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41568862098130229442616883 62353293147195344163925325)
        ·
          refine ⟨23382484930198254061471997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62353293147195344163925325 23382484930198254061471997)
          ·
            refine ⟨8768431848824345273051999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23382484930198254061471997 8768431848824345273051999)
            ·
              refine ⟨13152647773236517909577999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8768431848824345273051999 13152647773236517909577999)
              ·
                refine ⟨19728971659854776864366999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13152647773236517909577999 19728971659854776864366999)
                ·
                  refine ⟨29593457489782165296550499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19728971659854776864366999 29593457489782165296550499)
                  ·
                    refine ⟨44390186234673247944825749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29593457489782165296550499 44390186234673247944825749)
                    ·
                      refine ⟨2080789979750308497413707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44390186234673247944825749 2080789979750308497413707)
                      ·
                        rfl

theorem cell23_4052324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 1, 1, 1, 6].length) (baseStart_4052324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4052324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4052324 prefixEnd_4052324 := by exact prefixLift 4052324
  have htrace : WordTrace (prefixWord ++ tailWord_4052324) baseStart_4052324 baseEnd_4052324 := by
    simpa [prefixWord, tailWord_4052324, baseEnd_4052324] using wordTrace_append hprefix tailTrace_4052324
  have hstable : (prefixWord ++ tailWord_4052324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4052324).length < 2 ^ (prefixWord ++ tailWord_4052324).sum := by decide
  have hdescent : baseEnd_4052324 < baseStart_4052324 := by decide
  rcases family_descends (prefixWord ++ tailWord_4052324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4052328 : List Nat := [2, 1, 4, 2, 3, 1, 2, 2, 1, 1, 4]
def baseStart_4052328 : Nat := 118140960795 + 4052328 * 2 ^ 59
def prefixEnd_4052328 : Nat := 4983230072969 + 3 ^ 40 * 4052328 * 2
def baseEnd_4052328 : Nat := 2080792033672926481763689

theorem tailTrace_4052328 : CollatzResearch.WordTrace tailWord_4052328 prefixEnd_4052328 2080792033672926481763689 := by
  unfold tailWord_4052328
  simp only [CollatzResearch.WordTrace]
  refine ⟨73900272231557606684002819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98533696308743475578670425 73900272231557606684002819)
  ·
    refine ⟨110850408347336410026004229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73900272231557606684002819 110850408347336410026004229)
    ·
      refine ⟨20784451565125576879875793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110850408347336410026004229 20784451565125576879875793)
      ·
        refine ⟨15588338673844182659906845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20784451565125576879875793 15588338673844182659906845)
        ·
          refine ⟨5845627002691568497465067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15588338673844182659906845 5845627002691568497465067)
          ·
            refine ⟨8768440504037352746197601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5845627002691568497465067 8768440504037352746197601)
            ·
              refine ⟨6576330378028014559648201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8768440504037352746197601 6576330378028014559648201)
              ·
                refine ⟨4932247783521010919736151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6576330378028014559648201 4932247783521010919736151)
                ·
                  refine ⟨7398371675281516379604227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4932247783521010919736151 7398371675281516379604227)
                  ·
                    refine ⟨11097557512922274569406341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7398371675281516379604227 11097557512922274569406341)
                    ·
                      refine ⟨2080792033672926481763689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11097557512922274569406341 2080792033672926481763689)
                      ·
                        rfl

theorem cell23_4052328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 2, 2, 1, 1, 4].length) (baseStart_4052328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4052328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4052328 prefixEnd_4052328 := by exact prefixLift 4052328
  have htrace : WordTrace (prefixWord ++ tailWord_4052328) baseStart_4052328 baseEnd_4052328 := by
    simpa [prefixWord, tailWord_4052328, baseEnd_4052328] using wordTrace_append hprefix tailTrace_4052328
  have hstable : (prefixWord ++ tailWord_4052328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4052328).length < 2 ^ (prefixWord ++ tailWord_4052328).sum := by decide
  have hdescent : baseEnd_4052328 < baseStart_4052328 := by decide
  rcases family_descends (prefixWord ++ tailWord_4052328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4052345 : List Nat := [1, 2, 1, 3, 2, 1, 5, 3, 1, 2, 2]
def baseStart_4052345 : Nat := 118140960795 + 4052345 * 2 ^ 59
def prefixEnd_4052345 : Nat := 4983230072969 + 3 ^ 40 * 4052345 * 2
def baseEnd_4052345 : Nat := 2080800762844052915251111

theorem tailTrace_4052345 : CollatzResearch.WordTrace tailWord_4052345 prefixEnd_4052345 2080800762844052915251111 := by
  unfold tailWord_4052345
  simp only [CollatzResearch.WordTrace]
  refine ⟨147801164504053625271374489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98534109669369083514249659 147801164504053625271374489)
  ·
    refine ⟨110850873378040218953530867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147801164504053625271374489 110850873378040218953530867)
    ·
      refine ⟨166276310067060328430296301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110850873378040218953530867 166276310067060328430296301)
      ·
        refine ⟨62353616275147623161361113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166276310067060328430296301 62353616275147623161361113)
        ·
          refine ⟨46765212206360717371020835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62353616275147623161361113 46765212206360717371020835)
          ·
            refine ⟨70147818309541076056531253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46765212206360717371020835 70147818309541076056531253)
            ·
              refine ⟨6576357966519475880299805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70147818309541076056531253 6576357966519475880299805)
              ·
                refine ⟨2466134237444803455112427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6576357966519475880299805 2466134237444803455112427)
                ·
                  refine ⟨3699201356167205182668641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2466134237444803455112427 3699201356167205182668641)
                  ·
                    refine ⟨2774401017125403887001481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3699201356167205182668641 2774401017125403887001481)
                    ·
                      refine ⟨2080800762844052915251111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2774401017125403887001481 2080800762844052915251111)
                      ·
                        rfl

theorem cell23_4052345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5, 3, 1, 2, 2].length) (baseStart_4052345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4052345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4052345 prefixEnd_4052345 := by exact prefixLift 4052345
  have htrace : WordTrace (prefixWord ++ tailWord_4052345) baseStart_4052345 baseEnd_4052345 := by
    simpa [prefixWord, tailWord_4052345, baseEnd_4052345] using wordTrace_append hprefix tailTrace_4052345
  have hstable : (prefixWord ++ tailWord_4052345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4052345).length < 2 ^ (prefixWord ++ tailWord_4052345).sum := by decide
  have hdescent : baseEnd_4052345 < baseStart_4052345 := by decide
  rcases family_descends (prefixWord ++ tailWord_4052345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4052378 : List Nat := [3, 1, 1, 4, 1, 1, 3, 3, 2, 1, 3]
def baseStart_4052378 : Nat := 118140960795 + 4052378 * 2 ^ 59
def prefixEnd_4052378 : Nat := 4983230072969 + 3 ^ 40 * 4052378 * 2
def baseEnd_4052378 : Nat := 2080817707705651286138459

theorem tailTrace_4052378 : CollatzResearch.WordTrace tailWord_4052378 prefixEnd_4052378 2080817707705651286138459 := by
  unfold tailWord_4052378
  simp only [CollatzResearch.WordTrace]
  refine ⟨36950592028233517976831447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98534912075289381271550525 36950592028233517976831447)
  ·
    refine ⟨55425888042350276965247171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36950592028233517976831447 55425888042350276965247171)
    ·
      refine ⟨83138832063525415447870757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55425888042350276965247171 83138832063525415447870757)
      ·
        refine ⟨15588531011911015396475767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83138832063525415447870757 15588531011911015396475767)
        ·
          refine ⟨23382796517866523094713651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15588531011911015396475767 23382796517866523094713651)
          ·
            refine ⟨35074194776799784642070477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23382796517866523094713651 35074194776799784642070477)
            ·
              refine ⟨13152823041299919240776429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35074194776799784642070477 13152823041299919240776429)
              ·
                refine ⟨4932308640487469715291161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13152823041299919240776429 4932308640487469715291161)
                ·
                  refine ⟨3699231480365602286468371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4932308640487469715291161 3699231480365602286468371)
                  ·
                    refine ⟨5548847220548403429702557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3699231480365602286468371 5548847220548403429702557)
                    ·
                      refine ⟨2080817707705651286138459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5548847220548403429702557 2080817707705651286138459)
                      ·
                        rfl

theorem cell23_4052378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 3, 2, 1, 3].length) (baseStart_4052378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4052378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4052378 prefixEnd_4052378 := by exact prefixLift 4052378
  have htrace : WordTrace (prefixWord ++ tailWord_4052378) baseStart_4052378 baseEnd_4052378 := by
    simpa [prefixWord, tailWord_4052378, baseEnd_4052378] using wordTrace_append hprefix tailTrace_4052378
  have hstable : (prefixWord ++ tailWord_4052378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4052378).length < 2 ^ (prefixWord ++ tailWord_4052378).sum := by decide
  have hdescent : baseEnd_4052378 < baseStart_4052378 := by decide
  rcases family_descends (prefixWord ++ tailWord_4052378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4052382 : List Nat := [4, 3, 1, 2, 2, 2, 1, 2, 1, 2, 3]
def baseStart_4052382 : Nat := 118140960795 + 4052382 * 2 ^ 59
def prefixEnd_4052382 : Nat := 4983230072969 + 3 ^ 40 * 4052382 * 2
def baseEnd_4052382 : Nat := 2080819761628269270488441

theorem tailTrace_4052382 : CollatzResearch.WordTrace tailWord_4052382 prefixEnd_4052382 2080819761628269270488441 := by
  unfold tailWord_4052382
  simp only [CollatzResearch.WordTrace]
  refine ⟨18475314250614947573808925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98535009336613053726980933 18475314250614947573808925)
  ·
    refine ⟨6928242843980605340178347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18475314250614947573808925 6928242843980605340178347)
    ·
      refine ⟨10392364265970908010267521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6928242843980605340178347 10392364265970908010267521)
      ·
        refine ⟨7794273199478181007700641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10392364265970908010267521 7794273199478181007700641)
        ·
          refine ⟨5845704899608635755775481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7794273199478181007700641 5845704899608635755775481)
          ·
            refine ⟨4384278674706476816831611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5845704899608635755775481 4384278674706476816831611)
            ·
              refine ⟨6576418012059715225247417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4384278674706476816831611 6576418012059715225247417)
              ·
                refine ⟨4932313509044786418935563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6576418012059715225247417 4932313509044786418935563)
                ·
                  refine ⟨7398470263567179628403345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4932313509044786418935563 7398470263567179628403345)
                  ·
                    refine ⟨5548852697675384721302509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7398470263567179628403345 5548852697675384721302509)
                    ·
                      refine ⟨2080819761628269270488441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5548852697675384721302509 2080819761628269270488441)
                      ·
                        rfl

theorem cell23_4052382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_4052382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4052382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4052382 prefixEnd_4052382 := by exact prefixLift 4052382
  have htrace : WordTrace (prefixWord ++ tailWord_4052382) baseStart_4052382 baseEnd_4052382 := by
    simpa [prefixWord, tailWord_4052382, baseEnd_4052382] using wordTrace_append hprefix tailTrace_4052382
  have hstable : (prefixWord ++ tailWord_4052382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4052382).length < 2 ^ (prefixWord ++ tailWord_4052382).sum := by decide
  have hdescent : baseEnd_4052382 < baseStart_4052382 := by decide
  rcases family_descends (prefixWord ++ tailWord_4052382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4052414 : List Nat := [4, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6]
def baseStart_4052414 : Nat := 118140960795 + 4052414 * 2 ^ 59
def prefixEnd_4052414 : Nat := 4983230072969 + 3 ^ 40 * 4052414 * 2
def baseEnd_4052414 : Nat := 2080836193009213145288293

theorem tailTrace_4052414 : CollatzResearch.WordTrace tailWord_4052414 prefixEnd_4052414 2080836193009213145288293 := by
  unfold tailWord_4052414
  simp only [CollatzResearch.WordTrace]
  refine ⟨18475460142600456256954537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98535787427202433370424197 18475460142600456256954537)
  ·
    refine ⟨13856595106950342192715903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18475460142600456256954537 13856595106950342192715903)
    ·
      refine ⟨20784892660425513289073855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13856595106950342192715903 20784892660425513289073855)
      ·
        refine ⟨31177338990638269933610783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20784892660425513289073855 31177338990638269933610783)
        ·
          refine ⟨46766008485957404900416175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31177338990638269933610783 46766008485957404900416175)
          ·
            refine ⟨70149012728936107350624263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46766008485957404900416175 70149012728936107350624263)
            ·
              refine ⟨105223519093404161025936395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70149012728936107350624263 105223519093404161025936395)
              ·
                refine ⟨157835278640106241538904593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105223519093404161025936395 157835278640106241538904593)
                ·
                  refine ⟨118376458980079681154178445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 157835278640106241538904593 118376458980079681154178445)
                  ·
                    refine ⟨44391172117529880432816917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 118376458980079681154178445 44391172117529880432816917)
                    ·
                      refine ⟨2080836193009213145288293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44391172117529880432816917 2080836193009213145288293)
                      ·
                        rfl

theorem cell23_4052414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_4052414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4052414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4052414 prefixEnd_4052414 := by exact prefixLift 4052414
  have htrace : WordTrace (prefixWord ++ tailWord_4052414) baseStart_4052414 baseEnd_4052414 := by
    simpa [prefixWord, tailWord_4052414, baseEnd_4052414] using wordTrace_append hprefix tailTrace_4052414
  have hstable : (prefixWord ++ tailWord_4052414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4052414).length < 2 ^ (prefixWord ++ tailWord_4052414).sum := by decide
  have hdescent : baseEnd_4052414 < baseStart_4052414 := by decide
  rcases family_descends (prefixWord ++ tailWord_4052414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4052424 : List Nat := [2, 1, 3, 1, 3, 1, 2, 3, 7]
def baseStart_4052424 : Nat := 118140960795 + 4052424 * 2 ^ 59
def prefixEnd_4052424 : Nat := 4983230072969 + 3 ^ 40 * 4052424 * 2
def baseEnd_4052424 : Nat := 231204591979528678462583

theorem tailTrace_4052424 : CollatzResearch.WordTrace tailWord_4052424 prefixEnd_4052424 231204591979528678462583 := by
  unfold tailWord_4052424
  simp only [CollatzResearch.WordTrace]
  refine ⟨73902022935383710881750163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98536030580511614509000217 73902022935383710881750163)
  ·
    refine ⟨110853034403075566322625245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73902022935383710881750163 110853034403075566322625245)
    ·
      refine ⟨41569887901153337370984467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110853034403075566322625245 41569887901153337370984467)
      ·
        refine ⟨62354831851730006056476701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41569887901153337370984467 62354831851730006056476701)
        ·
          refine ⟨23383061944398752271178763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62354831851730006056476701 23383061944398752271178763)
          ·
            refine ⟨35074592916598128406768145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23383061944398752271178763 35074592916598128406768145)
            ·
              refine ⟨26305944687448596305076109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35074592916598128406768145 26305944687448596305076109)
              ·
                refine ⟨9864729257793223614403541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26305944687448596305076109 9864729257793223614403541)
                ·
                  refine ⟨231204591979528678462583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9864729257793223614403541 231204591979528678462583)
                  ·
                    rfl

theorem cell23_4052424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 3, 7].length) (baseStart_4052424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4052424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4052424 prefixEnd_4052424 := by exact prefixLift 4052424
  have htrace : WordTrace (prefixWord ++ tailWord_4052424) baseStart_4052424 baseEnd_4052424 := by
    simpa [prefixWord, tailWord_4052424, baseEnd_4052424] using wordTrace_append hprefix tailTrace_4052424
  have hstable : (prefixWord ++ tailWord_4052424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4052424).length < 2 ^ (prefixWord ++ tailWord_4052424).sum := by decide
  have hdescent : baseEnd_4052424 < baseStart_4052424 := by decide
  rcases family_descends (prefixWord ++ tailWord_4052424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4052469 : List Nat := [1, 3, 5, 1, 1, 3, 1, 2, 2, 2, 2]
def baseStart_4052469 : Nat := 118140960795 + 4052469 * 2 ^ 59
def prefixEnd_4052469 : Nat := 4983230072969 + 3 ^ 40 * 4052469 * 2
def baseEnd_4052469 : Nat := 2080864434445210430100541

theorem tailTrace_4052469 : CollatzResearch.WordTrace tailWord_4052469 prefixEnd_4052469 2080864434445210430100541 := by
  unfold tailWord_4052469
  simp only [CollatzResearch.WordTrace]
  refine ⟨147805687155604394448888461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98537124770402929632592307 147805687155604394448888461)
  ·
    refine ⟨55427132683351647918333173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147805687155604394448888461 55427132683351647918333173)
    ·
      refine ⟨5196293689064216992343735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55427132683351647918333173 5196293689064216992343735)
      ·
        refine ⟨7794440533596325488515603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5196293689064216992343735 7794440533596325488515603)
        ·
          refine ⟨11691660800394488232773405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7794440533596325488515603 11691660800394488232773405)
          ·
            refine ⟨4384372800147933087290027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11691660800394488232773405 4384372800147933087290027)
            ·
              refine ⟨6576559200221899630935041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4384372800147933087290027 6576559200221899630935041)
              ·
                refine ⟨4932419400166424723201281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6576559200221899630935041 4932419400166424723201281)
                ·
                  refine ⟨3699314550124818542400961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4932419400166424723201281 3699314550124818542400961)
                  ·
                    refine ⟨2774485912593613906800721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3699314550124818542400961 2774485912593613906800721)
                    ·
                      refine ⟨2080864434445210430100541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2774485912593613906800721 2080864434445210430100541)
                      ·
                        rfl

theorem cell23_4052469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 1, 2, 2, 2, 2].length) (baseStart_4052469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4052469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4052469 prefixEnd_4052469 := by exact prefixLift 4052469
  have htrace : WordTrace (prefixWord ++ tailWord_4052469) baseStart_4052469 baseEnd_4052469 := by
    simpa [prefixWord, tailWord_4052469, baseEnd_4052469] using wordTrace_append hprefix tailTrace_4052469
  have hstable : (prefixWord ++ tailWord_4052469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4052469).length < 2 ^ (prefixWord ++ tailWord_4052469).sum := by decide
  have hdescent : baseEnd_4052469 < baseStart_4052469 := by decide
  rcases family_descends (prefixWord ++ tailWord_4052469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4052486 : List Nat := [6, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2]
def baseStart_4052486 : Nat := 118140960795 + 4052486 * 2 ^ 59
def prefixEnd_4052486 : Nat := 4983230072969 + 3 ^ 40 * 4052486 * 2
def baseEnd_4052486 : Nat := 2080873163616336863587963

theorem tailTrace_4052486 : CollatzResearch.WordTrace tailWord_4052486 prefixEnd_4052486 2080873163616336863587963 := by
  unfold tailWord_4052486
  simp only [CollatzResearch.WordTrace]
  refine ⟨4618947099891962698508041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 98537538131028537568171541 4618947099891962698508041)
  ·
    refine ⟨3464210324918972023881031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4618947099891962698508041 3464210324918972023881031)
    ·
      refine ⟨5196315487378458035821547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3464210324918972023881031 5196315487378458035821547)
      ·
        refine ⟨7794473231067687053732321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5196315487378458035821547 7794473231067687053732321)
        ·
          refine ⟨5845854923300765290299241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7794473231067687053732321 5845854923300765290299241)
          ·
            refine ⟨4384391192475573967724431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5845854923300765290299241 4384391192475573967724431)
            ·
              refine ⟨6576586788713360951586647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4384391192475573967724431 6576586788713360951586647)
              ·
                refine ⟨9864880183070041427379971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6576586788713360951586647 9864880183070041427379971)
                ·
                  refine ⟨14797320274605062141069957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9864880183070041427379971 14797320274605062141069957)
                  ·
                    refine ⟨2774497551488449151450617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14797320274605062141069957 2774497551488449151450617)
                    ·
                      refine ⟨2080873163616336863587963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2774497551488449151450617 2080873163616336863587963)
                      ·
                        rfl

theorem cell23_4052486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2].length) (baseStart_4052486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4052486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4052486 prefixEnd_4052486 := by exact prefixLift 4052486
  have htrace : WordTrace (prefixWord ++ tailWord_4052486) baseStart_4052486 baseEnd_4052486 := by
    simpa [prefixWord, tailWord_4052486, baseEnd_4052486] using wordTrace_append hprefix tailTrace_4052486
  have hstable : (prefixWord ++ tailWord_4052486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4052486).length < 2 ^ (prefixWord ++ tailWord_4052486).sum := by decide
  have hdescent : baseEnd_4052486 < baseStart_4052486 := by decide
  rcases family_descends (prefixWord ++ tailWord_4052486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4052511 : List Nat := [1, 1, 2, 4, 1, 1, 4, 1, 1, 4, 3]
def baseStart_4052511 : Nat := 118140960795 + 4052511 * 2 ^ 59
def prefixEnd_4052511 : Nat := 4983230072969 + 3 ^ 40 * 4052511 * 2
def baseEnd_4052511 : Nat := 2080886000632699265775347

theorem tailTrace_4052511 : CollatzResearch.WordTrace tailWord_4052511 prefixEnd_4052511 2080886000632699265775347 := by
  unfold tailWord_4052511
  simp only [CollatzResearch.WordTrace]
  refine ⟨147807219021452235621917387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98538146014301490414611591 147807219021452235621917387)
  ·
    refine ⟨221710828532178353432876081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147807219021452235621917387 221710828532178353432876081)
    ·
      refine ⟨166283121399133765074657061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221710828532178353432876081 166283121399133765074657061)
      ·
        refine ⟨31178085262337580951498199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 166283121399133765074657061 31178085262337580951498199)
        ·
          refine ⟨46767127893506371427247299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31178085262337580951498199 46767127893506371427247299)
          ·
            refine ⟨70150691840259557140870949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46767127893506371427247299 70150691840259557140870949)
            ·
              refine ⟨13153254720048666963913303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70150691840259557140870949 13153254720048666963913303)
              ·
                refine ⟨19729882080073000445869955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13153254720048666963913303 19729882080073000445869955)
                ·
                  refine ⟨29594823120109500668804933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19729882080073000445869955 29594823120109500668804933)
                  ·
                    refine ⟨5549029335020531375400925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29594823120109500668804933 5549029335020531375400925)
                    ·
                      refine ⟨2080886000632699265775347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5549029335020531375400925 2080886000632699265775347)
                      ·
                        rfl

theorem cell23_4052511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 1, 1, 4, 3].length) (baseStart_4052511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4052511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4052511 prefixEnd_4052511 := by exact prefixLift 4052511
  have htrace : WordTrace (prefixWord ++ tailWord_4052511) baseStart_4052511 baseEnd_4052511 := by
    simpa [prefixWord, tailWord_4052511, baseEnd_4052511] using wordTrace_append hprefix tailTrace_4052511
  have hstable : (prefixWord ++ tailWord_4052511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4052511).length < 2 ^ (prefixWord ++ tailWord_4052511).sum := by decide
  have hdescent : baseEnd_4052511 < baseStart_4052511 := by decide
  rcases family_descends (prefixWord ++ tailWord_4052511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4052544 : List Nat := [2, 1, 1, 2, 2, 2, 1, 1, 2, 9]
def baseStart_4052544 : Nat := 118140960795 + 4052544 * 2 ^ 59
def prefixEnd_4052544 : Nat := 4983230072969 + 3 ^ 40 * 4052544 * 2
def baseEnd_4052544 : Nat := 693634315164765878887565

theorem tailTrace_4052544 : CollatzResearch.WordTrace tailWord_4052544 prefixEnd_4052544 693634315164765878887565 := by
  unfold tailWord_4052544
  simp only [CollatzResearch.WordTrace]
  refine ⟨73904211315166341128934343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98538948420221788171912457 73904211315166341128934343)
  ·
    refine ⟨110856316972749511693401515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73904211315166341128934343 110856316972749511693401515)
    ·
      refine ⟨166284475459124267540102273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110856316972749511693401515 166284475459124267540102273)
      ·
        refine ⟨124713356594343200655076705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166284475459124267540102273 124713356594343200655076705)
        ·
          refine ⟨93535017445757400491307529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124713356594343200655076705 93535017445757400491307529)
          ·
            refine ⟨70151263084318050368480647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93535017445757400491307529 70151263084318050368480647)
            ·
              refine ⟨105226894626477075552720971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70151263084318050368480647 105226894626477075552720971)
              ·
                refine ⟨157840341939715613329081457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105226894626477075552720971 157840341939715613329081457)
                ·
                  refine ⟨118380256454786709996811093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 157840341939715613329081457 118380256454786709996811093)
                  ·
                    refine ⟨693634315164765878887565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 118380256454786709996811093 693634315164765878887565)
                    ·
                      rfl

theorem cell23_4052544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 2, 9].length) (baseStart_4052544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4052544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4052544 prefixEnd_4052544 := by exact prefixLift 4052544
  have htrace : WordTrace (prefixWord ++ tailWord_4052544) baseStart_4052544 baseEnd_4052544 := by
    simpa [prefixWord, tailWord_4052544, baseEnd_4052544] using wordTrace_append hprefix tailTrace_4052544
  have hstable : (prefixWord ++ tailWord_4052544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4052544).length < 2 ^ (prefixWord ++ tailWord_4052544).sum := by decide
  have hdescent : baseEnd_4052544 < baseStart_4052544 := by decide
  rcases family_descends (prefixWord ++ tailWord_4052544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4052558 : List Nat := [4, 1, 1, 1, 1, 2, 1, 3, 5, 1, 3]
def baseStart_4052558 : Nat := 118140960795 + 4052558 * 2 ^ 59
def prefixEnd_4052558 : Nat := 4983230072969 + 3 ^ 40 * 4052558 * 2
def baseEnd_4052558 : Nat := 2080910134223460581887631

theorem tailTrace_4052558 : CollatzResearch.WordTrace tailWord_4052558 prefixEnd_4052558 2080910134223460581887631 := by
  unfold tailWord_4052558
  simp only [CollatzResearch.WordTrace]
  refine ⟨18476116656535245331109791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98539288834854641765918885 18476116656535245331109791)
  ·
    refine ⟨27714174984802867996664687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18476116656535245331109791 27714174984802867996664687)
    ·
      refine ⟨41571262477204301994997031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27714174984802867996664687 41571262477204301994997031)
      ·
        refine ⟨62356893715806452992495547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41571262477204301994997031 62356893715806452992495547)
        ·
          refine ⟨93535340573709679488743321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62356893715806452992495547 93535340573709679488743321)
          ·
            refine ⟨70151505430282259616557491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93535340573709679488743321 70151505430282259616557491)
            ·
              refine ⟨105227258145423389424836237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70151505430282259616557491 105227258145423389424836237)
              ·
                refine ⟨39460221804533771034313589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105227258145423389424836237 39460221804533771034313589)
                ·
                  refine ⟨3699395794175041034466899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39460221804533771034313589 3699395794175041034466899)
                  ·
                    refine ⟨5549093691262561551700349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3699395794175041034466899 5549093691262561551700349)
                    ·
                      refine ⟨2080910134223460581887631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5549093691262561551700349 2080910134223460581887631)
                      ·
                        rfl

theorem cell23_4052558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 3, 5, 1, 3].length) (baseStart_4052558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4052558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4052558 prefixEnd_4052558 := by exact prefixLift 4052558
  have htrace : WordTrace (prefixWord ++ tailWord_4052558) baseStart_4052558 baseEnd_4052558 := by
    simpa [prefixWord, tailWord_4052558, baseEnd_4052558] using wordTrace_append hprefix tailTrace_4052558
  have hstable : (prefixWord ++ tailWord_4052558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4052558).length < 2 ^ (prefixWord ++ tailWord_4052558).sum := by decide
  have hdescent : baseEnd_4052558 < baseStart_4052558 := by decide
  rcases family_descends (prefixWord ++ tailWord_4052558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4052561 : List Nat := [1, 2, 2, 1, 3, 2, 3, 1, 3, 5]
def baseStart_4052561 : Nat := 118140960795 + 4052561 * 2 ^ 59
def prefixEnd_4052561 : Nat := 4983230072969 + 3 ^ 40 * 4052561 * 2
def baseEnd_4052561 : Nat := 693637224888474690050039

theorem tailTrace_4052561 : CollatzResearch.WordTrace tailWord_4052561 prefixEnd_4052561 693637224888474690050039 := by
  unfold tailWord_4052561
  simp only [CollatzResearch.WordTrace]
  refine ⟨147809042671271094161237537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98539361780847396107491691 147809042671271094161237537)
  ·
    refine ⟨110856782003453320620928153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147809042671271094161237537 110856782003453320620928153)
    ·
      refine ⟨83142586502589990465696115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110856782003453320620928153 83142586502589990465696115)
      ·
        refine ⟨124713879753884985698544173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83142586502589990465696115 124713879753884985698544173)
        ·
          refine ⟨46767704907706869636954065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124713879753884985698544173 46767704907706869636954065)
          ·
            refine ⟨35075778680780152227715549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46767704907706869636954065 35075778680780152227715549)
            ·
              refine ⟨13153417005292557085393331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35075778680780152227715549 13153417005292557085393331)
              ·
                refine ⟨19730125507938835628089997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13153417005292557085393331 19730125507938835628089997)
                ·
                  refine ⟨7398797065477063360533749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19730125507938835628089997 7398797065477063360533749)
                  ·
                    refine ⟨693637224888474690050039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7398797065477063360533749 693637224888474690050039)
                    ·
                      rfl

theorem cell23_4052561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 1, 3, 5].length) (baseStart_4052561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4052561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4052561 prefixEnd_4052561 := by exact prefixLift 4052561
  have htrace : WordTrace (prefixWord ++ tailWord_4052561) baseStart_4052561 baseEnd_4052561 := by
    simpa [prefixWord, tailWord_4052561, baseEnd_4052561] using wordTrace_append hprefix tailTrace_4052561
  have hstable : (prefixWord ++ tailWord_4052561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4052561).length < 2 ^ (prefixWord ++ tailWord_4052561).sum := by decide
  have hdescent : baseEnd_4052561 < baseStart_4052561 := by decide
  rcases family_descends (prefixWord ++ tailWord_4052561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4052592 : List Nat := [2, 1, 1, 1, 6, 2, 1, 4, 1, 1, 3]
def baseStart_4052592 : Nat := 118140960795 + 4052592 * 2 ^ 59
def prefixEnd_4052592 : Nat := 4983230072969 + 3 ^ 40 * 4052592 * 2
def baseEnd_4052592 : Nat := 2080927592565713448862475

theorem tailTrace_4052592 : CollatzResearch.WordTrace tailWord_4052592 prefixEnd_4052592 2080927592565713448862475 := by
  unfold tailWord_4052592
  simp only [CollatzResearch.WordTrace]
  refine ⟨73905086667079393227808015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98540115556105857637077353 73905086667079393227808015)
  ·
    refine ⟨110857630000619089841712023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73905086667079393227808015 110857630000619089841712023)
    ·
      refine ⟨166286445000928634762568035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110857630000619089841712023 166286445000928634762568035)
      ·
        refine ⟨249429667501392952143852053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166286445000928634762568035 249429667501392952143852053)
        ·
          refine ⟨11692015664127794631743065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 249429667501392952143852053 11692015664127794631743065)
          ·
            refine ⟨8769011748095845973807299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11692015664127794631743065 8769011748095845973807299)
            ·
              refine ⟨13153517622143768960710949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8769011748095845973807299 13153517622143768960710949)
              ·
                refine ⟨2466284554151956680133303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13153517622143768960710949 2466284554151956680133303)
                ·
                  refine ⟨3699426831227935020199955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2466284554151956680133303 3699426831227935020199955)
                  ·
                    refine ⟨5549140246841902530299933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3699426831227935020199955 5549140246841902530299933)
                    ·
                      refine ⟨2080927592565713448862475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5549140246841902530299933 2080927592565713448862475)
                      ·
                        rfl

theorem cell23_4052592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 4, 1, 1, 3].length) (baseStart_4052592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4052592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4052592 prefixEnd_4052592 := by exact prefixLift 4052592
  have htrace : WordTrace (prefixWord ++ tailWord_4052592) baseStart_4052592 baseEnd_4052592 := by
    simpa [prefixWord, tailWord_4052592, baseEnd_4052592] using wordTrace_append hprefix tailTrace_4052592
  have hstable : (prefixWord ++ tailWord_4052592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4052592).length < 2 ^ (prefixWord ++ tailWord_4052592).sum := by decide
  have hdescent : baseEnd_4052592 < baseStart_4052592 := by decide
  rcases family_descends (prefixWord ++ tailWord_4052592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4052601 : List Nat := [1, 2, 1, 3, 3, 1, 2, 1, 3, 1, 5]
def baseStart_4052601 : Nat := 118140960795 + 4052601 * 2 ^ 59
def prefixEnd_4052601 : Nat := 4983230072969 + 3 ^ 40 * 4052601 * 2
def baseEnd_4052601 : Nat := 2080932213891603913649933

theorem tailTrace_4052601 : CollatzResearch.WordTrace tailWord_4052601 prefixEnd_4052601 2080932213891603913649933 := by
  unfold tailWord_4052601
  simp only [CollatzResearch.WordTrace]
  refine ⟨147810501591126180992693657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98540334394084120661795771 147810501591126180992693657)
  ·
    refine ⟨110857876193344635744520243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147810501591126180992693657 110857876193344635744520243)
    ·
      refine ⟨166286814290016953616780365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110857876193344635744520243 166286814290016953616780365)
      ·
        refine ⟨62357555358756357606292637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166286814290016953616780365 62357555358756357606292637)
        ·
          refine ⟨23384083259533634102359739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62357555358756357606292637 23384083259533634102359739)
          ·
            refine ⟨35076124889300451153539609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23384083259533634102359739 35076124889300451153539609)
            ·
              refine ⟨26307093666975338365154707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35076124889300451153539609 26307093666975338365154707)
              ·
                refine ⟨39460640500463007547732061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26307093666975338365154707 39460640500463007547732061)
                ·
                  refine ⟨14797740187673627830399523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39460640500463007547732061 14797740187673627830399523)
                  ·
                    refine ⟨22196610281510441745599285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14797740187673627830399523 22196610281510441745599285)
                    ·
                      refine ⟨2080932213891603913649933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22196610281510441745599285 2080932213891603913649933)
                      ·
                        rfl

theorem cell23_4052601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 1, 3, 1, 5].length) (baseStart_4052601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4052601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4052601 prefixEnd_4052601 := by exact prefixLift 4052601
  have htrace : WordTrace (prefixWord ++ tailWord_4052601) baseStart_4052601 baseEnd_4052601 := by
    simpa [prefixWord, tailWord_4052601, baseEnd_4052601] using wordTrace_append hprefix tailTrace_4052601
  have hstable : (prefixWord ++ tailWord_4052601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4052601).length < 2 ^ (prefixWord ++ tailWord_4052601).sum := by decide
  have hdescent : baseEnd_4052601 < baseStart_4052601 := by decide
  rcases family_descends (prefixWord ++ tailWord_4052601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4052608 : List Nat := [2, 1, 1, 2, 1, 4, 1, 5, 2, 4]
def baseStart_4052608 : Nat := 118140960795 + 4052608 * 2 ^ 59
def prefixEnd_4052608 : Nat := 4983230072969 + 3 ^ 40 * 4052608 * 2
def baseEnd_4052608 : Nat := 693645269418728462087467

theorem tailTrace_4052608 : CollatzResearch.WordTrace tailWord_4052608 prefixEnd_4052608 693645269418728462087467 := by
  unfold tailWord_4052608
  simp only [CollatzResearch.WordTrace]
  refine ⟨73905378451050410594099239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98540504601400547458798985 73905378451050410594099239)
  ·
    refine ⟨110858067676575615891148859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73905378451050410594099239 110858067676575615891148859)
    ·
      refine ⟨166287101514863423836723289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110858067676575615891148859 166287101514863423836723289)
      ·
        refine ⟨124715326136147567877542467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166287101514863423836723289 124715326136147567877542467)
        ·
          refine ⟨187072989204221351816313701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124715326136147567877542467 187072989204221351816313701)
          ·
            refine ⟨35076185475791503465558819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 187072989204221351816313701 35076185475791503465558819)
            ·
              refine ⟨52614278213687255198338229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35076185475791503465558819 52614278213687255198338229)
              ·
                refine ⟨4932588582533180174844209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52614278213687255198338229 4932588582533180174844209)
                ·
                  refine ⟨3699441436899885131133157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4932588582533180174844209 3699441436899885131133157)
                  ·
                    refine ⟨693645269418728462087467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3699441436899885131133157 693645269418728462087467)
                    ·
                      rfl

theorem cell23_4052608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 5, 2, 4].length) (baseStart_4052608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4052608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4052608 prefixEnd_4052608 := by exact prefixLift 4052608
  have htrace : WordTrace (prefixWord ++ tailWord_4052608) baseStart_4052608 baseEnd_4052608 := by
    simpa [prefixWord, tailWord_4052608, baseEnd_4052608] using wordTrace_append hprefix tailTrace_4052608
  have hstable : (prefixWord ++ tailWord_4052608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4052608).length < 2 ^ (prefixWord ++ tailWord_4052608).sum := by decide
  have hdescent : baseEnd_4052608 < baseStart_4052608 := by decide
  rcases family_descends (prefixWord ++ tailWord_4052608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4052615 : List Nat := [1, 1, 4, 2, 1, 3, 1, 1, 5, 2, 2]
def baseStart_4052615 : Nat := 118140960795 + 4052615 * 2 ^ 59
def prefixEnd_4052615 : Nat := 4983230072969 + 3 ^ 40 * 4052615 * 2
def baseEnd_4052615 : Nat := 2080939402620766858874869

theorem tailTrace_4052615 : CollatzResearch.WordTrace tailWord_4052615 prefixEnd_4052615 2080939402620766858874869 := by
  unfold tailWord_4052615
  simp only [CollatzResearch.WordTrace]
  refine ⟨147811012213075461383703299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98540674808716974255802199 147811012213075461383703299)
  ·
    refine ⟨221716518319613192075554949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147811012213075461383703299 221716518319613192075554949)
    ·
      refine ⟨41571847184927473514166553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 221716518319613192075554949 41571847184927473514166553)
      ·
        refine ⟨31178885388695605135624915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41571847184927473514166553 31178885388695605135624915)
        ·
          refine ⟨46768328083043407703437373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31178885388695605135624915 46768328083043407703437373)
          ·
            refine ⟨17538123031141277888789015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46768328083043407703437373 17538123031141277888789015)
            ·
              refine ⟨26307184546711916833183523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17538123031141277888789015 26307184546711916833183523)
              ·
                refine ⟨39460776820067875249775285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26307184546711916833183523 39460776820067875249775285)
                ·
                  refine ⟨3699447826881363304666433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39460776820067875249775285 3699447826881363304666433)
                  ·
                    refine ⟨2774585870161022478499825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3699447826881363304666433 2774585870161022478499825)
                    ·
                      refine ⟨2080939402620766858874869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2774585870161022478499825 2080939402620766858874869)
                      ·
                        rfl

theorem cell23_4052615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 1, 5, 2, 2].length) (baseStart_4052615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4052615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4052615 prefixEnd_4052615 := by exact prefixLift 4052615
  have htrace : WordTrace (prefixWord ++ tailWord_4052615) baseStart_4052615 baseEnd_4052615 := by
    simpa [prefixWord, tailWord_4052615, baseEnd_4052615] using wordTrace_append hprefix tailTrace_4052615
  have hstable : (prefixWord ++ tailWord_4052615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4052615).length < 2 ^ (prefixWord ++ tailWord_4052615).sum := by decide
  have hdescent : baseEnd_4052615 < baseStart_4052615 := by decide
  rcases family_descends (prefixWord ++ tailWord_4052615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4052632 : List Nat := [2, 1, 2, 4, 1, 4, 2, 1, 1, 1, 4]
def baseStart_4052632 : Nat := 118140960795 + 4052632 * 2 ^ 59
def prefixEnd_4052632 : Nat := 4983230072969 + 3 ^ 40 * 4052632 * 2
def baseEnd_4052632 : Nat := 2080948131791893292362291

theorem tailTrace_4052632 : CollatzResearch.WordTrace tailWord_4052632 prefixEnd_4052632 2080948131791893292362291 := by
  unfold tailWord_4052632
  simp only [CollatzResearch.WordTrace]
  refine ⟨73905816127006936643536075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98541088169342582191381433 73905816127006936643536075)
  ·
    refine ⟨110858724190510404965304113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73905816127006936643536075 110858724190510404965304113)
    ·
      refine ⟨83144043142882803723978085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110858724190510404965304113 83144043142882803723978085)
      ·
        refine ⟨15589508089290525698245891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83144043142882803723978085 15589508089290525698245891)
        ·
          refine ⟨23384262133935788547368837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15589508089290525698245891 23384262133935788547368837)
          ·
            refine ⟨4384549150112960352631657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23384262133935788547368837 4384549150112960352631657)
            ·
              refine ⟨3288411862584720264473743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4384549150112960352631657 3288411862584720264473743)
              ·
                refine ⟨4932617793877080396710615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3288411862584720264473743 4932617793877080396710615)
                ·
                  refine ⟨7398926690815620595065923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4932617793877080396710615 7398926690815620595065923)
                  ·
                    refine ⟨11098390036223430892598885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7398926690815620595065923 11098390036223430892598885)
                    ·
                      refine ⟨2080948131791893292362291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11098390036223430892598885 2080948131791893292362291)
                      ·
                        rfl

theorem cell23_4052632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 2, 1, 1, 1, 4].length) (baseStart_4052632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4052632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4052632 prefixEnd_4052632 := by exact prefixLift 4052632
  have htrace : WordTrace (prefixWord ++ tailWord_4052632) baseStart_4052632 baseEnd_4052632 := by
    simpa [prefixWord, tailWord_4052632, baseEnd_4052632] using wordTrace_append hprefix tailTrace_4052632
  have hstable : (prefixWord ++ tailWord_4052632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4052632).length < 2 ^ (prefixWord ++ tailWord_4052632).sum := by decide
  have hdescent : baseEnd_4052632 < baseStart_4052632 := by decide
  rcases family_descends (prefixWord ++ tailWord_4052632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4052638 : List Nat := [4, 3, 1, 1, 1, 3, 10]
def baseStart_4052638 : Nat := 118140960795 + 4052638 * 2 ^ 59
def prefixEnd_4052638 : Nat := 4983230072969 + 3 ^ 40 * 4052638 * 2
def baseEnd_4052638 : Nat := 25690755712047163813423

theorem tailTrace_4052638 : CollatzResearch.WordTrace tailWord_4052638 prefixEnd_4052638 25690755712047163813423 := by
  unfold tailWord_4052638
  simp only [CollatzResearch.WordTrace]
  refine ⟨18476481386499017038973821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98541234061328090874527045 18476481386499017038973821)
  ·
    refine ⟨6928680519937131389615183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18476481386499017038973821 6928680519937131389615183)
    ·
      refine ⟨10393020779905697084422775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6928680519937131389615183 10393020779905697084422775)
      ·
        refine ⟨15589531169858545626634163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10393020779905697084422775 15589531169858545626634163)
        ·
          refine ⟨23384296754787818439951245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15589531169858545626634163 23384296754787818439951245)
          ·
            refine ⟨8769111283045431914981717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23384296754787818439951245 8769111283045431914981717)
            ·
              refine ⟨25690755712047163813423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 8769111283045431914981717 25690755712047163813423)
              ·
                rfl

theorem cell23_4052638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 10].length) (baseStart_4052638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4052638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4052638 prefixEnd_4052638 := by exact prefixLift 4052638
  have htrace : WordTrace (prefixWord ++ tailWord_4052638) baseStart_4052638 baseEnd_4052638 := by
    simpa [prefixWord, tailWord_4052638, baseEnd_4052638] using wordTrace_append hprefix tailTrace_4052638
  have hstable : (prefixWord ++ tailWord_4052638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4052638).length < 2 ^ (prefixWord ++ tailWord_4052638).sum := by decide
  have hdescent : baseEnd_4052638 < baseStart_4052638 := by decide
  rcases family_descends (prefixWord ++ tailWord_4052638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4052642 : List Nat := [3, 3, 1, 4, 1, 1, 1, 1, 4, 4]
def baseStart_4052642 : Nat := 118140960795 + 4052642 * 2 ^ 59
def prefixEnd_4052642 : Nat := 4983230072969 + 3 ^ 40 * 4052642 * 2
def baseEnd_4052642 : Nat := 693651088866146084412415

theorem tailTrace_4052642 : CollatzResearch.WordTrace tailWord_4052642 prefixEnd_4052642 693651088866146084412415 := by
  unfold tailWord_4052642
  simp only [CollatzResearch.WordTrace]
  refine ⟨36952999245994411248734045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98541331322651763329957453 36952999245994411248734045)
  ·
    refine ⟨13857374717247904218275267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36952999245994411248734045 13857374717247904218275267)
    ·
      refine ⟨20786062075871856327412901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13857374717247904218275267 20786062075871856327412901)
      ·
        refine ⟨3897386639225973061389919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20786062075871856327412901 3897386639225973061389919)
        ·
          refine ⟨5846079958838959592084879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3897386639225973061389919 5846079958838959592084879)
          ·
            refine ⟨8769119938258439388127319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5846079958838959592084879 8769119938258439388127319)
            ·
              refine ⟨13153679907387659082190979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8769119938258439388127319 13153679907387659082190979)
              ·
                refine ⟨19730519861081488623286469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13153679907387659082190979 19730519861081488623286469)
                ·
                  refine ⟨3699472473952779116866213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19730519861081488623286469 3699472473952779116866213)
                  ·
                    refine ⟨693651088866146084412415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3699472473952779116866213 693651088866146084412415)
                    ·
                      rfl

theorem cell23_4052642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 1, 4, 4].length) (baseStart_4052642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4052642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4052642 prefixEnd_4052642 := by exact prefixLift 4052642
  have htrace : WordTrace (prefixWord ++ tailWord_4052642) baseStart_4052642 baseEnd_4052642 := by
    simpa [prefixWord, tailWord_4052642, baseEnd_4052642] using wordTrace_append hprefix tailTrace_4052642
  have hstable : (prefixWord ++ tailWord_4052642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4052642).length < 2 ^ (prefixWord ++ tailWord_4052642).sum := by decide
  have hdescent : baseEnd_4052642 < baseStart_4052642 := by decide
  rcases family_descends (prefixWord ++ tailWord_4052642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4052662 : List Nat := [5, 1, 3, 1, 1, 1, 3, 1, 1, 2, 4]
def baseStart_4052662 : Nat := 118140960795 + 4052662 * 2 ^ 59
def prefixEnd_4052662 : Nat := 4983230072969 + 3 ^ 40 * 4052662 * 2
def baseEnd_4052662 : Nat := 2080963536211528174987153

theorem tailTrace_4052662 : CollatzResearch.WordTrace tailWord_4052662 prefixEnd_4052662 2080963536211528174987153 := by
  unfold tailWord_4052662
  simp only [CollatzResearch.WordTrace]
  refine ⟨9238295402744074275666515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 98541817629270125607109493 9238295402744074275666515)
  ·
    refine ⟨13857443104116111413499773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9238295402744074275666515 13857443104116111413499773)
    ·
      refine ⟨5196541164043541780062415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13857443104116111413499773 5196541164043541780062415)
      ·
        refine ⟨7794811746065312670093623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5196541164043541780062415 7794811746065312670093623)
        ·
          refine ⟨11692217619097969005140435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7794811746065312670093623 11692217619097969005140435)
          ·
            refine ⟨17538326428646953507710653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11692217619097969005140435 17538326428646953507710653)
            ·
              refine ⟨6576872410742607565391495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17538326428646953507710653 6576872410742607565391495)
              ·
                refine ⟨9865308616113911348087243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6576872410742607565391495 9865308616113911348087243)
                ·
                  refine ⟨14797962924170867022130865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9865308616113911348087243 14797962924170867022130865)
                  ·
                    refine ⟨11098472193128150266598149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14797962924170867022130865 11098472193128150266598149)
                    ·
                      refine ⟨2080963536211528174987153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11098472193128150266598149 2080963536211528174987153)
                      ·
                        rfl

theorem cell23_4052662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_4052662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4052662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4052662 prefixEnd_4052662 := by exact prefixLift 4052662
  have htrace : WordTrace (prefixWord ++ tailWord_4052662) baseStart_4052662 baseEnd_4052662 := by
    simpa [prefixWord, tailWord_4052662, baseEnd_4052662] using wordTrace_append hprefix tailTrace_4052662
  have hstable : (prefixWord ++ tailWord_4052662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4052662).length < 2 ^ (prefixWord ++ tailWord_4052662).sum := by decide
  have hdescent : baseEnd_4052662 < baseStart_4052662 := by decide
  rcases family_descends (prefixWord ++ tailWord_4052662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4052665 : List Nat := [1, 2, 1, 4, 1, 1, 2, 5, 2, 1, 3]
def baseStart_4052665 : Nat := 118140960795 + 4052665 * 2 ^ 59
def prefixEnd_4052665 : Nat := 4983230072969 + 3 ^ 40 * 4052665 * 2
def baseEnd_4052665 : Nat := 2080965076653491663249639

theorem tailTrace_4052665 : CollatzResearch.WordTrace tailWord_4052665 prefixEnd_4052665 2080965076653491663249639 := by
  unfold tailWord_4052665
  simp only [CollatzResearch.WordTrace]
  refine ⟨147812835862894319923023449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98541890575262879948682299 147812835862894319923023449)
  ·
    refine ⟨110859626897170739942267587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147812835862894319923023449 110859626897170739942267587)
    ·
      refine ⟨166289440345756109913401381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110859626897170739942267587 166289440345756109913401381)
      ·
        refine ⟨31179270064829270608762759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 166289440345756109913401381 31179270064829270608762759)
        ·
          refine ⟨46768905097243905913144139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31179270064829270608762759 46768905097243905913144139)
          ·
            refine ⟨70153357645865858869716209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46768905097243905913144139 70153357645865858869716209)
            ·
              refine ⟨52615018234399394152287157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70153357645865858869716209 52615018234399394152287157)
              ·
                refine ⟨4932657959474943201776921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52615018234399394152287157 4932657959474943201776921)
                ·
                  refine ⟨3699493469606207401332691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4932657959474943201776921 3699493469606207401332691)
                  ·
                    refine ⟨5549240204409311101999037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3699493469606207401332691 5549240204409311101999037)
                    ·
                      refine ⟨2080965076653491663249639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5549240204409311101999037 2080965076653491663249639)
                      ·
                        rfl

theorem cell23_4052665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 5, 2, 1, 3].length) (baseStart_4052665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4052665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4052665 prefixEnd_4052665 := by exact prefixLift 4052665
  have htrace : WordTrace (prefixWord ++ tailWord_4052665) baseStart_4052665 baseEnd_4052665 := by
    simpa [prefixWord, tailWord_4052665, baseEnd_4052665] using wordTrace_append hprefix tailTrace_4052665
  have hstable : (prefixWord ++ tailWord_4052665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4052665).length < 2 ^ (prefixWord ++ tailWord_4052665).sum := by decide
  have hdescent : baseEnd_4052665 < baseStart_4052665 := by decide
  rcases family_descends (prefixWord ++ tailWord_4052665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4052708 : List Nat := [2, 3, 1, 1, 1, 3, 2, 1, 2, 4, 3]
def baseStart_4052708 : Nat := 118140960795 + 4052708 * 2 ^ 59
def prefixEnd_4052708 : Nat := 4983230072969 + 3 ^ 40 * 4052708 * 2
def baseEnd_4052708 : Nat := 2080987156321634995011941

theorem tailTrace_4052708 : CollatzResearch.WordTrace tailWord_4052708 prefixEnd_4052708 2080987156321634995011941 := by
  unfold tailWord_4052708
  simp only [CollatzResearch.WordTrace]
  refine ⟨73907202100869269133419389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98542936134492358844559185 73907202100869269133419389)
  ·
    refine ⟨27715200787825975925032271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73907202100869269133419389 27715200787825975925032271)
    ·
      refine ⟨41572801181738963887548407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27715200787825975925032271 41572801181738963887548407)
      ·
        refine ⟨62359201772608445831322611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41572801181738963887548407 62359201772608445831322611)
        ·
          refine ⟨93538802658912668746983917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62359201772608445831322611 93538802658912668746983917)
          ·
            refine ⟨35077050997092250780118969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93538802658912668746983917 35077050997092250780118969)
            ·
              refine ⟨26307788247819188085089227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35077050997092250780118969 26307788247819188085089227)
              ·
                refine ⟨39461682371728782127633841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26307788247819188085089227 39461682371728782127633841)
                ·
                  refine ⟨29596261778796586595725381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39461682371728782127633841 29596261778796586595725381)
                  ·
                    refine ⟨5549299083524359986698509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29596261778796586595725381 5549299083524359986698509)
                    ·
                      refine ⟨2080987156321634995011941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5549299083524359986698509 2080987156321634995011941)
                      ·
                        rfl

theorem cell23_4052708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 1, 2, 4, 3].length) (baseStart_4052708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4052708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4052708 prefixEnd_4052708 := by exact prefixLift 4052708
  have htrace : WordTrace (prefixWord ++ tailWord_4052708) baseStart_4052708 baseEnd_4052708 := by
    simpa [prefixWord, tailWord_4052708, baseEnd_4052708] using wordTrace_append hprefix tailTrace_4052708
  have hstable : (prefixWord ++ tailWord_4052708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4052708).length < 2 ^ (prefixWord ++ tailWord_4052708).sum := by decide
  have hdescent : baseEnd_4052708 < baseStart_4052708 := by decide
  rcases family_descends (prefixWord ++ tailWord_4052708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4052718 : List Nat := [4, 1, 2, 1, 1, 2, 2, 1, 1, 4, 4]
def baseStart_4052718 : Nat := 118140960795 + 4052718 * 2 ^ 59
def prefixEnd_4052718 : Nat := 4983230072969 + 3 ^ 40 * 4052718 * 2
def baseEnd_4052718 : Nat := 2080992291128179955886895

theorem tailTrace_4052718 : CollatzResearch.WordTrace tailWord_4052718 prefixEnd_4052718 2080992291128179955886895 := by
  unfold tailWord_4052718
  simp only [CollatzResearch.WordTrace]
  refine ⟨18476846116462788746837851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98543179287801539983135205 18476846116462788746837851)
  ·
    refine ⟨27715269174694183120256777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18476846116462788746837851 27715269174694183120256777)
    ·
      refine ⟨20786451881020637340192583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27715269174694183120256777 20786451881020637340192583)
      ·
        refine ⟨31179677821530956010288875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20786451881020637340192583 31179677821530956010288875)
        ·
          refine ⟨46769516732296434015433313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31179677821530956010288875 46769516732296434015433313)
          ·
            refine ⟨35077137549222325511574985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46769516732296434015433313 35077137549222325511574985)
            ·
              refine ⟨26307853161916744133681239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35077137549222325511574985 26307853161916744133681239)
              ·
                refine ⟨39461779742875116200521859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26307853161916744133681239 39461779742875116200521859)
                ·
                  refine ⟨59192669614312674300782789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39461779742875116200521859 59192669614312674300782789)
                  ·
                    refine ⟨11098625552683626431396773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59192669614312674300782789 11098625552683626431396773)
                    ·
                      refine ⟨2080992291128179955886895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11098625552683626431396773 2080992291128179955886895)
                      ·
                        rfl

theorem cell23_4052718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 1, 1, 4, 4].length) (baseStart_4052718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4052718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4052718 prefixEnd_4052718 := by exact prefixLift 4052718
  have htrace : WordTrace (prefixWord ++ tailWord_4052718) baseStart_4052718 baseEnd_4052718 := by
    simpa [prefixWord, tailWord_4052718, baseEnd_4052718] using wordTrace_append hprefix tailTrace_4052718
  have hstable : (prefixWord ++ tailWord_4052718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4052718).length < 2 ^ (prefixWord ++ tailWord_4052718).sum := by decide
  have hdescent : baseEnd_4052718 < baseStart_4052718 := by decide
  rcases family_descends (prefixWord ++ tailWord_4052718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4052762 : List Nat := [3, 1, 1, 3, 2, 2, 4, 2, 5]
def baseStart_4052762 : Nat := 118140960795 + 4052762 * 2 ^ 59
def prefixEnd_4052762 : Nat := 4983230072969 + 3 ^ 40 * 4052762 * 2
def baseEnd_4052762 : Nat := 231223876030775309304077

theorem tailTrace_4052762 : CollatzResearch.WordTrace tailWord_4052762 prefixEnd_4052762 231223876030775309304077 := by
  unfold tailWord_4052762
  simp only [CollatzResearch.WordTrace]
  refine ⟨36954093435885726372326135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98544249162361936992869693 36954093435885726372326135)
  ·
    refine ⟨55431140153828589558489203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36954093435885726372326135 55431140153828589558489203)
    ·
      refine ⟨83146710230742884337733805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55431140153828589558489203 83146710230742884337733805)
      ·
        refine ⟨31180016336528581626650177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83146710230742884337733805 31180016336528581626650177)
        ·
          refine ⟨23385012252396436219987633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31180016336528581626650177 23385012252396436219987633)
          ·
            refine ⟨17538759189297327164990725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23385012252396436219987633 17538759189297327164990725)
            ·
              refine ⟨3288517347993248843435761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17538759189297327164990725 3288517347993248843435761)
              ·
                refine ⟨2466388010994936632576821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3288517347993248843435761 2466388010994936632576821)
                ·
                  refine ⟨231223876030775309304077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2466388010994936632576821 231223876030775309304077)
                  ·
                    rfl

theorem cell23_4052762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 4, 2, 5].length) (baseStart_4052762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4052762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4052762 prefixEnd_4052762 := by exact prefixLift 4052762
  have htrace : WordTrace (prefixWord ++ tailWord_4052762) baseStart_4052762 baseEnd_4052762 := by
    simpa [prefixWord, tailWord_4052762, baseEnd_4052762] using wordTrace_append hprefix tailTrace_4052762
  have hstable : (prefixWord ++ tailWord_4052762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4052762).length < 2 ^ (prefixWord ++ tailWord_4052762).sum := by decide
  have hdescent : baseEnd_4052762 < baseStart_4052762 := by decide
  rcases family_descends (prefixWord ++ tailWord_4052762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4052768 : List Nat := [2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 5]
def baseStart_4052768 : Nat := 118140960795 + 4052768 * 2 ^ 59
def prefixEnd_4052768 : Nat := 4983230072969 + 3 ^ 40 * 4052768 * 2
def baseEnd_4052768 : Nat := 2081017965160904760261665

theorem tailTrace_4052768 : CollatzResearch.WordTrace tailWord_4052768 prefixEnd_4052768 2081017965160904760261665 := by
  unfold tailWord_4052768
  simp only [CollatzResearch.WordTrace]
  refine ⟨73908296290760584257011479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98544395054347445676015305 73908296290760584257011479)
  ·
    refine ⟨110862444436140876385517219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73908296290760584257011479 110862444436140876385517219)
    ·
      refine ⟨166293666654211314578275829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110862444436140876385517219 166293666654211314578275829)
      ·
        refine ⟨15590031248832310741713359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 166293666654211314578275829 15590031248832310741713359)
        ·
          refine ⟨23385046873248466112570039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15590031248832310741713359 23385046873248466112570039)
          ·
            refine ⟨35077570309872699168855059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23385046873248466112570039 35077570309872699168855059)
            ·
              refine ⟨52616355464809048753282589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35077570309872699168855059 52616355464809048753282589)
              ·
                refine ⟨19731133299303393282480971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52616355464809048753282589 19731133299303393282480971)
                ·
                  refine ⟨29596699948955089923721457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19731133299303393282480971 29596699948955089923721457)
                  ·
                    refine ⟨22197524961716317442791093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29596699948955089923721457 22197524961716317442791093)
                    ·
                      refine ⟨2081017965160904760261665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22197524961716317442791093 2081017965160904760261665)
                      ·
                        rfl

theorem cell23_4052768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_4052768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4052768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4052768 prefixEnd_4052768 := by exact prefixLift 4052768
  have htrace : WordTrace (prefixWord ++ tailWord_4052768) baseStart_4052768 baseEnd_4052768 := by
    simpa [prefixWord, tailWord_4052768, baseEnd_4052768] using wordTrace_append hprefix tailTrace_4052768
  have hstable : (prefixWord ++ tailWord_4052768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4052768).length < 2 ^ (prefixWord ++ tailWord_4052768).sum := by decide
  have hdescent : baseEnd_4052768 < baseStart_4052768 := by decide
  rcases family_descends (prefixWord ++ tailWord_4052768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4052808 : List Nat := [2, 1, 3, 1, 1, 4, 1, 1, 2, 1, 6]
def baseStart_4052808 : Nat := 118140960795 + 4052808 * 2 ^ 59
def prefixEnd_4052808 : Nat := 4983230072969 + 3 ^ 40 * 4052808 * 2
def baseEnd_4052808 : Nat := 2081038504387084603761481

theorem tailTrace_4052808 : CollatzResearch.WordTrace tailWord_4052808 prefixEnd_4052808 2081038504387084603761481 := by
  unfold tailWord_4052808
  simp only [CollatzResearch.WordTrace]
  refine ⟨73909025750688127672739539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98545367667584170230319385 73909025750688127672739539)
  ·
    refine ⟨110863538626032191509109309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73909025750688127672739539 110863538626032191509109309)
    ·
      refine ⟨41573826984762071815915991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110863538626032191509109309 41573826984762071815915991)
      ·
        refine ⟨62360740477143107723873987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41573826984762071815915991 62360740477143107723873987)
        ·
          refine ⟨93541110715714661585810981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62360740477143107723873987 93541110715714661585810981)
          ·
            refine ⟨17538958259196499047339559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93541110715714661585810981 17538958259196499047339559)
            ·
              refine ⟨26308437388794748571009339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17538958259196499047339559 26308437388794748571009339)
              ·
                refine ⟨39462656083192122856514009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26308437388794748571009339 39462656083192122856514009)
                ·
                  refine ⟨29596992062394092142385507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39462656083192122856514009 29596992062394092142385507)
                  ·
                    refine ⟨44395488093591138213578261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29596992062394092142385507 44395488093591138213578261)
                    ·
                      refine ⟨2081038504387084603761481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44395488093591138213578261 2081038504387084603761481)
                      ·
                        rfl

theorem cell23_4052808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 1, 2, 1, 6].length) (baseStart_4052808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4052808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4052808 prefixEnd_4052808 := by exact prefixLift 4052808
  have htrace : WordTrace (prefixWord ++ tailWord_4052808) baseStart_4052808 baseEnd_4052808 := by
    simpa [prefixWord, tailWord_4052808, baseEnd_4052808] using wordTrace_append hprefix tailTrace_4052808
  have hstable : (prefixWord ++ tailWord_4052808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4052808).length < 2 ^ (prefixWord ++ tailWord_4052808).sum := by decide
  have hdescent : baseEnd_4052808 < baseStart_4052808 := by decide
  rcases family_descends (prefixWord ++ tailWord_4052808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4052885 : List Nat := [1, 3, 2, 1, 1, 3, 2, 2, 3, 1, 4]
def baseStart_4052885 : Nat := 118140960795 + 4052885 * 2 ^ 59
def prefixEnd_4052885 : Nat := 4983230072969 + 3 ^ 40 * 4052885 * 2
def baseEnd_4052885 : Nat := 2081078042397480802498627

theorem tailTrace_4052885 : CollatzResearch.WordTrace tailWord_4052885 prefixEnd_4052885 2081078042397480802498627 := by
  unfold tailWord_4052885
  simp only [CollatzResearch.WordTrace]
  refine ⟨147820859922097297496032109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98547239948064864997354739 147820859922097297496032109)
  ·
    refine ⟨55432822470786486561012041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147820859922097297496032109 55432822470786486561012041)
    ·
      refine ⟨41574616853089864920759031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55432822470786486561012041 41574616853089864920759031)
      ·
        refine ⟨62361925279634797381138547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41574616853089864920759031 62361925279634797381138547)
        ·
          refine ⟨93542887919452196071707821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62361925279634797381138547 93542887919452196071707821)
          ·
            refine ⟨35078582969794573526890433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93542887919452196071707821 35078582969794573526890433)
            ·
              refine ⟨26308937227345930145167825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35078582969794573526890433 26308937227345930145167825)
              ·
                refine ⟨19731702920509447608875869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26308937227345930145167825 19731702920509447608875869)
                ·
                  refine ⟨7399388595191042853328451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19731702920509447608875869 7399388595191042853328451)
                  ·
                    refine ⟨11099082892786564279992677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7399388595191042853328451 11099082892786564279992677)
                    ·
                      refine ⟨2081078042397480802498627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11099082892786564279992677 2081078042397480802498627)
                      ·
                        rfl

theorem cell23_4052885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 2, 3, 1, 4].length) (baseStart_4052885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4052885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4052885 prefixEnd_4052885 := by exact prefixLift 4052885
  have htrace : WordTrace (prefixWord ++ tailWord_4052885) baseStart_4052885 baseEnd_4052885 := by
    simpa [prefixWord, tailWord_4052885, baseEnd_4052885] using wordTrace_append hprefix tailTrace_4052885
  have hstable : (prefixWord ++ tailWord_4052885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4052885).length < 2 ^ (prefixWord ++ tailWord_4052885).sum := by decide
  have hdescent : baseEnd_4052885 < baseStart_4052885 := by decide
  rcases family_descends (prefixWord ++ tailWord_4052885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4052886 : List Nat := [5, 3, 1, 1, 2, 1, 1, 3, 6]
def baseStart_4052886 : Nat := 118140960795 + 4052886 * 2 ^ 59
def prefixEnd_4052886 : Nat := 4983230072969 + 3 ^ 40 * 4052886 * 2
def baseEnd_4052886 : Nat := 231230950653126144287347

theorem tailTrace_4052886 : CollatzResearch.WordTrace tailWord_4052886 prefixEnd_4052886 231230950653126144287347 := by
  unfold tailWord_4052886
  simp only [CollatzResearch.WordTrace]
  refine ⟨9238806024693354666676157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 98547264263395783111212341 9238806024693354666676157)
  ·
    refine ⟨3464552259260008000003559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9238806024693354666676157 3464552259260008000003559)
    ·
      refine ⟨5196828388890012000005339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3464552259260008000003559 5196828388890012000005339)
      ·
        refine ⟨7795242583335018000008009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5196828388890012000005339 7795242583335018000008009)
        ·
          refine ⟨5846431937501263500006007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7795242583335018000008009 5846431937501263500006007)
          ·
            refine ⟨8769647906251895250009011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5846431937501263500006007 8769647906251895250009011)
            ·
              refine ⟨13154471859377842875013517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8769647906251895250009011 13154471859377842875013517)
              ·
                refine ⟨4932926947266691078130069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13154471859377842875013517 4932926947266691078130069)
                ·
                  refine ⟨231230950653126144287347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4932926947266691078130069 231230950653126144287347)
                  ·
                    rfl

theorem cell23_4052886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_4052886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4052886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4052886 prefixEnd_4052886 := by exact prefixLift 4052886
  have htrace : WordTrace (prefixWord ++ tailWord_4052886) baseStart_4052886 baseEnd_4052886 := by
    simpa [prefixWord, tailWord_4052886, baseEnd_4052886] using wordTrace_append hprefix tailTrace_4052886
  have hstable : (prefixWord ++ tailWord_4052886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4052886).length < 2 ^ (prefixWord ++ tailWord_4052886).sum := by decide
  have hdescent : baseEnd_4052886 < baseStart_4052886 := by decide
  rcases family_descends (prefixWord ++ tailWord_4052886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4052915 : List Nat := [1, 1, 1, 2, 3, 1, 5, 2, 1, 2, 4]
def baseStart_4052915 : Nat := 118140960795 + 4052915 * 2 ^ 59
def prefixEnd_4052915 : Nat := 4983230072969 + 3 ^ 40 * 4052915 * 2
def baseEnd_4052915 : Nat := 2081093446817115685123489

theorem tailTrace_4052915 : CollatzResearch.WordTrace tailWord_4052915 prefixEnd_4052915 2081093446817115685123489 := by
  unfold tailWord_4052915
  simp only [CollatzResearch.WordTrace]
  refine ⟨147821954111988612619624199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98547969407992408413082799 147821954111988612619624199)
  ·
    refine ⟨221732931167982918929436299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147821954111988612619624199 221732931167982918929436299)
    ·
      refine ⟨332599396751974378394154449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221732931167982918929436299 332599396751974378394154449)
      ·
        refine ⟨249449547563980783795615837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 332599396751974378394154449 249449547563980783795615837)
        ·
          refine ⟨93543580336492793923355939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 249449547563980783795615837 93543580336492793923355939)
          ·
            refine ⟨140315370504739190885033909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93543580336492793923355939 140315370504739190885033909)
            ·
              refine ⟨13154565984819299145471929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 140315370504739190885033909 13154565984819299145471929)
              ·
                refine ⟨9865924488614474359103947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13154565984819299145471929 9865924488614474359103947)
                ·
                  refine ⟨14798886732921711538655921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9865924488614474359103947 14798886732921711538655921)
                  ·
                    refine ⟨11099165049691283653991941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14798886732921711538655921 11099165049691283653991941)
                    ·
                      refine ⟨2081093446817115685123489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11099165049691283653991941 2081093446817115685123489)
                      ·
                        rfl

theorem cell23_4052915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 2, 1, 2, 4].length) (baseStart_4052915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4052915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4052915 prefixEnd_4052915 := by exact prefixLift 4052915
  have htrace : WordTrace (prefixWord ++ tailWord_4052915) baseStart_4052915 baseEnd_4052915 := by
    simpa [prefixWord, tailWord_4052915, baseEnd_4052915] using wordTrace_append hprefix tailTrace_4052915
  have hstable : (prefixWord ++ tailWord_4052915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4052915).length < 2 ^ (prefixWord ++ tailWord_4052915).sum := by decide
  have hdescent : baseEnd_4052915 < baseStart_4052915 := by decide
  rcases family_descends (prefixWord ++ tailWord_4052915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4052935 : List Nat := [1, 1, 4, 1, 1, 2, 1, 1, 5, 3, 3]
def baseStart_4052935 : Nat := 118140960795 + 4052935 * 2 ^ 59
def prefixEnd_4052935 : Nat := 4983230072969 + 3 ^ 40 * 4052935 * 2
def baseEnd_4052935 : Nat := 2081103716430205606873397

theorem tailTrace_4052935 : CollatzResearch.WordTrace tailWord_4052935 prefixEnd_4052935 2081103716430205606873397 := by
  unfold tailWord_4052935
  simp only [CollatzResearch.WordTrace]
  refine ⟨147822683571916156035352259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98548455714610770690234839 147822683571916156035352259)
  ·
    refine ⟨221734025357874234053028389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147822683571916156035352259 221734025357874234053028389)
    ·
      refine ⟨41575129754601418884942823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 221734025357874234053028389 41575129754601418884942823)
      ·
        refine ⟨62362694631902128327414235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41575129754601418884942823 62362694631902128327414235)
        ·
          refine ⟨93544041947853192491121353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62362694631902128327414235 93544041947853192491121353)
          ·
            refine ⟨70158031460889894368341015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93544041947853192491121353 70158031460889894368341015)
            ·
              refine ⟨105237047191334841552511523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70158031460889894368341015 105237047191334841552511523)
              ·
                refine ⟨157855570787002262328767285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105237047191334841552511523 157855570787002262328767285)
                ·
                  refine ⟨14798959761281462093321933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 157855570787002262328767285 14798959761281462093321933)
                  ·
                    refine ⟨5549609910480548284995725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14798959761281462093321933 5549609910480548284995725)
                    ·
                      refine ⟨2081103716430205606873397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5549609910480548284995725 2081103716430205606873397)
                      ·
                        rfl

theorem cell23_4052935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 5, 3, 3].length) (baseStart_4052935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4052935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4052935 prefixEnd_4052935 := by exact prefixLift 4052935
  have htrace : WordTrace (prefixWord ++ tailWord_4052935) baseStart_4052935 baseEnd_4052935 := by
    simpa [prefixWord, tailWord_4052935, baseEnd_4052935] using wordTrace_append hprefix tailTrace_4052935
  have hstable : (prefixWord ++ tailWord_4052935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4052935).length < 2 ^ (prefixWord ++ tailWord_4052935).sum := by decide
  have hdescent : baseEnd_4052935 < baseStart_4052935 := by decide
  rcases family_descends (prefixWord ++ tailWord_4052935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4052952 : List Nat := [2, 1, 2, 2, 2, 2, 4, 1, 1, 3, 3]
def baseStart_4052952 : Nat := 118140960795 + 4052952 * 2 ^ 59
def prefixEnd_4052952 : Nat := 4983230072969 + 3 ^ 40 * 4052952 * 2
def baseEnd_4052952 : Nat := 2081112445601332040360819

theorem tailTrace_4052952 : CollatzResearch.WordTrace tailWord_4052952 prefixEnd_4052952 2081112445601332040360819 := by
  unfold tailWord_4052952
  simp only [CollatzResearch.WordTrace]
  refine ⟨73911651806427283969360555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98548869075236378625814073 73911651806427283969360555)
  ·
    refine ⟨110867477709640925954040833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73911651806427283969360555 110867477709640925954040833)
    ·
      refine ⟨83150608282230694465530625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110867477709640925954040833 83150608282230694465530625)
      ·
        refine ⟨62362956211673020849147969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83150608282230694465530625 62362956211673020849147969)
        ·
          refine ⟨46772217158754765636860977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62362956211673020849147969 46772217158754765636860977)
          ·
            refine ⟨35079162869066074227645733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46772217158754765636860977 35079162869066074227645733)
            ·
              refine ⟨6577343037949888917683575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35079162869066074227645733 6577343037949888917683575)
              ·
                refine ⟨9866014556924833376525363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6577343037949888917683575 9866014556924833376525363)
                ·
                  refine ⟨14799021835387250064788045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9866014556924833376525363 14799021835387250064788045)
                  ·
                    refine ⟨5549633188270218774295517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14799021835387250064788045 5549633188270218774295517)
                    ·
                      refine ⟨2081112445601332040360819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5549633188270218774295517 2081112445601332040360819)
                      ·
                        rfl

theorem cell23_4052952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4, 1, 1, 3, 3].length) (baseStart_4052952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4052952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4052952 prefixEnd_4052952 := by exact prefixLift 4052952
  have htrace : WordTrace (prefixWord ++ tailWord_4052952) baseStart_4052952 baseEnd_4052952 := by
    simpa [prefixWord, tailWord_4052952, baseEnd_4052952] using wordTrace_append hprefix tailTrace_4052952
  have hstable : (prefixWord ++ tailWord_4052952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4052952).length < 2 ^ (prefixWord ++ tailWord_4052952).sum := by decide
  have hdescent : baseEnd_4052952 < baseStart_4052952 := by decide
  rcases family_descends (prefixWord ++ tailWord_4052952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4052985 : List Nat := [1, 2, 1, 3, 1, 4, 1, 2, 2, 6]
def baseStart_4052985 : Nat := 118140960795 + 4052985 * 2 ^ 59
def prefixEnd_4052985 : Nat := 4983230072969 + 3 ^ 40 * 4052985 * 2
def baseEnd_4052985 : Nat := 693709796820976803749389

theorem tailTrace_4052985 : CollatzResearch.WordTrace tailWord_4052985 prefixEnd_4052985 693709796820976803749389 := by
  unfold tailWord_4052985
  simp only [CollatzResearch.WordTrace]
  refine ⟨147824507221735014574672409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98549671481156676383114939 147824507221735014574672409)
  ·
    refine ⟨110868380416301260931004307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147824507221735014574672409 110868380416301260931004307)
    ·
      refine ⟨166302570624451891396506461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110868380416301260931004307 166302570624451891396506461)
      ·
        refine ⟨62363463984169459273689923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166302570624451891396506461 62363463984169459273689923)
        ·
          refine ⟨93545195976254188910534885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62363463984169459273689923 93545195976254188910534885)
          ·
            refine ⟨17539724245547660420725291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93545195976254188910534885 17539724245547660420725291)
            ·
              refine ⟨26309586368321490631087937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17539724245547660420725291 26309586368321490631087937)
              ·
                refine ⟨19732189776241117973315953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26309586368321490631087937 19732189776241117973315953)
                ·
                  refine ⟨14799142332180838479986965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19732189776241117973315953 14799142332180838479986965)
                  ·
                    refine ⟨693709796820976803749389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14799142332180838479986965 693709796820976803749389)
                    ·
                      rfl

theorem cell23_4052985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 2, 2, 6].length) (baseStart_4052985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4052985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4052985 prefixEnd_4052985 := by exact prefixLift 4052985
  have htrace : WordTrace (prefixWord ++ tailWord_4052985) baseStart_4052985 baseEnd_4052985 := by
    simpa [prefixWord, tailWord_4052985, baseEnd_4052985] using wordTrace_append hprefix tailTrace_4052985
  have hstable : (prefixWord ++ tailWord_4052985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4052985).length < 2 ^ (prefixWord ++ tailWord_4052985).sum := by decide
  have hdescent : baseEnd_4052985 < baseStart_4052985 := by decide
  rcases family_descends (prefixWord ++ tailWord_4052985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4052995 : List Nat := [1, 1, 1, 3, 2, 1, 1, 3, 1, 6, 3]
def baseStart_4052995 : Nat := 118140960795 + 4052995 * 2 ^ 59
def prefixEnd_4052995 : Nat := 4983230072969 + 3 ^ 40 * 4052995 * 2
def baseEnd_4052995 : Nat := 2081134525269475372123121

theorem tailTrace_4052995 : CollatzResearch.WordTrace tailWord_4052995 prefixEnd_4052995 2081134525269475372123121 := by
  unfold tailWord_4052995
  simp only [CollatzResearch.WordTrace]
  refine ⟨147824871951698786282536439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98549914634465857521690959 147824871951698786282536439)
  ·
    refine ⟨221737307927548179423804659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147824871951698786282536439 221737307927548179423804659)
    ·
      refine ⟨332605961891322269135706989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221737307927548179423804659 332605961891322269135706989)
      ·
        refine ⟨124727235709245850925890121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 332605961891322269135706989 124727235709245850925890121)
        ·
          refine ⟨93545426781934388194417591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124727235709245850925890121 93545426781934388194417591)
          ·
            refine ⟨140318140172901582291626387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93545426781934388194417591 140318140172901582291626387)
            ·
              refine ⟨210477210259352373437439581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140318140172901582291626387 210477210259352373437439581)
              ·
                refine ⟨78928953847257140039039843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 210477210259352373437439581 78928953847257140039039843)
                ·
                  refine ⟨118393430770885710058559765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78928953847257140039039843 118393430770885710058559765)
                  ·
                    refine ⟨5549692067385267658994989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 118393430770885710058559765 5549692067385267658994989)
                    ·
                      refine ⟨2081134525269475372123121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5549692067385267658994989 2081134525269475372123121)
                      ·
                        rfl

theorem cell23_4052995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 6, 3].length) (baseStart_4052995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4052995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4052995 prefixEnd_4052995 := by exact prefixLift 4052995
  have htrace : WordTrace (prefixWord ++ tailWord_4052995) baseStart_4052995 baseEnd_4052995 := by
    simpa [prefixWord, tailWord_4052995, baseEnd_4052995] using wordTrace_append hprefix tailTrace_4052995
  have hstable : (prefixWord ++ tailWord_4052995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4052995).length < 2 ^ (prefixWord ++ tailWord_4052995).sum := by decide
  have hdescent : baseEnd_4052995 < baseStart_4052995 := by decide
  rcases family_descends (prefixWord ++ tailWord_4052995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4053049 : List Nat := [1, 2, 1, 5, 3, 2, 1, 1, 7]
def baseStart_4053049 : Nat := 118140960795 + 4053049 * 2 ^ 59
def prefixEnd_4053049 : Nat := 4983230072969 + 3 ^ 40 * 4053049 * 2
def baseEnd_4053049 : Nat := 231240250358313128983097

theorem tailTrace_4053049 : CollatzResearch.WordTrace tailWord_4053049 prefixEnd_4053049 231240250358313128983097 := by
  unfold tailWord_4053049
  simp only [CollatzResearch.WordTrace]
  refine ⟨147826841493503153505002201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98551227662335435670001467 147826841493503153505002201)
  ·
    refine ⟨110870131120127365128751651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147826841493503153505002201 110870131120127365128751651)
    ·
      refine ⟨166305196680191047693127477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110870131120127365128751651 166305196680191047693127477)
      ·
        refine ⟨15591112188767910721230701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 166305196680191047693127477 15591112188767910721230701)
        ·
          refine ⟨5846667070787966520461513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15591112188767910721230701 5846667070787966520461513)
          ·
            refine ⟨4385000303090974890346135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5846667070787966520461513 4385000303090974890346135)
            ·
              refine ⟨6577500454636462335519203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4385000303090974890346135 6577500454636462335519203)
              ·
                refine ⟨9866250681954693503278805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6577500454636462335519203 9866250681954693503278805)
                ·
                  refine ⟨231240250358313128983097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9866250681954693503278805 231240250358313128983097)
                  ·
                    rfl

theorem cell23_4053049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 1, 1, 7].length) (baseStart_4053049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4053049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4053049 prefixEnd_4053049 := by exact prefixLift 4053049
  have htrace : WordTrace (prefixWord ++ tailWord_4053049) baseStart_4053049 baseEnd_4053049 := by
    simpa [prefixWord, tailWord_4053049, baseEnd_4053049] using wordTrace_append hprefix tailTrace_4053049
  have hstable : (prefixWord ++ tailWord_4053049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4053049).length < 2 ^ (prefixWord ++ tailWord_4053049).sum := by decide
  have hdescent : baseEnd_4053049 < baseStart_4053049 := by decide
  rcases family_descends (prefixWord ++ tailWord_4053049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4053055 : List Nat := [1, 1, 2, 2, 3, 1, 3, 1, 1, 1, 7]
def baseStart_4053055 : Nat := 118140960795 + 4053055 * 2 ^ 59
def prefixEnd_4053055 : Nat := 4983230072969 + 3 ^ 40 * 4053055 * 2
def baseEnd_4053055 : Nat := 2081165334108745137372845

theorem tailTrace_4053055 : CollatzResearch.WordTrace tailWord_4053055 prefixEnd_4053055 2081165334108745137372845 := by
  unfold tailWord_4053055
  simp only [CollatzResearch.WordTrace]
  refine ⟨147827060331481416529720619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98551373554320944353147079 147827060331481416529720619)
  ·
    refine ⟨221740590497222124794580929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147827060331481416529720619 221740590497222124794580929)
    ·
      refine ⟨166305442872916593595935697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221740590497222124794580929 166305442872916593595935697)
      ·
        refine ⟨124729082154687445196951773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166305442872916593595935697 124729082154687445196951773)
        ·
          refine ⟨46773405808007791948856915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124729082154687445196951773 46773405808007791948856915)
          ·
            refine ⟨70160108712011687923285373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46773405808007791948856915 70160108712011687923285373)
            ·
              refine ⟨26310040767004382971232015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70160108712011687923285373 26310040767004382971232015)
              ·
                refine ⟨39465061150506574456848023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26310040767004382971232015 39465061150506574456848023)
                ·
                  refine ⟨59197591725759861685272035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39465061150506574456848023 59197591725759861685272035)
                  ·
                    refine ⟨88796387588639792527908053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59197591725759861685272035 88796387588639792527908053)
                    ·
                      refine ⟨2081165334108745137372845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 88796387588639792527908053 2081165334108745137372845)
                      ·
                        rfl

theorem cell23_4053055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 1, 1, 1, 7].length) (baseStart_4053055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4053055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4053055 prefixEnd_4053055 := by exact prefixLift 4053055
  have htrace : WordTrace (prefixWord ++ tailWord_4053055) baseStart_4053055 baseEnd_4053055 := by
    simpa [prefixWord, tailWord_4053055, baseEnd_4053055] using wordTrace_append hprefix tailTrace_4053055
  have hstable : (prefixWord ++ tailWord_4053055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4053055).length < 2 ^ (prefixWord ++ tailWord_4053055).sum := by decide
  have hdescent : baseEnd_4053055 < baseStart_4053055 := by decide
  rcases family_descends (prefixWord ++ tailWord_4053055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4053102 : List Nat := [4, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5]
def baseStart_4053102 : Nat := 118140960795 + 4053102 * 2 ^ 59
def prefixEnd_4053102 : Nat := 4983230072969 + 3 ^ 40 * 4053102 * 2
def baseEnd_4053102 : Nat := 2081189467699506453485129

theorem tailTrace_4053102 : CollatzResearch.WordTrace tailWord_4053102 prefixEnd_4053102 2081189467699506453485129 := by
  unfold tailWord_4053102
  simp only [CollatzResearch.WordTrace]
  refine ⟨18478596820288892944585195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98552516374874095704454373 18478596820288892944585195)
  ·
    refine ⟨27717895230433339416877793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18478596820288892944585195 27717895230433339416877793)
    ·
      refine ⟨20788421422825004562658345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27717895230433339416877793 20788421422825004562658345)
      ·
        refine ⟨15591316067118753421993759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20788421422825004562658345 15591316067118753421993759)
        ·
          refine ⟨23386974100678130132990639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15591316067118753421993759 23386974100678130132990639)
          ·
            refine ⟨35080461151017195199485959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23386974100678130132990639 35080461151017195199485959)
            ·
              refine ⟨52620691726525792799228939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35080461151017195199485959 52620691726525792799228939)
              ·
                refine ⟨78931037589788689198843409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52620691726525792799228939 78931037589788689198843409)
                ·
                  refine ⟨59198278192341516899132557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78931037589788689198843409 59198278192341516899132557)
                  ·
                    refine ⟨22199354322128068837174709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59198278192341516899132557 22199354322128068837174709)
                    ·
                      refine ⟨2081189467699506453485129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22199354322128068837174709 2081189467699506453485129)
                      ·
                        rfl

theorem cell23_4053102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_4053102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4053102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4053102 prefixEnd_4053102 := by exact prefixLift 4053102
  have htrace : WordTrace (prefixWord ++ tailWord_4053102) baseStart_4053102 baseEnd_4053102 := by
    simpa [prefixWord, tailWord_4053102, baseEnd_4053102] using wordTrace_append hprefix tailTrace_4053102
  have hstable : (prefixWord ++ tailWord_4053102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4053102).length < 2 ^ (prefixWord ++ tailWord_4053102).sum := by decide
  have hdescent : baseEnd_4053102 < baseStart_4053102 := by decide
  rcases family_descends (prefixWord ++ tailWord_4053102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4053143 : List Nat := [1, 1, 3, 3, 4, 1, 2, 3, 1, 4]
def baseStart_4053143 : Nat := 118140960795 + 4053143 * 2 ^ 59
def prefixEnd_4053143 : Nat := 4983230072969 + 3 ^ 40 * 4053143 * 2
def baseEnd_4053143 : Nat := 693736840135446931024147

theorem tailTrace_4053143 : CollatzResearch.WordTrace tailWord_4053143 prefixEnd_4053143 693736840135446931024147 := by
  unfold tailWord_4053143
  simp only [CollatzResearch.WordTrace]
  refine ⟨147830269955162607558924083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98553513303441738372616055 147830269955162607558924083)
  ·
    refine ⟨221745404932743911338386125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147830269955162607558924083 221745404932743911338386125)
    ·
      refine ⟨83154526849778966751894797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221745404932743911338386125 83154526849778966751894797)
      ·
        refine ⟨31182947568667112531960549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83154526849778966751894797 31182947568667112531960549)
        ·
          refine ⟨5846802669125083599742603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31182947568667112531960549 5846802669125083599742603)
          ·
            refine ⟨8770204003687625399613905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5846802669125083599742603 8770204003687625399613905)
            ·
              refine ⟨6577653002765719049710429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8770204003687625399613905 6577653002765719049710429)
              ·
                refine ⟨2466619876037144643641411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6577653002765719049710429 2466619876037144643641411)
                ·
                  refine ⟨3699929814055716965462117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2466619876037144643641411 3699929814055716965462117)
                  ·
                    refine ⟨693736840135446931024147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3699929814055716965462117 693736840135446931024147)
                    ·
                      rfl

theorem cell23_4053143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 2, 3, 1, 4].length) (baseStart_4053143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4053143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4053143 prefixEnd_4053143 := by exact prefixLift 4053143
  have htrace : WordTrace (prefixWord ++ tailWord_4053143) baseStart_4053143 baseEnd_4053143 := by
    simpa [prefixWord, tailWord_4053143, baseEnd_4053143] using wordTrace_append hprefix tailTrace_4053143
  have hstable : (prefixWord ++ tailWord_4053143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4053143).length < 2 ^ (prefixWord ++ tailWord_4053143).sum := by decide
  have hdescent : baseEnd_4053143 < baseStart_4053143 := by decide
  rcases family_descends (prefixWord ++ tailWord_4053143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4053156 : List Nat := [2, 3, 1, 2, 4, 2, 1, 2, 6]
def baseStart_4053156 : Nat := 118140960795 + 4053156 * 2 ^ 59
def prefixEnd_4053156 : Nat := 4983230072969 + 3 ^ 40 * 4053156 * 2
def baseEnd_4053156 : Nat := 231246355072761026912209

theorem tailTrace_4053156 : CollatzResearch.WordTrace tailWord_4053156 prefixEnd_4053156 231246355072761026912209 := by
  unfold tailWord_4053156
  simp only [CollatzResearch.WordTrace]
  refine ⟨73915372052057755389573661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98553829402743673852764881 73915372052057755389573661)
  ·
    refine ⟨27718264519521658271090123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73915372052057755389573661 27718264519521658271090123)
    ·
      refine ⟨41577396779282487406635185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27718264519521658271090123 41577396779282487406635185)
      ·
        refine ⟨31183047584461865554976389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41577396779282487406635185 31183047584461865554976389)
        ·
          refine ⟨5846821422086599791558073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31183047584461865554976389 5846821422086599791558073)
          ·
            refine ⟨4385116066564949843668555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5846821422086599791558073 4385116066564949843668555)
            ·
              refine ⟨6577674099847424765502833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4385116066564949843668555 6577674099847424765502833)
              ·
                refine ⟨4933255574885568574127125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6577674099847424765502833 4933255574885568574127125)
                ·
                  refine ⟨231246355072761026912209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4933255574885568574127125 231246355072761026912209)
                  ·
                    rfl

theorem cell23_4053156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 1, 2, 6].length) (baseStart_4053156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4053156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4053156 prefixEnd_4053156 := by exact prefixLift 4053156
  have htrace : WordTrace (prefixWord ++ tailWord_4053156) baseStart_4053156 baseEnd_4053156 := by
    simpa [prefixWord, tailWord_4053156, baseEnd_4053156] using wordTrace_append hprefix tailTrace_4053156
  have hstable : (prefixWord ++ tailWord_4053156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4053156).length < 2 ^ (prefixWord ++ tailWord_4053156).sum := by decide
  have hdescent : baseEnd_4053156 < baseStart_4053156 := by decide
  rcases family_descends (prefixWord ++ tailWord_4053156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4053173 : List Nat := [1, 3, 3, 4, 1, 1, 3, 1, 6]
def baseStart_4053173 : Nat := 118140960795 + 4053173 * 2 ^ 59
def prefixEnd_4053173 : Nat := 4983230072969 + 3 ^ 40 * 4053173 * 2
def baseEnd_4053173 : Nat := 231247324980663963966367

theorem tailTrace_4053173 : CollatzResearch.WordTrace tailWord_4053173 prefixEnd_4053173 231247324980663963966367 := by
  unfold tailWord_4053173
  simp only [CollatzResearch.WordTrace]
  refine ⟨147831364145053922682516173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98554242763369281788344115 147831364145053922682516173)
  ·
    refine ⟨55436761554395221005943565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147831364145053922682516173 55436761554395221005943565)
    ·
      refine ⟨20788785582898207877228837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55436761554395221005943565 20788785582898207877228837)
      ·
        refine ⟨3897897296793413976980407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20788785582898207877228837 3897897296793413976980407)
        ·
          refine ⟨5846845945190120965470611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3897897296793413976980407 5846845945190120965470611)
          ·
            refine ⟨8770268917785181448205917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5846845945190120965470611 8770268917785181448205917)
            ·
              refine ⟨3288850844169443043077219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8770268917785181448205917 3288850844169443043077219)
              ·
                refine ⟨4933276266254164564615829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3288850844169443043077219 4933276266254164564615829)
                ·
                  refine ⟨231247324980663963966367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4933276266254164564615829 231247324980663963966367)
                  ·
                    rfl

theorem cell23_4053173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 3, 1, 6].length) (baseStart_4053173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4053173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4053173 prefixEnd_4053173 := by exact prefixLift 4053173
  have htrace : WordTrace (prefixWord ++ tailWord_4053173) baseStart_4053173 baseEnd_4053173 := by
    simpa [prefixWord, tailWord_4053173, baseEnd_4053173] using wordTrace_append hprefix tailTrace_4053173
  have hstable : (prefixWord ++ tailWord_4053173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4053173).length < 2 ^ (prefixWord ++ tailWord_4053173).sum := by decide
  have hdescent : baseEnd_4053173 < baseStart_4053173 := by decide
  rcases family_descends (prefixWord ++ tailWord_4053173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4053189 : List Nat := [1, 3, 1, 1, 1, 1, 5, 4, 1, 1, 4]
def baseStart_4053189 : Nat := 118140960795 + 4053189 * 2 ^ 59
def prefixEnd_4053189 : Nat := 4983230072969 + 3 ^ 40 * 4053189 * 2
def baseEnd_4053189 : Nat := 2081234140516447613097229

theorem tailTrace_4053189 : CollatzResearch.WordTrace tailWord_4053189 prefixEnd_4053189 2081234140516447613097229 := by
  unfold tailWord_4053189
  simp only [CollatzResearch.WordTrace]
  refine ⟨147831947712995957415098621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98554631808663971610065747 147831947712995957415098621)
  ·
    refine ⟨55436980392373484030661983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147831947712995957415098621 55436980392373484030661983)
    ·
      refine ⟨83155470588560226045992975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55436980392373484030661983 83155470588560226045992975)
      ·
        refine ⟨124733205882840339068989463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83155470588560226045992975 124733205882840339068989463)
        ·
          refine ⟨187099808824260508603484195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124733205882840339068989463 187099808824260508603484195)
          ·
            refine ⟨280649713236390762905226293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187099808824260508603484195 280649713236390762905226293)
            ·
              refine ⟨26310910615911634022364965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 280649713236390762905226293 26310910615911634022364965)
              ·
                refine ⟨4933295740483431379193431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26310910615911634022364965 4933295740483431379193431)
                ·
                  refine ⟨7399943610725147068790147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4933295740483431379193431 7399943610725147068790147)
                  ·
                    refine ⟨11099915416087720603185221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7399943610725147068790147 11099915416087720603185221)
                    ·
                      refine ⟨2081234140516447613097229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11099915416087720603185221 2081234140516447613097229)
                      ·
                        rfl

theorem cell23_4053189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 4, 1, 1, 4].length) (baseStart_4053189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4053189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4053189 prefixEnd_4053189 := by exact prefixLift 4053189
  have htrace : WordTrace (prefixWord ++ tailWord_4053189) baseStart_4053189 baseEnd_4053189 := by
    simpa [prefixWord, tailWord_4053189, baseEnd_4053189] using wordTrace_append hprefix tailTrace_4053189
  have hstable : (prefixWord ++ tailWord_4053189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4053189).length < 2 ^ (prefixWord ++ tailWord_4053189).sum := by decide
  have hdescent : baseEnd_4053189 < baseStart_4053189 := by decide
  rcases family_descends (prefixWord ++ tailWord_4053189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4053192 : List Nat := [2, 1, 3, 1, 2, 1, 1, 1, 5, 1, 5]
def baseStart_4053192 : Nat := 118140960795 + 4053192 * 2 ^ 59
def prefixEnd_4053192 : Nat := 4983230072969 + 3 ^ 40 * 4053192 * 2
def baseEnd_4053192 : Nat := 2081235680958411101359715

theorem tailTrace_4053192 : CollatzResearch.WordTrace tailWord_4053192 prefixEnd_4053192 2081235680958411101359715 := by
  unfold tailWord_4053192
  simp only [CollatzResearch.WordTrace]
  refine ⟨73916028565992544463728915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98554704754656725951638553 73916028565992544463728915)
  ·
    refine ⟨110874042848988816695593373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73916028565992544463728915 110874042848988816695593373)
    ·
      refine ⟨41577766068370806260847515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110874042848988816695593373 41577766068370806260847515)
      ·
        refine ⟨62366649102556209391271273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41577766068370806260847515 62366649102556209391271273)
        ·
          refine ⟨46774986826917157043453455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62366649102556209391271273 46774986826917157043453455)
          ·
            refine ⟨70162480240375735565180183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46774986826917157043453455 70162480240375735565180183)
            ·
              refine ⟨105243720360563603347770275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70162480240375735565180183 105243720360563603347770275)
              ·
                refine ⟨157865580540845405021655413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105243720360563603347770275 157865580540845405021655413)
                ·
                  refine ⟨14799898175704256720780195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 157865580540845405021655413 14799898175704256720780195)
                  ·
                    refine ⟨22199847263556385081170293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14799898175704256720780195 22199847263556385081170293)
                    ·
                      refine ⟨2081235680958411101359715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22199847263556385081170293 2081235680958411101359715)
                      ·
                        rfl

theorem cell23_4053192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 5, 1, 5].length) (baseStart_4053192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4053192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4053192 prefixEnd_4053192 := by exact prefixLift 4053192
  have htrace : WordTrace (prefixWord ++ tailWord_4053192) baseStart_4053192 baseEnd_4053192 := by
    simpa [prefixWord, tailWord_4053192, baseEnd_4053192] using wordTrace_append hprefix tailTrace_4053192
  have hstable : (prefixWord ++ tailWord_4053192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4053192).length < 2 ^ (prefixWord ++ tailWord_4053192).sum := by decide
  have hdescent : baseEnd_4053192 < baseStart_4053192 := by decide
  rcases family_descends (prefixWord ++ tailWord_4053192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4053256 : List Nat := [2, 1, 3, 2, 3, 2, 1, 2, 1, 3, 3]
def baseStart_4053256 : Nat := 118140960795 + 4053256 * 2 ^ 59
def prefixEnd_4053256 : Nat := 4983230072969 + 3 ^ 40 * 4053256 * 2
def baseEnd_4053256 : Nat := 2081268543720298850959421

theorem tailTrace_4053256 : CollatzResearch.WordTrace tailWord_4053256 prefixEnd_4053256 2081268543720298850959421 := by
  unfold tailWord_4053256
  simp only [CollatzResearch.WordTrace]
  refine ⟨73917195701876613928893811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98556260935835485238525081 73917195701876613928893811)
  ·
    refine ⟨110875793552814920893340717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73917195701876613928893811 110875793552814920893340717)
    ·
      refine ⟨41578422582305595335002769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110875793552814920893340717 41578422582305595335002769)
      ·
        refine ⟨31183816936729196501252077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41578422582305595335002769 31183816936729196501252077)
        ·
          refine ⟨11693931351273448687969529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31183816936729196501252077 11693931351273448687969529)
          ·
            refine ⟨8770448513455086515977147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11693931351273448687969529 8770448513455086515977147)
            ·
              refine ⟨13155672770182629773965721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8770448513455086515977147 13155672770182629773965721)
              ·
                refine ⟨9866754577636972330474291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13155672770182629773965721 9866754577636972330474291)
                ·
                  refine ⟨14800131866455458495711437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9866754577636972330474291 14800131866455458495711437)
                  ·
                    refine ⟨5550049449920796935891789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14800131866455458495711437 5550049449920796935891789)
                    ·
                      refine ⟨2081268543720298850959421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5550049449920796935891789 2081268543720298850959421)
                      ·
                        rfl

theorem cell23_4053256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 2, 1, 3, 3].length) (baseStart_4053256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4053256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4053256 prefixEnd_4053256 := by exact prefixLift 4053256
  have htrace : WordTrace (prefixWord ++ tailWord_4053256) baseStart_4053256 baseEnd_4053256 := by
    simpa [prefixWord, tailWord_4053256, baseEnd_4053256] using wordTrace_append hprefix tailTrace_4053256
  have hstable : (prefixWord ++ tailWord_4053256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4053256).length < 2 ^ (prefixWord ++ tailWord_4053256).sum := by decide
  have hdescent : baseEnd_4053256 < baseStart_4053256 := by decide
  rcases family_descends (prefixWord ++ tailWord_4053256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4053274 : List Nat := [3, 1, 1, 3, 4, 2, 2, 2, 1, 2, 2]
def baseStart_4053274 : Nat := 118140960795 + 4053274 * 2 ^ 59
def prefixEnd_4053274 : Nat := 4983230072969 + 3 ^ 40 * 4053274 * 2
def baseEnd_4053274 : Nat := 2081277786372079780534339

theorem tailTrace_4053274 : CollatzResearch.WordTrace tailWord_4053274 prefixEnd_4053274 2081277786372079780534339 := by
  unfold tailWord_4053274
  simp only [CollatzResearch.WordTrace]
  refine ⟨36958761979422004232985719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98556698611792011287961917 36958761979422004232985719)
  ·
    refine ⟨55438142969133006349478579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36958761979422004232985719 55438142969133006349478579)
    ·
      refine ⟨83157214453699509524217869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55438142969133006349478579 83157214453699509524217869)
      ·
        refine ⟨31183955420137316071581701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83157214453699509524217869 31183955420137316071581701)
        ·
          refine ⟨5846991641275746763421569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31183955420137316071581701 5846991641275746763421569)
          ·
            refine ⟨4385243730956810072566177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5846991641275746763421569 4385243730956810072566177)
            ·
              refine ⟨3288932798217607554424633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4385243730956810072566177 3288932798217607554424633)
              ·
                refine ⟨2466699598663205665818475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3288932798217607554424633 2466699598663205665818475)
                ·
                  refine ⟨3700049397994808498727713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2466699598663205665818475 3700049397994808498727713)
                  ·
                    refine ⟨2775037048496106374045785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3700049397994808498727713 2775037048496106374045785)
                    ·
                      refine ⟨2081277786372079780534339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2775037048496106374045785 2081277786372079780534339)
                      ·
                        rfl

theorem cell23_4053274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 2, 2, 1, 2, 2].length) (baseStart_4053274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4053274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4053274 prefixEnd_4053274 := by exact prefixLift 4053274
  have htrace : WordTrace (prefixWord ++ tailWord_4053274) baseStart_4053274 baseEnd_4053274 := by
    simpa [prefixWord, tailWord_4053274, baseEnd_4053274] using wordTrace_append hprefix tailTrace_4053274
  have hstable : (prefixWord ++ tailWord_4053274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4053274).length < 2 ^ (prefixWord ++ tailWord_4053274).sum := by decide
  have hdescent : baseEnd_4053274 < baseStart_4053274 := by decide
  rcases family_descends (prefixWord ++ tailWord_4053274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4053279 : List Nat := [1, 1, 2, 4, 3, 1, 1, 1, 2, 3, 4]
def baseStart_4053279 : Nat := 118140960795 + 4053279 * 2 ^ 59
def prefixEnd_4053279 : Nat := 4983230072969 + 3 ^ 40 * 4053279 * 2
def baseEnd_4053279 : Nat := 2081280353775352260971815

theorem tailTrace_4053279 : CollatzResearch.WordTrace tailWord_4053279 prefixEnd_4053279 2081280353775352260971815 := by
  unfold tailWord_4053279
  simp only [CollatzResearch.WordTrace]
  refine ⟨147835230282669902785874891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98556820188446601857249927 147835230282669902785874891)
  ·
    refine ⟨221752845424004854178812337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147835230282669902785874891 221752845424004854178812337)
    ·
      refine ⟨166314634068003640634109253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221752845424004854178812337 166314634068003640634109253)
      ·
        refine ⟨31183993887750682618895485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 166314634068003640634109253 31183993887750682618895485)
        ·
          refine ⟨11693997707906505982085807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31183993887750682618895485 11693997707906505982085807)
          ·
            refine ⟨17540996561859758973128711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11693997707906505982085807 17540996561859758973128711)
            ·
              refine ⟨26311494842789638459693067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17540996561859758973128711 26311494842789638459693067)
              ·
                refine ⟨39467242264184457689539601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26311494842789638459693067 39467242264184457689539601)
                ·
                  refine ⟨29600431698138343267154701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39467242264184457689539601 29600431698138343267154701)
                  ·
                    refine ⟨11100161886801878725183013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29600431698138343267154701 11100161886801878725183013)
                    ·
                      refine ⟨2081280353775352260971815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11100161886801878725183013 2081280353775352260971815)
                      ·
                        rfl

theorem cell23_4053279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 1, 2, 3, 4].length) (baseStart_4053279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4053279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4053279 prefixEnd_4053279 := by exact prefixLift 4053279
  have htrace : WordTrace (prefixWord ++ tailWord_4053279) baseStart_4053279 baseEnd_4053279 := by
    simpa [prefixWord, tailWord_4053279, baseEnd_4053279] using wordTrace_append hprefix tailTrace_4053279
  have hstable : (prefixWord ++ tailWord_4053279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4053279).length < 2 ^ (prefixWord ++ tailWord_4053279).sum := by decide
  have hdescent : baseEnd_4053279 < baseStart_4053279 := by decide
  rcases family_descends (prefixWord ++ tailWord_4053279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4053299 : List Nat := [1, 1, 1, 2, 5, 1, 1, 2, 2, 4, 3]
def baseStart_4053299 : Nat := 118140960795 + 4053299 * 2 ^ 59
def prefixEnd_4053299 : Nat := 4983230072969 + 3 ^ 40 * 4053299 * 2
def baseEnd_4053299 : Nat := 2081290623388442182721723

theorem tailTrace_4053299 : CollatzResearch.WordTrace tailWord_4053299 prefixEnd_4053299 2081290623388442182721723 := by
  unfold tailWord_4053299
  simp only [CollatzResearch.WordTrace]
  refine ⟨147835959742597446201602951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98557306495064964134401967 147835959742597446201602951)
  ·
    refine ⟨221753939613896169302404427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147835959742597446201602951 221753939613896169302404427)
    ·
      refine ⟨332630909420844253953606641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221753939613896169302404427 332630909420844253953606641)
      ·
        refine ⟨249473182065633190465204981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 332630909420844253953606641 249473182065633190465204981)
        ·
          refine ⟨23388110818653111606112967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 249473182065633190465204981 23388110818653111606112967)
          ·
            refine ⟨35082166227979667409169451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23388110818653111606112967 35082166227979667409169451)
            ·
              refine ⟨52623249341969501113754177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35082166227979667409169451 52623249341969501113754177)
              ·
                refine ⟨39467437006477125835315633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52623249341969501113754177 39467437006477125835315633)
                ·
                  refine ⟨29600577754857844376486725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39467437006477125835315633 29600577754857844376486725)
                  ·
                    refine ⟨5550108329035845820591261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29600577754857844376486725 5550108329035845820591261)
                    ·
                      refine ⟨2081290623388442182721723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5550108329035845820591261 2081290623388442182721723)
                      ·
                        rfl

theorem cell23_4053299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 2, 2, 4, 3].length) (baseStart_4053299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4053299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4053299 prefixEnd_4053299 := by exact prefixLift 4053299
  have htrace : WordTrace (prefixWord ++ tailWord_4053299) baseStart_4053299 baseEnd_4053299 := by
    simpa [prefixWord, tailWord_4053299, baseEnd_4053299] using wordTrace_append hprefix tailTrace_4053299
  have hstable : (prefixWord ++ tailWord_4053299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4053299).length < 2 ^ (prefixWord ++ tailWord_4053299).sum := by decide
  have hdescent : baseEnd_4053299 < baseStart_4053299 := by decide
  rcases family_descends (prefixWord ++ tailWord_4053299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4053330 : List Nat := [3, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2]
def baseStart_4053330 : Nat := 118140960795 + 4053330 * 2 ^ 59
def prefixEnd_4053330 : Nat := 4983230072969 + 3 ^ 40 * 4053330 * 2
def baseEnd_4053330 : Nat := 2081306541288731561434081

theorem tailTrace_4053330 : CollatzResearch.WordTrace tailWord_4053330 prefixEnd_4053330 2081306541288731561434081 := by
  unfold tailWord_4053330
  simp only [CollatzResearch.WordTrace]
  refine ⟨36959272601371284623995361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98558060270323425663987629 36959272601371284623995361)
  ·
    refine ⟨27719454451028463467996521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36959272601371284623995361 27719454451028463467996521)
    ·
      refine ⟨20789590838271347600997391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27719454451028463467996521 20789590838271347600997391)
      ·
        refine ⟨31184386257407021401496087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20789590838271347600997391 31184386257407021401496087)
        ·
          refine ⟨46776579386110532102244131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31184386257407021401496087 46776579386110532102244131)
          ·
            refine ⟨70164869079165798153366197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46776579386110532102244131 70164869079165798153366197)
            ·
              refine ⟨6577956476171793576878081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70164869079165798153366197 6577956476171793576878081)
              ·
                refine ⟨4933467357128845182658561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6577956476171793576878081 4933467357128845182658561)
                ·
                  refine ⟨3700100517846633886993921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4933467357128845182658561 3700100517846633886993921)
                  ·
                    refine ⟨2775075388384975415245441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3700100517846633886993921 2775075388384975415245441)
                    ·
                      refine ⟨2081306541288731561434081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2775075388384975415245441 2081306541288731561434081)
                      ·
                        rfl

theorem cell23_4053330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2].length) (baseStart_4053330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4053330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4053330 prefixEnd_4053330 := by exact prefixLift 4053330
  have htrace : WordTrace (prefixWord ++ tailWord_4053330) baseStart_4053330 baseEnd_4053330 := by
    simpa [prefixWord, tailWord_4053330, baseEnd_4053330] using wordTrace_append hprefix tailTrace_4053330
  have hstable : (prefixWord ++ tailWord_4053330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4053330).length < 2 ^ (prefixWord ++ tailWord_4053330).sum := by decide
  have hdescent : baseEnd_4053330 < baseStart_4053330 := by decide
  rcases family_descends (prefixWord ++ tailWord_4053330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4053349 : List Nat := [1, 3, 1, 3, 1, 3, 1, 2, 1, 7]
def baseStart_4053349 : Nat := 118140960795 + 4053349 * 2 ^ 59
def prefixEnd_4053349 : Nat := 4983230072969 + 3 ^ 40 * 4053349 * 2
def baseEnd_4053349 : Nat := 693772099140388995698831

theorem tailTrace_4053349 : CollatzResearch.WordTrace tailWord_4053349 prefixEnd_4053349 693772099140388995698831 := by
  unfold tailWord_4053349
  simp only [CollatzResearch.WordTrace]
  refine ⟨147837783392416304740923101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98558522261610869827282067 147837783392416304740923101)
  ·
    refine ⟨55439168772156114277846163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147837783392416304740923101 55439168772156114277846163)
    ·
      refine ⟨83158753158234171416769245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55439168772156114277846163 83158753158234171416769245)
      ·
        refine ⟨31184532434337814281288467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83158753158234171416769245 31184532434337814281288467)
        ·
          refine ⟨46776798651506721421932701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31184532434337814281288467 46776798651506721421932701)
          ·
            refine ⟨17541299494315020533224763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46776798651506721421932701 17541299494315020533224763)
            ·
              refine ⟨26311949241472530799837145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17541299494315020533224763 26311949241472530799837145)
              ·
                refine ⟨19733961931104398099877859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26311949241472530799837145 19733961931104398099877859)
                ·
                  refine ⟨29600942896656597149816789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19733961931104398099877859 29600942896656597149816789)
                  ·
                    refine ⟨693772099140388995698831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29600942896656597149816789 693772099140388995698831)
                    ·
                      rfl

theorem cell23_4053349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 2, 1, 7].length) (baseStart_4053349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4053349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4053349 prefixEnd_4053349 := by exact prefixLift 4053349
  have htrace : WordTrace (prefixWord ++ tailWord_4053349) baseStart_4053349 baseEnd_4053349 := by
    simpa [prefixWord, tailWord_4053349, baseEnd_4053349] using wordTrace_append hprefix tailTrace_4053349
  have hstable : (prefixWord ++ tailWord_4053349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4053349).length < 2 ^ (prefixWord ++ tailWord_4053349).sum := by decide
  have hdescent : baseEnd_4053349 < baseStart_4053349 := by decide
  rcases family_descends (prefixWord ++ tailWord_4053349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4053399 : List Nat := [1, 1, 3, 3, 1, 1, 2, 2, 2, 1, 6]
def baseStart_4053399 : Nat := 118140960795 + 4053399 * 2 ^ 59
def prefixEnd_4053399 : Nat := 4983230072969 + 3 ^ 40 * 4053399 * 2
def baseEnd_4053399 : Nat := 2081341971453891791471263

theorem tailTrace_4053399 : CollatzResearch.WordTrace tailWord_4053399 prefixEnd_4053399 2081341971453891791471263 := by
  unfold tailWord_4053399
  simp only [CollatzResearch.WordTrace]
  refine ⟨147839607042235163280243251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98559738028156775520162167 147839607042235163280243251)
  ·
    refine ⟨221759410563352744920364877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147839607042235163280243251 221759410563352744920364877)
    ·
      refine ⟨83159778961257279345136829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221759410563352744920364877 83159778961257279345136829)
      ·
        refine ⟨31184917110471479754426311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83159778961257279345136829 31184917110471479754426311)
        ·
          refine ⟨46777375665707219631639467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31184917110471479754426311 46777375665707219631639467)
          ·
            refine ⟨70166063498560829447459201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46777375665707219631639467 70166063498560829447459201)
            ·
              refine ⟨52624547623920622085594401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70166063498560829447459201 52624547623920622085594401)
              ·
                refine ⟨39468410717940466564195801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52624547623920622085594401 39468410717940466564195801)
                ·
                  refine ⟨29601308038455349923146851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39468410717940466564195801 29601308038455349923146851)
                  ·
                    refine ⟨44401962057683024884720277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29601308038455349923146851 44401962057683024884720277)
                    ·
                      refine ⟨2081341971453891791471263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44401962057683024884720277 2081341971453891791471263)
                      ·
                        rfl

theorem cell23_4053399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_4053399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4053399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4053399 prefixEnd_4053399 := by exact prefixLift 4053399
  have htrace : WordTrace (prefixWord ++ tailWord_4053399) baseStart_4053399 baseEnd_4053399 := by
    simpa [prefixWord, tailWord_4053399, baseEnd_4053399] using wordTrace_append hprefix tailTrace_4053399
  have hstable : (prefixWord ++ tailWord_4053399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4053399).length < 2 ^ (prefixWord ++ tailWord_4053399).sum := by decide
  have hdescent : baseEnd_4053399 < baseStart_4053399 := by decide
  rcases family_descends (prefixWord ++ tailWord_4053399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4053447 : List Nat := [1, 1, 4, 1, 1, 6, 2, 2, 1, 4]
def baseStart_4053447 : Nat := 118140960795 + 4053447 * 2 ^ 59
def prefixEnd_4053447 : Nat := 4983230072969 + 3 ^ 40 * 4053447 * 2
def baseEnd_4053447 : Nat := 693788872841769201223681

theorem tailTrace_4053447 : CollatzResearch.WordTrace tailWord_4053447 prefixEnd_4053447 693788872841769201223681 := by
  unfold tailWord_4053447
  simp only [CollatzResearch.WordTrace]
  refine ⟨147841357746061267477990595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98560905164040844985327063 147841357746061267477990595)
  ·
    refine ⟨221762036619091901216985893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147841357746061267477990595 221762036619091901216985893)
    ·
      refine ⟨41580381866079731478184855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 221762036619091901216985893 41580381866079731478184855)
      ·
        refine ⟨62370572799119597217277283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41580381866079731478184855 62370572799119597217277283)
        ·
          refine ⟨93555859198679395825915925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62370572799119597217277283 93555859198679395825915925)
          ·
            refine ⟨4385430899938096679339809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 93555859198679395825915925 4385430899938096679339809)
            ·
              refine ⟨3289073174953572509504857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4385430899938096679339809 3289073174953572509504857)
              ·
                refine ⟨2466804881215179382128643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3289073174953572509504857 2466804881215179382128643)
                ·
                  refine ⟨3700207321822769073192965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2466804881215179382128643 3700207321822769073192965)
                  ·
                    refine ⟨693788872841769201223681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3700207321822769073192965 693788872841769201223681)
                    ·
                      rfl

theorem cell23_4053447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 2, 2, 1, 4].length) (baseStart_4053447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4053447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4053447 prefixEnd_4053447 := by exact prefixLift 4053447
  have htrace : WordTrace (prefixWord ++ tailWord_4053447) baseStart_4053447 baseEnd_4053447 := by
    simpa [prefixWord, tailWord_4053447, baseEnd_4053447] using wordTrace_append hprefix tailTrace_4053447
  have hstable : (prefixWord ++ tailWord_4053447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4053447).length < 2 ^ (prefixWord ++ tailWord_4053447).sum := by decide
  have hdescent : baseEnd_4053447 < baseStart_4053447 := by decide
  rcases family_descends (prefixWord ++ tailWord_4053447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4053474 : List Nat := [3, 3, 3, 2, 1, 2, 1, 1, 2, 2, 3]
def baseStart_4053474 : Nat := 118140960795 + 4053474 * 2 ^ 59
def prefixEnd_4053474 : Nat := 4983230072969 + 3 ^ 40 * 4053474 * 2
def baseEnd_4053474 : Nat := 2081380482502978998033419

theorem tailTrace_4053474 : CollatzResearch.WordTrace tailWord_4053474 prefixEnd_4053474 2081380482502978998033419 := by
  unfold tailWord_4053474
  simp only [CollatzResearch.WordTrace]
  refine ⟨36960585629240862772305869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98561561677975634059482317 36960585629240862772305869)
  ·
    refine ⟨13860219610965323539614701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36960585629240862772305869 13860219610965323539614701)
    ·
      refine ⟨5197582354111996327355513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13860219610965323539614701 5197582354111996327355513)
      ·
        refine ⟨3898186765583997245516635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5197582354111996327355513 3898186765583997245516635)
        ·
          refine ⟨5847280148375995868274953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3898186765583997245516635 5847280148375995868274953)
          ·
            refine ⟨4385460111281996901206215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5847280148375995868274953 4385460111281996901206215)
            ·
              refine ⟨6578190166922995351809323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4385460111281996901206215 6578190166922995351809323)
              ·
                refine ⟨9867285250384493027713985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6578190166922995351809323 9867285250384493027713985)
                ·
                  refine ⟨7400463937788369770785489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9867285250384493027713985 7400463937788369770785489)
                  ·
                    refine ⟨5550347953341277328089117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7400463937788369770785489 5550347953341277328089117)
                    ·
                      refine ⟨2081380482502978998033419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5550347953341277328089117 2081380482502978998033419)
                      ·
                        rfl

theorem cell23_4053474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_4053474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4053474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4053474 prefixEnd_4053474 := by exact prefixLift 4053474
  have htrace : WordTrace (prefixWord ++ tailWord_4053474) baseStart_4053474 baseEnd_4053474 := by
    simpa [prefixWord, tailWord_4053474, baseEnd_4053474] using wordTrace_append hprefix tailTrace_4053474
  have hstable : (prefixWord ++ tailWord_4053474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4053474).length < 2 ^ (prefixWord ++ tailWord_4053474).sum := by decide
  have hdescent : baseEnd_4053474 < baseStart_4053474 := by decide
  rcases family_descends (prefixWord ++ tailWord_4053474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4053480 : List Nat := [2, 1, 4, 1, 1, 3, 3, 1, 2, 3, 2]
def baseStart_4053480 : Nat := 118140960795 + 4053480 * 2 ^ 59
def prefixEnd_4053480 : Nat := 4983230072969 + 3 ^ 40 * 4053480 * 2
def baseEnd_4053480 : Nat := 2081383563386905974558391

theorem tailTrace_4053480 : CollatzResearch.WordTrace tailWord_4053480 prefixEnd_4053480 2081383563386905974558391 := by
  unfold tailWord_4053480
  simp only [CollatzResearch.WordTrace]
  refine ⟨73921280677470857056970947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98561707569961142742627929 73921280677470857056970947)
  ·
    refine ⟨110881921016206285585456421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73921280677470857056970947 110881921016206285585456421)
    ·
      refine ⟨20790360190538678547273079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110881921016206285585456421 20790360190538678547273079)
      ·
        refine ⟨31185540285808017820909619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20790360190538678547273079 31185540285808017820909619)
        ·
          refine ⟨46778310428712026731364429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31185540285808017820909619 46778310428712026731364429)
          ·
            refine ⟨17541866410767010024261661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46778310428712026731364429 17541866410767010024261661)
            ·
              refine ⟨6578199904037628759098123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17541866410767010024261661 6578199904037628759098123)
              ·
                refine ⟨9867299856056443138647185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6578199904037628759098123 9867299856056443138647185)
                ·
                  refine ⟨7400474892042332353985389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9867299856056443138647185 7400474892042332353985389)
                  ·
                    refine ⟨2775178084515874632744521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7400474892042332353985389 2775178084515874632744521)
                    ·
                      refine ⟨2081383563386905974558391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2775178084515874632744521 2081383563386905974558391)
                      ·
                        rfl

theorem cell23_4053480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3, 1, 2, 3, 2].length) (baseStart_4053480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4053480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4053480 prefixEnd_4053480 := by exact prefixLift 4053480
  have htrace : WordTrace (prefixWord ++ tailWord_4053480) baseStart_4053480 baseEnd_4053480 := by
    simpa [prefixWord, tailWord_4053480, baseEnd_4053480] using wordTrace_append hprefix tailTrace_4053480
  have hstable : (prefixWord ++ tailWord_4053480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4053480).length < 2 ^ (prefixWord ++ tailWord_4053480).sum := by decide
  have hdescent : baseEnd_4053480 < baseStart_4053480 := by decide
  rcases family_descends (prefixWord ++ tailWord_4053480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4053490 : List Nat := [3, 2, 1, 4, 2, 1, 1, 3, 1, 5]
def baseStart_4053490 : Nat := 118140960795 + 4053490 * 2 ^ 59
def prefixEnd_4053490 : Nat := 4983230072969 + 3 ^ 40 * 4053490 * 2
def baseEnd_4053490 : Nat := 693796232731150311811115

theorem tailTrace_4053490 : CollatzResearch.WordTrace tailWord_4053490 prefixEnd_4053490 693796232731150311811115 := by
  unfold tailWord_4053490
  simp only [CollatzResearch.WordTrace]
  refine ⟨36960731521226371455451481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98561950723270323881203949 36960731521226371455451481)
  ·
    refine ⟨27720548640919778591588611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36960731521226371455451481 27720548640919778591588611)
    ·
      refine ⟨41580822961379667887382917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27720548640919778591588611 41580822961379667887382917)
      ·
        refine ⟨7796404305258687728884297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41580822961379667887382917 7796404305258687728884297)
        ·
          refine ⟨5847303228944015796663223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7796404305258687728884297 5847303228944015796663223)
          ·
            refine ⟨8770954843416023694994835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5847303228944015796663223 8770954843416023694994835)
            ·
              refine ⟨13156432265124035542492253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8770954843416023694994835 13156432265124035542492253)
              ·
                refine ⟨4933662099421513328434595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13156432265124035542492253 4933662099421513328434595)
                ·
                  refine ⟨7400493149132269992651893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4933662099421513328434595 7400493149132269992651893)
                  ·
                    refine ⟨693796232731150311811115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7400493149132269992651893 693796232731150311811115)
                    ·
                      rfl

theorem cell23_4053490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 3, 1, 5].length) (baseStart_4053490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4053490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4053490 prefixEnd_4053490 := by exact prefixLift 4053490
  have htrace : WordTrace (prefixWord ++ tailWord_4053490) baseStart_4053490 baseEnd_4053490 := by
    simpa [prefixWord, tailWord_4053490, baseEnd_4053490] using wordTrace_append hprefix tailTrace_4053490
  have hstable : (prefixWord ++ tailWord_4053490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4053490).length < 2 ^ (prefixWord ++ tailWord_4053490).sum := by decide
  have hdescent : baseEnd_4053490 < baseStart_4053490 := by decide
  rcases family_descends (prefixWord ++ tailWord_4053490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4053496 : List Nat := [2, 1, 2, 1, 1, 4, 2, 3, 1, 1, 5]
def baseStart_4053496 : Nat := 118140960795 + 4053496 * 2 ^ 59
def prefixEnd_4053496 : Nat := 4983230072969 + 3 ^ 40 * 4053496 * 2
def baseEnd_4053496 : Nat := 2081391779077377911958317

theorem tailTrace_4053496 : CollatzResearch.WordTrace tailWord_4053496 prefixEnd_4053496 2081391779077377911958317 := by
  unfold tailWord_4053496
  simp only [CollatzResearch.WordTrace]
  refine ⟨73921572461441874423262171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98562096615255832564349561 73921572461441874423262171)
  ·
    refine ⟨110882358692162811634893257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73921572461441874423262171 110882358692162811634893257)
    ·
      refine ⟨83161769019122108726169943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110882358692162811634893257 83161769019122108726169943)
      ·
        refine ⟨124742653528683163089254915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83161769019122108726169943 124742653528683163089254915)
        ·
          refine ⟨187113980293024744633882373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124742653528683163089254915 187113980293024744633882373)
          ·
            refine ⟨35083871304942139618852945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 187113980293024744633882373 35083871304942139618852945)
            ·
              refine ⟨26312903478706604714139709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35083871304942139618852945 26312903478706604714139709)
              ·
                refine ⟨9867338804514976767802391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26312903478706604714139709 9867338804514976767802391)
                ·
                  refine ⟨14801008206772465151703587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9867338804514976767802391 14801008206772465151703587)
                  ·
                    refine ⟨22201512310158697727555381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14801008206772465151703587 22201512310158697727555381)
                    ·
                      refine ⟨2081391779077377911958317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22201512310158697727555381 2081391779077377911958317)
                      ·
                        rfl

theorem cell23_4053496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 3, 1, 1, 5].length) (baseStart_4053496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4053496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4053496 prefixEnd_4053496 := by exact prefixLift 4053496
  have htrace : WordTrace (prefixWord ++ tailWord_4053496) baseStart_4053496 baseEnd_4053496 := by
    simpa [prefixWord, tailWord_4053496, baseEnd_4053496] using wordTrace_append hprefix tailTrace_4053496
  have hstable : (prefixWord ++ tailWord_4053496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4053496).length < 2 ^ (prefixWord ++ tailWord_4053496).sum := by decide
  have hdescent : baseEnd_4053496 < baseStart_4053496 := by decide
  rcases family_descends (prefixWord ++ tailWord_4053496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4053527 : List Nat := [1, 1, 3, 6, 1, 1, 2, 2, 1, 1, 4]
def baseStart_4053527 : Nat := 118140960795 + 4053527 * 2 ^ 59
def prefixEnd_4053527 : Nat := 4983230072969 + 3 ^ 40 * 4053527 * 2
def baseEnd_4053527 : Nat := 2081407696977667290670675

theorem tailTrace_4053527 : CollatzResearch.WordTrace tailWord_4053527 prefixEnd_4053527 2081407696977667290670675 := by
  unfold tailWord_4053527
  simp only [CollatzResearch.WordTrace]
  refine ⟨147844275585771441140902835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98562850390514294093935223 147844275585771441140902835)
  ·
    refine ⟨221766413378657161711354253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147844275585771441140902835 221766413378657161711354253)
    ·
      refine ⟨83162405016996435641757845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221766413378657161711354253 83162405016996435641757845)
      ·
        refine ⟨3898237735171707920707399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 83162405016996435641757845 3898237735171707920707399)
        ·
          refine ⟨5847356602757561881061099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3898237735171707920707399 5847356602757561881061099)
          ·
            refine ⟨8771034904136342821591649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5847356602757561881061099 8771034904136342821591649)
            ·
              refine ⟨6578276178102257116193737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8771034904136342821591649 6578276178102257116193737)
              ·
                refine ⟨4933707133576692837145303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6578276178102257116193737 4933707133576692837145303)
                ·
                  refine ⟨7400560700365039255717955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4933707133576692837145303 7400560700365039255717955)
                  ·
                    refine ⟨11100841050547558883576933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7400560700365039255717955 11100841050547558883576933)
                    ·
                      refine ⟨2081407696977667290670675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11100841050547558883576933 2081407696977667290670675)
                      ·
                        rfl

theorem cell23_4053527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_4053527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4053527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4053527 prefixEnd_4053527 := by exact prefixLift 4053527
  have htrace : WordTrace (prefixWord ++ tailWord_4053527) baseStart_4053527 baseEnd_4053527 := by
    simpa [prefixWord, tailWord_4053527, baseEnd_4053527] using wordTrace_append hprefix tailTrace_4053527
  have hstable : (prefixWord ++ tailWord_4053527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4053527).length < 2 ^ (prefixWord ++ tailWord_4053527).sum := by decide
  have hdescent : baseEnd_4053527 < baseStart_4053527 := by decide
  rcases family_descends (prefixWord ++ tailWord_4053527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4053533 : List Nat := [1, 4, 2, 2, 1, 2, 4, 7]
def baseStart_4053533 : Nat := 118140960795 + 4053533 * 2 ^ 59
def prefixEnd_4053533 : Nat := 4983230072969 + 3 ^ 40 * 4053533 * 2
def baseEnd_4053533 : Nat := 77089288068947935822061

theorem tailTrace_4053533 : CollatzResearch.WordTrace tailWord_4053533 prefixEnd_4053533 77089288068947935822061 := by
  unfold tailWord_4053533
  simp only [CollatzResearch.WordTrace]
  refine ⟨147844494423749704165621253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98562996282499802777080835 147844494423749704165621253)
  ·
    refine ⟨27720842704453069531053985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147844494423749704165621253 27720842704453069531053985)
    ·
      refine ⟨20790632028339802148290489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27720842704453069531053985 20790632028339802148290489)
      ·
        refine ⟨15592974021254851611217867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20790632028339802148290489 15592974021254851611217867)
        ·
          refine ⟨23389461031882277416826801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15592974021254851611217867 23389461031882277416826801)
          ·
            refine ⟨17542095773911708062620101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23389461031882277416826801 17542095773911708062620101)
            ·
              refine ⟨3289142957608445261741269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17542095773911708062620101 3289142957608445261741269)
              ·
                refine ⟨77089288068947935822061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3289142957608445261741269 77089288068947935822061)
                ·
                  rfl

theorem cell23_4053533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 4, 7].length) (baseStart_4053533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4053533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4053533 prefixEnd_4053533 := by exact prefixLift 4053533
  have htrace : WordTrace (prefixWord ++ tailWord_4053533) baseStart_4053533 baseEnd_4053533 := by
    simpa [prefixWord, tailWord_4053533, baseEnd_4053533] using wordTrace_append hprefix tailTrace_4053533
  have hstable : (prefixWord ++ tailWord_4053533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4053533).length < 2 ^ (prefixWord ++ tailWord_4053533).sum := by decide
  have hdescent : baseEnd_4053533 < baseStart_4053533 := by decide
  rcases family_descends (prefixWord ++ tailWord_4053533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4053550 : List Nat := [4, 1, 3, 1, 4, 1, 9]
def baseStart_4053550 : Nat := 118140960795 + 4053550 * 2 ^ 59
def prefixEnd_4053550 : Nat := 4983230072969 + 3 ^ 40 * 4053550 * 2
def baseEnd_4053550 : Nat := 25696537123860749391149

theorem tailTrace_4053550 : CollatzResearch.WordTrace tailWord_4053550 prefixEnd_4053550 25696537123860749391149 := by
  unfold tailWord_4053550
  simp only [CollatzResearch.WordTrace]
  refine ⟨18480639308086014508623763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98563409643125410712660069 18480639308086014508623763)
  ·
    refine ⟨27720958962129021762935645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18480639308086014508623763 27720958962129021762935645)
    ·
      refine ⟨10395359610798383161100867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27720958962129021762935645 10395359610798383161100867)
      ·
        refine ⟨15593039416197574741651301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10395359610798383161100867 15593039416197574741651301)
        ·
          refine ⟨2923694890537045264059619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15593039416197574741651301 2923694890537045264059619)
          ·
            refine ⟨4385542335805567896089429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2923694890537045264059619 4385542335805567896089429)
            ·
              refine ⟨25696537123860749391149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4385542335805567896089429 25696537123860749391149)
              ·
                rfl

theorem cell23_4053550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 9].length) (baseStart_4053550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4053550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4053550 prefixEnd_4053550 := by exact prefixLift 4053550
  have htrace : WordTrace (prefixWord ++ tailWord_4053550) baseStart_4053550 baseEnd_4053550 := by
    simpa [prefixWord, tailWord_4053550, baseEnd_4053550] using wordTrace_append hprefix tailTrace_4053550
  have hstable : (prefixWord ++ tailWord_4053550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4053550).length < 2 ^ (prefixWord ++ tailWord_4053550).sum := by decide
  have hdescent : baseEnd_4053550 < baseStart_4053550 := by decide
  rcases family_descends (prefixWord ++ tailWord_4053550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4053560 : List Nat := [2, 1, 2, 1, 4, 1, 2, 4, 2, 1, 3]
def baseStart_4053560 : Nat := 118140960795 + 4053560 * 2 ^ 59
def prefixEnd_4053560 : Nat := 4983230072969 + 3 ^ 40 * 4053560 * 2
def baseEnd_4053560 : Nat := 2081424641839265661558023

theorem tailTrace_4053560 : CollatzResearch.WordTrace tailWord_4053560 prefixEnd_4053560 2081424641839265661558023 := by
  unfold tailWord_4053560
  simp only [CollatzResearch.WordTrace]
  refine ⟨73922739597325943888427067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98563652796434591851236089 73922739597325943888427067)
  ·
    refine ⟨110884109395988915832640601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73922739597325943888427067 110884109395988915832640601)
    ·
      refine ⟨83163082046991686874480451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110884109395988915832640601 83163082046991686874480451)
      ·
        refine ⟨124744623070487530311720677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83163082046991686874480451 124744623070487530311720677)
        ·
          refine ⟨23389616825716411933447627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124744623070487530311720677 23389616825716411933447627)
          ·
            refine ⟨35084425238574617900171441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23389616825716411933447627 35084425238574617900171441)
            ·
              refine ⟨26313318928930963425128581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35084425238574617900171441 26313318928930963425128581)
              ·
                refine ⟨4933747299174555642211609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26313318928930963425128581 4933747299174555642211609)
                ·
                  refine ⟨3700310474380916731658707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4933747299174555642211609 3700310474380916731658707)
                  ·
                    refine ⟨5550465711571375097488061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3700310474380916731658707 5550465711571375097488061)
                    ·
                      refine ⟨2081424641839265661558023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5550465711571375097488061 2081424641839265661558023)
                      ·
                        rfl

theorem cell23_4053560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 4, 2, 1, 3].length) (baseStart_4053560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4053560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4053560 prefixEnd_4053560 := by exact prefixLift 4053560
  have htrace : WordTrace (prefixWord ++ tailWord_4053560) baseStart_4053560 baseEnd_4053560 := by
    simpa [prefixWord, tailWord_4053560, baseEnd_4053560] using wordTrace_append hprefix tailTrace_4053560
  have hstable : (prefixWord ++ tailWord_4053560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4053560).length < 2 ^ (prefixWord ++ tailWord_4053560).sum := by decide
  have hdescent : baseEnd_4053560 < baseStart_4053560 := by decide
  rcases family_descends (prefixWord ++ tailWord_4053560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4053576 : List Nat := [2, 1, 3, 1, 1, 1, 1, 5, 2, 6]
def baseStart_4053576 : Nat := 118140960795 + 4053576 * 2 ^ 59
def prefixEnd_4053576 : Nat := 4983230072969 + 3 ^ 40 * 4053576 * 2
def baseEnd_4053576 : Nat := 693810952509912532985983

theorem tailTrace_4053576 : CollatzResearch.WordTrace tailWord_4053576 prefixEnd_4053576 693810952509912532985983 := by
  unfold tailWord_4053576
  simp only [CollatzResearch.WordTrace]
  refine ⟨73923031381296961254718291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98564041841729281672957721 73923031381296961254718291)
  ·
    refine ⟨110884547071945441882077437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73923031381296961254718291 110884547071945441882077437)
    ·
      refine ⟨41581705151979540705779039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110884547071945441882077437 41581705151979540705779039)
      ·
        refine ⟨62372557727969311058668559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41581705151979540705779039 62372557727969311058668559)
        ·
          refine ⟨93558836591953966588002839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62372557727969311058668559 93558836591953966588002839)
          ·
            refine ⟨140338254887930949882004259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93558836591953966588002839 140338254887930949882004259)
            ·
              refine ⟨210507382331896424823006389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140338254887930949882004259 210507382331896424823006389)
              ·
                refine ⟨19735067093615289827156849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 210507382331896424823006389 19735067093615289827156849)
                ·
                  refine ⟨14801300320211467370367637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19735067093615289827156849 14801300320211467370367637)
                  ·
                    refine ⟨693810952509912532985983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14801300320211467370367637 693810952509912532985983)
                    ·
                      rfl

theorem cell23_4053576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 5, 2, 6].length) (baseStart_4053576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4053576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4053576 prefixEnd_4053576 := by exact prefixLift 4053576
  have htrace : WordTrace (prefixWord ++ tailWord_4053576) baseStart_4053576 baseEnd_4053576 := by
    simpa [prefixWord, tailWord_4053576, baseEnd_4053576] using wordTrace_append hprefix tailTrace_4053576
  have hstable : (prefixWord ++ tailWord_4053576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4053576).length < 2 ^ (prefixWord ++ tailWord_4053576).sum := by decide
  have hdescent : baseEnd_4053576 < baseStart_4053576 := by decide
  rcases family_descends (prefixWord ++ tailWord_4053576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4053598 : List Nat := [4, 4, 1, 2, 1, 1, 3, 1, 1, 2, 3]
def baseStart_4053598 : Nat := 118140960795 + 4053598 * 2 ^ 59
def prefixEnd_4053598 : Nat := 4983230072969 + 3 ^ 40 * 4053598 * 2
def baseEnd_4053598 : Nat := 2081444154104136512882849

theorem tailTrace_4053598 : CollatzResearch.WordTrace tailWord_4053598 prefixEnd_4053598 2081444154104136512882849 := by
  unfold tailWord_4053598
  simp only [CollatzResearch.WordTrace]
  refine ⟨18480858146064277533342181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98564576779009480177824965 18480858146064277533342181)
  ·
    refine ⟨3465160902387052037501659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18480858146064277533342181 3465160902387052037501659)
    ·
      refine ⟨5197741353580578056252489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3465160902387052037501659 5197741353580578056252489)
      ·
        refine ⟨3898306015185433542189367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5197741353580578056252489 3898306015185433542189367)
        ·
          refine ⟨5847459022778150313284051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3898306015185433542189367 5847459022778150313284051)
          ·
            refine ⟨8771188534167225469926077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5847459022778150313284051 8771188534167225469926077)
            ·
              refine ⟨3289195700312709551222279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8771188534167225469926077 3289195700312709551222279)
              ·
                refine ⟨4933793550469064326833419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3289195700312709551222279 4933793550469064326833419)
                ·
                  refine ⟨7400690325703596490250129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4933793550469064326833419 7400690325703596490250129)
                  ·
                    refine ⟨5550517744277697367687597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7400690325703596490250129 5550517744277697367687597)
                    ·
                      refine ⟨2081444154104136512882849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5550517744277697367687597 2081444154104136512882849)
                      ·
                        rfl

theorem cell23_4053598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_4053598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4053598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4053598 prefixEnd_4053598 := by exact prefixLift 4053598
  have htrace : WordTrace (prefixWord ++ tailWord_4053598) baseStart_4053598 baseEnd_4053598 := by
    simpa [prefixWord, tailWord_4053598, baseEnd_4053598] using wordTrace_append hprefix tailTrace_4053598
  have hstable : (prefixWord ++ tailWord_4053598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4053598).length < 2 ^ (prefixWord ++ tailWord_4053598).sum := by decide
  have hdescent : baseEnd_4053598 < baseStart_4053598 := by decide
  rcases family_descends (prefixWord ++ tailWord_4053598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4053600 : List Nat := [2, 1, 1, 3, 2, 1, 2, 1, 6, 2, 2]
def baseStart_4053600 : Nat := 118140960795 + 4053600 * 2 ^ 59
def prefixEnd_4053600 : Nat := 4983230072969 + 3 ^ 40 * 4053600 * 2
def baseEnd_4053600 : Nat := 2081445181065445505057839

theorem tailTrace_4053600 : CollatzResearch.WordTrace tailWord_4053600 prefixEnd_4053600 2081445181065445505057839 := by
  unfold tailWord_4053600
  simp only [CollatzResearch.WordTrace]
  refine ⟨73923469057253487304155127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98564625409671316405540169 73923469057253487304155127)
  ·
    refine ⟨110885203585880230956232691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73923469057253487304155127 110885203585880230956232691)
    ·
      refine ⟨166327805378820346434349037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110885203585880230956232691 166327805378820346434349037)
      ·
        refine ⟨62372927017057629912880889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166327805378820346434349037 62372927017057629912880889)
        ·
          refine ⟨46779695262793222434660667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62372927017057629912880889 46779695262793222434660667)
          ·
            refine ⟨70169542894189833651991001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46779695262793222434660667 70169542894189833651991001)
            ·
              refine ⟨52627157170642375238993251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70169542894189833651991001 52627157170642375238993251)
              ·
                refine ⟨78940735755963562858489877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52627157170642375238993251 78940735755963562858489877)
                ·
                  refine ⟨3700346988560792008991713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 78940735755963562858489877 3700346988560792008991713)
                  ·
                    refine ⟨2775260241420594006743785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3700346988560792008991713 2775260241420594006743785)
                    ·
                      refine ⟨2081445181065445505057839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2775260241420594006743785 2081445181065445505057839)
                      ·
                        rfl

theorem cell23_4053600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 6, 2, 2].length) (baseStart_4053600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4053600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4053600 prefixEnd_4053600 := by exact prefixLift 4053600
  have htrace : WordTrace (prefixWord ++ tailWord_4053600) baseStart_4053600 baseEnd_4053600 := by
    simpa [prefixWord, tailWord_4053600, baseEnd_4053600] using wordTrace_append hprefix tailTrace_4053600
  have hstable : (prefixWord ++ tailWord_4053600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4053600).length < 2 ^ (prefixWord ++ tailWord_4053600).sum := by decide
  have hdescent : baseEnd_4053600 < baseStart_4053600 := by decide
  rcases family_descends (prefixWord ++ tailWord_4053600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4053690 : List Nat := [3, 1, 1, 1, 2, 3, 1, 3, 2, 4, 2]
def baseStart_4053690 : Nat := 118140960795 + 4053690 * 2 ^ 59
def prefixEnd_4053690 : Nat := 4983230072969 + 3 ^ 40 * 4053690 * 2
def baseEnd_4053690 : Nat := 2081491394324350152932425

theorem tailTrace_4053690 : CollatzResearch.WordTrace tailWord_4053690 prefixEnd_4053690 2081491394324350152932425 := by
  unfold tailWord_4053690
  simp only [CollatzResearch.WordTrace]
  refine ⟨36962555171045229994771631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98566813789453946652724349 36962555171045229994771631)
  ·
    refine ⟨55443832756567844992157447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36962555171045229994771631 55443832756567844992157447)
    ·
      refine ⟨83165749134851767488236171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55443832756567844992157447 83165749134851767488236171)
      ·
        refine ⟨124748623702277651232354257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83165749134851767488236171 124748623702277651232354257)
        ·
          refine ⟨93561467776708238424265693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124748623702277651232354257 93561467776708238424265693)
          ·
            refine ⟨35085550416265589409099635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93561467776708238424265693 35085550416265589409099635)
            ·
              refine ⟨52628325624398384113649453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35085550416265589409099635 52628325624398384113649453)
              ·
                refine ⟨19735622109149394042618545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52628325624398384113649453 19735622109149394042618545)
                ·
                  refine ⟨14801716581862045531963909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19735622109149394042618545 14801716581862045531963909)
                  ·
                    refine ⟨2775321859099133537243233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14801716581862045531963909 2775321859099133537243233)
                    ·
                      refine ⟨2081491394324350152932425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2775321859099133537243233 2081491394324350152932425)
                      ·
                        rfl

theorem cell23_4053690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 3, 2, 4, 2].length) (baseStart_4053690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4053690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4053690 prefixEnd_4053690 := by exact prefixLift 4053690
  have htrace : WordTrace (prefixWord ++ tailWord_4053690) baseStart_4053690 baseEnd_4053690 := by
    simpa [prefixWord, tailWord_4053690, baseEnd_4053690] using wordTrace_append hprefix tailTrace_4053690
  have hstable : (prefixWord ++ tailWord_4053690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4053690).length < 2 ^ (prefixWord ++ tailWord_4053690).sum := by decide
  have hdescent : baseEnd_4053690 < baseStart_4053690 := by decide
  rcases family_descends (prefixWord ++ tailWord_4053690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4053710 : List Nat := [4, 1, 1, 1, 3, 2, 2, 1, 1, 4, 3]
def baseStart_4053710 : Nat := 118140960795 + 4053710 * 2 ^ 59
def prefixEnd_4053710 : Nat := 4983230072969 + 3 ^ 40 * 4053710 * 2
def baseEnd_4053710 : Nat := 2081501663937440074682333

theorem tailTrace_4053710 : CollatzResearch.WordTrace tailWord_4053710 prefixEnd_4053710 2081501663937440074682333 := by
  unfold tailWord_4053710
  simp only [CollatzResearch.WordTrace]
  refine ⟨18481368768013557924351823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98567300096072308929876389 18481368768013557924351823)
  ·
    refine ⟨27722053152020336886527735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18481368768013557924351823 27722053152020336886527735)
    ·
      refine ⟨41583079728030505329791603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27722053152020336886527735 41583079728030505329791603)
      ·
        refine ⟨62374619592045757994687405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41583079728030505329791603 62374619592045757994687405)
        ·
          refine ⟨23390482347017159248007777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62374619592045757994687405 23390482347017159248007777)
          ·
            refine ⟨17542861760262869436005833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23390482347017159248007777 17542861760262869436005833)
            ·
              refine ⟨13157146320197152077004375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17542861760262869436005833 13157146320197152077004375)
              ·
                refine ⟨19735719480295728115506563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13157146320197152077004375 19735719480295728115506563)
                ·
                  refine ⟨29603579220443592173259845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19735719480295728115506563 29603579220443592173259845)
                  ·
                    refine ⟨5550671103833173532486221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29603579220443592173259845 5550671103833173532486221)
                    ·
                      refine ⟨2081501663937440074682333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5550671103833173532486221 2081501663937440074682333)
                      ·
                        rfl

theorem cell23_4053710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 1, 1, 4, 3].length) (baseStart_4053710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4053710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4053710 prefixEnd_4053710 := by exact prefixLift 4053710
  have htrace : WordTrace (prefixWord ++ tailWord_4053710) baseStart_4053710 baseEnd_4053710 := by
    simpa [prefixWord, tailWord_4053710, baseEnd_4053710] using wordTrace_append hprefix tailTrace_4053710
  have hstable : (prefixWord ++ tailWord_4053710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4053710).length < 2 ^ (prefixWord ++ tailWord_4053710).sum := by decide
  have hdescent : baseEnd_4053710 < baseStart_4053710 := by decide
  rcases family_descends (prefixWord ++ tailWord_4053710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4053774 : List Nat := [4, 1, 1, 2, 1, 1, 1, 7, 1, 1, 3]
def baseStart_4053774 : Nat := 118140960795 + 4053774 * 2 ^ 59
def prefixEnd_4053774 : Nat := 4983230072969 + 3 ^ 40 * 4053774 * 2
def baseEnd_4053774 : Nat := 2081534526699327824282039

theorem tailTrace_4053774 : CollatzResearch.WordTrace tailWord_4053774 prefixEnd_4053774 2081534526699327824282039 := by
  unfold tailWord_4053774
  simp only [CollatzResearch.WordTrace]
  refine ⟨18481660551984575290643047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98568856277251068216762917 18481660551984575290643047)
  ·
    refine ⟨27722490827976862935964571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18481660551984575290643047 27722490827976862935964571)
    ·
      refine ⟨41583736241965294403946857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27722490827976862935964571 41583736241965294403946857)
      ·
        refine ⟨31187802181473970802960143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41583736241965294403946857 31187802181473970802960143)
        ·
          refine ⟨46781703272210956204440215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31187802181473970802960143 46781703272210956204440215)
          ·
            refine ⟨70172554908316434306660323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46781703272210956204440215 70172554908316434306660323)
            ·
              refine ⟨105258832362474651459990485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70172554908316434306660323 105258832362474651459990485)
              ·
                refine ⟨2467003883495499643593527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 105258832362474651459990485 2467003883495499643593527)
                ·
                  refine ⟨3700505825243249465390291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2467003883495499643593527 3700505825243249465390291)
                  ·
                    refine ⟨5550758737864874198085437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3700505825243249465390291 5550758737864874198085437)
                    ·
                      refine ⟨2081534526699327824282039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5550758737864874198085437 2081534526699327824282039)
                      ·
                        rfl

theorem cell23_4053774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 7, 1, 1, 3].length) (baseStart_4053774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4053774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4053774 prefixEnd_4053774 := by exact prefixLift 4053774
  have htrace : WordTrace (prefixWord ++ tailWord_4053774) baseStart_4053774 baseEnd_4053774 := by
    simpa [prefixWord, tailWord_4053774, baseEnd_4053774] using wordTrace_append hprefix tailTrace_4053774
  have hstable : (prefixWord ++ tailWord_4053774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4053774).length < 2 ^ (prefixWord ++ tailWord_4053774).sum := by decide
  have hdescent : baseEnd_4053774 < baseStart_4053774 := by decide
  rcases family_descends (prefixWord ++ tailWord_4053774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4053791 : List Nat := [1, 1, 2, 4, 2, 2, 4, 2, 1, 1, 3]
def baseStart_4053791 : Nat := 118140960795 + 4053791 * 2 ^ 59
def prefixEnd_4053791 : Nat := 4983230072969 + 3 ^ 40 * 4053791 * 2
def baseEnd_4053791 : Nat := 2081543255870454257769461

theorem tailTrace_4053791 : CollatzResearch.WordTrace tailWord_4053791 prefixEnd_4053791 2081543255870454257769461 := by
  unfold tailWord_4053791
  simp only [CollatzResearch.WordTrace]
  refine ⟨147853904456815014228513227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98569269637876676152342151 147853904456815014228513227)
  ·
    refine ⟨221780856685222521342769841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147853904456815014228513227 221780856685222521342769841)
    ·
      refine ⟨166335642513916891007077381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221780856685222521342769841 166335642513916891007077381)
      ·
        refine ⟨31187932971359417063827009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 166335642513916891007077381 31187932971359417063827009)
        ·
          refine ⟨23390949728519562797870257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31187932971359417063827009 23390949728519562797870257)
          ·
            refine ⟨17543212296389672098402693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23390949728519562797870257 17543212296389672098402693)
            ·
              refine ⟨3289352305573063518450505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17543212296389672098402693 3289352305573063518450505)
              ·
                refine ⟨2467014229179797638837879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3289352305573063518450505 2467014229179797638837879)
                ·
                  refine ⟨3700521343769696458256819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2467014229179797638837879 3700521343769696458256819)
                  ·
                    refine ⟨5550782015654544687385229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3700521343769696458256819 5550782015654544687385229)
                    ·
                      refine ⟨2081543255870454257769461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5550782015654544687385229 2081543255870454257769461)
                      ·
                        rfl

theorem cell23_4053791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 4, 2, 1, 1, 3].length) (baseStart_4053791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4053791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4053791 prefixEnd_4053791 := by exact prefixLift 4053791
  have htrace : WordTrace (prefixWord ++ tailWord_4053791) baseStart_4053791 baseEnd_4053791 := by
    simpa [prefixWord, tailWord_4053791, baseEnd_4053791] using wordTrace_append hprefix tailTrace_4053791
  have hstable : (prefixWord ++ tailWord_4053791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4053791).length < 2 ^ (prefixWord ++ tailWord_4053791).sum := by decide
  have hdescent : baseEnd_4053791 < baseStart_4053791 := by decide
  rcases family_descends (prefixWord ++ tailWord_4053791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4053800 : List Nat := [2, 1, 5, 1, 1, 1, 2, 1, 3, 1, 5]
def baseStart_4053800 : Nat := 118140960795 + 4053800 * 2 ^ 59
def prefixEnd_4053800 : Nat := 4983230072969 + 3 ^ 40 * 4053800 * 2
def baseEnd_4053800 : Nat := 2081547877196344722556919

theorem tailTrace_4053800 : CollatzResearch.WordTrace tailWord_4053800 prefixEnd_4053800 2081547877196344722556919 := by
  unfold tailWord_4053800
  simp only [CollatzResearch.WordTrace]
  refine ⟨73927116356891204382795427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98569488475854939177060569 73927116356891204382795427)
  ·
    refine ⟨110890674535336806574193141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73927116356891204382795427 110890674535336806574193141)
    ·
      refine ⟨10396000737687825616330607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 110890674535336806574193141 10396000737687825616330607)
      ·
        refine ⟨15594001106531738424495911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10396000737687825616330607 15594001106531738424495911)
        ·
          refine ⟨23391001659797607636743867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15594001106531738424495911 23391001659797607636743867)
          ·
            refine ⟨35086502489696411455115801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23391001659797607636743867 35086502489696411455115801)
            ·
              refine ⟨26314876867272308591336851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35086502489696411455115801 26314876867272308591336851)
              ·
                refine ⟨39472315300908462887005277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26314876867272308591336851 39472315300908462887005277)
                ·
                  refine ⟨14802118237840673582626979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39472315300908462887005277 14802118237840673582626979)
                  ·
                    refine ⟨22203177356761010373940469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14802118237840673582626979 22203177356761010373940469)
                    ·
                      refine ⟨2081547877196344722556919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22203177356761010373940469 2081547877196344722556919)
                      ·
                        rfl

theorem cell23_4053800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_4053800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4053800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4053800 prefixEnd_4053800 := by exact prefixLift 4053800
  have htrace : WordTrace (prefixWord ++ tailWord_4053800) baseStart_4053800 baseEnd_4053800 := by
    simpa [prefixWord, tailWord_4053800, baseEnd_4053800] using wordTrace_append hprefix tailTrace_4053800
  have hstable : (prefixWord ++ tailWord_4053800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4053800).length < 2 ^ (prefixWord ++ tailWord_4053800).sum := by decide
  have hdescent : baseEnd_4053800 < baseStart_4053800 := by decide
  rcases family_descends (prefixWord ++ tailWord_4053800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4053828 : List Nat := [2, 3, 4, 2, 1, 2, 2, 1, 1, 5]
def baseStart_4053828 : Nat := 118140960795 + 4053828 * 2 ^ 59
def prefixEnd_4053828 : Nat := 4983230072969 + 3 ^ 40 * 4053828 * 2
def baseEnd_4053828 : Nat := 693854084884890204335597

theorem tailTrace_4053828 : CollatzResearch.WordTrace tailWord_4053828 prefixEnd_4053828 693854084884890204335597 := by
  unfold tailWord_4053828
  simp only [CollatzResearch.WordTrace]
  refine ⟨73927626978840484773805069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98570169305120646365073425 73927626978840484773805069)
  ·
    refine ⟨27722860117065181790176901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73927626978840484773805069 27722860117065181790176901)
    ·
      refine ⟨5198036271949721585658169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27722860117065181790176901 5198036271949721585658169)
      ·
        refine ⟨3898527203962291189243627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5198036271949721585658169 3898527203962291189243627)
        ·
          refine ⟨5847790805943436783865441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3898527203962291189243627 5847790805943436783865441)
          ·
            refine ⟨4385843104457577587899081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5847790805943436783865441 4385843104457577587899081)
            ·
              refine ⟨3289382328343183190924311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4385843104457577587899081 3289382328343183190924311)
              ·
                refine ⟨4934073492514774786386467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3289382328343183190924311 4934073492514774786386467)
                ·
                  refine ⟨7401110238772162179579701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4934073492514774786386467 7401110238772162179579701)
                  ·
                    refine ⟨693854084884890204335597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7401110238772162179579701 693854084884890204335597)
                    ·
                      rfl

theorem cell23_4053828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_4053828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4053828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4053828 prefixEnd_4053828 := by exact prefixLift 4053828
  have htrace : WordTrace (prefixWord ++ tailWord_4053828) baseStart_4053828 baseEnd_4053828 := by
    simpa [prefixWord, tailWord_4053828, baseEnd_4053828] using wordTrace_append hprefix tailTrace_4053828
  have hstable : (prefixWord ++ tailWord_4053828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4053828).length < 2 ^ (prefixWord ++ tailWord_4053828).sum := by decide
  have hdescent : baseEnd_4053828 < baseStart_4053828 := by decide
  rcases family_descends (prefixWord ++ tailWord_4053828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4053837 : List Nat := [1, 6, 1, 2, 2, 1, 10]
def baseStart_4053837 : Nat := 118140960795 + 4053837 * 2 ^ 59
def prefixEnd_4053837 : Nat := 4983230072969 + 3 ^ 40 * 4053837 * 2
def baseEnd_4053837 : Nat := 25698356493587173799929

theorem tailTrace_4053837 : CollatzResearch.WordTrace tailWord_4053837 prefixEnd_4053837 25698356493587173799929 := by
  unfold tailWord_4053837
  simp only [CollatzResearch.WordTrace]
  refine ⟨147855582214648364084687765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98570388143098909389791843 147855582214648364084687765)
  ·
    refine ⟨6930730416311642066469739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 147855582214648364084687765 6930730416311642066469739)
    ·
      refine ⟨10396095624467463099704609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6930730416311642066469739 10396095624467463099704609)
      ·
        refine ⟨7797071718350597324778457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10396095624467463099704609 7797071718350597324778457)
        ·
          refine ⟨5847803788762947993583843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7797071718350597324778457 5847803788762947993583843)
          ·
            refine ⟨8771705683144421990375765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5847803788762947993583843 8771705683144421990375765)
            ·
              refine ⟨25698356493587173799929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 8771705683144421990375765 25698356493587173799929)
              ·
                rfl

theorem cell23_4053837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 10].length) (baseStart_4053837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4053837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4053837 prefixEnd_4053837 := by exact prefixLift 4053837
  have htrace : WordTrace (prefixWord ++ tailWord_4053837) baseStart_4053837 baseEnd_4053837 := by
    simpa [prefixWord, tailWord_4053837, baseEnd_4053837] using wordTrace_append hprefix tailTrace_4053837
  have hstable : (prefixWord ++ tailWord_4053837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4053837).length < 2 ^ (prefixWord ++ tailWord_4053837).sum := by decide
  have hdescent : baseEnd_4053837 < baseStart_4053837 := by decide
  rcases family_descends (prefixWord ++ tailWord_4053837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4053841 : List Nat := [1, 2, 2, 1, 7, 1, 1, 2, 2, 4]
def baseStart_4053841 : Nat := 118140960795 + 4053841 * 2 ^ 59
def prefixEnd_4053841 : Nat := 4983230072969 + 3 ^ 40 * 4053841 * 2
def baseEnd_4053841 : Nat := 693856309967726354048077

theorem tailTrace_4053841 : CollatzResearch.WordTrace tailWord_4053841 prefixEnd_4053841 693856309967726354048077 := by
  unfold tailWord_4053841
  simp only [CollatzResearch.WordTrace]
  refine ⟨147855728106633872767833377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98570485404422581845222251 147855728106633872767833377)
  ·
    refine ⟨110891796079975404575875033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147855728106633872767833377 110891796079975404575875033)
    ·
      refine ⟨83168847059981553431906275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110891796079975404575875033 83168847059981553431906275)
      ·
        refine ⟨124753270589972330147859413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83168847059981553431906275 124753270589972330147859413)
        ·
          refine ⟨2923904779452476487840455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 124753270589972330147859413 2923904779452476487840455)
          ·
            refine ⟨4385857169178714731760683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2923904779452476487840455 4385857169178714731760683)
            ·
              refine ⟨6578785753768072097641025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4385857169178714731760683 6578785753768072097641025)
              ·
                refine ⟨4934089315326054073230769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6578785753768072097641025 4934089315326054073230769)
                ·
                  refine ⟨3700566986494540554923077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4934089315326054073230769 3700566986494540554923077)
                  ·
                    refine ⟨693856309967726354048077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3700566986494540554923077 693856309967726354048077)
                    ·
                      rfl

theorem cell23_4053841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 1, 2, 2, 4].length) (baseStart_4053841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4053841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4053841 prefixEnd_4053841 := by exact prefixLift 4053841
  have htrace : WordTrace (prefixWord ++ tailWord_4053841) baseStart_4053841 baseEnd_4053841 := by
    simpa [prefixWord, tailWord_4053841, baseEnd_4053841] using wordTrace_append hprefix tailTrace_4053841
  have hstable : (prefixWord ++ tailWord_4053841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4053841).length < 2 ^ (prefixWord ++ tailWord_4053841).sum := by decide
  have hdescent : baseEnd_4053841 < baseStart_4053841 := by decide
  rcases family_descends (prefixWord ++ tailWord_4053841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4053857 : List Nat := [1, 2, 3, 1, 1, 1, 2, 4, 3, 3, 2]
def baseStart_4053857 : Nat := 118140960795 + 4053857 * 2 ^ 59
def prefixEnd_4053857 : Nat := 4983230072969 + 3 ^ 40 * 4053857 * 2
def baseEnd_4053857 : Nat := 2081577145593650999544157

theorem tailTrace_4053857 : CollatzResearch.WordTrace tailWord_4053857 prefixEnd_4053857 2081577145593650999544157 := by
  unfold tailWord_4053857
  simp only [CollatzResearch.WordTrace]
  refine ⟨147856311674575907500415825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98570874449717271666943883 147856311674575907500415825)
  ·
    refine ⟨110892233755931930625311869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147856311674575907500415825 110892233755931930625311869)
    ·
      refine ⟨41584587658474473984491951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110892233755931930625311869 41584587658474473984491951)
      ·
        refine ⟨62376881487711710976737927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41584587658474473984491951 62376881487711710976737927)
        ·
          refine ⟨93565322231567566465106891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62376881487711710976737927 93565322231567566465106891)
          ·
            refine ⟨140347983347351349697660337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93565322231567566465106891 140347983347351349697660337)
            ·
              refine ⟨105260987510513512273245253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140347983347351349697660337 105260987510513512273245253)
              ·
                refine ⟨19736435158221283551233485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105260987510513512273245253 19736435158221283551233485)
                ·
                  refine ⟨7401163184332981331712557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19736435158221283551233485 7401163184332981331712557)
                  ·
                    refine ⟨2775436194124867999392209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7401163184332981331712557 2775436194124867999392209)
                    ·
                      refine ⟨2081577145593650999544157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2775436194124867999392209 2081577145593650999544157)
                      ·
                        rfl

theorem cell23_4053857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 4, 3, 3, 2].length) (baseStart_4053857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4053857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4053857 prefixEnd_4053857 := by exact prefixLift 4053857
  have htrace : WordTrace (prefixWord ++ tailWord_4053857) baseStart_4053857 baseEnd_4053857 := by
    simpa [prefixWord, tailWord_4053857, baseEnd_4053857] using wordTrace_append hprefix tailTrace_4053857
  have hstable : (prefixWord ++ tailWord_4053857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4053857).length < 2 ^ (prefixWord ++ tailWord_4053857).sum := by decide
  have hdescent : baseEnd_4053857 < baseStart_4053857 := by decide
  rcases family_descends (prefixWord ++ tailWord_4053857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4053864 : List Nat := [2, 1, 4, 2, 1, 4, 1, 1, 1, 3, 3]
def baseStart_4053864 : Nat := 118140960795 + 4053864 * 2 ^ 59
def prefixEnd_4053864 : Nat := 4983230072969 + 3 ^ 40 * 4053864 * 2
def baseEnd_4053864 : Nat := 2081580739958232472156625

theorem tailTrace_4053864 : CollatzResearch.WordTrace tailWord_4053864 prefixEnd_4053864 2081580739958232472156625 := by
  unfold tailWord_4053864
  simp only [CollatzResearch.WordTrace]
  refine ⟨73928283492775273847960323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98571044657033698463947097 73928283492775273847960323)
  ·
    refine ⟨110892425239162910771940485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73928283492775273847960323 110892425239162910771940485)
    ·
      refine ⟨20792329732343045769738841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110892425239162910771940485 20792329732343045769738841)
      ·
        refine ⟨15594247299257284327304131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20792329732343045769738841 15594247299257284327304131)
        ·
          refine ⟨23391370948885926490956197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15594247299257284327304131 23391370948885926490956197)
          ·
            refine ⟨4385882052916111217054287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23391370948885926490956197 4385882052916111217054287)
            ·
              refine ⟨6578823079374166825581431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4385882052916111217054287 6578823079374166825581431)
              ·
                refine ⟨9868234619061250238372147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6578823079374166825581431 9868234619061250238372147)
                ·
                  refine ⟨14802351928591875357558221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9868234619061250238372147 14802351928591875357558221)
                  ·
                    refine ⟨5550881973221953259084333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14802351928591875357558221 5550881973221953259084333)
                    ·
                      refine ⟨2081580739958232472156625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5550881973221953259084333 2081580739958232472156625)
                      ·
                        rfl

theorem cell23_4053864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 1, 1, 1, 3, 3].length) (baseStart_4053864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4053864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4053864 prefixEnd_4053864 := by exact prefixLift 4053864
  have htrace : WordTrace (prefixWord ++ tailWord_4053864) baseStart_4053864 baseEnd_4053864 := by
    simpa [prefixWord, tailWord_4053864, baseEnd_4053864] using wordTrace_append hprefix tailTrace_4053864
  have hstable : (prefixWord ++ tailWord_4053864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4053864).length < 2 ^ (prefixWord ++ tailWord_4053864).sum := by decide
  have hdescent : baseEnd_4053864 < baseStart_4053864 := by decide
  rcases family_descends (prefixWord ++ tailWord_4053864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4053874 : List Nat := [3, 2, 1, 2, 1, 1, 3, 4, 1, 3, 2]
def baseStart_4053874 : Nat := 118140960795 + 4053874 * 2 ^ 59
def prefixEnd_4053874 : Nat := 4983230072969 + 3 ^ 40 * 4053874 * 2
def baseEnd_4053874 : Nat := 2081585874764777433031579

theorem tailTrace_4053874 : CollatzResearch.WordTrace tailWord_4053874 prefixEnd_4053874 2081585874764777433031579 := by
  unfold tailWord_4053874
  simp only [CollatzResearch.WordTrace]
  refine ⟨36964232928878579850946169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98571287810342879602523117 36964232928878579850946169)
  ·
    refine ⟨27723174696658934888209627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36964232928878579850946169 27723174696658934888209627)
    ·
      refine ⟨41584762044988402332314441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27723174696658934888209627 41584762044988402332314441)
      ·
        refine ⟨31188571533741301749235831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41584762044988402332314441 31188571533741301749235831)
        ·
          refine ⟨46782857300611952623853747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31188571533741301749235831 46782857300611952623853747)
          ·
            refine ⟨70174285950917928935780621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46782857300611952623853747 70174285950917928935780621)
            ·
              refine ⟨26315357231594223350917733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70174285950917928935780621 26315357231594223350917733)
              ·
                refine ⟨4934129480923916878297075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26315357231594223350917733 4934129480923916878297075)
                ·
                  refine ⟨7401194221385875317445613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4934129480923916878297075 7401194221385875317445613)
                  ·
                    refine ⟨2775447833019703244042105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7401194221385875317445613 2775447833019703244042105)
                    ·
                      refine ⟨2081585874764777433031579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2775447833019703244042105 2081585874764777433031579)
                      ·
                        rfl

theorem cell23_4053874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 4, 1, 3, 2].length) (baseStart_4053874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4053874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4053874 prefixEnd_4053874 := by exact prefixLift 4053874
  have htrace : WordTrace (prefixWord ++ tailWord_4053874) baseStart_4053874 baseEnd_4053874 := by
    simpa [prefixWord, tailWord_4053874, baseEnd_4053874] using wordTrace_append hprefix tailTrace_4053874
  have hstable : (prefixWord ++ tailWord_4053874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4053874).length < 2 ^ (prefixWord ++ tailWord_4053874).sum := by decide
  have hdescent : baseEnd_4053874 < baseStart_4053874 := by decide
  rcases family_descends (prefixWord ++ tailWord_4053874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4053887 : List Nat := [1, 1, 2, 2, 1, 1, 4, 4, 1, 4, 2]
def baseStart_4053887 : Nat := 118140960795 + 4053887 * 2 ^ 59
def prefixEnd_4053887 : Nat := 4983230072969 + 3 ^ 40 * 4053887 * 2
def baseEnd_4053887 : Nat := 2081592550013285882169019

theorem tailTrace_4053887 : CollatzResearch.WordTrace tailWord_4053887 prefixEnd_4053887 2081592550013285882169019 := by
  unfold tailWord_4053887
  simp only [CollatzResearch.WordTrace]
  refine ⟨147857405864467222624007915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98571603909644815082671943 147857405864467222624007915)
  ·
    refine ⟨221786108796700833936011873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147857405864467222624007915 221786108796700833936011873)
    ·
      refine ⟨166339581597525625452008905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221786108796700833936011873 166339581597525625452008905)
      ·
        refine ⟨124754686198144219089006679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166339581597525625452008905 124754686198144219089006679)
        ·
          refine ⟨187132029297216328633510019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124754686198144219089006679 187132029297216328633510019)
          ·
            refine ⟨280698043945824492950265029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187132029297216328633510019 280698043945824492950265029)
            ·
              refine ⟨52630883239842092428174693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 280698043945824492950265029 52630883239842092428174693)
              ·
                refine ⟨9868290607470392330282755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52630883239842092428174693 9868290607470392330282755)
                ·
                  refine ⟨14802435911205588495424133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9868290607470392330282755 14802435911205588495424133)
                  ·
                    refine ⟨2775456733351047842892025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14802435911205588495424133 2775456733351047842892025)
                    ·
                      refine ⟨2081592550013285882169019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2775456733351047842892025 2081592550013285882169019)
                      ·
                        rfl

theorem cell23_4053887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 4, 1, 4, 2].length) (baseStart_4053887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4053887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4053887 prefixEnd_4053887 := by exact prefixLift 4053887
  have htrace : WordTrace (prefixWord ++ tailWord_4053887) baseStart_4053887 baseEnd_4053887 := by
    simpa [prefixWord, tailWord_4053887, baseEnd_4053887] using wordTrace_append hprefix tailTrace_4053887
  have hstable : (prefixWord ++ tailWord_4053887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4053887).length < 2 ^ (prefixWord ++ tailWord_4053887).sum := by decide
  have hdescent : baseEnd_4053887 < baseStart_4053887 := by decide
  rcases family_descends (prefixWord ++ tailWord_4053887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4053900 : List Nat := [2, 2, 1, 2, 1, 2, 2, 1, 4, 2, 4]
def baseStart_4053900 : Nat := 118140960795 + 4053900 * 2 ^ 59
def prefixEnd_4053900 : Nat := 4983230072969 + 3 ^ 40 * 4053900 * 2
def baseEnd_4053900 : Nat := 2081599225261794331306459

theorem tailTrace_4053900 : CollatzResearch.WordTrace tailWord_4053900 prefixEnd_4053900 2081599225261794331306459 := by
  unfold tailWord_4053900
  simp only [CollatzResearch.WordTrace]
  refine ⟨73928940006710062922115577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98571920008946750562820769 73928940006710062922115577)
  ·
    refine ⟨55446705005032547191586683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73928940006710062922115577 55446705005032547191586683)
    ·
      refine ⟨83170057507548820787380025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55446705005032547191586683 83170057507548820787380025)
      ·
        refine ⟨62377543130661615590535019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83170057507548820787380025 62377543130661615590535019)
        ·
          refine ⟨93566314695992423385802529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62377543130661615590535019 93566314695992423385802529)
          ·
            refine ⟨70174736021994317539351897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93566314695992423385802529 70174736021994317539351897)
            ·
              refine ⟨52631052016495738154513923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70174736021994317539351897 52631052016495738154513923)
              ·
                refine ⟨78946578024743607231770885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52631052016495738154513923 78946578024743607231770885)
                ·
                  refine ⟨14802483379639426355957041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78946578024743607231770885 14802483379639426355957041)
                  ·
                    refine ⟨11101862534729569766967781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14802483379639426355957041 11101862534729569766967781)
                    ·
                      refine ⟨2081599225261794331306459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11101862534729569766967781 2081599225261794331306459)
                      ·
                        rfl

theorem cell23_4053900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 4, 2, 4].length) (baseStart_4053900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4053900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4053900 prefixEnd_4053900 := by exact prefixLift 4053900
  have htrace : WordTrace (prefixWord ++ tailWord_4053900) baseStart_4053900 baseEnd_4053900 := by
    simpa [prefixWord, tailWord_4053900, baseEnd_4053900] using wordTrace_append hprefix tailTrace_4053900
  have hstable : (prefixWord ++ tailWord_4053900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4053900).length < 2 ^ (prefixWord ++ tailWord_4053900).sum := by decide
  have hdescent : baseEnd_4053900 < baseStart_4053900 := by decide
  rcases family_descends (prefixWord ++ tailWord_4053900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4053994 : List Nat := [3, 1, 3, 1, 2, 2, 3, 1, 2, 1, 4]
def baseStart_4053994 : Nat := 118140960795 + 4053994 * 2 ^ 59
def prefixEnd_4053994 : Nat := 4983230072969 + 3 ^ 40 * 4053994 * 2
def baseEnd_4053994 : Nat := 2081647492443316963531027

theorem tailTrace_4053994 : CollatzResearch.WordTrace tailWord_4053994 prefixEnd_4053994 2081647492443316963531027 := by
  unfold tailWord_4053994
  simp only [CollatzResearch.WordTrace]
  refine ⟨36965327118769894974538259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98574205650053053265435357 36965327118769894974538259)
  ·
    refine ⟨55447990678154842461807389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36965327118769894974538259 55447990678154842461807389)
    ·
      refine ⟨20792996504308065923177771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55447990678154842461807389 20792996504308065923177771)
      ·
        refine ⟨31189494756462098884766657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20792996504308065923177771 31189494756462098884766657)
        ·
          refine ⟨23392121067346574163574993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31189494756462098884766657 23392121067346574163574993)
          ·
            refine ⟨17544090800509930622681245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23392121067346574163574993 17544090800509930622681245)
            ·
              refine ⟨6579034050191223983505467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17544090800509930622681245 6579034050191223983505467)
              ·
                refine ⟨9868551075286835975258201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6579034050191223983505467 9868551075286835975258201)
                ·
                  refine ⟨7401413306465126981443651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9868551075286835975258201 7401413306465126981443651)
                  ·
                    refine ⟨11102119959697690472165477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7401413306465126981443651 11102119959697690472165477)
                    ·
                      refine ⟨2081647492443316963531027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11102119959697690472165477 2081647492443316963531027)
                      ·
                        rfl

theorem cell23_4053994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3, 1, 2, 1, 4].length) (baseStart_4053994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4053994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4053994 prefixEnd_4053994 := by exact prefixLift 4053994
  have htrace : WordTrace (prefixWord ++ tailWord_4053994) baseStart_4053994 baseEnd_4053994 := by
    simpa [prefixWord, tailWord_4053994, baseEnd_4053994] using wordTrace_append hprefix tailTrace_4053994
  have hstable : (prefixWord ++ tailWord_4053994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4053994).length < 2 ^ (prefixWord ++ tailWord_4053994).sum := by decide
  have hdescent : baseEnd_4053994 < baseStart_4053994 := by decide
  rcases family_descends (prefixWord ++ tailWord_4053994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4054000 : List Nat := [2, 1, 1, 1, 3, 2, 1, 4, 8]
def baseStart_4054000 : Nat := 118140960795 + 4054000 * 2 ^ 59
def prefixEnd_4054000 : Nat := 4983230072969 + 3 ^ 40 * 4054000 * 2
def baseEnd_4054000 : Nat := 231294508147471548895111

theorem tailTrace_4054000 : CollatzResearch.WordTrace tailWord_4054000 prefixEnd_4054000 231294508147471548895111 := by
  unfold tailWord_4054000
  simp only [CollatzResearch.WordTrace]
  refine ⟨73930763656528921461435727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98574351542038561948580969 73930763656528921461435727)
  ·
    refine ⟨110896145484793382192153591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73930763656528921461435727 110896145484793382192153591)
    ·
      refine ⟨166344218227190073288230387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110896145484793382192153591 166344218227190073288230387)
      ·
        refine ⟨249516327340785109932345581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166344218227190073288230387 249516327340785109932345581)
        ·
          refine ⟨93568622752794416224629593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 249516327340785109932345581 93568622752794416224629593)
          ·
            refine ⟨70176467064595812168472195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93568622752794416224629593 70176467064595812168472195)
            ·
              refine ⟨105264700596893718252708293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70176467064595812168472195 105264700596893718252708293)
              ·
                refine ⟨19737131361917572172382805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105264700596893718252708293 19737131361917572172382805)
                ·
                  refine ⟨231294508147471548895111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19737131361917572172382805 231294508147471548895111)
                  ·
                    rfl

theorem cell23_4054000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 4, 8].length) (baseStart_4054000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4054000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4054000 prefixEnd_4054000 := by exact prefixLift 4054000
  have htrace : WordTrace (prefixWord ++ tailWord_4054000) baseStart_4054000 baseEnd_4054000 := by
    simpa [prefixWord, tailWord_4054000, baseEnd_4054000] using wordTrace_append hprefix tailTrace_4054000
  have hstable : (prefixWord ++ tailWord_4054000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4054000).length < 2 ^ (prefixWord ++ tailWord_4054000).sum := by decide
  have hdescent : baseEnd_4054000 < baseStart_4054000 := by decide
  rcases family_descends (prefixWord ++ tailWord_4054000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4054017 : List Nat := [1, 2, 4, 1, 2, 3, 1, 1, 8]
def baseStart_4054017 : Nat := 118140960795 + 4054017 * 2 ^ 59
def prefixEnd_4054017 : Nat := 4983230072969 + 3 ^ 40 * 4054017 * 2
def baseEnd_4054017 : Nat := 231295478055374485949269

theorem tailTrace_4054017 : CollatzResearch.WordTrace tailWord_4054017 prefixEnd_4054017 231295478055374485949269 := by
  unfold tailWord_4054017
  simp only [CollatzResearch.WordTrace]
  refine ⟨147862147353996254826240305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98574764902664169884160203 147862147353996254826240305)
  ·
    refine ⟨110896610515497191119680229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147862147353996254826240305 110896610515497191119680229)
    ·
      refine ⟨20793114471655723334940043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110896610515497191119680229 20793114471655723334940043)
      ·
        refine ⟨31189671707483585002410065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20793114471655723334940043 31189671707483585002410065)
        ·
          refine ⟨23392253780612688751807549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31189671707483585002410065 23392253780612688751807549)
          ·
            refine ⟨8772095167729758281927831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23392253780612688751807549 8772095167729758281927831)
            ·
              refine ⟨13158142751594637422891747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8772095167729758281927831 13158142751594637422891747)
              ·
                refine ⟨19737214127391956134337621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13158142751594637422891747 19737214127391956134337621)
                ·
                  refine ⟨231295478055374485949269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19737214127391956134337621 231295478055374485949269)
                  ·
                    rfl

theorem cell23_4054017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 1, 8].length) (baseStart_4054017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4054017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4054017 prefixEnd_4054017 := by exact prefixLift 4054017
  have htrace : WordTrace (prefixWord ++ tailWord_4054017) baseStart_4054017 baseEnd_4054017 := by
    simpa [prefixWord, tailWord_4054017, baseEnd_4054017] using wordTrace_append hprefix tailTrace_4054017
  have hstable : (prefixWord ++ tailWord_4054017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4054017).length < 2 ^ (prefixWord ++ tailWord_4054017).sum := by decide
  have hdescent : baseEnd_4054017 < baseStart_4054017 := by decide
  rcases family_descends (prefixWord ++ tailWord_4054017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4054055 : List Nat := [1, 1, 7, 1, 1, 3, 1, 3, 1, 4]
def baseStart_4054055 : Nat := 118140960795 + 4054055 * 2 ^ 59
def prefixEnd_4054055 : Nat := 4983230072969 + 3 ^ 40 * 4054055 * 2
def baseEnd_4054055 : Nat := 693892938254413741622749

theorem tailTrace_4054055 : CollatzResearch.WordTrace tailWord_4054055 prefixEnd_4054055 693892938254413741622749 := by
  unfold tailWord_4054055
  simp only [CollatzResearch.WordTrace]
  refine ⟨147863533327858587316123619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98575688885239058210749079 147863533327858587316123619)
  ·
    refine ⟨221795299991787880974185429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147863533327858587316123619 221795299991787880974185429)
    ·
      refine ⟨5198327343557528460332471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 221795299991787880974185429 5198327343557528460332471)
      ·
        refine ⟨7797491015336292690498707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5198327343557528460332471 7797491015336292690498707)
        ·
          refine ⟨11696236523004439035748061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7797491015336292690498707 11696236523004439035748061)
          ·
            refine ⟨4386088696126664638405523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11696236523004439035748061 4386088696126664638405523)
            ·
              refine ⟨6579133044189996957608285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4386088696126664638405523 6579133044189996957608285)
              ·
                refine ⟨2467174891571248859103107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6579133044189996957608285 2467174891571248859103107)
                ·
                  refine ⟨3700762337356873288654661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2467174891571248859103107 3700762337356873288654661)
                  ·
                    refine ⟨693892938254413741622749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3700762337356873288654661 693892938254413741622749)
                    ·
                      rfl

theorem cell23_4054055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_4054055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4054055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4054055 prefixEnd_4054055 := by exact prefixLift 4054055
  have htrace : WordTrace (prefixWord ++ tailWord_4054055) baseStart_4054055 baseEnd_4054055 := by
    simpa [prefixWord, tailWord_4054055, baseEnd_4054055] using wordTrace_append hprefix tailTrace_4054055
  have hstable : (prefixWord ++ tailWord_4054055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4054055).length < 2 ^ (prefixWord ++ tailWord_4054055).sum := by decide
  have hdescent : baseEnd_4054055 < baseStart_4054055 := by decide
  rcases family_descends (prefixWord ++ tailWord_4054055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4054067 : List Nat := [1, 1, 1, 2, 4, 1, 1, 2, 5, 1, 4]
def baseStart_4054067 : Nat := 118140960795 + 4054067 * 2 ^ 59
def prefixEnd_4054067 : Nat := 4983230072969 + 3 ^ 40 * 4054067 * 2
def baseEnd_4054067 : Nat := 2081684976531095177918191

theorem tailTrace_4054067 : CollatzResearch.WordTrace tailWord_4054067 prefixEnd_4054067 2081684976531095177918191 := by
  unfold tailWord_4054067
  simp only [CollatzResearch.WordTrace]
  refine ⟨147863971003815113365560455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98575980669210075577040303 147863971003815113365560455)
  ·
    refine ⟨221795956505722670048340683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147863971003815113365560455 221795956505722670048340683)
    ·
      refine ⟨332693934758584005072511025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221795956505722670048340683 332693934758584005072511025)
      ·
        refine ⟨249520451068938003804383269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 332693934758584005072511025 249520451068938003804383269)
        ·
          refine ⟨46785084575425875713321863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 249520451068938003804383269 46785084575425875713321863)
          ·
            refine ⟨70177626863138813569982795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46785084575425875713321863 70177626863138813569982795)
            ·
              refine ⟨105266440294708220354974193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70177626863138813569982795 105266440294708220354974193)
              ·
                refine ⟨78949830221031165266230645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105266440294708220354974193 78949830221031165266230645)
                ·
                  refine ⟨7401546583221671743709123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78949830221031165266230645 7401546583221671743709123)
                  ·
                    refine ⟨11102319874832507615563685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7401546583221671743709123 11102319874832507615563685)
                    ·
                      refine ⟨2081684976531095177918191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11102319874832507615563685 2081684976531095177918191)
                      ·
                        rfl

theorem cell23_4054067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 5, 1, 4].length) (baseStart_4054067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4054067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4054067 prefixEnd_4054067 := by exact prefixLift 4054067
  have htrace : WordTrace (prefixWord ++ tailWord_4054067) baseStart_4054067 baseEnd_4054067 := by
    simpa [prefixWord, tailWord_4054067, baseEnd_4054067] using wordTrace_append hprefix tailTrace_4054067
  have hstable : (prefixWord ++ tailWord_4054067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4054067).length < 2 ^ (prefixWord ++ tailWord_4054067).sum := by decide
  have hdescent : baseEnd_4054067 < baseStart_4054067 := by decide
  rcases family_descends (prefixWord ++ tailWord_4054067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4054078 : List Nat := [4, 2, 1, 3, 1, 1, 3, 1, 3, 1, 3]
def baseStart_4054078 : Nat := 118140960795 + 4054078 * 2 ^ 59
def prefixEnd_4054078 : Nat := 4983230072969 + 3 ^ 40 * 4054078 * 2
def baseEnd_4054078 : Nat := 2081690624818294634880641

theorem tailTrace_4054078 : CollatzResearch.WordTrace tailWord_4054078 prefixEnd_4054078 2081690624818294634880641 := by
  unfold tailWord_4054078
  simp only [CollatzResearch.WordTrace]
  refine ⟨18483046525846907780526361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98576248137850174829473925 18483046525846907780526361)
  ·
    refine ⟨13862284894385180835394771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18483046525846907780526361 13862284894385180835394771)
    ·
      refine ⟨20793427341577771253092157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13862284894385180835394771 20793427341577771253092157)
      ·
        refine ⟨7797535253091664219909559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20793427341577771253092157 7797535253091664219909559)
        ·
          refine ⟨11696302879637496329864339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7797535253091664219909559 11696302879637496329864339)
          ·
            refine ⟨17544454319456244494796509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11696302879637496329864339 17544454319456244494796509)
            ·
              refine ⟨6579170369796091685548691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17544454319456244494796509 6579170369796091685548691)
              ·
                refine ⟨9868755554694137528323037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6579170369796091685548691 9868755554694137528323037)
                ·
                  refine ⟨3700783333010301573121139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9868755554694137528323037 3700783333010301573121139)
                  ·
                    refine ⟨5551174999515452359681709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3700783333010301573121139 5551174999515452359681709)
                    ·
                      refine ⟨2081690624818294634880641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5551174999515452359681709 2081690624818294634880641)
                      ·
                        rfl

theorem cell23_4054078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_4054078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4054078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4054078 prefixEnd_4054078 := by exact prefixLift 4054078
  have htrace : WordTrace (prefixWord ++ tailWord_4054078) baseStart_4054078 baseEnd_4054078 := by
    simpa [prefixWord, tailWord_4054078, baseEnd_4054078] using wordTrace_append hprefix tailTrace_4054078
  have hstable : (prefixWord ++ tailWord_4054078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4054078).length < 2 ^ (prefixWord ++ tailWord_4054078).sum := by decide
  have hdescent : baseEnd_4054078 < baseStart_4054078 := by decide
  rcases family_descends (prefixWord ++ tailWord_4054078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4054097 : List Nat := [1, 2, 2, 1, 3, 1, 4, 1, 1, 1, 6]
def baseStart_4054097 : Nat := 118140960795 + 4054097 * 2 ^ 59
def prefixEnd_4054097 : Nat := 4983230072969 + 3 ^ 40 * 4054097 * 2
def baseEnd_4054097 : Nat := 2081700380950730060543053

theorem tailTrace_4054097 : CollatzResearch.WordTrace tailWord_4054097 prefixEnd_4054097 2081700380950730060543053 := by
  unfold tailWord_4054097
  simp only [CollatzResearch.WordTrace]
  refine ⟨147865065193706428489152545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98576710129137618992768363 147865065193706428489152545)
  ·
    refine ⟨110898798895279821366864409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147865065193706428489152545 110898798895279821366864409)
    ·
      refine ⟨83174099171459866025148307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110898798895279821366864409 83174099171459866025148307)
      ·
        refine ⟨124761148757189799037722461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83174099171459866025148307 124761148757189799037722461)
        ·
          refine ⟨46785430783946174639145923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124761148757189799037722461 46785430783946174639145923)
          ·
            refine ⟨70178146175919261958718885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46785430783946174639145923 70178146175919261958718885)
            ·
              refine ⟨13158402407984861617259791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70178146175919261958718885 13158402407984861617259791)
              ·
                refine ⟨19737603611977292425889687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13158402407984861617259791 19737603611977292425889687)
                ·
                  refine ⟨29606405417965938638834531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19737603611977292425889687 29606405417965938638834531)
                  ·
                    refine ⟨44409608126948907958251797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29606405417965938638834531 44409608126948907958251797)
                    ·
                      refine ⟨2081700380950730060543053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44409608126948907958251797 2081700380950730060543053)
                      ·
                        rfl

theorem cell23_4054097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 1, 1, 1, 6].length) (baseStart_4054097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4054097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4054097 prefixEnd_4054097 := by exact prefixLift 4054097
  have htrace : WordTrace (prefixWord ++ tailWord_4054097) baseStart_4054097 baseEnd_4054097 := by
    simpa [prefixWord, tailWord_4054097, baseEnd_4054097] using wordTrace_append hprefix tailTrace_4054097
  have hstable : (prefixWord ++ tailWord_4054097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4054097).length < 2 ^ (prefixWord ++ tailWord_4054097).sum := by decide
  have hdescent : baseEnd_4054097 < baseStart_4054097 := by decide
  rcases family_descends (prefixWord ++ tailWord_4054097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4054101 : List Nat := [1, 3, 2, 2, 1, 2, 2, 1, 5, 2, 2]
def baseStart_4054101 : Nat := 118140960795 + 4054101 * 2 ^ 59
def prefixEnd_4054101 : Nat := 4983230072969 + 3 ^ 40 * 4054101 * 2
def baseEnd_4054101 : Nat := 2081702434873348044893035

theorem tailTrace_4054101 : CollatzResearch.WordTrace tailWord_4054101 prefixEnd_4054101 2081702434873348044893035 := by
  unfold tailWord_4054101
  simp only [CollatzResearch.WordTrace]
  refine ⟨147865211085691937172298157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98576807390461291448198771 147865211085691937172298157)
  ·
    refine ⟨55449454157134476439611809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147865211085691937172298157 55449454157134476439611809)
    ·
      refine ⟨41587090617850857329708857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55449454157134476439611809 41587090617850857329708857)
      ·
        refine ⟨31190317963388142997281643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41587090617850857329708857 31190317963388142997281643)
        ·
          refine ⟨46785476945082214495922465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31190317963388142997281643 46785476945082214495922465)
          ·
            refine ⟨35089107708811660871941849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46785476945082214495922465 35089107708811660871941849)
            ·
              refine ⟨26316830781608745653956387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35089107708811660871941849 26316830781608745653956387)
              ·
                refine ⟨39475246172413118480934581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26316830781608745653956387 39475246172413118480934581)
                ·
                  refine ⟨3700804328663729857587617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39475246172413118480934581 3700804328663729857587617)
                  ·
                    refine ⟨2775603246497797393190713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3700804328663729857587617 2775603246497797393190713)
                    ·
                      refine ⟨2081702434873348044893035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2775603246497797393190713 2081702434873348044893035)
                      ·
                        rfl

theorem cell23_4054101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 1, 5, 2, 2].length) (baseStart_4054101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4054101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4054101 prefixEnd_4054101 := by exact prefixLift 4054101
  have htrace : WordTrace (prefixWord ++ tailWord_4054101) baseStart_4054101 baseEnd_4054101 := by
    simpa [prefixWord, tailWord_4054101, baseEnd_4054101] using wordTrace_append hprefix tailTrace_4054101
  have hstable : (prefixWord ++ tailWord_4054101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4054101).length < 2 ^ (prefixWord ++ tailWord_4054101).sum := by decide
  have hdescent : baseEnd_4054101 < baseStart_4054101 := by decide
  rcases family_descends (prefixWord ++ tailWord_4054101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4054104 : List Nat := [2, 1, 2, 2, 1, 3, 3, 1, 3, 2, 3]
def baseStart_4054104 : Nat := 118140960795 + 4054104 * 2 ^ 59
def prefixEnd_4054104 : Nat := 4983230072969 + 3 ^ 40 * 4054104 * 2
def baseEnd_4054104 : Nat := 2081703975315311533155521

theorem tailTrace_4054104 : CollatzResearch.WordTrace tailWord_4054104 prefixEnd_4054104 2081703975315311533155521 := by
  unfold tailWord_4054104
  simp only [CollatzResearch.WordTrace]
  refine ⟨73932660252340534342328683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98576880336454045789771577 73932660252340534342328683)
  ·
    refine ⟨110898990378510801513493025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73932660252340534342328683 110898990378510801513493025)
    ·
      refine ⟨83174242783883101135119769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110898990378510801513493025 83174242783883101135119769)
      ·
        refine ⟨62380682087912325851339827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83174242783883101135119769 62380682087912325851339827)
        ·
          refine ⟨93571023131868488777009741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62380682087912325851339827 93571023131868488777009741)
          ·
            refine ⟨35089133674450683291378653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93571023131868488777009741 35089133674450683291378653)
            ·
              refine ⟨13158425127919006234266995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35089133674450683291378653 13158425127919006234266995)
              ·
                refine ⟨19737637691878509351400493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13158425127919006234266995 19737637691878509351400493)
                ·
                  refine ⟨7401614134454441006775185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19737637691878509351400493 7401614134454441006775185)
                  ·
                    refine ⟨5551210600840830755081389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7401614134454441006775185 5551210600840830755081389)
                    ·
                      refine ⟨2081703975315311533155521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5551210600840830755081389 2081703975315311533155521)
                      ·
                        rfl

theorem cell23_4054104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 1, 3, 2, 3].length) (baseStart_4054104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4054104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4054104 prefixEnd_4054104 := by exact prefixLift 4054104
  have htrace : WordTrace (prefixWord ++ tailWord_4054104) baseStart_4054104 baseEnd_4054104 := by
    simpa [prefixWord, tailWord_4054104, baseEnd_4054104] using wordTrace_append hprefix tailTrace_4054104
  have hstable : (prefixWord ++ tailWord_4054104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4054104).length < 2 ^ (prefixWord ++ tailWord_4054104).sum := by decide
  have hdescent : baseEnd_4054104 < baseStart_4054104 := by decide
  rcases family_descends (prefixWord ++ tailWord_4054104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4054187 : List Nat := [1, 1, 1, 1, 2, 1, 1, 1, 2, 8, 4]
def baseStart_4054187 : Nat := 118140960795 + 4054187 * 2 ^ 59
def prefixEnd_4054187 : Nat := 4983230072969 + 3 ^ 40 * 4054187 * 2
def baseEnd_4054187 : Nat := 2081746594209634708417639

theorem tailTrace_4054187 : CollatzResearch.WordTrace tailWord_4054187 prefixEnd_4054187 2081746594209634708417639 := by
  unfold tailWord_4054187
  simp only [CollatzResearch.WordTrace]
  refine ⟨147868347763380373859928815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98578898508920249239952543 147868347763380373859928815)
  ·
    refine ⟨221802521645070560789893223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147868347763380373859928815 221802521645070560789893223)
    ·
      refine ⟨332703782467605841184839835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221802521645070560789893223 332703782467605841184839835)
      ·
        refine ⟨499055673701408761777259753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332703782467605841184839835 499055673701408761777259753)
        ·
          refine ⟨374291755276056571332944815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 499055673701408761777259753 374291755276056571332944815)
          ·
            refine ⟨561437632914084856999417223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 374291755276056571332944815 561437632914084856999417223)
            ·
              refine ⟨842156449371127285499125835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 561437632914084856999417223 842156449371127285499125835)
              ·
                refine ⟨1263234674056690928248688753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 842156449371127285499125835 1263234674056690928248688753)
                ·
                  refine ⟨947426005542518196186516565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1263234674056690928248688753 947426005542518196186516565)
                  ·
                    refine ⟨11102648502451385111560741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 947426005542518196186516565 11102648502451385111560741)
                    ·
                      refine ⟨2081746594209634708417639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11102648502451385111560741 2081746594209634708417639)
                      ·
                        rfl

theorem cell23_4054187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 8, 4].length) (baseStart_4054187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4054187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4054187 prefixEnd_4054187 := by exact prefixLift 4054187
  have htrace : WordTrace (prefixWord ++ tailWord_4054187) baseStart_4054187 baseEnd_4054187 := by
    simpa [prefixWord, tailWord_4054187, baseEnd_4054187] using wordTrace_append hprefix tailTrace_4054187
  have hstable : (prefixWord ++ tailWord_4054187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4054187).length < 2 ^ (prefixWord ++ tailWord_4054187).sum := by decide
  have hdescent : baseEnd_4054187 < baseStart_4054187 := by decide
  rcases family_descends (prefixWord ++ tailWord_4054187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4054217 : List Nat := [1, 2, 1, 1, 2, 1, 1, 2, 2, 4, 6]
def baseStart_4054217 : Nat := 118140960795 + 4054217 * 2 ^ 59
def prefixEnd_4054217 : Nat := 4983230072969 + 3 ^ 40 * 4054217 * 2
def baseEnd_4054217 : Nat := 2081761998629269591042501

theorem tailTrace_4054217 : CollatzResearch.WordTrace tailWord_4054217 prefixEnd_4054217 2081761998629269591042501 := by
  unfold tailWord_4054217
  simp only [CollatzResearch.WordTrace]
  refine ⟨147869441953271688983520905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98579627968847792655680603 147869441953271688983520905)
  ·
    refine ⟨110902081464953766737640679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147869441953271688983520905 110902081464953766737640679)
    ·
      refine ⟨166353122197430650106461019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110902081464953766737640679 166353122197430650106461019)
      ·
        refine ⟨249529683296145975159691529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166353122197430650106461019 249529683296145975159691529)
        ·
          refine ⟨187147262472109481369768647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 249529683296145975159691529 187147262472109481369768647)
          ·
            refine ⟨280720893708164222054652971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187147262472109481369768647 280720893708164222054652971)
            ·
              refine ⟨421081340562246333081979457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 280720893708164222054652971 421081340562246333081979457)
              ·
                refine ⟨315811005421684749811484593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 421081340562246333081979457 315811005421684749811484593)
                ·
                  refine ⟨236858254066263562358613445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 315811005421684749811484593 236858254066263562358613445)
                  ·
                    refine ⟨44410922637424417942240021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 236858254066263562358613445 44410922637424417942240021)
                    ·
                      refine ⟨2081761998629269591042501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44410922637424417942240021 2081761998629269591042501)
                      ·
                        rfl

theorem cell23_4054217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 4, 6].length) (baseStart_4054217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4054217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4054217 prefixEnd_4054217 := by exact prefixLift 4054217
  have htrace : WordTrace (prefixWord ++ tailWord_4054217) baseStart_4054217 baseEnd_4054217 := by
    simpa [prefixWord, tailWord_4054217, baseEnd_4054217] using wordTrace_append hprefix tailTrace_4054217
  have hstable : (prefixWord ++ tailWord_4054217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4054217).length < 2 ^ (prefixWord ++ tailWord_4054217).sum := by decide
  have hdescent : baseEnd_4054217 < baseStart_4054217 := by decide
  rcases family_descends (prefixWord ++ tailWord_4054217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4054228 : List Nat := [2, 4, 1, 4, 1, 1, 1, 1, 2, 1, 5]
def baseStart_4054228 : Nat := 118140960795 + 4054228 * 2 ^ 59
def prefixEnd_4054228 : Nat := 4983230072969 + 3 ^ 40 * 4054228 * 2
def baseEnd_4054228 : Nat := 2081767646916469048004951

theorem tailTrace_4054228 : CollatzResearch.WordTrace tailWord_4054228 prefixEnd_4054228 2081767646916469048004951 := by
  unfold tailWord_4054228
  simp only [CollatzResearch.WordTrace]
  refine ⟨73934921578115918931085669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98579895437487891908114225 73934921578115918931085669)
  ·
    refine ⟨13862797795896734799578563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73934921578115918931085669 13862797795896734799578563)
    ·
      refine ⟨20794196693845102199367845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13862797795896734799578563 20794196693845102199367845)
      ·
        refine ⟨3898911880095956662381471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20794196693845102199367845 3898911880095956662381471)
        ·
          refine ⟨5848367820143934993572207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3898911880095956662381471 5848367820143934993572207)
          ·
            refine ⟨8772551730215902490358311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5848367820143934993572207 8772551730215902490358311)
            ·
              refine ⟨13158827595323853735537467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8772551730215902490358311 13158827595323853735537467)
              ·
                refine ⟨19738241392985780603306201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13158827595323853735537467 19738241392985780603306201)
                ·
                  refine ⟨14803681044739335452479651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19738241392985780603306201 14803681044739335452479651)
                  ·
                    refine ⟨22205521567109003178719477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14803681044739335452479651 22205521567109003178719477)
                    ·
                      refine ⟨2081767646916469048004951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22205521567109003178719477 2081767646916469048004951)
                      ·
                        rfl

theorem cell23_4054228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_4054228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4054228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4054228 prefixEnd_4054228 := by exact prefixLift 4054228
  have htrace : WordTrace (prefixWord ++ tailWord_4054228) baseStart_4054228 baseEnd_4054228 := by
    simpa [prefixWord, tailWord_4054228, baseEnd_4054228] using wordTrace_append hprefix tailTrace_4054228
  have hstable : (prefixWord ++ tailWord_4054228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4054228).length < 2 ^ (prefixWord ++ tailWord_4054228).sum := by decide
  have hdescent : baseEnd_4054228 < baseStart_4054228 := by decide
  rcases family_descends (prefixWord ++ tailWord_4054228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4054231 : List Nat := [1, 1, 3, 2, 1, 2, 5, 3, 5]
def baseStart_4054231 : Nat := 118140960795 + 4054231 * 2 ^ 59
def prefixEnd_4054231 : Nat := 4983230072969 + 3 ^ 40 * 4054231 * 2
def baseEnd_4054231 : Nat := 231307687484270281807493

theorem tailTrace_4054231 : CollatzResearch.WordTrace tailWord_4054231 prefixEnd_4054231 231307687484270281807493 := by
  unfold tailWord_4054231
  simp only [CollatzResearch.WordTrace]
  refine ⟨147869952575220969374530547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98579968383480646249687031 147869952575220969374530547)
  ·
    refine ⟨221804928862831454061795821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147869952575220969374530547 221804928862831454061795821)
    ·
      refine ⟨83176848323561795273173433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221804928862831454061795821 83176848323561795273173433)
      ·
        refine ⟨62382636242671346454880075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83176848323561795273173433 62382636242671346454880075)
        ·
          refine ⟨93573954364007019682320113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62382636242671346454880075 93573954364007019682320113)
          ·
            refine ⟨70180465773005264761740085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93573954364007019682320113 70180465773005264761740085)
            ·
              refine ⟨6579418666219243571413133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70180465773005264761740085 6579418666219243571413133)
              ·
                refine ⟨2467281999832216339279925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6579418666219243571413133 2467281999832216339279925)
                ·
                  refine ⟨231307687484270281807493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2467281999832216339279925 231307687484270281807493)
                  ·
                    rfl

theorem cell23_4054231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5, 3, 5].length) (baseStart_4054231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4054231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4054231 prefixEnd_4054231 := by exact prefixLift 4054231
  have htrace : WordTrace (prefixWord ++ tailWord_4054231) baseStart_4054231 baseEnd_4054231 := by
    simpa [prefixWord, tailWord_4054231, baseEnd_4054231] using wordTrace_append hprefix tailTrace_4054231
  have hstable : (prefixWord ++ tailWord_4054231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4054231).length < 2 ^ (prefixWord ++ tailWord_4054231).sum := by decide
  have hdescent : baseEnd_4054231 < baseStart_4054231 := by decide
  rcases family_descends (prefixWord ++ tailWord_4054231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4054244 : List Nat := [2, 3, 1, 1, 1, 2, 3, 1, 4, 5]
def baseStart_4054244 : Nat := 118140960795 + 4054244 * 2 ^ 59
def prefixEnd_4054244 : Nat := 4983230072969 + 3 ^ 40 * 4054244 * 2
def baseEnd_4054244 : Nat := 693925287535646995134959

theorem tailTrace_4054244 : CollatzResearch.WordTrace tailWord_4054244 prefixEnd_4054244 693925287535646995134959 := by
  unfold tailWord_4054244
  simp only [CollatzResearch.WordTrace]
  refine ⟨73935213362086936297376893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98580284482782581729835857 73935213362086936297376893)
  ·
    refine ⟨27725705010782601111516335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73935213362086936297376893 27725705010782601111516335)
    ·
      refine ⟨41588557516173901667274503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27725705010782601111516335 41588557516173901667274503)
      ·
        refine ⟨62382836274260852500911755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41588557516173901667274503 62382836274260852500911755)
        ·
          refine ⟨93574254411391278751367633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62382836274260852500911755 93574254411391278751367633)
          ·
            refine ⟨70180690808543459063525725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93574254411391278751367633 70180690808543459063525725)
            ·
              refine ⟨26317759053203797148822147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70180690808543459063525725 26317759053203797148822147)
              ·
                refine ⟨39476638579805695723233221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26317759053203797148822147 39476638579805695723233221)
                ·
                  refine ⟨7401869733713567948106229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39476638579805695723233221 7401869733713567948106229)
                  ·
                    refine ⟨693925287535646995134959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7401869733713567948106229 693925287535646995134959)
                    ·
                      rfl

theorem cell23_4054244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 1, 4, 5].length) (baseStart_4054244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4054244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4054244 prefixEnd_4054244 := by exact prefixLift 4054244
  have htrace : WordTrace (prefixWord ++ tailWord_4054244) baseStart_4054244 baseEnd_4054244 := by
    simpa [prefixWord, tailWord_4054244, baseEnd_4054244] using wordTrace_append hprefix tailTrace_4054244
  have hstable : (prefixWord ++ tailWord_4054244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4054244).length < 2 ^ (prefixWord ++ tailWord_4054244).sum := by decide
  have hdescent : baseEnd_4054244 < baseStart_4054244 := by decide
  rcases family_descends (prefixWord ++ tailWord_4054244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4054248 : List Nat := [2, 1, 4, 1, 2, 1, 5, 2, 5]
def baseStart_4054248 : Nat := 118140960795 + 4054248 * 2 ^ 59
def prefixEnd_4054248 : Nat := 4983230072969 + 3 ^ 40 * 4054248 * 2
def baseEnd_4054248 : Nat := 231308657392173218861651

theorem tailTrace_4054248 : CollatzResearch.WordTrace tailWord_4054248 prefixEnd_4054248 231308657392173218861651 := by
  unfold tailWord_4054248
  simp only [CollatzResearch.WordTrace]
  refine ⟨73935286308079690638949699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98580381744106254185266265 73935286308079690638949699)
  ·
    refine ⟨110902929462119535958424549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73935286308079690638949699 110902929462119535958424549)
    ·
      refine ⟨20794299274147412992204603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110902929462119535958424549 20794299274147412992204603)
      ·
        refine ⟨31191448911221119488306905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20794299274147412992204603 31191448911221119488306905)
        ·
          refine ⟨23393586683415839616230179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31191448911221119488306905 23393586683415839616230179)
          ·
            refine ⟨35090380025123759424345269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23393586683415839616230179 35090380025123759424345269)
            ·
              refine ⟨3289723127355352446032369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35090380025123759424345269 3289723127355352446032369)
              ·
                refine ⟨2467292345516514334524277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3289723127355352446032369 2467292345516514334524277)
                ·
                  refine ⟨231308657392173218861651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2467292345516514334524277 231308657392173218861651)
                  ·
                    rfl

theorem cell23_4054248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 5, 2, 5].length) (baseStart_4054248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4054248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4054248 prefixEnd_4054248 := by exact prefixLift 4054248
  have htrace : WordTrace (prefixWord ++ tailWord_4054248) baseStart_4054248 baseEnd_4054248 := by
    simpa [prefixWord, tailWord_4054248, baseEnd_4054248] using wordTrace_append hprefix tailTrace_4054248
  have hstable : (prefixWord ++ tailWord_4054248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4054248).length < 2 ^ (prefixWord ++ tailWord_4054248).sum := by decide
  have hdescent : baseEnd_4054248 < baseStart_4054248 := by decide
  rcases family_descends (prefixWord ++ tailWord_4054248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4054254 : List Nat := [4, 1, 2, 1, 1, 1, 3, 1, 1, 1, 7]
def baseStart_4054254 : Nat := 118140960795 + 4054254 * 2 ^ 59
def prefixEnd_4054254 : Nat := 4983230072969 + 3 ^ 40 * 4054254 * 2
def baseEnd_4054254 : Nat := 2081780997413485946279831

theorem tailTrace_4054254 : CollatzResearch.WordTrace tailWord_4054254 prefixEnd_4054254 2081780997413485946279831 := by
  unfold tailWord_4054254
  simp only [CollatzResearch.WordTrace]
  refine ⟨18483848931767205537827227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98580527636091762868411877 18483848931767205537827227)
  ·
    refine ⟨27725773397650808306740841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18483848931767205537827227 27725773397650808306740841)
    ·
      refine ⟨20794330048238106230055631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27725773397650808306740841 20794330048238106230055631)
      ·
        refine ⟨31191495072357159345083447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20794330048238106230055631 31191495072357159345083447)
        ·
          refine ⟨46787242608535739017625171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31191495072357159345083447 46787242608535739017625171)
          ·
            refine ⟨70180863912803608526437757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46787242608535739017625171 70180863912803608526437757)
            ·
              refine ⟨26317823967301353197414159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70180863912803608526437757 26317823967301353197414159)
              ·
                refine ⟨39476735950952029796121239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26317823967301353197414159 39476735950952029796121239)
                ·
                  refine ⟨59215103926428044694181859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39476735950952029796121239 59215103926428044694181859)
                  ·
                    refine ⟨88822655889642067041272789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59215103926428044694181859 88822655889642067041272789)
                    ·
                      refine ⟨2081780997413485946279831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 88822655889642067041272789 2081780997413485946279831)
                      ·
                        rfl

theorem cell23_4054254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_4054254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4054254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4054254 prefixEnd_4054254 := by exact prefixLift 4054254
  have htrace : WordTrace (prefixWord ++ tailWord_4054254) baseStart_4054254 baseEnd_4054254 := by
    simpa [prefixWord, tailWord_4054254, baseEnd_4054254] using wordTrace_append hprefix tailTrace_4054254
  have hstable : (prefixWord ++ tailWord_4054254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4054254).length < 2 ^ (prefixWord ++ tailWord_4054254).sum := by decide
  have hdescent : baseEnd_4054254 < baseStart_4054254 := by decide
  rcases family_descends (prefixWord ++ tailWord_4054254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4054281 : List Nat := [1, 2, 1, 1, 3, 3, 4, 1, 2, 1, 4]
def baseStart_4054281 : Nat := 118140960795 + 4054281 * 2 ^ 59
def prefixEnd_4054281 : Nat := 4983230072969 + 3 ^ 40 * 4054281 * 2
def baseEnd_4054281 : Nat := 2081794861391157340642207

theorem tailTrace_4054281 : CollatzResearch.WordTrace tailWord_4054281 prefixEnd_4054281 2081794861391157340642207 := by
  unfold tailWord_4054281
  simp only [CollatzResearch.WordTrace]
  refine ⟨147871776225039827913850697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98581184150026551942567131 147871776225039827913850697)
  ·
    refine ⟨110903832168779870935388023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147871776225039827913850697 110903832168779870935388023)
    ·
      refine ⟨166355748253169806403082035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110903832168779870935388023 166355748253169806403082035)
      ·
        refine ⟨249533622379754709604623053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166355748253169806403082035 249533622379754709604623053)
        ·
          refine ⟨93575108392408016101733645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 249533622379754709604623053 93575108392408016101733645)
          ·
            refine ⟨35090665647153006038150117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93575108392408016101733645 35090665647153006038150117)
            ·
              refine ⟨6579499808841188632153147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35090665647153006038150117 6579499808841188632153147)
              ·
                refine ⟨9869249713261782948229721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6579499808841188632153147 9869249713261782948229721)
                ·
                  refine ⟨7401937284946337211172291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9869249713261782948229721 7401937284946337211172291)
                  ·
                    refine ⟨11102905927419505816758437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7401937284946337211172291 11102905927419505816758437)
                    ·
                      refine ⟨2081794861391157340642207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11102905927419505816758437 2081794861391157340642207)
                      ·
                        rfl

theorem cell23_4054281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4, 1, 2, 1, 4].length) (baseStart_4054281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4054281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4054281 prefixEnd_4054281 := by exact prefixLift 4054281
  have htrace : WordTrace (prefixWord ++ tailWord_4054281) baseStart_4054281 baseEnd_4054281 := by
    simpa [prefixWord, tailWord_4054281, baseEnd_4054281] using wordTrace_append hprefix tailTrace_4054281
  have hstable : (prefixWord ++ tailWord_4054281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4054281).length < 2 ^ (prefixWord ++ tailWord_4054281).sum := by decide
  have hdescent : baseEnd_4054281 < baseStart_4054281 := by decide
  rcases family_descends (prefixWord ++ tailWord_4054281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4054321 : List Nat := [1, 2, 2, 3, 3, 1, 2, 3, 6]
def baseStart_4054321 : Nat := 118140960795 + 4054321 * 2 ^ 59
def prefixEnd_4054321 : Nat := 4983230072969 + 3 ^ 40 * 4054321 * 2
def baseEnd_4054321 : Nat := 231312822290815242682447

theorem tailTrace_4054321 : CollatzResearch.WordTrace tailWord_4054321 prefixEnd_4054321 231312822290815242682447 := by
  unfold tailWord_4054321
  simp only [CollatzResearch.WordTrace]
  refine ⟨147873235144894914745306817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98582156763263276496871211 147873235144894914745306817)
  ·
    refine ⟨110904926358671186058980113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147873235144894914745306817 110904926358671186058980113)
    ·
      refine ⟨83178694769003389544235085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110904926358671186058980113 83178694769003389544235085)
      ·
        refine ⟨31192010538376271079088157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83178694769003389544235085 31192010538376271079088157)
        ·
          refine ⟨11697003951891101654658059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31192010538376271079088157 11697003951891101654658059)
          ·
            refine ⟨17545505927836652481987089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11697003951891101654658059 17545505927836652481987089)
            ·
              refine ⟨13159129445877489361490317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17545505927836652481987089 13159129445877489361490317)
              ·
                refine ⟨4934673542204058510558869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13159129445877489361490317 4934673542204058510558869)
                ·
                  refine ⟨231312822290815242682447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4934673542204058510558869 231312822290815242682447)
                  ·
                    rfl

theorem cell23_4054321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 3, 6].length) (baseStart_4054321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4054321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4054321 prefixEnd_4054321 := by exact prefixLift 4054321
  have htrace : WordTrace (prefixWord ++ tailWord_4054321) baseStart_4054321 baseEnd_4054321 := by
    simpa [prefixWord, tailWord_4054321, baseEnd_4054321] using wordTrace_append hprefix tailTrace_4054321
  have hstable : (prefixWord ++ tailWord_4054321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4054321).length < 2 ^ (prefixWord ++ tailWord_4054321).sum := by decide
  have hdescent : baseEnd_4054321 < baseStart_4054321 := by decide
  rcases family_descends (prefixWord ++ tailWord_4054321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4054344 : List Nat := [2, 1, 3, 1, 1, 2, 1, 1, 2, 4, 5]
def baseStart_4054344 : Nat := 118140960795 + 4054344 * 2 ^ 59
def prefixEnd_4054344 : Nat := 4983230072969 + 3 ^ 40 * 4054344 * 2
def baseEnd_4054344 : Nat := 2081827210672390594154417

theorem tailTrace_4054344 : CollatzResearch.WordTrace tailWord_4054344 prefixEnd_4054344 2081827210672390594154417 := by
  unfold tailWord_4054344
  simp only [CollatzResearch.WordTrace]
  refine ⟨73937037011905794836697043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98582716015874393115596057 73937037011905794836697043)
  ·
    refine ⟨110905555517858692255045565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73937037011905794836697043 110905555517858692255045565)
    ·
      refine ⟨41589583319197009595642087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110905555517858692255045565 41589583319197009595642087)
      ·
        refine ⟨62384374978795514393463131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41589583319197009595642087 62384374978795514393463131)
        ·
          refine ⟨93576562468193271590194697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62384374978795514393463131 93576562468193271590194697)
          ·
            refine ⟨70182421851144953692646023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93576562468193271590194697 70182421851144953692646023)
            ·
              refine ⟨105273632776717430538969035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70182421851144953692646023 105273632776717430538969035)
              ·
                refine ⟨157910449165076145808453553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105273632776717430538969035 157910449165076145808453553)
                ·
                  refine ⟨118432836873807109356340165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 157910449165076145808453553 118432836873807109356340165)
                  ·
                    refine ⟨22206156913838833004313781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 118432836873807109356340165 22206156913838833004313781)
                    ·
                      refine ⟨2081827210672390594154417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22206156913838833004313781 2081827210672390594154417)
                      ·
                        rfl

theorem cell23_4054344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 2, 4, 5].length) (baseStart_4054344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4054344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4054344 prefixEnd_4054344 := by exact prefixLift 4054344
  have htrace : WordTrace (prefixWord ++ tailWord_4054344) baseStart_4054344 baseEnd_4054344 := by
    simpa [prefixWord, tailWord_4054344, baseEnd_4054344] using wordTrace_append hprefix tailTrace_4054344
  have hstable : (prefixWord ++ tailWord_4054344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4054344).length < 2 ^ (prefixWord ++ tailWord_4054344).sum := by decide
  have hdescent : baseEnd_4054344 < baseStart_4054344 := by decide
  rcases family_descends (prefixWord ++ tailWord_4054344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4054394 : List Nat := [3, 1, 1, 1, 1, 1, 2, 13]
def baseStart_4054394 : Nat := 118140960795 + 4054394 * 2 ^ 59
def prefixEnd_4054394 : Nat := 4983230072969 + 3 ^ 40 * 4054394 * 2
def baseEnd_4054394 : Nat := 77105662396485755501081

theorem tailTrace_4054394 : CollatzResearch.WordTrace tailWord_4054394 prefixEnd_4054394 77105662396485755501081 := by
  unfold tailWord_4054394
  simp only [CollatzResearch.WordTrace]
  refine ⟨36968974418407612053178559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98583931782420298808476157 36968974418407612053178559)
  ·
    refine ⟨55453461627611418079767839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36968974418407612053178559 55453461627611418079767839)
    ·
      refine ⟨83180192441417127119651759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55453461627611418079767839 83180192441417127119651759)
      ·
        refine ⟨124770288662125690679477639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83180192441417127119651759 124770288662125690679477639)
        ·
          refine ⟨187155432993188536019216459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124770288662125690679477639 187155432993188536019216459)
          ·
            refine ⟨280733149489782804028824689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187155432993188536019216459 280733149489782804028824689)
            ·
              refine ⟨210549862117337103021618517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 280733149489782804028824689 210549862117337103021618517)
              ·
                refine ⟨77105662396485755501081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 210549862117337103021618517 77105662396485755501081)
                ·
                  rfl

theorem cell23_4054394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 13].length) (baseStart_4054394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4054394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4054394 prefixEnd_4054394 := by exact prefixLift 4054394
  have htrace : WordTrace (prefixWord ++ tailWord_4054394) baseStart_4054394 baseEnd_4054394 := by
    simpa [prefixWord, tailWord_4054394, baseEnd_4054394] using wordTrace_append hprefix tailTrace_4054394
  have hstable : (prefixWord ++ tailWord_4054394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4054394).length < 2 ^ (prefixWord ++ tailWord_4054394).sum := by decide
  have hdescent : baseEnd_4054394 < baseStart_4054394 := by decide
  rcases family_descends (prefixWord ++ tailWord_4054394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4054408 : List Nat := [2, 1, 3, 3, 1, 3, 2, 1, 1, 1, 5]
def baseStart_4054408 : Nat := 118140960795 + 4054408 * 2 ^ 59
def prefixEnd_4054408 : Nat := 4983230072969 + 3 ^ 40 * 4054408 * 2
def baseEnd_4054408 : Nat := 2081860073434278343754123

theorem tailTrace_4054408 : CollatzResearch.WordTrace tailWord_4054408 prefixEnd_4054408 2081860073434278343754123 := by
  unfold tailWord_4054408
  simp only [CollatzResearch.WordTrace]
  refine ⟨73938204147789864301861939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98584272197053152402482585 73938204147789864301861939)
  ·
    refine ⟨110907306221684796452792909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73938204147789864301861939 110907306221684796452792909)
    ·
      refine ⟨41590239833131798669797341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110907306221684796452792909 41590239833131798669797341)
      ·
        refine ⟨15596339937424424501174003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41590239833131798669797341 15596339937424424501174003)
        ·
          refine ⟨23394509906136636751761005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15596339937424424501174003 23394509906136636751761005)
          ·
            refine ⟨8772941214801238781910377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23394509906136636751761005 8772941214801238781910377)
            ·
              refine ⟨6579705911100929086432783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8772941214801238781910377 6579705911100929086432783)
              ·
                refine ⟨9869558866651393629649175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6579705911100929086432783 9869558866651393629649175)
                ·
                  refine ⟨14804338299977090444473763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9869558866651393629649175 14804338299977090444473763)
                  ·
                    refine ⟨22206507449965635666710645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14804338299977090444473763 22206507449965635666710645)
                    ·
                      refine ⟨2081860073434278343754123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22206507449965635666710645 2081860073434278343754123)
                      ·
                        rfl

theorem cell23_4054408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2, 1, 1, 1, 5].length) (baseStart_4054408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4054408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4054408 prefixEnd_4054408 := by exact prefixLift 4054408
  have htrace : WordTrace (prefixWord ++ tailWord_4054408) baseStart_4054408 baseEnd_4054408 := by
    simpa [prefixWord, tailWord_4054408, baseEnd_4054408] using wordTrace_append hprefix tailTrace_4054408
  have hstable : (prefixWord ++ tailWord_4054408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4054408).length < 2 ^ (prefixWord ++ tailWord_4054408).sum := by decide
  have hdescent : baseEnd_4054408 < baseStart_4054408 := by decide
  rcases family_descends (prefixWord ++ tailWord_4054408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4054471 : List Nat := [1, 1, 4, 1, 1, 3, 2, 2, 2, 6]
def baseStart_4054471 : Nat := 118140960795 + 4054471 * 2 ^ 59
def prefixEnd_4054471 : Nat := 4983230072969 + 3 ^ 40 * 4054471 * 2
def baseEnd_4054471 : Nat := 693964140905170532422111

theorem tailTrace_4054471 : CollatzResearch.WordTrace tailWord_4054471 prefixEnd_4054471 693964140905170532422111 := by
  unfold tailWord_4054471
  simp only [CollatzResearch.WordTrace]
  refine ⟨147878706094351490363267267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98585804062900993575511511 147878706094351490363267267)
  ·
    refine ⟨221818059141527235544900901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147878706094351490363267267 221818059141527235544900901)
    ·
      refine ⟨41590886089036356664668919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 221818059141527235544900901 41590886089036356664668919)
      ·
        refine ⟨62386329133554534997003379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41590886089036356664668919 62386329133554534997003379)
        ·
          refine ⟨93579493700331802495505069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62386329133554534997003379 93579493700331802495505069)
          ·
            refine ⟨35092310137624425935814401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93579493700331802495505069 35092310137624425935814401)
            ·
              refine ⟨26319232603218319451860801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35092310137624425935814401 26319232603218319451860801)
              ·
                refine ⟨19739424452413739588895601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26319232603218319451860801 19739424452413739588895601)
                ·
                  refine ⟨14804568339310304691671701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19739424452413739588895601 14804568339310304691671701)
                  ·
                    refine ⟨693964140905170532422111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14804568339310304691671701 693964140905170532422111)
                    ·
                      rfl

theorem cell23_4054471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 2, 2, 6].length) (baseStart_4054471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4054471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4054471 prefixEnd_4054471 := by exact prefixLift 4054471
  have htrace : WordTrace (prefixWord ++ tailWord_4054471) baseStart_4054471 baseEnd_4054471 := by
    simpa [prefixWord, tailWord_4054471, baseEnd_4054471] using wordTrace_append hprefix tailTrace_4054471
  have hstable : (prefixWord ++ tailWord_4054471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4054471).length < 2 ^ (prefixWord ++ tailWord_4054471).sum := by decide
  have hdescent : baseEnd_4054471 < baseStart_4054471 := by decide
  rcases family_descends (prefixWord ++ tailWord_4054471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4054495 : List Nat := [1, 1, 2, 3, 3, 1, 4, 1, 1, 4, 2]
def baseStart_4054495 : Nat := 118140960795 + 4054495 * 2 ^ 59
def prefixEnd_4054495 : Nat := 4983230072969 + 3 ^ 40 * 4054495 * 2
def baseEnd_4054495 : Nat := 2081904746251219503366223

theorem tailTrace_4054495 : CollatzResearch.WordTrace tailWord_4054495 prefixEnd_4054495 2081904746251219503366223 := by
  unfold tailWord_4054495
  simp only [CollatzResearch.WordTrace]
  refine ⟨147879581446264542462140939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98586387630843028308093959 147879581446264542462140939)
  ·
    refine ⟨221819372169396813693211409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147879581446264542462140939 221819372169396813693211409)
    ·
      refine ⟨166364529127047610269908557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221819372169396813693211409 166364529127047610269908557)
      ·
        refine ⟨62386698422642853851215709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166364529127047610269908557 62386698422642853851215709)
        ·
          refine ⟨23395011908491070194205891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62386698422642853851215709 23395011908491070194205891)
          ·
            refine ⟨35092517862736605291308837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23395011908491070194205891 35092517862736605291308837)
            ·
              refine ⟨6579847099263113492120407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35092517862736605291308837 6579847099263113492120407)
              ·
                refine ⟨9869770648894670238180611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6579847099263113492120407 9869770648894670238180611)
                ·
                  refine ⟨14804655973342005357270917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9869770648894670238180611 14804655973342005357270917)
                  ·
                    refine ⟨2775872995001626004488297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14804655973342005357270917 2775872995001626004488297)
                    ·
                      refine ⟨2081904746251219503366223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2775872995001626004488297 2081904746251219503366223)
                      ·
                        rfl

theorem cell23_4054495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4, 1, 1, 4, 2].length) (baseStart_4054495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4054495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4054495 prefixEnd_4054495 := by exact prefixLift 4054495
  have htrace : WordTrace (prefixWord ++ tailWord_4054495) baseStart_4054495 baseEnd_4054495 := by
    simpa [prefixWord, tailWord_4054495, baseEnd_4054495] using wordTrace_append hprefix tailTrace_4054495
  have hstable : (prefixWord ++ tailWord_4054495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4054495).length < 2 ^ (prefixWord ++ tailWord_4054495).sum := by decide
  have hdescent : baseEnd_4054495 < baseStart_4054495 := by decide
  rcases family_descends (prefixWord ++ tailWord_4054495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4054535 : List Nat := [1, 1, 4, 3, 2, 1, 2, 4, 5]
def baseStart_4054535 : Nat := 118140960795 + 4054535 * 2 ^ 59
def prefixEnd_4054535 : Nat := 4983230072969 + 3 ^ 40 * 4054535 * 2
def baseEnd_4054535 : Nat := 231325031719711038540671

theorem tailTrace_4054535 : CollatzResearch.WordTrace tailWord_4054535 prefixEnd_4054535 231325031719711038540671 := by
  unfold tailWord_4054535
  simp only [CollatzResearch.WordTrace]
  refine ⟨147881040366119629293597059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98587360244079752862398039 147881040366119629293597059)
  ·
    refine ⟨221821560549179443940395589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147881040366119629293597059 221821560549179443940395589)
    ·
      refine ⟨41591542602971145738824173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 221821560549179443940395589 41591542602971145738824173)
      ·
        refine ⟨15596828476114179652059065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41591542602971145738824173 15596828476114179652059065)
        ·
          refine ⟨11697621357085634739044299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15596828476114179652059065 11697621357085634739044299)
          ·
            refine ⟨17546432035628452108566449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11697621357085634739044299 17546432035628452108566449)
            ·
              refine ⟨13159824026721339081424837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17546432035628452108566449 13159824026721339081424837)
              ·
                refine ⟨2467467005010251077767157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13159824026721339081424837 2467467005010251077767157)
                ·
                  refine ⟨231325031719711038540671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2467467005010251077767157 231325031719711038540671)
                  ·
                    rfl

theorem cell23_4054535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 4, 5].length) (baseStart_4054535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4054535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4054535 prefixEnd_4054535 := by exact prefixLift 4054535
  have htrace : WordTrace (prefixWord ++ tailWord_4054535) baseStart_4054535 baseEnd_4054535 := by
    simpa [prefixWord, tailWord_4054535, baseEnd_4054535] using wordTrace_append hprefix tailTrace_4054535
  have hstable : (prefixWord ++ tailWord_4054535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4054535).length < 2 ^ (prefixWord ++ tailWord_4054535).sum := by decide
  have hdescent : baseEnd_4054535 < baseStart_4054535 := by decide
  rcases family_descends (prefixWord ++ tailWord_4054535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4054571 : List Nat := [1, 1, 1, 1, 2, 1, 3, 1, 4, 3, 5]
def baseStart_4054571 : Nat := 118140960795 + 4054571 * 2 ^ 59
def prefixEnd_4054571 : Nat := 4983230072969 + 3 ^ 40 * 4054571 * 2
def baseEnd_4054571 : Nat := 2081943770780961206015873

theorem tailTrace_4054571 : CollatzResearch.WordTrace tailWord_4054571 prefixEnd_4054571 2081943770780961206015873 := by
  unfold tailWord_4054571
  simp only [CollatzResearch.WordTrace]
  refine ⟨147882353393989207441907567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98588235595992804961271711 147882353393989207441907567)
  ·
    refine ⟨221823530090983811162861351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147882353393989207441907567 221823530090983811162861351)
    ·
      refine ⟨332735295136475716744292027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221823530090983811162861351 332735295136475716744292027)
      ·
        refine ⟨499102942704713575116438041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332735295136475716744292027 499102942704713575116438041)
        ·
          refine ⟨374327207028535181337328531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 499102942704713575116438041 374327207028535181337328531)
          ·
            refine ⟨561490810542802772005992797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 374327207028535181337328531 561490810542802772005992797)
            ·
              refine ⟨210559053953551039502247299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 561490810542802772005992797 210559053953551039502247299)
              ·
                refine ⟨315838580930326559253370949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 210559053953551039502247299 315838580930326559253370949)
                ·
                  refine ⟨59219733924436229860007053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 315838580930326559253370949 59219733924436229860007053)
                  ·
                    refine ⟨22207400221663586197502645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59219733924436229860007053 22207400221663586197502645)
                    ·
                      refine ⟨2081943770780961206015873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22207400221663586197502645 2081943770780961206015873)
                      ·
                        rfl

theorem cell23_4054571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 4, 3, 5].length) (baseStart_4054571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4054571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4054571 prefixEnd_4054571 := by exact prefixLift 4054571
  have htrace : WordTrace (prefixWord ++ tailWord_4054571) baseStart_4054571 baseEnd_4054571 := by
    simpa [prefixWord, tailWord_4054571, baseEnd_4054571] using wordTrace_append hprefix tailTrace_4054571
  have hstable : (prefixWord ++ tailWord_4054571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4054571).length < 2 ^ (prefixWord ++ tailWord_4054571).sum := by decide
  have hdescent : baseEnd_4054571 < baseStart_4054571 := by decide
  rcases family_descends (prefixWord ++ tailWord_4054571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4054582 : List Nat := [5, 1, 2, 1, 3, 1, 1, 2, 2, 5]
def baseStart_4054582 : Nat := 118140960795 + 4054582 * 2 ^ 59
def prefixEnd_4054582 : Nat := 4983230072969 + 3 ^ 40 * 4054582 * 2
def baseEnd_4054582 : Nat := 693983139689386887659441

theorem tailTrace_4054582 : CollatzResearch.WordTrace tailWord_4054582 prefixEnd_4054582 693983139689386887659441 := by
  unfold tailWord_4054582
  simp only [CollatzResearch.WordTrace]
  refine ⟨9242672162309334770034875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 98588503064632904213705333 9242672162309334770034875)
  ·
    refine ⟨13864008243464002155052313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9242672162309334770034875 13864008243464002155052313)
    ·
      refine ⟨10398006182598001616289235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13864008243464002155052313 10398006182598001616289235)
      ·
        refine ⟨15597009273897002424433853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10398006182598001616289235 15597009273897002424433853)
        ·
          refine ⟨5848878477711375909162695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15597009273897002424433853 5848878477711375909162695)
          ·
            refine ⟨8773317716567063863744043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5848878477711375909162695 8773317716567063863744043)
            ·
              refine ⟨13159976574850595795616065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8773317716567063863744043 13159976574850595795616065)
              ·
                refine ⟨9869982431137946846712049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13159976574850595795616065 9869982431137946846712049)
                ·
                  refine ⟨7402486823353460135034037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9869982431137946846712049 7402486823353460135034037)
                  ·
                    refine ⟨693983139689386887659441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7402486823353460135034037 693983139689386887659441)
                    ·
                      rfl

theorem cell23_4054582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 2, 2, 5].length) (baseStart_4054582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4054582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4054582 prefixEnd_4054582 := by exact prefixLift 4054582
  have htrace : WordTrace (prefixWord ++ tailWord_4054582) baseStart_4054582 baseEnd_4054582 := by
    simpa [prefixWord, tailWord_4054582, baseEnd_4054582] using wordTrace_append hprefix tailTrace_4054582
  have hstable : (prefixWord ++ tailWord_4054582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4054582).length < 2 ^ (prefixWord ++ tailWord_4054582).sum := by decide
  have hdescent : baseEnd_4054582 < baseStart_4054582 := by decide
  rcases family_descends (prefixWord ++ tailWord_4054582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4054585 : List Nat := [1, 2, 1, 5, 1, 3, 1, 2, 2, 1, 4]
def baseStart_4054585 : Nat := 118140960795 + 4054585 * 2 ^ 59
def prefixEnd_4054585 : Nat := 4983230072969 + 3 ^ 40 * 4054585 * 2
def baseEnd_4054585 : Nat := 2081950959510124151240809

theorem tailTrace_4054585 : CollatzResearch.WordTrace tailWord_4054585 prefixEnd_4054585 2081950959510124151240809 := by
  unfold tailWord_4054585
  simp only [CollatzResearch.WordTrace]
  refine ⟨147882864015938487832917209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98588576010625658555278139 147882864015938487832917209)
  ·
    refine ⟨110912148011953865874687907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147882864015938487832917209 110912148011953865874687907)
    ·
      refine ⟨166368222017930798812031861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110912148011953865874687907 166368222017930798812031861)
      ·
        refine ⟨15597020814181012388627987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 166368222017930798812031861 15597020814181012388627987)
        ·
          refine ⟨23395531221271518582941981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15597020814181012388627987 23395531221271518582941981)
          ·
            refine ⟨8773324207976819468603243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23395531221271518582941981 8773324207976819468603243)
            ·
              refine ⟨13159986311965229202904865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8773324207976819468603243 13159986311965229202904865)
              ·
                refine ⟨9869989733973921902178649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13159986311965229202904865 9869989733973921902178649)
                ·
                  refine ⟨7402492300480441426633987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9869989733973921902178649 7402492300480441426633987)
                  ·
                    refine ⟨11103738450720662139950981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7402492300480441426633987 11103738450720662139950981)
                    ·
                      refine ⟨2081950959510124151240809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11103738450720662139950981 2081950959510124151240809)
                      ·
                        rfl

theorem cell23_4054585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_4054585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4054585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4054585 prefixEnd_4054585 := by exact prefixLift 4054585
  have htrace : WordTrace (prefixWord ++ tailWord_4054585) baseStart_4054585 baseEnd_4054585 := by
    simpa [prefixWord, tailWord_4054585, baseEnd_4054585] using wordTrace_append hprefix tailTrace_4054585
  have hstable : (prefixWord ++ tailWord_4054585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4054585).length < 2 ^ (prefixWord ++ tailWord_4054585).sum := by decide
  have hdescent : baseEnd_4054585 < baseStart_4054585 := by decide
  rcases family_descends (prefixWord ++ tailWord_4054585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4054608 : List Nat := [2, 1, 1, 1, 1, 3, 5, 3, 6]
def baseStart_4054608 : Nat := 118140960795 + 4054608 * 2 ^ 59
def prefixEnd_4054608 : Nat := 4983230072969 + 3 ^ 40 * 4054608 * 2
def baseEnd_4054608 : Nat := 231329196618353062361467

theorem tailTrace_4054608 : CollatzResearch.WordTrace tailWord_4054608 prefixEnd_4054608 231329196618353062361467 := by
  unfold tailWord_4054608
  simp only [CollatzResearch.WordTrace]
  refine ⟨73941851447427581380502239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98589135263236775174002985 73941851447427581380502239)
  ·
    refine ⟨110912777171141372070753359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73941851447427581380502239 110912777171141372070753359)
    ·
      refine ⟨166369165756712058106130039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110912777171141372070753359 166369165756712058106130039)
      ·
        refine ⟨249553748635068087159195059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166369165756712058106130039 249553748635068087159195059)
        ·
          refine ⟨374330622952602130738792589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249553748635068087159195059 374330622952602130738792589)
          ·
            refine ⟨140373983607225799027047221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 374330622952602130738792589 140373983607225799027047221)
            ·
              refine ⟨13160060963177418658785677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 140373983607225799027047221 13160060963177418658785677)
              ·
                refine ⟨4935022861191531997044629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13160060963177418658785677 4935022861191531997044629)
                ·
                  refine ⟨231329196618353062361467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4935022861191531997044629 231329196618353062361467)
                  ·
                    rfl

theorem cell23_4054608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 3, 6].length) (baseStart_4054608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4054608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4054608 prefixEnd_4054608 := by exact prefixLift 4054608
  have htrace : WordTrace (prefixWord ++ tailWord_4054608) baseStart_4054608 baseEnd_4054608 := by
    simpa [prefixWord, tailWord_4054608, baseEnd_4054608] using wordTrace_append hprefix tailTrace_4054608
  have hstable : (prefixWord ++ tailWord_4054608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4054608).length < 2 ^ (prefixWord ++ tailWord_4054608).sum := by decide
  have hdescent : baseEnd_4054608 < baseStart_4054608 := by decide
  rcases family_descends (prefixWord ++ tailWord_4054608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4054618 : List Nat := [3, 1, 1, 2, 1, 1, 1, 3, 2, 5, 3]
def baseStart_4054618 : Nat := 118140960795 + 4054618 * 2 ^ 59
def prefixEnd_4054618 : Nat := 4983230072969 + 3 ^ 40 * 4054618 * 2
def baseEnd_4054618 : Nat := 2081967904371722522128157

theorem tailTrace_4054618 : CollatzResearch.WordTrace tailWord_4054618 prefixEnd_4054618 2081967904371722522128157 := by
  unfold tailWord_4054618
  simp only [CollatzResearch.WordTrace]
  refine ⟨36971016906204733617217127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98589378416545956312579005 36971016906204733617217127)
  ·
    refine ⟨55456525359307100425825691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36971016906204733617217127 55456525359307100425825691)
    ·
      refine ⟨83184788038960650638738537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55456525359307100425825691 83184788038960650638738537)
      ·
        refine ⟨62388591029220487979053903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83184788038960650638738537 62388591029220487979053903)
        ·
          refine ⟨93582886543830731968580855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62388591029220487979053903 93582886543830731968580855)
          ·
            refine ⟨140374329815746097952871283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93582886543830731968580855 140374329815746097952871283)
            ·
              refine ⟨210561494723619146929306925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140374329815746097952871283 210561494723619146929306925)
              ·
                refine ⟨78960560521357180098490097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 210561494723619146929306925 78960560521357180098490097)
                ·
                  refine ⟨59220420391017885073867573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78960560521357180098490097 59220420391017885073867573)
                  ·
                    refine ⟨5551914411657926725675085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59220420391017885073867573 5551914411657926725675085)
                    ·
                      refine ⟨2081967904371722522128157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5551914411657926725675085 2081967904371722522128157)
                      ·
                        rfl

theorem cell23_4054618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 2, 5, 3].length) (baseStart_4054618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4054618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4054618 prefixEnd_4054618 := by exact prefixLift 4054618
  have htrace : WordTrace (prefixWord ++ tailWord_4054618) baseStart_4054618 baseEnd_4054618 := by
    simpa [prefixWord, tailWord_4054618, baseEnd_4054618] using wordTrace_append hprefix tailTrace_4054618
  have hstable : (prefixWord ++ tailWord_4054618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4054618).length < 2 ^ (prefixWord ++ tailWord_4054618).sum := by decide
  have hdescent : baseEnd_4054618 < baseStart_4054618 := by decide
  rcases family_descends (prefixWord ++ tailWord_4054618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4054646 : List Nat := [5, 1, 1, 2, 2, 1, 4, 2, 1, 4]
def baseStart_4054646 : Nat := 118140960795 + 4054646 * 2 ^ 59
def prefixEnd_4054646 : Nat := 4983230072969 + 3 ^ 40 * 4054646 * 2
def baseEnd_4054646 : Nat := 693994093943349470859343

theorem tailTrace_4054646 : CollatzResearch.WordTrace tailWord_4054646 prefixEnd_4054646 693994093943349470859343 := by
  unfold tailWord_4054646
  simp only [CollatzResearch.WordTrace]
  refine ⟨9242818054294843453180487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 98590059245811663500591861 9242818054294843453180487)
  ·
    refine ⟨13864227081442265179770731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9242818054294843453180487 13864227081442265179770731)
    ·
      refine ⟨20796340622163397769656097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13864227081442265179770731 20796340622163397769656097)
      ·
        refine ⟨15597255466622548327242073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20796340622163397769656097 15597255466622548327242073)
        ·
          refine ⟨11697941599966911245431555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15597255466622548327242073 11697941599966911245431555)
          ·
            refine ⟨17546912399950366868147333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11697941599966911245431555 17546912399950366868147333)
            ·
              refine ⟨3290046074990693787777625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17546912399950366868147333 3290046074990693787777625)
              ·
                refine ⟨2467534556243020340833219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3290046074990693787777625 2467534556243020340833219)
                ·
                  refine ⟨3701301834364530511249829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2467534556243020340833219 3701301834364530511249829)
                  ·
                    refine ⟨693994093943349470859343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3701301834364530511249829 693994093943349470859343)
                    ·
                      rfl

theorem cell23_4054646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 4, 2, 1, 4].length) (baseStart_4054646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4054646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4054646 prefixEnd_4054646 := by exact prefixLift 4054646
  have htrace : WordTrace (prefixWord ++ tailWord_4054646) baseStart_4054646 baseEnd_4054646 := by
    simpa [prefixWord, tailWord_4054646, baseEnd_4054646] using wordTrace_append hprefix tailTrace_4054646
  have hstable : (prefixWord ++ tailWord_4054646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4054646).length < 2 ^ (prefixWord ++ tailWord_4054646).sum := by decide
  have hdescent : baseEnd_4054646 < baseStart_4054646 := by decide
  rcases family_descends (prefixWord ++ tailWord_4054646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4054679 : List Nat := [1, 1, 3, 3, 2, 4, 1, 1, 2, 3, 2]
def baseStart_4054679 : Nat := 118140960795 + 4054679 * 2 ^ 59
def prefixEnd_4054679 : Nat := 4983230072969 + 3 ^ 40 * 4054679 * 2
def baseEnd_4054679 : Nat := 2081999226691646783465377

theorem tailTrace_4054679 : CollatzResearch.WordTrace tailWord_4054679 prefixEnd_4054679 2081999226691646783465377 := by
  unfold tailWord_4054679
  simp only [CollatzResearch.WordTrace]
  refine ⟨147886292477597941886839091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98590861651731961257892727 147886292477597941886839091)
  ·
    refine ⟨221829438716396912830258637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147886292477597941886839091 221829438716396912830258637)
    ·
      refine ⟨83186039518648842311346989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221829438716396912830258637 83186039518648842311346989)
      ·
        refine ⟨31194764819493315866755121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83186039518648842311346989 31194764819493315866755121)
        ·
          refine ⟨23396073614619986900066341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31194764819493315866755121 23396073614619986900066341)
          ·
            refine ⟨4386763802741247543762439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23396073614619986900066341 4386763802741247543762439)
            ·
              refine ⟨6580145704111871315643659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4386763802741247543762439 6580145704111871315643659)
              ·
                refine ⟨9870218556167806973465489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6580145704111871315643659 9870218556167806973465489)
                ·
                  refine ⟨7402663917125855230099117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9870218556167806973465489 7402663917125855230099117)
                  ·
                    refine ⟨2775998968922195711287169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7402663917125855230099117 2775998968922195711287169)
                    ·
                      refine ⟨2081999226691646783465377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2775998968922195711287169 2081999226691646783465377)
                      ·
                        rfl

theorem cell23_4054679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 1, 1, 2, 3, 2].length) (baseStart_4054679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4054679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4054679 prefixEnd_4054679 := by exact prefixLift 4054679
  have htrace : WordTrace (prefixWord ++ tailWord_4054679) baseStart_4054679 baseEnd_4054679 := by
    simpa [prefixWord, tailWord_4054679, baseEnd_4054679] using wordTrace_append hprefix tailTrace_4054679
  have hstable : (prefixWord ++ tailWord_4054679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4054679).length < 2 ^ (prefixWord ++ tailWord_4054679).sum := by decide
  have hdescent : baseEnd_4054679 < baseStart_4054679 := by decide
  rcases family_descends (prefixWord ++ tailWord_4054679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4054685 : List Nat := [1, 4, 2, 1, 1, 1, 1, 4, 4, 4]
def baseStart_4054685 : Nat := 118140960795 + 4054685 * 2 ^ 59
def prefixEnd_4054685 : Nat := 4983230072969 + 3 ^ 40 * 4054685 * 2
def baseEnd_4054685 : Nat := 694000769191857919996783

theorem tailTrace_4054685 : CollatzResearch.WordTrace tailWord_4054685 prefixEnd_4054685 694000769191857919996783 := by
  unfold tailWord_4054685
  simp only [CollatzResearch.WordTrace]
  refine ⟨147886511315576204911557509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98591007543717469941038339 147886511315576204911557509)
  ·
    refine ⟨27728720871670538420917033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147886511315576204911557509 27728720871670538420917033)
    ·
      refine ⟨20796540653752903815687775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27728720871670538420917033 20796540653752903815687775)
      ·
        refine ⟨31194810980629355723531663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20796540653752903815687775 31194810980629355723531663)
        ·
          refine ⟨46792216470944033585297495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31194810980629355723531663 46792216470944033585297495)
          ·
            refine ⟨70188324706416050377946243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46792216470944033585297495 70188324706416050377946243)
            ·
              refine ⟨105282487059624075566919365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70188324706416050377946243 105282487059624075566919365)
              ·
                refine ⟨19740466323679514168797381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105282487059624075566919365 19740466323679514168797381)
                ·
                  refine ⟨3701337435689908906649509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19740466323679514168797381 3701337435689908906649509)
                  ·
                    refine ⟨694000769191857919996783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3701337435689908906649509 694000769191857919996783)
                    ·
                      rfl

theorem cell23_4054685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 4, 4, 4].length) (baseStart_4054685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4054685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4054685 prefixEnd_4054685 := by exact prefixLift 4054685
  have htrace : WordTrace (prefixWord ++ tailWord_4054685) baseStart_4054685 baseEnd_4054685 := by
    simpa [prefixWord, tailWord_4054685, baseEnd_4054685] using wordTrace_append hprefix tailTrace_4054685
  have hstable : (prefixWord ++ tailWord_4054685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4054685).length < 2 ^ (prefixWord ++ tailWord_4054685).sum := by decide
  have hdescent : baseEnd_4054685 < baseStart_4054685 := by decide
  rcases family_descends (prefixWord ++ tailWord_4054685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4054686 : List Nat := [4, 3, 1, 1, 1, 2, 1, 5, 1, 1, 3]
def baseStart_4054686 : Nat := 118140960795 + 4054686 * 2 ^ 59
def prefixEnd_4054686 : Nat := 4983230072969 + 3 ^ 40 * 4054686 * 2
def baseEnd_4054686 : Nat := 2082002821056228256077845

theorem tailTrace_4054686 : CollatzResearch.WordTrace tailWord_4054686 prefixEnd_4054686 2082002821056228256077845 := by
  unfold tailWord_4054686
  simp only [CollatzResearch.WordTrace]
  refine ⟨18485818473571572760292989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98591031859048388054895941 18485818473571572760292989)
  ·
    refine ⟨6932181927589339785109871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18485818473571572760292989 6932181927589339785109871)
    ·
      refine ⟨10398272891384009677664807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6932181927589339785109871 10398272891384009677664807)
      ·
        refine ⟨15597409337076014516497211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10398272891384009677664807 15597409337076014516497211)
        ·
          refine ⟨23396114005614021774745817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15597409337076014516497211 23396114005614021774745817)
          ·
            refine ⟨17547085504210516331059363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23396114005614021774745817 17547085504210516331059363)
            ·
              refine ⟨26320628256315774496589045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17547085504210516331059363 26320628256315774496589045)
              ·
                refine ⟨2467558899029603859055223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26320628256315774496589045 2467558899029603859055223)
                ·
                  refine ⟨3701338348544405788582835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2467558899029603859055223 3701338348544405788582835)
                  ·
                    refine ⟨5552007522816608682874253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3701338348544405788582835 5552007522816608682874253)
                    ·
                      refine ⟨2082002821056228256077845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5552007522816608682874253 2082002821056228256077845)
                      ·
                        rfl

theorem cell23_4054686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 5, 1, 1, 3].length) (baseStart_4054686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4054686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4054686 prefixEnd_4054686 := by exact prefixLift 4054686
  have htrace : WordTrace (prefixWord ++ tailWord_4054686) baseStart_4054686 baseEnd_4054686 := by
    simpa [prefixWord, tailWord_4054686, baseEnd_4054686] using wordTrace_append hprefix tailTrace_4054686
  have hstable : (prefixWord ++ tailWord_4054686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4054686).length < 2 ^ (prefixWord ++ tailWord_4054686).sum := by decide
  have hdescent : baseEnd_4054686 < baseStart_4054686 := by decide
  rcases family_descends (prefixWord ++ tailWord_4054686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4054689 : List Nat := [1, 2, 3, 3, 2, 3, 2, 1, 1, 5]
def baseStart_4054689 : Nat := 118140960795 + 4054689 * 2 ^ 59
def prefixEnd_4054689 : Nat := 4983230072969 + 3 ^ 40 * 4054689 * 2
def baseEnd_4054689 : Nat := 694001453832730581446777

theorem tailTrace_4054689 : CollatzResearch.WordTrace tailWord_4054689 prefixEnd_4054689 694001453832730581446777 := by
  unfold tailWord_4054689
  simp only [CollatzResearch.WordTrace]
  refine ⟨147886657207561713594703121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98591104805041142396468747 147886657207561713594703121)
  ·
    refine ⟨110914992905671285196027341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147886657207561713594703121 110914992905671285196027341)
    ·
      refine ⟨41593122339626731948510253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110914992905671285196027341 41593122339626731948510253)
      ·
        refine ⟨15597420877360024480691345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41593122339626731948510253 15597420877360024480691345)
        ·
          refine ⟨11698065658020018360518509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15597420877360024480691345 11698065658020018360518509)
          ·
            refine ⟨4386774621757506885194441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11698065658020018360518509 4386774621757506885194441)
            ·
              refine ⟨3290080966318130163895831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4386774621757506885194441 3290080966318130163895831)
              ·
                refine ⟨4935121449477195245843747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3290080966318130163895831 4935121449477195245843747)
                ·
                  refine ⟨7402682174215792868765621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4935121449477195245843747 7402682174215792868765621)
                  ·
                    refine ⟨694001453832730581446777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7402682174215792868765621 694001453832730581446777)
                    ·
                      rfl

theorem cell23_4054689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 2, 1, 1, 5].length) (baseStart_4054689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4054689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4054689 prefixEnd_4054689 := by exact prefixLift 4054689
  have htrace : WordTrace (prefixWord ++ tailWord_4054689) baseStart_4054689 baseEnd_4054689 := by
    simpa [prefixWord, tailWord_4054689, baseEnd_4054689] using wordTrace_append hprefix tailTrace_4054689
  have hstable : (prefixWord ++ tailWord_4054689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4054689).length < 2 ^ (prefixWord ++ tailWord_4054689).sum := by decide
  have hdescent : baseEnd_4054689 < baseStart_4054689 := by decide
  rcases family_descends (prefixWord ++ tailWord_4054689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4054692 : List Nat := [2, 3, 1, 2, 2, 3, 1, 3, 1, 1, 4]
def baseStart_4054692 : Nat := 118140960795 + 4054692 * 2 ^ 59
def prefixEnd_4054692 : Nat := 4983230072969 + 3 ^ 40 * 4054692 * 2
def baseEnd_4054692 : Nat := 2082005901940155232602817

theorem tailTrace_4054692 : CollatzResearch.WordTrace tailWord_4054692 prefixEnd_4054692 2082005901940155232602817 := by
  unfold tailWord_4054692
  simp only [CollatzResearch.WordTrace]
  refine ⟨73943383313275422553531165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98591177751033896738041553 73943383313275422553531165)
  ·
    refine ⟨27728768742478283457574187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73943383313275422553531165 27728768742478283457574187)
    ·
      refine ⟨41593153113717425186361281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27728768742478283457574187 41593153113717425186361281)
      ·
        refine ⟨31194864835288068889770961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41593153113717425186361281 31194864835288068889770961)
        ·
          refine ⟨23396148626466051667328221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31194864835288068889770961 23396148626466051667328221)
          ·
            refine ⟨8773555734924769375248083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23396148626466051667328221 8773555734924769375248083)
            ·
              refine ⟨13160333602387154062872125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8773555734924769375248083 13160333602387154062872125)
              ·
                refine ⟨4935125100895182773577047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13160333602387154062872125 4935125100895182773577047)
                ·
                  refine ⟨7402687651342774160365571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4935125100895182773577047 7402687651342774160365571)
                  ·
                    refine ⟨11104031477014161240548357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7402687651342774160365571 11104031477014161240548357)
                    ·
                      refine ⟨2082005901940155232602817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11104031477014161240548357 2082005901940155232602817)
                      ·
                        rfl

theorem cell23_4054692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 3, 1, 1, 4].length) (baseStart_4054692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4054692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4054692 prefixEnd_4054692 := by exact prefixLift 4054692
  have htrace : WordTrace (prefixWord ++ tailWord_4054692) baseStart_4054692 baseEnd_4054692 := by
    simpa [prefixWord, tailWord_4054692, baseEnd_4054692] using wordTrace_append hprefix tailTrace_4054692
  have hstable : (prefixWord ++ tailWord_4054692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4054692).length < 2 ^ (prefixWord ++ tailWord_4054692).sum := by decide
  have hdescent : baseEnd_4054692 < baseStart_4054692 := by decide
  rcases family_descends (prefixWord ++ tailWord_4054692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4054726 : List Nat := [6, 1, 2, 1, 1, 1, 1, 4, 1, 1, 4]
def baseStart_4054726 : Nat := 118140960795 + 4054726 * 2 ^ 59
def prefixEnd_4054726 : Nat := 4983230072969 + 3 ^ 40 * 4054726 * 2
def baseEnd_4054726 : Nat := 2082023360282408099577661

theorem tailTrace_4054726 : CollatzResearch.WordTrace tailWord_4054726 prefixEnd_4054726 2082023360282408099577661 := by
  unfold tailWord_4054726
  simp only [CollatzResearch.WordTrace]
  refine ⟨4621500209638364653556251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 98592004472285112609200021 4621500209638364653556251)
  ·
    refine ⟨6932250314457546980334377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4621500209638364653556251 6932250314457546980334377)
    ·
      refine ⟨5199187735843160235250783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6932250314457546980334377 5199187735843160235250783)
      ·
        refine ⟨7798781603764740352876175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5199187735843160235250783 7798781603764740352876175)
        ·
          refine ⟨11698172405647110529314263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7798781603764740352876175 11698172405647110529314263)
          ·
            refine ⟨17547258608470665793971395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11698172405647110529314263 17547258608470665793971395)
            ·
              refine ⟨26320887912705998690957093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17547258608470665793971395 26320887912705998690957093)
              ·
                refine ⟨4935166483632374754554455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26320887912705998690957093 4935166483632374754554455)
                ·
                  refine ⟨7402749725448562131831683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4935166483632374754554455 7402749725448562131831683)
                  ·
                    refine ⟨11104124588172843197747525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7402749725448562131831683 11104124588172843197747525)
                    ·
                      refine ⟨2082023360282408099577661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11104124588172843197747525 2082023360282408099577661)
                      ·
                        rfl

theorem cell23_4054726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_4054726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4054726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4054726 prefixEnd_4054726 := by exact prefixLift 4054726
  have htrace : WordTrace (prefixWord ++ tailWord_4054726) baseStart_4054726 baseEnd_4054726 := by
    simpa [prefixWord, tailWord_4054726, baseEnd_4054726] using wordTrace_append hprefix tailTrace_4054726
  have hstable : (prefixWord ++ tailWord_4054726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4054726).length < 2 ^ (prefixWord ++ tailWord_4054726).sum := by decide
  have hdescent : baseEnd_4054726 < baseStart_4054726 := by decide
  rcases family_descends (prefixWord ++ tailWord_4054726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4054735 : List Nat := [1, 1, 2, 1, 1, 3, 1, 2, 2, 7, 2]
def baseStart_4054735 : Nat := 118140960795 + 4054735 * 2 ^ 59
def prefixEnd_4054735 : Nat := 4983230072969 + 3 ^ 40 * 4054735 * 2
def baseEnd_4054735 : Nat := 2082027981608298564365119

theorem tailTrace_4054735 : CollatzResearch.WordTrace tailWord_4054735 prefixEnd_4054735 2082027981608298564365119 := by
  unfold tailWord_4054735
  simp only [CollatzResearch.WordTrace]
  refine ⟨147888334965395063450877659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98592223310263375633918439 147888334965395063450877659)
  ·
    refine ⟨221832502448092595176316489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147888334965395063450877659 221832502448092595176316489)
    ·
      refine ⟨166374376836069446382237367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221832502448092595176316489 166374376836069446382237367)
      ·
        refine ⟨249561565254104169573356051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166374376836069446382237367 249561565254104169573356051)
        ·
          refine ⟨374342347881156254360034077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249561565254104169573356051 374342347881156254360034077)
          ·
            refine ⟨140378380455433595385012779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 374342347881156254360034077 140378380455433595385012779)
            ·
              refine ⟨210567570683150393077519169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140378380455433595385012779 210567570683150393077519169)
              ·
                refine ⟨157925678012362794808139377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 210567570683150393077519169 157925678012362794808139377)
                ·
                  refine ⟨118444258509272096106104533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 157925678012362794808139377 118444258509272096106104533)
                  ·
                    refine ⟨2776037308811064752486825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 118444258509272096106104533 2776037308811064752486825)
                    ·
                      refine ⟨2082027981608298564365119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2776037308811064752486825 2082027981608298564365119)
                      ·
                        rfl

theorem cell23_4054735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 7, 2].length) (baseStart_4054735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4054735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4054735 prefixEnd_4054735 := by exact prefixLift 4054735
  have htrace : WordTrace (prefixWord ++ tailWord_4054735) baseStart_4054735 baseEnd_4054735 := by
    simpa [prefixWord, tailWord_4054735, baseEnd_4054735] using wordTrace_append hprefix tailTrace_4054735
  have hstable : (prefixWord ++ tailWord_4054735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4054735).length < 2 ^ (prefixWord ++ tailWord_4054735).sum := by decide
  have hdescent : baseEnd_4054735 < baseStart_4054735 := by decide
  rcases family_descends (prefixWord ++ tailWord_4054735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4054749 : List Nat := [1, 4, 3, 3, 2, 1, 9]
def baseStart_4054749 : Nat := 118140960795 + 4054749 * 2 ^ 59
def prefixEnd_4054749 : Nat := 4983230072969 + 3 ^ 40 * 4054749 * 2
def baseEnd_4054749 : Nat := 25704137905400759377655

theorem tailTrace_4054749 : CollatzResearch.WordTrace tailWord_4054749 prefixEnd_4054749 25704137905400759377655 := by
  unfold tailWord_4054749
  simp only [CollatzResearch.WordTrace]
  refine ⟨147888845587344343841887301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98592563724896229227924867 147888845587344343841887301)
  ·
    refine ⟨27729158547627064470353869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147888845587344343841887301 27729158547627064470353869)
    ·
      refine ⟨10398434455360149176382701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27729158547627064470353869 10398434455360149176382701)
      ·
        refine ⟨3899412920760055941143513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10398434455360149176382701 3899412920760055941143513)
        ·
          refine ⟨2924559690570041955857635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3899412920760055941143513 2924559690570041955857635)
          ·
            refine ⟨4386839535855062933786453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2924559690570041955857635 4386839535855062933786453)
            ·
              refine ⟨25704137905400759377655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4386839535855062933786453 25704137905400759377655)
              ·
                rfl

theorem cell23_4054749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 9].length) (baseStart_4054749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4054749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4054749 prefixEnd_4054749 := by exact prefixLift 4054749
  have htrace : WordTrace (prefixWord ++ tailWord_4054749) baseStart_4054749 baseEnd_4054749 := by
    simpa [prefixWord, tailWord_4054749, baseEnd_4054749] using wordTrace_append hprefix tailTrace_4054749
  have hstable : (prefixWord ++ tailWord_4054749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4054749).length < 2 ^ (prefixWord ++ tailWord_4054749).sum := by decide
  have hdescent : baseEnd_4054749 < baseStart_4054749 := by decide
  rcases family_descends (prefixWord ++ tailWord_4054749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4054785 : List Nat := [1, 2, 4, 1, 1, 1, 3, 2, 2, 1, 5]
def baseStart_4054785 : Nat := 118140960795 + 4054785 * 2 ^ 59
def prefixEnd_4054785 : Nat := 4983230072969 + 3 ^ 40 * 4054785 * 2
def baseEnd_4054785 : Nat := 2082053655641023368739889

theorem tailTrace_4054785 : CollatzResearch.WordTrace tailWord_4054785 prefixEnd_4054785 2082053655641023368739889 := by
  unfold tailWord_4054785
  simp only [CollatzResearch.WordTrace]
  refine ⟨147890158615213921990197809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98593439076809281326798539 147890158615213921990197809)
  ·
    refine ⟨110917618961410441492648357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147890158615213921990197809 110917618961410441492648357)
    ·
      refine ⟨20797053555264457779871567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110917618961410441492648357 20797053555264457779871567)
      ·
        refine ⟨31195580332896686669807351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20797053555264457779871567 31195580332896686669807351)
        ·
          refine ⟨46793370499345030004711027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31195580332896686669807351 46793370499345030004711027)
          ·
            refine ⟨70190055749017545007066541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46793370499345030004711027 70190055749017545007066541)
            ·
              refine ⟨26321270905881579377649953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70190055749017545007066541 26321270905881579377649953)
              ·
                refine ⟨19740953179411184533237465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26321270905881579377649953 19740953179411184533237465)
                ·
                  refine ⟨14805714884558388399928099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19740953179411184533237465 14805714884558388399928099)
                  ·
                    refine ⟨22208572326837582599892149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14805714884558388399928099 22208572326837582599892149)
                    ·
                      refine ⟨2082053655641023368739889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22208572326837582599892149 2082053655641023368739889)
                      ·
                        rfl

theorem cell23_4054785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 2, 2, 1, 5].length) (baseStart_4054785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4054785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4054785 prefixEnd_4054785 := by exact prefixLift 4054785
  have htrace : WordTrace (prefixWord ++ tailWord_4054785) baseStart_4054785 baseEnd_4054785 := by
    simpa [prefixWord, tailWord_4054785, baseEnd_4054785] using wordTrace_append hprefix tailTrace_4054785
  have hstable : (prefixWord ++ tailWord_4054785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4054785).length < 2 ^ (prefixWord ++ tailWord_4054785).sum := by decide
  have hdescent : baseEnd_4054785 < baseStart_4054785 := by decide
  rcases family_descends (prefixWord ++ tailWord_4054785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4054790 : List Nat := [6, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4]
def baseStart_4054790 : Nat := 118140960795 + 4054790 * 2 ^ 59
def prefixEnd_4054790 : Nat := 4983230072969 + 3 ^ 40 * 4054790 * 2
def baseEnd_4054790 : Nat := 2082056223044295849177367

theorem tailTrace_4054790 : CollatzResearch.WordTrace tailWord_4054790 prefixEnd_4054790 2082056223044295849177367 := by
  unfold tailWord_4054790
  simp only [CollatzResearch.WordTrace]
  refine ⟨4621573155631118995129057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 98593560653463871896086549 4621573155631118995129057)
  ·
    refine ⟨3466179866723339246346793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4621573155631118995129057 3466179866723339246346793)
    ·
      refine ⟨2599634900042504434760095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3466179866723339246346793 2599634900042504434760095)
      ·
        refine ⟨3899452350063756652140143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2599634900042504434760095 3899452350063756652140143)
        ·
          refine ⟨5849178525095634978210215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3899452350063756652140143 5849178525095634978210215)
          ·
            refine ⟨8773767787643452467315323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5849178525095634978210215 8773767787643452467315323)
            ·
              refine ⟨13160651681465178700972985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8773767787643452467315323 13160651681465178700972985)
              ·
                refine ⟨9870488761098884025729739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13160651681465178700972985 9870488761098884025729739)
                ·
                  refine ⟨14805733141648326038594609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9870488761098884025729739 14805733141648326038594609)
                  ·
                    refine ⟨11104299856236244528945957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14805733141648326038594609 11104299856236244528945957)
                    ·
                      refine ⟨2082056223044295849177367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11104299856236244528945957 2082056223044295849177367)
                      ·
                        rfl

theorem cell23_4054790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_4054790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4054790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4054790 prefixEnd_4054790 := by exact prefixLift 4054790
  have htrace : WordTrace (prefixWord ++ tailWord_4054790) baseStart_4054790 baseEnd_4054790 := by
    simpa [prefixWord, tailWord_4054790, baseEnd_4054790] using wordTrace_append hprefix tailTrace_4054790
  have hstable : (prefixWord ++ tailWord_4054790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4054790).length < 2 ^ (prefixWord ++ tailWord_4054790).sum := by decide
  have hdescent : baseEnd_4054790 < baseStart_4054790 := by decide
  rcases family_descends (prefixWord ++ tailWord_4054790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4054797 : List Nat := [1, 7, 2, 1, 1, 1, 3, 1, 1, 2, 3]
def baseStart_4054797 : Nat := 118140960795 + 4054797 * 2 ^ 59
def prefixEnd_4054797 : Nat := 4983230072969 + 3 ^ 40 * 4054797 * 2
def baseEnd_4054797 : Nat := 2082059817408877321789835

theorem tailTrace_4054797 : CollatzResearch.WordTrace tailWord_4054797 prefixEnd_4054797 2082059817408877321789835 := by
  unfold tailWord_4054797
  simp only [CollatzResearch.WordTrace]
  refine ⟨147890596291170448039634645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98593730860780298693089763 147890596291170448039634645)
  ·
    refine ⟨3466185850574307375928937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 147890596291170448039634645 3466185850574307375928937)
    ·
      refine ⟨2599639387930730531946703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3466185850574307375928937 2599639387930730531946703)
      ·
        refine ⟨3899459081896095797920055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2599639387930730531946703 3899459081896095797920055)
        ·
          refine ⟨5849188622844143696880083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3899459081896095797920055 5849188622844143696880083)
          ·
            refine ⟨8773782934266215545320125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5849188622844143696880083 8773782934266215545320125)
            ·
              refine ⟨3290168600349830829495047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8773782934266215545320125 3290168600349830829495047)
              ·
                refine ⟨4935252900524746244242571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3290168600349830829495047 4935252900524746244242571)
                ·
                  refine ⟨7402879350787119366363857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4935252900524746244242571 7402879350787119366363857)
                  ·
                    refine ⟨5552159513090339524772893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7402879350787119366363857 5552159513090339524772893)
                    ·
                      refine ⟨2082059817408877321789835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5552159513090339524772893 2082059817408877321789835)
                      ·
                        rfl

theorem cell23_4054797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_4054797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4054797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4054797 prefixEnd_4054797 := by exact prefixLift 4054797
  have htrace : WordTrace (prefixWord ++ tailWord_4054797) baseStart_4054797 baseEnd_4054797 := by
    simpa [prefixWord, tailWord_4054797, baseEnd_4054797] using wordTrace_append hprefix tailTrace_4054797
  have hstable : (prefixWord ++ tailWord_4054797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4054797).length < 2 ^ (prefixWord ++ tailWord_4054797).sum := by decide
  have hdescent : baseEnd_4054797 < baseStart_4054797 := by decide
  rcases family_descends (prefixWord ++ tailWord_4054797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4054816 : List Nat := [2, 1, 1, 5, 1, 1, 4, 2, 2, 2, 2]
def baseStart_4054816 : Nat := 118140960795 + 4054816 * 2 ^ 59
def prefixEnd_4054816 : Nat := 4983230072969 + 3 ^ 40 * 4054816 * 2
def baseEnd_4054816 : Nat := 2082069573541312747452247

theorem tailTrace_4054816 : CollatzResearch.WordTrace tailWord_4054816 prefixEnd_4054816 2082069573541312747452247 := by
  unfold tailWord_4054816
  simp only [CollatzResearch.WordTrace]
  refine ⟨73945644639050807142288151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98594192852067742856384201 73945644639050807142288151)
  ·
    refine ⟨110918466958576210713432227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73945644639050807142288151 110918466958576210713432227)
    ·
      refine ⟨166377700437864316070148341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110918466958576210713432227 166377700437864316070148341)
      ·
        refine ⟨15597909416049779631576407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 166377700437864316070148341 15597909416049779631576407)
        ·
          refine ⟨23396864124074669447364611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15597909416049779631576407 23396864124074669447364611)
          ·
            refine ⟨35095296186112004171046917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23396864124074669447364611 35095296186112004171046917)
            ·
              refine ⟨6580368034896000782071297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35095296186112004171046917 6580368034896000782071297)
              ·
                refine ⟨4935276026172000586553473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6580368034896000782071297 4935276026172000586553473)
                ·
                  refine ⟨3701457019629000439915105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4935276026172000586553473 3701457019629000439915105)
                  ·
                    refine ⟨2776092764721750329936329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3701457019629000439915105 2776092764721750329936329)
                    ·
                      refine ⟨2082069573541312747452247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2776092764721750329936329 2082069573541312747452247)
                      ·
                        rfl

theorem cell23_4054816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4, 2, 2, 2, 2].length) (baseStart_4054816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4054816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4054816 prefixEnd_4054816 := by exact prefixLift 4054816
  have htrace : WordTrace (prefixWord ++ tailWord_4054816) baseStart_4054816 baseEnd_4054816 := by
    simpa [prefixWord, tailWord_4054816, baseEnd_4054816] using wordTrace_append hprefix tailTrace_4054816
  have hstable : (prefixWord ++ tailWord_4054816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4054816).length < 2 ^ (prefixWord ++ tailWord_4054816).sum := by decide
  have hdescent : baseEnd_4054816 < baseStart_4054816 := by decide
  rcases family_descends (prefixWord ++ tailWord_4054816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4054885 : List Nat := [1, 3, 1, 3, 1, 1, 1, 1, 4, 1, 6]
def baseStart_4054885 : Nat := 118140960795 + 4054885 * 2 ^ 59
def prefixEnd_4054885 : Nat := 4983230072969 + 3 ^ 40 * 4054885 * 2
def baseEnd_4054885 : Nat := 2082105003706472977489429

theorem tailTrace_4054885 : CollatzResearch.WordTrace tailWord_4054885 prefixEnd_4054885 2082105003706472977489429 := by
  unfold tailWord_4054885
  simp only [CollatzResearch.WordTrace]
  refine ⟨147893805914851639068838109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98595870609901092712558739 147893805914851639068838109)
  ·
    refine ⟨55460177218069364650814291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147893805914851639068838109 55460177218069364650814291)
    ·
      refine ⟨83190265827104046976221437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55460177218069364650814291 83190265827104046976221437)
      ·
        refine ⟨31196349685164017616083039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83190265827104046976221437 31196349685164017616083039)
        ·
          refine ⟨46794524527746026424124559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31196349685164017616083039 46794524527746026424124559)
          ·
            refine ⟨70191786791619039636186839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46794524527746026424124559 70191786791619039636186839)
            ·
              refine ⟨105287680187428559454280259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70191786791619039636186839 105287680187428559454280259)
              ·
                refine ⟨157931520281142839181420389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105287680187428559454280259 157931520281142839181420389)
                ·
                  refine ⟨29612160052714282346516323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 157931520281142839181420389 29612160052714282346516323)
                  ·
                    refine ⟨44418240079071423519774485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29612160052714282346516323 44418240079071423519774485)
                    ·
                      refine ⟨2082105003706472977489429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44418240079071423519774485 2082105003706472977489429)
                      ·
                        rfl

theorem cell23_4054885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_4054885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4054885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4054885 prefixEnd_4054885 := by exact prefixLift 4054885
  have htrace : WordTrace (prefixWord ++ tailWord_4054885) baseStart_4054885 baseEnd_4054885 := by
    simpa [prefixWord, tailWord_4054885, baseEnd_4054885] using wordTrace_append hprefix tailTrace_4054885
  have hstable : (prefixWord ++ tailWord_4054885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4054885).length < 2 ^ (prefixWord ++ tailWord_4054885).sum := by decide
  have hdescent : baseEnd_4054885 < baseStart_4054885 := by decide
  rcases family_descends (prefixWord ++ tailWord_4054885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4054892 : List Nat := [2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 3]
def baseStart_4054892 : Nat := 118140960795 + 4054892 * 2 ^ 59
def prefixEnd_4054892 : Nat := 4983230072969 + 3 ^ 40 * 4054892 * 2
def baseEnd_4054892 : Nat := 2082108598071054450101897

theorem tailTrace_4054892 : CollatzResearch.WordTrace tailWord_4054892 prefixEnd_4054892 2082108598071054450101897 := by
  unfold tailWord_4054892
  simp only [CollatzResearch.WordTrace]
  refine ⟨73947030612913139632171465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98596040817217519509561953 73947030612913139632171465)
  ·
    refine ⟨55460272959684854724128599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73947030612913139632171465 55460272959684854724128599)
    ·
      refine ⟨83190409439527282086192899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55460272959684854724128599 83190409439527282086192899)
      ·
        refine ⟨124785614159290923129289349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83190409439527282086192899 124785614159290923129289349)
        ·
          refine ⟨23397302654867048086741753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124785614159290923129289349 23397302654867048086741753)
          ·
            refine ⟨17547976991150286065056315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23397302654867048086741753 17547976991150286065056315)
            ·
              refine ⟨26321965486725429097584473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17547976991150286065056315 26321965486725429097584473)
              ·
                refine ⟨19741474115044071823188355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26321965486725429097584473 19741474115044071823188355)
                ·
                  refine ⟨29612211172566107734782533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19741474115044071823188355 29612211172566107734782533)
                  ·
                    refine ⟨5552289594856145200271725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29612211172566107734782533 5552289594856145200271725)
                    ·
                      refine ⟨2082108598071054450101897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5552289594856145200271725 2082108598071054450101897)
                      ·
                        rfl

theorem cell23_4054892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 3].length) (baseStart_4054892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4054892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4054892 prefixEnd_4054892 := by exact prefixLift 4054892
  have htrace : WordTrace (prefixWord ++ tailWord_4054892) baseStart_4054892 baseEnd_4054892 := by
    simpa [prefixWord, tailWord_4054892, baseEnd_4054892] using wordTrace_append hprefix tailTrace_4054892
  have hstable : (prefixWord ++ tailWord_4054892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4054892).length < 2 ^ (prefixWord ++ tailWord_4054892).sum := by decide
  have hdescent : baseEnd_4054892 < baseStart_4054892 := by decide
  rcases family_descends (prefixWord ++ tailWord_4054892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4054916 : List Nat := [2, 3, 2, 1, 1, 1, 5, 3, 1, 4]
def baseStart_4054916 : Nat := 118140960795 + 4054916 * 2 ^ 59
def prefixEnd_4054916 : Nat := 4983230072969 + 3 ^ 40 * 4054916 * 2
def baseEnd_4054916 : Nat := 694040307202254118733929

theorem tailTrace_4054916 : CollatzResearch.WordTrace tailWord_4054916 prefixEnd_4054916 694040307202254118733929 := by
  unfold tailWord_4054916
  simp only [CollatzResearch.WordTrace]
  refine ⟨73947468288869665681608301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98596624385159554242144401 73947468288869665681608301)
  ·
    refine ⟨27730300608326124630603113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73947468288869665681608301 27730300608326124630603113)
    ·
      refine ⟨20797725456244593472952335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27730300608326124630603113 20797725456244593472952335)
      ·
        refine ⟨31196588184366890209428503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20797725456244593472952335 31196588184366890209428503)
        ·
          refine ⟨46794882276550335314142755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31196588184366890209428503 46794882276550335314142755)
          ·
            refine ⟨70192323414825502971214133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46794882276550335314142755 70192323414825502971214133)
            ·
              refine ⟨6580530320139890903551325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70192323414825502971214133 6580530320139890903551325)
              ·
                refine ⟨2467698870052459088831747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6580530320139890903551325 2467698870052459088831747)
                ·
                  refine ⟨3701548305078688633247621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2467698870052459088831747 3701548305078688633247621)
                  ·
                    refine ⟨694040307202254118733929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3701548305078688633247621 694040307202254118733929)
                    ·
                      rfl

theorem cell23_4054916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5, 3, 1, 4].length) (baseStart_4054916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4054916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4054916 prefixEnd_4054916 := by exact prefixLift 4054916
  have htrace : WordTrace (prefixWord ++ tailWord_4054916) baseStart_4054916 baseEnd_4054916 := by
    simpa [prefixWord, tailWord_4054916, baseEnd_4054916] using wordTrace_append hprefix tailTrace_4054916
  have hstable : (prefixWord ++ tailWord_4054916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4054916).length < 2 ^ (prefixWord ++ tailWord_4054916).sum := by decide
  have hdescent : baseEnd_4054916 < baseStart_4054916 := by decide
  rcases family_descends (prefixWord ++ tailWord_4054916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4055030 : List Nat := [5, 1, 1, 1, 4, 2, 2, 1, 1, 1, 4]
def baseStart_4055030 : Nat := 118140960795 + 4055030 * 2 ^ 59
def prefixEnd_4055030 : Nat := 4983230072969 + 3 ^ 40 * 4055030 * 2
def baseEnd_4055030 : Nat := 2082179458401374910176263

theorem tailTrace_4055030 : CollatzResearch.WordTrace tailWord_4055030 prefixEnd_4055030 2082179458401374910176263 := by
  unfold tailWord_4055030
  simp only [CollatzResearch.WordTrace]
  refine ⟨9243693406207895552054159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 98599396332884219221911029 9243693406207895552054159)
  ·
    refine ⟨13865540109311843328081239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9243693406207895552054159 13865540109311843328081239)
    ·
      refine ⟨20798310163967764992121859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13865540109311843328081239 20798310163967764992121859)
      ·
        refine ⟨31197465245951647488182789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20798310163967764992121859 31197465245951647488182789)
        ·
          refine ⟨5849524733615933904034273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31197465245951647488182789 5849524733615933904034273)
          ·
            refine ⟨4387143550211950428025705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5849524733615933904034273 4387143550211950428025705)
            ·
              refine ⟨3290357662658962821019279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4387143550211950428025705 3290357662658962821019279)
              ·
                refine ⟨4935536493988444231528919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3290357662658962821019279 4935536493988444231528919)
                ·
                  refine ⟨7403304740982666347293379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4935536493988444231528919 7403304740982666347293379)
                  ·
                    refine ⟨11104957111473999520940069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7403304740982666347293379 11104957111473999520940069)
                    ·
                      refine ⟨2082179458401374910176263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11104957111473999520940069 2082179458401374910176263)
                      ·
                        rfl

theorem cell23_4055030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 2, 1, 1, 1, 4].length) (baseStart_4055030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4055030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4055030 prefixEnd_4055030 := by exact prefixLift 4055030
  have htrace : WordTrace (prefixWord ++ tailWord_4055030) baseStart_4055030 baseEnd_4055030 := by
    simpa [prefixWord, tailWord_4055030, baseEnd_4055030] using wordTrace_append hprefix tailTrace_4055030
  have hstable : (prefixWord ++ tailWord_4055030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4055030).length < 2 ^ (prefixWord ++ tailWord_4055030).sum := by decide
  have hdescent : baseEnd_4055030 < baseStart_4055030 := by decide
  rcases family_descends (prefixWord ++ tailWord_4055030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4055033 : List Nat := [1, 2, 1, 3, 1, 6, 2, 1, 1, 2, 3]
def baseStart_4055033 : Nat := 118140960795 + 4055033 * 2 ^ 59
def prefixEnd_4055033 : Nat := 4983230072969 + 3 ^ 40 * 4055033 * 2
def baseEnd_4055033 : Nat := 2082180998843338398438749

theorem tailTrace_4055033 : CollatzResearch.WordTrace tailWord_4055033 prefixEnd_4055033 2082180998843338398438749 := by
  unfold tailWord_4055033
  simp only [CollatzResearch.WordTrace]
  refine ⟨147899203918315460345225753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98599469278876973563483835 147899203918315460345225753)
  ·
    refine ⟨110924402938736595258919315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147899203918315460345225753 110924402938736595258919315)
    ·
      refine ⟨166386604408104892888378973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110924402938736595258919315 166386604408104892888378973)
      ·
        refine ⟨62394976653039334833142115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166386604408104892888378973 62394976653039334833142115)
        ·
          refine ⟨93592464979559002249713173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62394976653039334833142115 93592464979559002249713173)
          ·
            refine ⟨4387146795916828230455305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 93592464979559002249713173 4387146795916828230455305)
            ·
              refine ⟨3290360096937621172841479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4387146795916828230455305 3290360096937621172841479)
              ·
                refine ⟨4935540145406431759262219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3290360096937621172841479 4935540145406431759262219)
                ·
                  refine ⟨7403310218109647638893329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4935540145406431759262219 7403310218109647638893329)
                  ·
                    refine ⟨5552482663582235729169997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7403310218109647638893329 5552482663582235729169997)
                    ·
                      refine ⟨2082180998843338398438749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5552482663582235729169997 2082180998843338398438749)
                      ·
                        rfl

theorem cell23_4055033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 2, 1, 1, 2, 3].length) (baseStart_4055033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4055033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4055033 prefixEnd_4055033 := by exact prefixLift 4055033
  have htrace : WordTrace (prefixWord ++ tailWord_4055033) baseStart_4055033 baseEnd_4055033 := by
    simpa [prefixWord, tailWord_4055033, baseEnd_4055033] using wordTrace_append hprefix tailTrace_4055033
  have hstable : (prefixWord ++ tailWord_4055033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4055033).length < 2 ^ (prefixWord ++ tailWord_4055033).sum := by decide
  have hdescent : baseEnd_4055033 < baseStart_4055033 := by decide
  rcases family_descends (prefixWord ++ tailWord_4055033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4055060 : List Nat := [2, 4, 3, 2, 1, 2, 1, 1, 1, 2, 4]
def baseStart_4055060 : Nat := 118140960795 + 4055060 * 2 ^ 59
def prefixEnd_4055060 : Nat := 4983230072969 + 3 ^ 40 * 4055060 * 2
def baseEnd_4055060 : Nat := 2082194862821009792801125

theorem tailTrace_4055060 : CollatzResearch.WordTrace tailWord_4055060 prefixEnd_4055060 2082194862821009792801125 := by
  unfold tailWord_4055060
  simp only [CollatzResearch.WordTrace]
  refine ⟨73950094344608821978229317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98600125792811762637639089 73950094344608821978229317)
  ·
    refine ⟨13865642689614154120917997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73950094344608821978229317 13865642689614154120917997)
    ·
      refine ⟨5199616008605307795344249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13865642689614154120917997 5199616008605307795344249)
      ·
        refine ⟨3899712006453980846508187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5199616008605307795344249 3899712006453980846508187)
        ·
          refine ⟨5849568009680971269762281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3899712006453980846508187 5849568009680971269762281)
          ·
            refine ⟨4387176007260728452321711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5849568009680971269762281 4387176007260728452321711)
            ·
              refine ⟨6580764010891092678482567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4387176007260728452321711 6580764010891092678482567)
              ·
                refine ⟨9871146016336639017723851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6580764010891092678482567 9871146016336639017723851)
                ·
                  refine ⟨14806719024504958526585777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9871146016336639017723851 14806719024504958526585777)
                  ·
                    refine ⟨11105039268378718894939333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14806719024504958526585777 11105039268378718894939333)
                    ·
                      refine ⟨2082194862821009792801125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11105039268378718894939333 2082194862821009792801125)
                      ·
                        rfl

theorem cell23_4055060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_4055060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4055060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4055060 prefixEnd_4055060 := by exact prefixLift 4055060
  have htrace : WordTrace (prefixWord ++ tailWord_4055060) baseStart_4055060 baseEnd_4055060 := by
    simpa [prefixWord, tailWord_4055060, baseEnd_4055060] using wordTrace_append hprefix tailTrace_4055060
  have hstable : (prefixWord ++ tailWord_4055060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4055060).length < 2 ^ (prefixWord ++ tailWord_4055060).sum := by decide
  have hdescent : baseEnd_4055060 < baseStart_4055060 := by decide
  rcases family_descends (prefixWord ++ tailWord_4055060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4055063 : List Nat := [1, 1, 3, 5, 2, 2, 1, 1, 1, 3, 3]
def baseStart_4055063 : Nat := 118140960795 + 4055063 * 2 ^ 59
def prefixEnd_4055063 : Nat := 4983230072969 + 3 ^ 40 * 4055063 * 2
def baseEnd_4055063 : Nat := 2082196403262973281063611

theorem tailTrace_4055063 : CollatzResearch.WordTrace tailWord_4055063 prefixEnd_4055063 2082196403262973281063611 := by
  unfold tailWord_4055063
  simp only [CollatzResearch.WordTrace]
  refine ⟨147900298108206775468817843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98600198738804516979211895 147900298108206775468817843)
  ·
    refine ⟨221850447162310163203226765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147900298108206775468817843 221850447162310163203226765)
    ·
      refine ⟨83193917685866311201210037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221850447162310163203226765 83193917685866311201210037)
      ·
        refine ⟨7799429783049966675113441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 83193917685866311201210037 7799429783049966675113441)
        ·
          refine ⟨5849572337287475006335081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7799429783049966675113441 5849572337287475006335081)
          ·
            refine ⟨4387179252965606254751311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5849572337287475006335081 4387179252965606254751311)
            ·
              refine ⟨6580768879448409382126967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4387179252965606254751311 6580768879448409382126967)
              ·
                refine ⟨9871153319172614073190451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6580768879448409382126967 9871153319172614073190451)
                ·
                  refine ⟨14806729978758921109785677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9871153319172614073190451 14806729978758921109785677)
                  ·
                    refine ⟨5552523742034595416169629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14806729978758921109785677 5552523742034595416169629)
                    ·
                      refine ⟨2082196403262973281063611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5552523742034595416169629 2082196403262973281063611)
                      ·
                        rfl

theorem cell23_4055063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_4055063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4055063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4055063 prefixEnd_4055063 := by exact prefixLift 4055063
  have htrace : WordTrace (prefixWord ++ tailWord_4055063) baseStart_4055063 baseEnd_4055063 := by
    simpa [prefixWord, tailWord_4055063, baseEnd_4055063] using wordTrace_append hprefix tailTrace_4055063
  have hstable : (prefixWord ++ tailWord_4055063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4055063).length < 2 ^ (prefixWord ++ tailWord_4055063).sum := by decide
  have hdescent : baseEnd_4055063 < baseStart_4055063 := by decide
  rcases family_descends (prefixWord ++ tailWord_4055063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4055089 : List Nat := [1, 2, 2, 3, 1, 4, 1, 1, 2, 1, 5]
def baseStart_4055089 : Nat := 118140960795 + 4055089 * 2 ^ 59
def prefixEnd_4055089 : Nat := 4983230072969 + 3 ^ 40 * 4055089 * 2
def baseEnd_4055089 : Nat := 2082209753759990179338491

theorem tailTrace_4055089 : CollatzResearch.WordTrace tailWord_4055089 prefixEnd_4055089 2082209753759990179338491 := by
  unfold tailWord_4055089
  simp only [CollatzResearch.WordTrace]
  refine ⟨147901246406112581909264321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98600830937408387939509547 147901246406112581909264321)
  ·
    refine ⟨110925934804584436431948241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147901246406112581909264321 110925934804584436431948241)
    ·
      refine ⟨83194451103438327323961181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110925934804584436431948241 83194451103438327323961181)
      ·
        refine ⟨31197919163789372746485443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83194451103438327323961181 31197919163789372746485443)
        ·
          refine ⟨46796878745684059119728165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31197919163789372746485443 46796878745684059119728165)
          ·
            refine ⟨8774414764815761084949031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46796878745684059119728165 8774414764815761084949031)
            ·
              refine ⟨13161622147223641627423547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8774414764815761084949031 13161622147223641627423547)
              ·
                refine ⟨19742433220835462441135321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13161622147223641627423547 19742433220835462441135321)
                ·
                  refine ⟨14806824915626596830851491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19742433220835462441135321 14806824915626596830851491)
                  ·
                    refine ⟨22210237373439895246277237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14806824915626596830851491 22210237373439895246277237)
                    ·
                      refine ⟨2082209753759990179338491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22210237373439895246277237 2082209753759990179338491)
                      ·
                        rfl

theorem cell23_4055089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 1, 2, 1, 5].length) (baseStart_4055089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4055089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4055089 prefixEnd_4055089 := by exact prefixLift 4055089
  have htrace : WordTrace (prefixWord ++ tailWord_4055089) baseStart_4055089 baseEnd_4055089 := by
    simpa [prefixWord, tailWord_4055089, baseEnd_4055089] using wordTrace_append hprefix tailTrace_4055089
  have hstable : (prefixWord ++ tailWord_4055089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4055089).length < 2 ^ (prefixWord ++ tailWord_4055089).sum := by decide
  have hdescent : baseEnd_4055089 < baseStart_4055089 := by decide
  rcases family_descends (prefixWord ++ tailWord_4055089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4055112 : List Nat := [2, 1, 3, 1, 1, 1, 2, 1, 2, 1, 8]
def baseStart_4055112 : Nat := 118140960795 + 4055112 * 2 ^ 59
def prefixEnd_4055112 : Nat := 4983230072969 + 3 ^ 40 * 4055112 * 2
def baseEnd_4055112 : Nat := 2082221563815043589350885

theorem tailTrace_4055112 : CollatzResearch.WordTrace tailWord_4055112 prefixEnd_4055112 2082221563815043589350885 := by
  unfold tailWord_4055112
  simp only [CollatzResearch.WordTrace]
  refine ⟨73951042642514628418675795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98601390190019504558234393 73951042642514628418675795)
  ·
    refine ⟨110926563963771942628013693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73951042642514628418675795 110926563963771942628013693)
    ·
      refine ⟨41597461486414478485505135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110926563963771942628013693 41597461486414478485505135)
      ·
        refine ⟨62396192229621717728257703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41597461486414478485505135 62396192229621717728257703)
        ·
          refine ⟨93594288344432576592386555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62396192229621717728257703 93594288344432576592386555)
          ·
            refine ⟨140391432516648864888579833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93594288344432576592386555 140391432516648864888579833)
            ·
              refine ⟨105293574387486648666434875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140391432516648864888579833 105293574387486648666434875)
              ·
                refine ⟨157940361581229972999652313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105293574387486648666434875 157940361581229972999652313)
                ·
                  refine ⟨118455271185922479749739235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 157940361581229972999652313 118455271185922479749739235)
                  ·
                    refine ⟨177682906778883719624608853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 118455271185922479749739235 177682906778883719624608853)
                    ·
                      refine ⟨2082221563815043589350885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 177682906778883719624608853 2082221563815043589350885)
                      ·
                        rfl

theorem cell23_4055112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 2, 1, 8].length) (baseStart_4055112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4055112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4055112 prefixEnd_4055112 := by exact prefixLift 4055112
  have htrace : WordTrace (prefixWord ++ tailWord_4055112) baseStart_4055112 baseEnd_4055112 := by
    simpa [prefixWord, tailWord_4055112, baseEnd_4055112] using wordTrace_append hprefix tailTrace_4055112
  have hstable : (prefixWord ++ tailWord_4055112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4055112).length < 2 ^ (prefixWord ++ tailWord_4055112).sum := by decide
  have hdescent : baseEnd_4055112 < baseStart_4055112 := by decide
  rcases family_descends (prefixWord ++ tailWord_4055112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4055139 : List Nat := [1, 1, 1, 5, 1, 1, 3, 3, 2, 5]
def baseStart_4055139 : Nat := 118140960795 + 4055139 * 2 ^ 59
def prefixEnd_4055139 : Nat := 4983230072969 + 3 ^ 40 * 4055139 * 2
def baseEnd_4055139 : Nat := 694078475930904994571087

theorem tailTrace_4055139 : CollatzResearch.WordTrace tailWord_4055139 prefixEnd_4055139 694078475930904994571087 := by
  unfold tailWord_4055139
  simp only [CollatzResearch.WordTrace]
  refine ⟨147903070055931440448584471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98602046703954293632389647 147903070055931440448584471)
  ·
    refine ⟨221854605083897160672876707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147903070055931440448584471 221854605083897160672876707)
    ·
      refine ⟨332781907625845741009315061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221854605083897160672876707 332781907625845741009315061)
      ·
        refine ⟨31198303839923038219623287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 332781907625845741009315061 31198303839923038219623287)
        ·
          refine ⟨46797455759884557329434931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31198303839923038219623287 46797455759884557329434931)
          ·
            refine ⟨70196183639826835994152397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46797455759884557329434931 70196183639826835994152397)
            ·
              refine ⟨26323568864935063497807149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70196183639826835994152397 26323568864935063497807149)
              ·
                refine ⟨9871338324350648811677681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26323568864935063497807149 9871338324350648811677681)
                ·
                  refine ⟨7403503743262986608758261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9871338324350648811677681 7403503743262986608758261)
                  ·
                    refine ⟨694078475930904994571087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7403503743262986608758261 694078475930904994571087)
                    ·
                      rfl

theorem cell23_4055139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 3, 2, 5].length) (baseStart_4055139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4055139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4055139 prefixEnd_4055139 := by exact prefixLift 4055139
  have htrace : WordTrace (prefixWord ++ tailWord_4055139) baseStart_4055139 baseEnd_4055139 := by
    simpa [prefixWord, tailWord_4055139, baseEnd_4055139] using wordTrace_append hprefix tailTrace_4055139
  have hstable : (prefixWord ++ tailWord_4055139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4055139).length < 2 ^ (prefixWord ++ tailWord_4055139).sum := by decide
  have hdescent : baseEnd_4055139 < baseStart_4055139 := by decide
  rcases family_descends (prefixWord ++ tailWord_4055139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4055149 : List Nat := [1, 5, 1, 1, 2, 1, 1, 1, 3, 2, 5]
def baseStart_4055149 : Nat := 118140960795 + 4055149 * 2 ^ 59
def prefixEnd_4055149 : Nat := 4983230072969 + 3 ^ 40 * 4055149 * 2
def baseEnd_4055149 : Nat := 2082240562599259944588215

theorem tailTrace_4055149 : CollatzResearch.WordTrace tailWord_4055149 prefixEnd_4055149 2082240562599259944588215 := by
  unfold tailWord_4055149
  simp only [CollatzResearch.WordTrace]
  refine ⟨147903434785895212156448501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98602289857263474770965667 147903434785895212156448501)
  ·
    refine ⟨13865947011177676139667047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 147903434785895212156448501 13865947011177676139667047)
    ·
      refine ⟨20798920516766514209500571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13865947011177676139667047 20798920516766514209500571)
      ·
        refine ⟨31198380775149771314250857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20798920516766514209500571 31198380775149771314250857)
        ·
          refine ⟨23398785581362328485688143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31198380775149771314250857 23398785581362328485688143)
          ·
            refine ⟨35098178372043492728532215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23398785581362328485688143 35098178372043492728532215)
            ·
              refine ⟨52647267558065239092798323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35098178372043492728532215 52647267558065239092798323)
              ·
                refine ⟨78970901337097858639197485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52647267558065239092798323 78970901337097858639197485)
                ·
                  refine ⟨29614088001411696989699057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78970901337097858639197485 29614088001411696989699057)
                  ·
                    refine ⟨22210566001058772742274293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29614088001411696989699057 22210566001058772742274293)
                    ·
                      refine ⟨2082240562599259944588215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22210566001058772742274293 2082240562599259944588215)
                      ·
                        rfl

theorem cell23_4055149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_4055149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4055149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4055149 prefixEnd_4055149 := by exact prefixLift 4055149
  have htrace : WordTrace (prefixWord ++ tailWord_4055149) baseStart_4055149 baseEnd_4055149 := by
    simpa [prefixWord, tailWord_4055149, baseEnd_4055149] using wordTrace_append hprefix tailTrace_4055149
  have hstable : (prefixWord ++ tailWord_4055149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4055149).length < 2 ^ (prefixWord ++ tailWord_4055149).sum := by decide
  have hdescent : baseEnd_4055149 < baseStart_4055149 := by decide
  rcases family_descends (prefixWord ++ tailWord_4055149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4055196 : List Nat := [2, 2, 3, 2, 1, 1, 3, 1, 1, 4, 3]
def baseStart_4055196 : Nat := 118140960795 + 4055196 * 2 ^ 59
def prefixEnd_4055196 : Nat := 4983230072969 + 3 ^ 40 * 4055196 * 2
def baseEnd_4055196 : Nat := 2082264696190021260700499

theorem tailTrace_4055196 : CollatzResearch.WordTrace tailWord_4055196 prefixEnd_4055196 2082264696190021260700499 := by
  unfold tailWord_4055196
  simp only [CollatzResearch.WordTrace]
  refine ⟨73952574508362469591704721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98603432677816626122272961 73952574508362469591704721)
  ·
    refine ⟨55464430881271852193778541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73952574508362469591704721 55464430881271852193778541)
    ·
      refine ⟨20799161580476944572666953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55464430881271852193778541 20799161580476944572666953)
      ·
        refine ⟨15599371185357708429500215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20799161580476944572666953 15599371185357708429500215)
        ·
          refine ⟨23399056778036562644250323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15599371185357708429500215 23399056778036562644250323)
          ·
            refine ⟨35098585167054843966375485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23399056778036562644250323 35098585167054843966375485)
            ·
              refine ⟨13161969437645566487390807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35098585167054843966375485 13161969437645566487390807)
              ·
                refine ⟨19742954156468349731086211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13161969437645566487390807 19742954156468349731086211)
                ·
                  refine ⟨29614431234702524596629317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19742954156468349731086211 29614431234702524596629317)
                  ·
                    refine ⟨5552705856506723361867997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29614431234702524596629317 5552705856506723361867997)
                    ·
                      refine ⟨2082264696190021260700499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5552705856506723361867997 2082264696190021260700499)
                      ·
                        rfl

theorem cell23_4055196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 1, 1, 4, 3].length) (baseStart_4055196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4055196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4055196 prefixEnd_4055196 := by exact prefixLift 4055196
  have htrace : WordTrace (prefixWord ++ tailWord_4055196) baseStart_4055196 baseEnd_4055196 := by
    simpa [prefixWord, tailWord_4055196, baseEnd_4055196] using wordTrace_append hprefix tailTrace_4055196
  have hstable : (prefixWord ++ tailWord_4055196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4055196).length < 2 ^ (prefixWord ++ tailWord_4055196).sum := by decide
  have hdescent : baseEnd_4055196 < baseStart_4055196 := by decide
  rcases family_descends (prefixWord ++ tailWord_4055196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4055254 : List Nat := [5, 2, 1, 2, 1, 3, 1, 3, 1, 4]
def baseStart_4055254 : Nat := 118140960795 + 4055254 * 2 ^ 59
def prefixEnd_4055254 : Nat := 4983230072969 + 3 ^ 40 * 4055254 * 2
def baseEnd_4055254 : Nat := 694098159355994011258411

theorem tailTrace_4055254 : CollatzResearch.WordTrace tailWord_4055254 prefixEnd_4055254 694098159355994011258411 := by
  unfold tailWord_4055254
  simp only [CollatzResearch.WordTrace]
  refine ⟨9244204028157175943063801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 98604842967009876726013877 9244204028157175943063801)
  ·
    refine ⟨6933153021117881957297851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9244204028157175943063801 6933153021117881957297851)
    ·
      refine ⟨10399729531676822935946777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6933153021117881957297851 10399729531676822935946777)
      ·
        refine ⟨7799797148757617201960083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10399729531676822935946777 7799797148757617201960083)
        ·
          refine ⟨11699695723136425802940125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7799797148757617201960083 11699695723136425802940125)
          ·
            refine ⟨4387385896176159676102547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11699695723136425802940125 4387385896176159676102547)
            ·
              refine ⟨6581078844264239514153821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4387385896176159676102547 6581078844264239514153821)
              ·
                refine ⟨2467904566599089817807683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6581078844264239514153821 2467904566599089817807683)
                ·
                  refine ⟨3701856849898634726711525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2467904566599089817807683 3701856849898634726711525)
                  ·
                    refine ⟨694098159355994011258411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3701856849898634726711525 694098159355994011258411)
                    ·
                      rfl

theorem cell23_4055254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 1, 3, 1, 4].length) (baseStart_4055254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4055254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4055254 prefixEnd_4055254 := by exact prefixLift 4055254
  have htrace : WordTrace (prefixWord ++ tailWord_4055254) baseStart_4055254 baseEnd_4055254 := by
    simpa [prefixWord, tailWord_4055254, baseEnd_4055254] using wordTrace_append hprefix tailTrace_4055254
  have hstable : (prefixWord ++ tailWord_4055254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4055254).length < 2 ^ (prefixWord ++ tailWord_4055254).sum := by decide
  have hdescent : baseEnd_4055254 < baseStart_4055254 := by decide
  rcases family_descends (prefixWord ++ tailWord_4055254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4055276 : List Nat := [2, 2, 1, 1, 2, 3, 1, 3, 4, 4]
def baseStart_4055276 : Nat := 118140960795 + 4055276 * 2 ^ 59
def prefixEnd_4055276 : Nat := 4983230072969 + 3 ^ 40 * 4055276 * 2
def baseEnd_4055276 : Nat := 694101924880793649233377

theorem tailTrace_4055276 : CollatzResearch.WordTrace tailWord_4055276 prefixEnd_4055276 694101924880793649233377 := by
  unfold tailWord_4055276
  simp only [CollatzResearch.WordTrace]
  refine ⟨73954033428217556423160841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98605377904290075230881121 73954033428217556423160841)
  ·
    refine ⟨55465525071163167317370631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73954033428217556423160841 55465525071163167317370631)
    ·
      refine ⟨83198287606744750976055947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55465525071163167317370631 83198287606744750976055947)
      ·
        refine ⟨124797431410117126464083921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83198287606744750976055947 124797431410117126464083921)
        ·
          refine ⟨93598073557587844848062941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124797431410117126464083921 93598073557587844848062941)
          ·
            refine ⟨35099277584095441818023603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93598073557587844848062941 35099277584095441818023603)
            ·
              refine ⟨52648916376143162727035405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35099277584095441818023603 52648916376143162727035405)
              ·
                refine ⟨19743343641053686022638277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52648916376143162727035405 19743343641053686022638277)
                ·
                  refine ⟨3701876932697566129244677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19743343641053686022638277 3701876932697566129244677)
                  ·
                    refine ⟨694101924880793649233377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3701876932697566129244677 694101924880793649233377)
                    ·
                      rfl

theorem cell23_4055276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 4].length) (baseStart_4055276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4055276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4055276 prefixEnd_4055276 := by exact prefixLift 4055276
  have htrace : WordTrace (prefixWord ++ tailWord_4055276) baseStart_4055276 baseEnd_4055276 := by
    simpa [prefixWord, tailWord_4055276, baseEnd_4055276] using wordTrace_append hprefix tailTrace_4055276
  have hstable : (prefixWord ++ tailWord_4055276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4055276).length < 2 ^ (prefixWord ++ tailWord_4055276).sum := by decide
  have hdescent : baseEnd_4055276 < baseStart_4055276 := by decide
  rcases family_descends (prefixWord ++ tailWord_4055276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4055277 : List Nat := [1, 5, 1, 2, 3, 2, 1, 1, 3, 1, 3]
def baseStart_4055277 : Nat := 118140960795 + 4055277 * 2 ^ 59
def prefixEnd_4055277 : Nat := 4983230072969 + 3 ^ 40 * 4055277 * 2
def baseEnd_4055277 : Nat := 2082306288123035443787627

theorem tailTrace_4055277 : CollatzResearch.WordTrace tailWord_4055277 prefixEnd_4055277 2082306288123035443787627 := by
  unfold tailWord_4055277
  simp only [CollatzResearch.WordTrace]
  refine ⟨147908103329431490017108085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98605402219620993344738723 147908103329431490017108085)
  ·
    refine ⟨13866384687134202189103883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 147908103329431490017108085 13866384687134202189103883)
    ·
      refine ⟨20799577030701303283655825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13866384687134202189103883 20799577030701303283655825)
      ·
        refine ⟨15599682773025977462741869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20799577030701303283655825 15599682773025977462741869)
        ·
          refine ⟨5849881039884741548528201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15599682773025977462741869 5849881039884741548528201)
          ·
            refine ⟨4387410779913556161396151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5849881039884741548528201 4387410779913556161396151)
            ·
              refine ⟨6581116169870334242094227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4387410779913556161396151 6581116169870334242094227)
              ·
                refine ⟨9871674254805501363141341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6581116169870334242094227 9871674254805501363141341)
                ·
                  refine ⟨3701877845552063011178003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9871674254805501363141341 3701877845552063011178003)
                  ·
                    refine ⟨5552816768328094516767005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3701877845552063011178003 5552816768328094516767005)
                    ·
                      refine ⟨2082306288123035443787627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5552816768328094516767005 2082306288123035443787627)
                      ·
                        rfl

theorem cell23_4055277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 1, 1, 3, 1, 3].length) (baseStart_4055277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4055277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4055277 prefixEnd_4055277 := by exact prefixLift 4055277
  have htrace : WordTrace (prefixWord ++ tailWord_4055277) baseStart_4055277 baseEnd_4055277 := by
    simpa [prefixWord, tailWord_4055277, baseEnd_4055277] using wordTrace_append hprefix tailTrace_4055277
  have hstable : (prefixWord ++ tailWord_4055277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4055277).length < 2 ^ (prefixWord ++ tailWord_4055277).sum := by decide
  have hdescent : baseEnd_4055277 < baseStart_4055277 := by decide
  rcases family_descends (prefixWord ++ tailWord_4055277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4055320 : List Nat := [2, 1, 2, 3, 1, 2, 5, 1, 1, 2, 3]
def baseStart_4055320 : Nat := 118140960795 + 4055320 * 2 ^ 59
def prefixEnd_4055320 : Nat := 4983230072969 + 3 ^ 40 * 4055320 * 2
def baseEnd_4055320 : Nat := 2082328367791178775549929

theorem tailTrace_4055320 : CollatzResearch.WordTrace tailWord_4055320 prefixEnd_4055320 2082328367791178775549929 := by
  unfold tailWord_4055320
  simp only [CollatzResearch.WordTrace]
  refine ⟨73954835834137854180461707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98606447778850472240615609 73954835834137854180461707)
  ·
    refine ⟨110932253751206781270692561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73954835834137854180461707 110932253751206781270692561)
    ·
      refine ⟨83199190313405085953019421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110932253751206781270692561 83199190313405085953019421)
      ·
        refine ⟨31199696367526907232382283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83199190313405085953019421 31199696367526907232382283)
        ·
          refine ⟨46799544551290360848573425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31199696367526907232382283 46799544551290360848573425)
          ·
            refine ⟨35099658413467770636430069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46799544551290360848573425 35099658413467770636430069)
            ·
              refine ⟨3290592976262603497165319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35099658413467770636430069 3290592976262603497165319)
              ·
                refine ⟨4935889464393905245747979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3290592976262603497165319 4935889464393905245747979)
                ·
                  refine ⟨7403834196590857868621969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4935889464393905245747979 7403834196590857868621969)
                  ·
                    refine ⟨5552875647443143401466477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7403834196590857868621969 5552875647443143401466477)
                    ·
                      refine ⟨2082328367791178775549929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5552875647443143401466477 2082328367791178775549929)
                      ·
                        rfl

theorem cell23_4055320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 5, 1, 1, 2, 3].length) (baseStart_4055320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4055320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4055320 prefixEnd_4055320 := by exact prefixLift 4055320
  have htrace : WordTrace (prefixWord ++ tailWord_4055320) baseStart_4055320 baseEnd_4055320 := by
    simpa [prefixWord, tailWord_4055320, baseEnd_4055320] using wordTrace_append hprefix tailTrace_4055320
  have hstable : (prefixWord ++ tailWord_4055320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4055320).length < 2 ^ (prefixWord ++ tailWord_4055320).sum := by decide
  have hdescent : baseEnd_4055320 < baseStart_4055320 := by decide
  rcases family_descends (prefixWord ++ tailWord_4055320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4055343 : List Nat := [1, 1, 2, 1, 2, 1, 5, 2, 3, 3, 2]
def baseStart_4055343 : Nat := 118140960795 + 4055343 * 2 ^ 59
def prefixEnd_4055343 : Nat := 4983230072969 + 3 ^ 40 * 4055343 * 2
def baseEnd_4055343 : Nat := 2082340177846232185562323

theorem tailTrace_4055343 : CollatzResearch.WordTrace tailWord_4055343 prefixEnd_4055343 2082340177846232185562323 := by
  unfold tailWord_4055343
  simp only [CollatzResearch.WordTrace]
  refine ⟨147910510547192383289010683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98607007031461588859340455 147910510547192383289010683)
  ·
    refine ⟨221865765820788574933516025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147910510547192383289010683 221865765820788574933516025)
    ·
      refine ⟨166399324365591431200137019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221865765820788574933516025 166399324365591431200137019)
      ·
        refine ⟨249598986548387146800205529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166399324365591431200137019 249598986548387146800205529)
        ·
          refine ⟨187199239911290360100154147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 249598986548387146800205529 187199239911290360100154147)
          ·
            refine ⟨280798859866935540150231221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187199239911290360100154147 280798859866935540150231221)
            ·
              refine ⟨26324893112525206889084177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 280798859866935540150231221 26324893112525206889084177)
              ·
                refine ⟨19743669834393905166813133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26324893112525206889084177 19743669834393905166813133)
                ·
                  refine ⟨7403876187897714437554925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19743669834393905166813133 7403876187897714437554925)
                  ·
                    refine ⟨2776453570461642914083097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7403876187897714437554925 2776453570461642914083097)
                    ·
                      refine ⟨2082340177846232185562323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2776453570461642914083097 2082340177846232185562323)
                      ·
                        rfl

theorem cell23_4055343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 2, 3, 3, 2].length) (baseStart_4055343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4055343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4055343 prefixEnd_4055343 := by exact prefixLift 4055343
  have htrace : WordTrace (prefixWord ++ tailWord_4055343) baseStart_4055343 baseEnd_4055343 := by
    simpa [prefixWord, tailWord_4055343, baseEnd_4055343] using wordTrace_append hprefix tailTrace_4055343
  have hstable : (prefixWord ++ tailWord_4055343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4055343).length < 2 ^ (prefixWord ++ tailWord_4055343).sum := by decide
  have hdescent : baseEnd_4055343 < baseStart_4055343 := by decide
  rcases family_descends (prefixWord ++ tailWord_4055343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4055356 : List Nat := [2, 2, 2, 2, 1, 2, 1, 2, 2, 3, 4]
def baseStart_4055356 : Nat := 118140960795 + 4055356 * 2 ^ 59
def prefixEnd_4055356 : Nat := 4983230072969 + 3 ^ 40 * 4055356 * 2
def baseEnd_4055356 : Nat := 2082346853094740634699763

theorem tailTrace_4055356 : CollatzResearch.WordTrace tailWord_4055356 prefixEnd_4055356 2082346853094740634699763 := by
  unfold tailWord_4055356
  simp only [CollatzResearch.WordTrace]
  refine ⟨73955492348072643254616961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98607323130763524339489281 73955492348072643254616961)
  ·
    refine ⟨55466619261054482440962721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73955492348072643254616961 55466619261054482440962721)
    ·
      refine ⟨41599964445790861830722041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55466619261054482440962721 41599964445790861830722041)
      ·
        refine ⟨31199973334343146373041531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41599964445790861830722041 31199973334343146373041531)
        ·
          refine ⟨46799960001514719559562297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31199973334343146373041531 46799960001514719559562297)
          ·
            refine ⟨35099970001136039669671723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46799960001514719559562297 35099970001136039669671723)
            ·
              refine ⟨52649955001704059504507585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35099970001136039669671723 52649955001704059504507585)
              ·
                refine ⟨39487466251278044628380689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52649955001704059504507585 39487466251278044628380689)
                ·
                  refine ⟨29615599688458533471285517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39487466251278044628380689 29615599688458533471285517)
                  ·
                    refine ⟨11105849883171950051732069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29615599688458533471285517 11105849883171950051732069)
                    ·
                      refine ⟨2082346853094740634699763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11105849883171950051732069 2082346853094740634699763)
                      ·
                        rfl

theorem cell23_4055356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 2, 2, 3, 4].length) (baseStart_4055356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4055356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4055356 prefixEnd_4055356 := by exact prefixLift 4055356
  have htrace : WordTrace (prefixWord ++ tailWord_4055356) baseStart_4055356 baseEnd_4055356 := by
    simpa [prefixWord, tailWord_4055356, baseEnd_4055356] using wordTrace_append hprefix tailTrace_4055356
  have hstable : (prefixWord ++ tailWord_4055356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4055356).length < 2 ^ (prefixWord ++ tailWord_4055356).sum := by decide
  have hdescent : baseEnd_4055356 < baseStart_4055356 := by decide
  rcases family_descends (prefixWord ++ tailWord_4055356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4055377 : List Nat := [1, 2, 2, 1, 4, 2, 4, 1, 1, 3, 2]
def baseStart_4055377 : Nat := 118140960795 + 4055377 * 2 ^ 59
def prefixEnd_4055377 : Nat := 4983230072969 + 3 ^ 40 * 4055377 * 2
def baseEnd_4055377 : Nat := 2082357636188485052537167

theorem tailTrace_4055377 : CollatzResearch.WordTrace tailWord_4055377 prefixEnd_4055377 2082357636188485052537167 := by
  unfold tailWord_4055377
  simp only [CollatzResearch.WordTrace]
  refine ⟨147911750629069207095748385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98607833752712804730498923 147911750629069207095748385)
  ·
    refine ⟨110933812971801905321811289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147911750629069207095748385 110933812971801905321811289)
    ·
      refine ⟨83200359728851428991358467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110933812971801905321811289 83200359728851428991358467)
      ·
        refine ⟨124800539593277143487037701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83200359728851428991358467 124800539593277143487037701)
        ·
          refine ⟨23400101173739464403819569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124800539593277143487037701 23400101173739464403819569)
          ·
            refine ⟨17550075880304598302864677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23400101173739464403819569 17550075880304598302864677)
            ·
              refine ⟨3290639227557112181787127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17550075880304598302864677 3290639227557112181787127)
              ·
                refine ⟨4935958841335668272680691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3290639227557112181787127 4935958841335668272680691)
                ·
                  refine ⟨7403938262003502409021037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4935958841335668272680691 7403938262003502409021037)
                  ·
                    refine ⟨2776476848251313403382889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7403938262003502409021037 2776476848251313403382889)
                    ·
                      refine ⟨2082357636188485052537167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2776476848251313403382889 2082357636188485052537167)
                      ·
                        rfl

theorem cell23_4055377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 4, 1, 1, 3, 2].length) (baseStart_4055377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4055377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4055377 prefixEnd_4055377 := by exact prefixLift 4055377
  have htrace : WordTrace (prefixWord ++ tailWord_4055377) baseStart_4055377 baseEnd_4055377 := by
    simpa [prefixWord, tailWord_4055377, baseEnd_4055377] using wordTrace_append hprefix tailTrace_4055377
  have hstable : (prefixWord ++ tailWord_4055377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4055377).length < 2 ^ (prefixWord ++ tailWord_4055377).sum := by decide
  have hdescent : baseEnd_4055377 < baseStart_4055377 := by decide
  rcases family_descends (prefixWord ++ tailWord_4055377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4055413 : List Nat := [1, 3, 4, 1, 2, 1, 2, 2, 7]
def baseStart_4055413 : Nat := 118140960795 + 4055413 * 2 ^ 59
def prefixEnd_4055413 : Nat := 4983230072969 + 3 ^ 40 * 4055413 * 2
def baseEnd_4055413 : Nat := 231375124610227434631889

theorem tailTrace_4055413 : CollatzResearch.WordTrace tailWord_4055413 prefixEnd_4055413 231375124610227434631889 := by
  unfold tailWord_4055413
  simp only [CollatzResearch.WordTrace]
  refine ⟨147913063656938785244058893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98608709104625856829372595 147913063656938785244058893)
  ·
    refine ⟨55467398871352044466522085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147913063656938785244058893 55467398871352044466522085)
    ·
      refine ⟨10400137288378508337472891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55467398871352044466522085 10400137288378508337472891)
      ·
        refine ⟨15600205932567762506209337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10400137288378508337472891 15600205932567762506209337)
        ·
          refine ⟨11700154449425821879657003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15600205932567762506209337 11700154449425821879657003)
          ·
            refine ⟨17550231674138732819485505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11700154449425821879657003 17550231674138732819485505)
            ·
              refine ⟨13162673755604049614614129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17550231674138732819485505 13162673755604049614614129)
              ·
                refine ⟨9872005316703037210960597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13162673755604049614614129 9872005316703037210960597)
                ·
                  refine ⟨231375124610227434631889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9872005316703037210960597 231375124610227434631889)
                  ·
                    rfl

theorem cell23_4055413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 2, 7].length) (baseStart_4055413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4055413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4055413 prefixEnd_4055413 := by exact prefixLift 4055413
  have htrace : WordTrace (prefixWord ++ tailWord_4055413) baseStart_4055413 baseEnd_4055413 := by
    simpa [prefixWord, tailWord_4055413, baseEnd_4055413] using wordTrace_append hprefix tailTrace_4055413
  have hstable : (prefixWord ++ tailWord_4055413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4055413).length < 2 ^ (prefixWord ++ tailWord_4055413).sum := by decide
  have hdescent : baseEnd_4055413 < baseStart_4055413 := by decide
  rcases family_descends (prefixWord ++ tailWord_4055413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4055541 : List Nat := [1, 3, 5, 1, 2, 1, 2, 3, 1, 4]
def baseStart_4055541 : Nat := 118140960795 + 4055541 * 2 ^ 59
def prefixEnd_4055541 : Nat := 4983230072969 + 3 ^ 40 * 4055541 * 2
def baseEnd_4055541 : Nat := 694147282338607470295471

theorem tailTrace_4055541 : CollatzResearch.WordTrace tailWord_4055541 prefixEnd_4055541 694147282338607470295471 := by
  unfold tailWord_4055541
  simp only [CollatzResearch.WordTrace]
  refine ⟨147917732200475063104718477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98611821466983375403145651 147917732200475063104718477)
  ·
    refine ⟨55469149575178148664269429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147917732200475063104718477 55469149575178148664269429)
    ·
      refine ⟨5200232772672951437275259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55469149575178148664269429 5200232772672951437275259)
      ·
        refine ⟨7800349159009427155912889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5200232772672951437275259 7800349159009427155912889)
        ·
          refine ⟨5850261869257070366934667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7800349159009427155912889 5850261869257070366934667)
          ·
            refine ⟨8775392803885605550402001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5850261869257070366934667 8775392803885605550402001)
            ·
              refine ⟨6581544602914204162801501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8775392803885605550402001 6581544602914204162801501)
              ·
                refine ⟨2468079226092826561050563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6581544602914204162801501 2468079226092826561050563)
                ·
                  refine ⟨3702118839139239841575845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2468079226092826561050563 3702118839139239841575845)
                  ·
                    refine ⟨694147282338607470295471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3702118839139239841575845 694147282338607470295471)
                    ·
                      rfl

theorem cell23_4055541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_4055541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4055541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4055541 prefixEnd_4055541 := by exact prefixLift 4055541
  have htrace : WordTrace (prefixWord ++ tailWord_4055541) baseStart_4055541 baseEnd_4055541 := by
    simpa [prefixWord, tailWord_4055541, baseEnd_4055541] using wordTrace_append hprefix tailTrace_4055541
  have hstable : (prefixWord ++ tailWord_4055541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4055541).length < 2 ^ (prefixWord ++ tailWord_4055541).sum := by decide
  have hdescent : baseEnd_4055541 < baseStart_4055541 := by decide
  rcases family_descends (prefixWord ++ tailWord_4055541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4055554 : List Nat := [3, 4, 1, 2, 2, 2, 1, 2, 6]
def baseStart_4055554 : Nat := 118140960795 + 4055554 * 2 ^ 59
def prefixEnd_4055554 : Nat := 4983230072969 + 3 ^ 40 * 4055554 * 2
def baseEnd_4055554 : Nat := 231383169140481206669317

theorem tailTrace_4055554 : CollatzResearch.WordTrace tailWord_4055554 prefixEnd_4055554 231383169140481206669317 := by
  unfold tailWord_4055554
  simp only [CollatzResearch.WordTrace]
  refine ⟨36979551587356991581235429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98612137566285310883294477 36979551587356991581235429)
  ·
    refine ⟨6933665922629435921481643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36979551587356991581235429 6933665922629435921481643)
    ·
      refine ⟨10400498883944153882222465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6933665922629435921481643 10400498883944153882222465)
      ·
        refine ⟨7800374162958115411666849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10400498883944153882222465 7800374162958115411666849)
        ·
          refine ⟨5850280622218586558750137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7800374162958115411666849 5850280622218586558750137)
          ·
            refine ⟨4387710466663939919062603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5850280622218586558750137 4387710466663939919062603)
            ·
              refine ⟨6581565699995909878593905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4387710466663939919062603 6581565699995909878593905)
              ·
                refine ⟨4936174274996932408945429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6581565699995909878593905 4936174274996932408945429)
                ·
                  refine ⟨231383169140481206669317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4936174274996932408945429 231383169140481206669317)
                  ·
                    rfl

theorem cell23_4055554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 1, 2, 6].length) (baseStart_4055554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4055554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4055554 prefixEnd_4055554 := by exact prefixLift 4055554
  have htrace : WordTrace (prefixWord ++ tailWord_4055554) baseStart_4055554 baseEnd_4055554 := by
    simpa [prefixWord, tailWord_4055554, baseEnd_4055554] using wordTrace_append hprefix tailTrace_4055554
  have hstable : (prefixWord ++ tailWord_4055554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4055554).length < 2 ^ (prefixWord ++ tailWord_4055554).sum := by decide
  have hdescent : baseEnd_4055554 < baseStart_4055554 := by decide
  rcases family_descends (prefixWord ++ tailWord_4055554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4055558 : List Nat := [6, 2, 1, 1, 1, 1, 2, 4, 1, 4]
def baseStart_4055558 : Nat := 118140960795 + 4055558 * 2 ^ 59
def prefixEnd_4055558 : Nat := 4983230072969 + 3 ^ 40 * 4055558 * 2
def baseEnd_4055558 : Nat := 694150192062316281457945

theorem tailTrace_4055558 : CollatzResearch.WordTrace tailWord_4055558 prefixEnd_4055558 694150192062316281457945 := by
  unfold tailWord_4055558
  simp only [CollatzResearch.WordTrace]
  refine ⟨4622448507544171094002729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 98612234827608983338724885 4622448507544171094002729)
  ·
    refine ⟨3466836380658128320502047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4622448507544171094002729 3466836380658128320502047)
    ·
      refine ⟨5200254570987192480753071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3466836380658128320502047 5200254570987192480753071)
      ·
        refine ⟨7800381856480788721129607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5200254570987192480753071 7800381856480788721129607)
        ·
          refine ⟨11700572784721183081694411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7800381856480788721129607 11700572784721183081694411)
          ·
            refine ⟨17550859177081774622541617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11700572784721183081694411 17550859177081774622541617)
            ·
              refine ⟨13163144382811330966906213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17550859177081774622541617 13163144382811330966906213)
              ·
                refine ⟨2468089571777124556294915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13163144382811330966906213 2468089571777124556294915)
                ·
                  refine ⟨3702134357665686834442373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2468089571777124556294915 3702134357665686834442373)
                  ·
                    refine ⟨694150192062316281457945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3702134357665686834442373 694150192062316281457945)
                    ·
                      rfl

theorem cell23_4055558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_4055558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4055558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4055558 prefixEnd_4055558 := by exact prefixLift 4055558
  have htrace : WordTrace (prefixWord ++ tailWord_4055558) baseStart_4055558 baseEnd_4055558 := by
    simpa [prefixWord, tailWord_4055558, baseEnd_4055558] using wordTrace_append hprefix tailTrace_4055558
  have hstable : (prefixWord ++ tailWord_4055558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4055558).length < 2 ^ (prefixWord ++ tailWord_4055558).sum := by decide
  have hdescent : baseEnd_4055558 < baseStart_4055558 := by decide
  rcases family_descends (prefixWord ++ tailWord_4055558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4055564 : List Nat := [2, 2, 1, 2, 4, 1, 2, 4, 1, 1, 3]
def baseStart_4055564 : Nat := 118140960795 + 4055564 * 2 ^ 59
def prefixEnd_4055564 : Nat := 4983230072969 + 3 ^ 40 * 4055564 * 2
def baseEnd_4055564 : Nat := 2082453657070875820898807

theorem tailTrace_4055564 : CollatzResearch.WordTrace tailWord_4055564 prefixEnd_4055564 2082453657070875820898807 := by
  unfold tailWord_4055564
  simp only [CollatzResearch.WordTrace]
  refine ⟨73959285539695869016402873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98612380719594492021870497 73959285539695869016402873)
  ·
    refine ⟨55469464154771901762302155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73959285539695869016402873 55469464154771901762302155)
    ·
      refine ⟨83204196232157852643453233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55469464154771901762302155 83204196232157852643453233)
      ·
        refine ⟨62403147174118389482589925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83204196232157852643453233 62403147174118389482589925)
        ·
          refine ⟨11700590095147198027985611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62403147174118389482589925 11700590095147198027985611)
          ·
            refine ⟨17550885142720797041978417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11700590095147198027985611 17550885142720797041978417)
            ·
              refine ⟨13163163857040597781483813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17550885142720797041978417 13163163857040597781483813)
              ·
                refine ⟨2468093223195112084028215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13163163857040597781483813 2468093223195112084028215)
                ·
                  refine ⟨3702139834792668126042323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2468093223195112084028215 3702139834792668126042323)
                  ·
                    refine ⟨5553209752189002189063485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3702139834792668126042323 5553209752189002189063485)
                    ·
                      refine ⟨2082453657070875820898807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5553209752189002189063485 2082453657070875820898807)
                      ·
                        rfl

theorem cell23_4055564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 4, 1, 1, 3].length) (baseStart_4055564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4055564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4055564 prefixEnd_4055564 := by exact prefixLift 4055564
  have htrace : WordTrace (prefixWord ++ tailWord_4055564) baseStart_4055564 baseEnd_4055564 := by
    simpa [prefixWord, tailWord_4055564, baseEnd_4055564] using wordTrace_append hprefix tailTrace_4055564
  have hstable : (prefixWord ++ tailWord_4055564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4055564).length < 2 ^ (prefixWord ++ tailWord_4055564).sum := by decide
  have hdescent : baseEnd_4055564 < baseStart_4055564 := by decide
  rcases family_descends (prefixWord ++ tailWord_4055564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4055580 : List Nat := [2, 2, 3, 1, 2, 2, 3, 1, 1, 6]
def baseStart_4055580 : Nat := 118140960795 + 4055580 * 2 ^ 59
def prefixEnd_4055580 : Nat := 4983230072969 + 3 ^ 40 * 4055580 * 2
def baseEnd_4055580 : Nat := 694153957587115919432911

theorem tailTrace_4055580 : CollatzResearch.WordTrace tailWord_4055580 prefixEnd_4055580 694153957587115919432911 := by
  unfold tailWord_4055580
  simp only [CollatzResearch.WordTrace]
  refine ⟨73959577323666886382694097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98612769764889181843592129 73959577323666886382694097)
  ·
    refine ⟨55469682992750164787020573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73959577323666886382694097 55469682992750164787020573)
    ·
      refine ⟨20801131122281311795132715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55469682992750164787020573 20801131122281311795132715)
      ·
        refine ⟨31201696683421967692699073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20801131122281311795132715 31201696683421967692699073)
        ·
          refine ⟨23401272512566475769524305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31201696683421967692699073 23401272512566475769524305)
          ·
            refine ⟨17550954384424856827143229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23401272512566475769524305 17550954384424856827143229)
            ·
              refine ⟨6581607894159321310178711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17550954384424856827143229 6581607894159321310178711)
              ·
                refine ⟨9872411841238981965268067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6581607894159321310178711 9872411841238981965268067)
                ·
                  refine ⟨14808617761858472947902101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9872411841238981965268067 14808617761858472947902101)
                  ·
                    refine ⟨694153957587115919432911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14808617761858472947902101 694153957587115919432911)
                    ·
                      rfl

theorem cell23_4055580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3, 1, 1, 6].length) (baseStart_4055580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4055580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4055580 prefixEnd_4055580 := by exact prefixLift 4055580
  have htrace : WordTrace (prefixWord ++ tailWord_4055580) baseStart_4055580 baseEnd_4055580 := by
    simpa [prefixWord, tailWord_4055580, baseEnd_4055580] using wordTrace_append hprefix tailTrace_4055580
  have hstable : (prefixWord ++ tailWord_4055580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4055580).length < 2 ^ (prefixWord ++ tailWord_4055580).sum := by decide
  have hdescent : baseEnd_4055580 < baseStart_4055580 := by decide
  rcases family_descends (prefixWord ++ tailWord_4055580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4055587 : List Nat := [1, 1, 1, 4, 4, 2, 2, 2, 1, 1, 4]
def baseStart_4055587 : Nat := 118140960795 + 4055587 * 2 ^ 59
def prefixEnd_4055587 : Nat := 4983230072969 + 3 ^ 40 * 4055587 * 2
def baseEnd_4055587 : Nat := 2082465467125929230911201

theorem tailTrace_4055587 : CollatzResearch.WordTrace tailWord_4055587 prefixEnd_4055587 2082465467125929230911201 := by
  unfold tailWord_4055587
  simp only [CollatzResearch.WordTrace]
  refine ⟨147919409958308412960893015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98612939972205608640595343 147919409958308412960893015)
  ·
    refine ⟨221879114937462619441339523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147919409958308412960893015 221879114937462619441339523)
    ·
      refine ⟨332818672406193929162009285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221879114937462619441339523 332818672406193929162009285)
      ·
        refine ⟨62403501076161361717876741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 332818672406193929162009285 62403501076161361717876741)
        ·
          refine ⟨11700656451780255322101889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62403501076161361717876741 11700656451780255322101889)
          ·
            refine ⟨8775492338835191491576417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11700656451780255322101889 8775492338835191491576417)
            ·
              refine ⟨6581619254126393618682313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8775492338835191491576417 6581619254126393618682313)
              ·
                refine ⟨4936214440594795214011735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6581619254126393618682313 4936214440594795214011735)
                ·
                  refine ⟨7404321660892192821017603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4936214440594795214011735 7404321660892192821017603)
                  ·
                    refine ⟨11106482491338289231526405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7404321660892192821017603 11106482491338289231526405)
                    ·
                      refine ⟨2082465467125929230911201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11106482491338289231526405 2082465467125929230911201)
                      ·
                        rfl

theorem cell23_4055587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2, 2, 1, 1, 4].length) (baseStart_4055587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4055587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4055587 prefixEnd_4055587 := by exact prefixLift 4055587
  have htrace : WordTrace (prefixWord ++ tailWord_4055587) baseStart_4055587 baseEnd_4055587 := by
    simpa [prefixWord, tailWord_4055587, baseEnd_4055587] using wordTrace_append hprefix tailTrace_4055587
  have hstable : (prefixWord ++ tailWord_4055587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4055587).length < 2 ^ (prefixWord ++ tailWord_4055587).sum := by decide
  have hdescent : baseEnd_4055587 < baseStart_4055587 := by decide
  rcases family_descends (prefixWord ++ tailWord_4055587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4055598 : List Nat := [4, 1, 3, 1, 3, 2, 1, 3, 1, 1, 3]
def baseStart_4055598 : Nat := 118140960795 + 4055598 * 2 ^ 59
def prefixEnd_4055598 : Nat := 4983230072969 + 3 ^ 40 * 4055598 * 2
def baseEnd_4055598 : Nat := 2082471115413128687873651

theorem tailTrace_4055598 : CollatzResearch.WordTrace tailWord_4055598 prefixEnd_4055598 2082471115413128687873651 := by
  unfold tailWord_4055598
  simp only [CollatzResearch.WordTrace]
  refine ⟨18489976395158570229942931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98613207440845707893028965 18489976395158570229942931)
  ·
    refine ⟨27734964592737855344914397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18489976395158570229942931 27734964592737855344914397)
    ·
      refine ⟨10400611722276695754342899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27734964592737855344914397 10400611722276695754342899)
      ·
        refine ⟨15600917583415043631514349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10400611722276695754342899 15600917583415043631514349)
        ·
          refine ⟨5850344093780641361817881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15600917583415043631514349 5850344093780641361817881)
          ·
            refine ⟨4387758070335481021363411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5850344093780641361817881 4387758070335481021363411)
            ·
              refine ⟨6581637105503221532045117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4387758070335481021363411 6581637105503221532045117)
              ·
                refine ⟨2468113914563708074516919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6581637105503221532045117 2468113914563708074516919)
                ·
                  refine ⟨3702170871845562111775379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2468113914563708074516919 3702170871845562111775379)
                  ·
                    refine ⟨5553256307768343167663069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3702170871845562111775379 5553256307768343167663069)
                    ·
                      refine ⟨2082471115413128687873651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5553256307768343167663069 2082471115413128687873651)
                      ·
                        rfl

theorem cell23_4055598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 1, 3, 1, 1, 3].length) (baseStart_4055598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4055598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4055598 prefixEnd_4055598 := by exact prefixLift 4055598
  have htrace : WordTrace (prefixWord ++ tailWord_4055598) baseStart_4055598 baseEnd_4055598 := by
    simpa [prefixWord, tailWord_4055598, baseEnd_4055598] using wordTrace_append hprefix tailTrace_4055598
  have hstable : (prefixWord ++ tailWord_4055598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4055598).length < 2 ^ (prefixWord ++ tailWord_4055598).sum := by decide
  have hdescent : baseEnd_4055598 < baseStart_4055598 := by decide
  rcases family_descends (prefixWord ++ tailWord_4055598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4055680 : List Nat := [2, 1, 1, 2, 1, 5, 1, 1, 2, 4, 3]
def baseStart_4055680 : Nat := 118140960795 + 4055680 * 2 ^ 59
def prefixEnd_4055680 : Nat := 4983230072969 + 3 ^ 40 * 4055680 * 2
def baseEnd_4055680 : Nat := 2082513220826797367048273

theorem tailTrace_4055680 : CollatzResearch.WordTrace tailWord_4055680 prefixEnd_4055680 2082513220826797367048273 := by
  unfold tailWord_4055680
  simp only [CollatzResearch.WordTrace]
  refine ⟨73961400973485744922014247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98615201297980993229352329 73961400973485744922014247)
  ·
    refine ⟨110942101460228617383021371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73961400973485744922014247 110942101460228617383021371)
    ·
      refine ⟨166413152190342926074532057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110942101460228617383021371 166413152190342926074532057)
      ·
        refine ⟨124809864142757194555899043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166413152190342926074532057 124809864142757194555899043)
        ·
          refine ⟨187214796214135791833848565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124809864142757194555899043 187214796214135791833848565)
          ·
            refine ⟨17551387145075230484423303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 187214796214135791833848565 17551387145075230484423303)
            ·
              refine ⟨26327080717612845726634955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17551387145075230484423303 26327080717612845726634955)
              ·
                refine ⟨39490621076419268589952433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26327080717612845726634955 39490621076419268589952433)
                ·
                  refine ⟨29617965807314451442464325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39490621076419268589952433 29617965807314451442464325)
                  ·
                    refine ⟨5553368588871459645462061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29617965807314451442464325 5553368588871459645462061)
                    ·
                      refine ⟨2082513220826797367048273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5553368588871459645462061 2082513220826797367048273)
                      ·
                        rfl

theorem cell23_4055680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 1, 2, 4, 3].length) (baseStart_4055680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4055680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4055680 prefixEnd_4055680 := by exact prefixLift 4055680
  have htrace : WordTrace (prefixWord ++ tailWord_4055680) baseStart_4055680 baseEnd_4055680 := by
    simpa [prefixWord, tailWord_4055680, baseEnd_4055680] using wordTrace_append hprefix tailTrace_4055680
  have hstable : (prefixWord ++ tailWord_4055680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4055680).length < 2 ^ (prefixWord ++ tailWord_4055680).sum := by decide
  have hdescent : baseEnd_4055680 < baseStart_4055680 := by decide
  rcases family_descends (prefixWord ++ tailWord_4055680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4055694 : List Nat := [4, 1, 1, 3, 1, 1, 4, 1, 1, 4, 2]
def baseStart_4055694 : Nat := 118140960795 + 4055694 * 2 ^ 59
def prefixEnd_4055694 : Nat := 4983230072969 + 3 ^ 40 * 4055694 * 2
def baseEnd_4055694 : Nat := 2082520409555960312273209

theorem tailTrace_4055694 : CollatzResearch.WordTrace tailWord_4055694 prefixEnd_4055694 2082520409555960312273209 := by
  unfold tailWord_4055694
  simp only [CollatzResearch.WordTrace]
  refine ⟨18490414071115096279379767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98615541712613846823358757 18490414071115096279379767)
  ·
    refine ⟨27735621106672644419069651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18490414071115096279379767 27735621106672644419069651)
    ·
      refine ⟨41603431660008966628604477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27735621106672644419069651 41603431660008966628604477)
      ·
        refine ⟨15601286872503362485726679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41603431660008966628604477 15601286872503362485726679)
        ·
          refine ⟨23401930308755043728590019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15601286872503362485726679 23401930308755043728590019)
          ·
            refine ⟨35102895463132565592885029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23401930308755043728590019 35102895463132565592885029)
            ·
              refine ⟨6581792899337356048665943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35102895463132565592885029 6581792899337356048665943)
              ·
                refine ⟨9872689349006034072998915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6581792899337356048665943 9872689349006034072998915)
                ·
                  refine ⟨14809034023509051109498373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9872689349006034072998915 14809034023509051109498373)
                  ·
                    refine ⟨2776693879407947083030945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14809034023509051109498373 2776693879407947083030945)
                    ·
                      refine ⟨2082520409555960312273209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2776693879407947083030945 2082520409555960312273209)
                      ·
                        rfl

theorem cell23_4055694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4, 1, 1, 4, 2].length) (baseStart_4055694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4055694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4055694 prefixEnd_4055694 := by exact prefixLift 4055694
  have htrace : WordTrace (prefixWord ++ tailWord_4055694) baseStart_4055694 baseEnd_4055694 := by
    simpa [prefixWord, tailWord_4055694, baseEnd_4055694] using wordTrace_append hprefix tailTrace_4055694
  have hstable : (prefixWord ++ tailWord_4055694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4055694).length < 2 ^ (prefixWord ++ tailWord_4055694).sum := by decide
  have hdescent : baseEnd_4055694 < baseStart_4055694 := by decide
  rcases family_descends (prefixWord ++ tailWord_4055694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4055730 : List Nat := [3, 2, 1, 1, 1, 2, 1, 3, 4, 5]
def baseStart_4055730 : Nat := 118140960795 + 4055730 * 2 ^ 59
def prefixEnd_4055730 : Nat := 4983230072969 + 3 ^ 40 * 4055730 * 2
def baseEnd_4055730 : Nat := 694179631619840723807681

theorem tailTrace_4055730 : CollatzResearch.WordTrace tailWord_4055730 prefixEnd_4055730 694179631619840723807681 := by
  unfold tailWord_4055730
  simp only [CollatzResearch.WordTrace]
  refine ⟨36981156399197587095837161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98616417064526898922232429 36981156399197587095837161)
  ·
    refine ⟨27735867299398190321877871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36981156399197587095837161 27735867299398190321877871)
    ·
      refine ⟨41603800949097285482816807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27735867299398190321877871 41603800949097285482816807)
      ·
        refine ⟨62405701423645928224225211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41603800949097285482816807 62405701423645928224225211)
        ·
          refine ⟨93608552135468892336337817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62405701423645928224225211 93608552135468892336337817)
          ·
            refine ⟨70206414101601669252253363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93608552135468892336337817 70206414101601669252253363)
            ·
              refine ⟨105309621152402503878380045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70206414101601669252253363 105309621152402503878380045)
              ·
                refine ⟨39491107932150938954392517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105309621152402503878380045 39491107932150938954392517)
                ·
                  refine ⟨7404582737278301053948597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39491107932150938954392517 7404582737278301053948597)
                  ·
                    refine ⟨694179631619840723807681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7404582737278301053948597 694179631619840723807681)
                    ·
                      rfl

theorem cell23_4055730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 3, 4, 5].length) (baseStart_4055730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4055730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4055730 prefixEnd_4055730 := by exact prefixLift 4055730
  have htrace : WordTrace (prefixWord ++ tailWord_4055730) baseStart_4055730 baseEnd_4055730 := by
    simpa [prefixWord, tailWord_4055730, baseEnd_4055730] using wordTrace_append hprefix tailTrace_4055730
  have hstable : (prefixWord ++ tailWord_4055730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4055730).length < 2 ^ (prefixWord ++ tailWord_4055730).sum := by decide
  have hdescent : baseEnd_4055730 < baseStart_4055730 := by decide
  rcases family_descends (prefixWord ++ tailWord_4055730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4055740 : List Nat := [2, 2, 2, 3, 1, 1, 2, 1, 1, 1, 7]
def baseStart_4055740 : Nat := 118140960795 + 4055740 * 2 ^ 59
def prefixEnd_4055740 : Nat := 4983230072969 + 3 ^ 40 * 4055740 * 2
def baseEnd_4055740 : Nat := 2082544029666067132297997

theorem tailTrace_4055740 : CollatzResearch.WordTrace tailWord_4055740 prefixEnd_4055740 2082544029666067132297997 := by
  unfold tailWord_4055740
  simp only [CollatzResearch.WordTrace]
  refine ⟨73962495163377060045606337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98616660217836080060808449 73962495163377060045606337)
  ·
    refine ⟨55471871372532795034204753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73962495163377060045606337 55471871372532795034204753)
    ·
      refine ⟨41603903529399596275653565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55471871372532795034204753 41603903529399596275653565)
      ·
        refine ⟨15601463823524848603370087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41603903529399596275653565 15601463823524848603370087)
        ·
          refine ⟨23402195735287272905055131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15601463823524848603370087 23402195735287272905055131)
          ·
            refine ⟨35103293602930909357582697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23402195735287272905055131 35103293602930909357582697)
            ·
              refine ⟨26327470202198182018187023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35103293602930909357582697 26327470202198182018187023)
              ·
                refine ⟨39491205303297273027280535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26327470202198182018187023 39491205303297273027280535)
                ·
                  refine ⟨59236807954945909540920803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39491205303297273027280535 59236807954945909540920803)
                  ·
                    refine ⟨88855211932418864311381205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59236807954945909540920803 88855211932418864311381205)
                    ·
                      refine ⟨2082544029666067132297997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 88855211932418864311381205 2082544029666067132297997)
                      ·
                        rfl

theorem cell23_4055740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_4055740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4055740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4055740 prefixEnd_4055740 := by exact prefixLift 4055740
  have htrace : WordTrace (prefixWord ++ tailWord_4055740) baseStart_4055740 baseEnd_4055740 := by
    simpa [prefixWord, tailWord_4055740, baseEnd_4055740] using wordTrace_append hprefix tailTrace_4055740
  have hstable : (prefixWord ++ tailWord_4055740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4055740).length < 2 ^ (prefixWord ++ tailWord_4055740).sum := by decide
  have hdescent : baseEnd_4055740 < baseStart_4055740 := by decide
  rcases family_descends (prefixWord ++ tailWord_4055740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4055745 : List Nat := [1, 2, 6, 2, 2, 1, 1, 1, 1, 4, 2]
def baseStart_4055745 : Nat := 118140960795 + 4055745 * 2 ^ 59
def prefixEnd_4055745 : Nat := 4983230072969 + 3 ^ 40 * 4055745 * 2
def baseEnd_4055745 : Nat := 2082546597069339612735475

theorem tailTrace_4055745 : CollatzResearch.WordTrace tailWord_4055745 prefixEnd_4055745 2082546597069339612735475 := by
  unfold tailWord_4055745
  simp only [CollatzResearch.WordTrace]
  refine ⟨147925172691736005945144689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98616781794490670630096459 147925172691736005945144689)
  ·
    refine ⟨110943879518802004458858517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147925172691736005945144689 110943879518802004458858517)
    ·
      refine ⟨5200494352443843959008993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 110943879518802004458858517 5200494352443843959008993)
      ·
        refine ⟨3900370764332882969256745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5200494352443843959008993 3900370764332882969256745)
        ·
          refine ⟨2925278073249662226942559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3900370764332882969256745 2925278073249662226942559)
          ·
            refine ⟨4387917109874493340413839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2925278073249662226942559 4387917109874493340413839)
            ·
              refine ⟨6581875664811740010620759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4387917109874493340413839 6581875664811740010620759)
              ·
                refine ⟨9872813497217610015931139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6581875664811740010620759 9872813497217610015931139)
                ·
                  refine ⟨14809220245826415023896709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9872813497217610015931139 14809220245826415023896709)
                  ·
                    refine ⟨2776728796092452816980633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14809220245826415023896709 2776728796092452816980633)
                    ·
                      refine ⟨2082546597069339612735475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2776728796092452816980633 2082546597069339612735475)
                      ·
                        rfl

theorem cell23_4055745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_4055745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4055745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4055745 prefixEnd_4055745 := by exact prefixLift 4055745
  have htrace : WordTrace (prefixWord ++ tailWord_4055745) baseStart_4055745 baseEnd_4055745 := by
    simpa [prefixWord, tailWord_4055745, baseEnd_4055745] using wordTrace_append hprefix tailTrace_4055745
  have hstable : (prefixWord ++ tailWord_4055745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4055745).length < 2 ^ (prefixWord ++ tailWord_4055745).sum := by decide
  have hdescent : baseEnd_4055745 < baseStart_4055745 := by decide
  rcases family_descends (prefixWord ++ tailWord_4055745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4055784 : List Nat := [2, 1, 4, 1, 4, 1, 1, 2, 2, 1, 4]
def baseStart_4055784 : Nat := 118140960795 + 4055784 * 2 ^ 59
def prefixEnd_4055784 : Nat := 4983230072969 + 3 ^ 40 * 4055784 * 2
def baseEnd_4055784 : Nat := 2082566622814864960147795

theorem tailTrace_4055784 : CollatzResearch.WordTrace tailWord_4055784 prefixEnd_4055784 2082566622814864960147795 := by
  unfold tailWord_4055784
  simp only [CollatzResearch.WordTrace]
  refine ⟨73963297569297357802907203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98617730092396477070542937 73963297569297357802907203)
  ·
    refine ⟨110944946353946036704360805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73963297569297357802907203 110944946353946036704360805)
    ·
      refine ⟨20802177441364881882067651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110944946353946036704360805 20802177441364881882067651)
      ·
        refine ⟨31203266162047322823101477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20802177441364881882067651 31203266162047322823101477)
        ·
          refine ⟨5850612405383873029331527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31203266162047322823101477 5850612405383873029331527)
          ·
            refine ⟨8775918608075809543997291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5850612405383873029331527 8775918608075809543997291)
            ·
              refine ⟨13163877912113714315995937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8775918608075809543997291 13163877912113714315995937)
              ·
                refine ⟨9872908434085285736996953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13163877912113714315995937 9872908434085285736996953)
                ·
                  refine ⟨7404681325563964302747715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9872908434085285736996953 7404681325563964302747715)
                  ·
                    refine ⟨11107021988345946454121573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7404681325563964302747715 11107021988345946454121573)
                    ·
                      refine ⟨2082566622814864960147795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11107021988345946454121573 2082566622814864960147795)
                      ·
                        rfl

theorem cell23_4055784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 2, 2, 1, 4].length) (baseStart_4055784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4055784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4055784 prefixEnd_4055784 := by exact prefixLift 4055784
  have htrace : WordTrace (prefixWord ++ tailWord_4055784) baseStart_4055784 baseEnd_4055784 := by
    simpa [prefixWord, tailWord_4055784, baseEnd_4055784] using wordTrace_append hprefix tailTrace_4055784
  have hstable : (prefixWord ++ tailWord_4055784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4055784).length < 2 ^ (prefixWord ++ tailWord_4055784).sum := by decide
  have hdescent : baseEnd_4055784 < baseStart_4055784 := by decide
  rcases family_descends (prefixWord ++ tailWord_4055784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4055794 : List Nat := [3, 2, 1, 3, 1, 2, 3, 1, 3, 4]
def baseStart_4055794 : Nat := 118140960795 + 4055794 * 2 ^ 59
def prefixEnd_4055794 : Nat := 4983230072969 + 3 ^ 40 * 4055794 * 2
def baseEnd_4055794 : Nat := 694190585873803307007583

theorem tailTrace_4055794 : CollatzResearch.WordTrace tailWord_4055794 prefixEnd_4055794 694190585873803307007583 := by
  unfold tailWord_4055794
  simp only [CollatzResearch.WordTrace]
  refine ⟨36981739967139621828419609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98617973245705658209118957 36981739967139621828419609)
  ·
    refine ⟨27736304975354716371314707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36981739967139621828419609 27736304975354716371314707)
    ·
      refine ⟨41604457463032074556972061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27736304975354716371314707 41604457463032074556972061)
      ·
        refine ⟨15601671548637027958864523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41604457463032074556972061 15601671548637027958864523)
        ·
          refine ⟨23402507322955541938296785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15601671548637027958864523 23402507322955541938296785)
          ·
            refine ⟨17551880492216656453722589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23402507322955541938296785 17551880492216656453722589)
            ·
              refine ⟨6581955184581246170145971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17551880492216656453722589 6581955184581246170145971)
              ·
                refine ⟨9872932776871869255218957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6581955184581246170145971 9872932776871869255218957)
                ·
                  refine ⟨3702349791326950970707109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9872932776871869255218957 3702349791326950970707109)
                  ·
                    refine ⟨694190585873803307007583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3702349791326950970707109 694190585873803307007583)
                    ·
                      rfl

theorem cell23_4055794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3, 1, 3, 4].length) (baseStart_4055794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4055794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4055794 prefixEnd_4055794 := by exact prefixLift 4055794
  have htrace : WordTrace (prefixWord ++ tailWord_4055794) baseStart_4055794 baseEnd_4055794 := by
    simpa [prefixWord, tailWord_4055794, baseEnd_4055794] using wordTrace_append hprefix tailTrace_4055794
  have hstable : (prefixWord ++ tailWord_4055794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4055794).length < 2 ^ (prefixWord ++ tailWord_4055794).sum := by decide
  have hdescent : baseEnd_4055794 < baseStart_4055794 := by decide
  rcases family_descends (prefixWord ++ tailWord_4055794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4055854 : List Nat := [4, 1, 3, 2, 1, 1, 1, 2, 3, 5]
def baseStart_4055854 : Nat := 118140960795 + 4055854 * 2 ^ 59
def prefixEnd_4055854 : Nat := 4983230072969 + 3 ^ 40 * 4055854 * 2
def baseEnd_4055854 : Nat := 694200855486893228757491

theorem tailTrace_4055854 : CollatzResearch.WordTrace tailWord_4055854 prefixEnd_4055854 694200855486893228757491 := by
  unfold tailWord_4055854
  simp only [CollatzResearch.WordTrace]
  refine ⟨18491143531042639695107827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98619432165560745040575077 18491143531042639695107827)
  ·
    refine ⟨27736715296563959542661741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18491143531042639695107827 27736715296563959542661741)
    ·
      refine ⟨10401268236211484828498153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27736715296563959542661741 10401268236211484828498153)
      ·
        refine ⟨7800951177158613621373615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10401268236211484828498153 7800951177158613621373615)
        ·
          refine ⟨11701426765737920432060423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7800951177158613621373615 11701426765737920432060423)
          ·
            refine ⟨17552140148606880648090635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11701426765737920432060423 17552140148606880648090635)
            ·
              refine ⟨26328210222910320972135953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17552140148606880648090635 26328210222910320972135953)
              ·
                refine ⟨19746157667182740729101965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26328210222910320972135953 19746157667182740729101965)
                ·
                  refine ⟨7404809125193527773413237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19746157667182740729101965 7404809125193527773413237)
                  ·
                    refine ⟨694200855486893228757491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7404809125193527773413237 694200855486893228757491)
                    ·
                      rfl

theorem cell23_4055854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_4055854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4055854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4055854 prefixEnd_4055854 := by exact prefixLift 4055854
  have htrace : WordTrace (prefixWord ++ tailWord_4055854) baseStart_4055854 baseEnd_4055854 := by
    simpa [prefixWord, tailWord_4055854, baseEnd_4055854] using wordTrace_append hprefix tailTrace_4055854
  have hstable : (prefixWord ++ tailWord_4055854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4055854).length < 2 ^ (prefixWord ++ tailWord_4055854).sum := by decide
  have hdescent : baseEnd_4055854 < baseStart_4055854 := by decide
  rcases family_descends (prefixWord ++ tailWord_4055854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4055857 : List Nat := [1, 2, 2, 3, 2, 1, 1, 1, 5, 1, 4]
def baseStart_4055857 : Nat := 118140960795 + 4055857 * 2 ^ 59
def prefixEnd_4055857 : Nat := 4983230072969 + 3 ^ 40 * 4055857 * 2
def baseEnd_4055857 : Nat := 2082604106902643174534959

theorem tailTrace_4055857 : CollatzResearch.WordTrace tailWord_4055857 prefixEnd_4055857 2082604106902643174534959 := by
  unfold tailWord_4055857
  simp only [CollatzResearch.WordTrace]
  refine ⟨147929257667330249073221825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98619505111553499382147883 147929257667330249073221825)
  ·
    refine ⟨110946943250497686804916369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147929257667330249073221825 110946943250497686804916369)
    ·
      refine ⟨83210207437873265103687277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110946943250497686804916369 83210207437873265103687277)
      ·
        refine ⟨31203827789202474413882729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83210207437873265103687277 31203827789202474413882729)
        ·
          refine ⟨23402870841901855810412047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31203827789202474413882729 23402870841901855810412047)
          ·
            refine ⟨35104306262852783715618071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23402870841901855810412047 35104306262852783715618071)
            ·
              refine ⟨52656459394279175573427107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35104306262852783715618071 52656459394279175573427107)
              ·
                refine ⟨78984689091418763360140661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52656459394279175573427107 78984689091418763360140661)
                ·
                  refine ⟨7404814602320509065013187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78984689091418763360140661 7404814602320509065013187)
                  ·
                    refine ⟨11107221903480763597519781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7404814602320509065013187 11107221903480763597519781)
                    ·
                      refine ⟨2082604106902643174534959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11107221903480763597519781 2082604106902643174534959)
                      ·
                        rfl

theorem cell23_4055857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 5, 1, 4].length) (baseStart_4055857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4055857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4055857 prefixEnd_4055857 := by exact prefixLift 4055857
  have htrace : WordTrace (prefixWord ++ tailWord_4055857) baseStart_4055857 baseEnd_4055857 := by
    simpa [prefixWord, tailWord_4055857, baseEnd_4055857] using wordTrace_append hprefix tailTrace_4055857
  have hstable : (prefixWord ++ tailWord_4055857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4055857).length < 2 ^ (prefixWord ++ tailWord_4055857).sum := by decide
  have hdescent : baseEnd_4055857 < baseStart_4055857 := by decide
  rcases family_descends (prefixWord ++ tailWord_4055857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4055908 : List Nat := [2, 3, 1, 1, 4, 2, 2, 1, 3, 2, 2]
def baseStart_4055908 : Nat := 118140960795 + 4055908 * 2 ^ 59
def prefixEnd_4055908 : Nat := 4983230072969 + 3 ^ 40 * 4055908 * 2
def baseEnd_4055908 : Nat := 2082630294416022474997225

theorem tailTrace_4055908 : CollatzResearch.WordTrace tailWord_4055908 prefixEnd_4055908 2082630294416022474997225 := by
  unfold tailWord_4055908
  simp only [CollatzResearch.WordTrace]
  refine ⟨73965558895072742391664189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98620745193430323188885585 73965558895072742391664189)
  ·
    refine ⟨27737084585652278396874071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73965558895072742391664189 27737084585652278396874071)
    ·
      refine ⟨41605626878478417595311107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27737084585652278396874071 41605626878478417595311107)
      ·
        refine ⟨62408440317717626392966661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41605626878478417595311107 62408440317717626392966661)
        ·
          refine ⟨11701582559572054948681249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62408440317717626392966661 11701582559572054948681249)
          ·
            refine ⟨8776186919679041211510937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11701582559572054948681249 8776186919679041211510937)
            ·
              refine ⟨6582140189759280908633203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8776186919679041211510937 6582140189759280908633203)
              ·
                refine ⟨9873210284638921362949805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6582140189759280908633203 9873210284638921362949805)
                ·
                  refine ⟨3702453856739595511106177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9873210284638921362949805 3702453856739595511106177)
                  ·
                    refine ⟨2776840392554696633329633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3702453856739595511106177 2776840392554696633329633)
                    ·
                      refine ⟨2082630294416022474997225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2776840392554696633329633 2082630294416022474997225)
                      ·
                        rfl

theorem cell23_4055908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2, 1, 3, 2, 2].length) (baseStart_4055908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4055908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4055908 prefixEnd_4055908 := by exact prefixLift 4055908
  have htrace : WordTrace (prefixWord ++ tailWord_4055908) baseStart_4055908 baseEnd_4055908 := by
    simpa [prefixWord, tailWord_4055908, baseEnd_4055908] using wordTrace_append hprefix tailTrace_4055908
  have hstable : (prefixWord ++ tailWord_4055908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4055908).length < 2 ^ (prefixWord ++ tailWord_4055908).sum := by decide
  have hdescent : baseEnd_4055908 < baseStart_4055908 := by decide
  rcases family_descends (prefixWord ++ tailWord_4055908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4055918 : List Nat := [4, 1, 2, 3, 3, 1, 1, 1, 1, 6]
def baseStart_4055918 : Nat := 118140960795 + 4055918 * 2 ^ 59
def prefixEnd_4055918 : Nat := 4983230072969 + 3 ^ 40 * 4055918 * 2
def baseEnd_4055918 : Nat := 694211809740855811957393

theorem tailTrace_4055918 : CollatzResearch.WordTrace tailWord_4055918 prefixEnd_4055918 694211809740855811957393 := by
  unfold tailWord_4055918
  simp only [CollatzResearch.WordTrace]
  refine ⟨18491435315013657061399051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98620988346739504327461605 18491435315013657061399051)
  ·
    refine ⟨27737152972520485592098577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18491435315013657061399051 27737152972520485592098577)
    ·
      refine ⟨20802864729390364194073933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27737152972520485592098577 20802864729390364194073933)
      ·
        refine ⟨7801074273521386572777725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20802864729390364194073933 7801074273521386572777725)
        ·
          refine ⟨2925402852570519964791647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7801074273521386572777725 2925402852570519964791647)
          ·
            refine ⟨4388104278855779947187471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2925402852570519964791647 4388104278855779947187471)
            ·
              refine ⟨6582156418283669920781207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4388104278855779947187471 6582156418283669920781207)
              ·
                refine ⟨9873234627425504881171811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6582156418283669920781207 9873234627425504881171811)
                ·
                  refine ⟨14809851941138257321757717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9873234627425504881171811 14809851941138257321757717)
                  ·
                    refine ⟨694211809740855811957393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14809851941138257321757717 694211809740855811957393)
                    ·
                      rfl

theorem cell23_4055918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 1, 1, 1, 6].length) (baseStart_4055918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4055918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4055918 prefixEnd_4055918 := by exact prefixLift 4055918
  have htrace : WordTrace (prefixWord ++ tailWord_4055918) baseStart_4055918 baseEnd_4055918 := by
    simpa [prefixWord, tailWord_4055918, baseEnd_4055918] using wordTrace_append hprefix tailTrace_4055918
  have hstable : (prefixWord ++ tailWord_4055918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4055918).length < 2 ^ (prefixWord ++ tailWord_4055918).sum := by decide
  have hdescent : baseEnd_4055918 < baseStart_4055918 := by decide
  rcases family_descends (prefixWord ++ tailWord_4055918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4055977 : List Nat := [1, 2, 1, 1, 1, 1, 6, 1, 1, 4, 4]
def baseStart_4055977 : Nat := 118140960795 + 4055977 * 2 ^ 59
def prefixEnd_4055977 : Nat := 4983230072969 + 3 ^ 40 * 4055977 * 2
def baseEnd_4055977 : Nat := 2082665724581182705034407

theorem tailTrace_4055977 : CollatzResearch.WordTrace tailWord_4055977 prefixEnd_4055977 2082665724581182705034407 := by
  unfold tailWord_4055977
  simp only [CollatzResearch.WordTrace]
  refine ⟨147933634426895509567590185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98622422951263673045060123 147933634426895509567590185)
  ·
    refine ⟨110950225820171632175692639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147933634426895509567590185 110950225820171632175692639)
    ·
      refine ⟨166425338730257448263538959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110950225820171632175692639 166425338730257448263538959)
      ·
        refine ⟨249638008095386172395308439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166425338730257448263538959 249638008095386172395308439)
        ·
          refine ⟨374457012143079258592962659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249638008095386172395308439 374457012143079258592962659)
          ·
            refine ⟨561685518214618887889443989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 374457012143079258592962659 561685518214618887889443989)
            ·
              refine ⟨26329008666310260369817687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 561685518214618887889443989 26329008666310260369817687)
              ·
                refine ⟨39493512999465390554726531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26329008666310260369817687 39493512999465390554726531)
                ·
                  refine ⟨59240269499198085832089797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39493512999465390554726531 59240269499198085832089797)
                  ·
                    refine ⟨11107550531099641093516837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59240269499198085832089797 11107550531099641093516837)
                    ·
                      refine ⟨2082665724581182705034407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11107550531099641093516837 2082665724581182705034407)
                      ·
                        rfl

theorem cell23_4055977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 1, 1, 4, 4].length) (baseStart_4055977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4055977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4055977 prefixEnd_4055977 := by exact prefixLift 4055977
  have htrace : WordTrace (prefixWord ++ tailWord_4055977) baseStart_4055977 baseEnd_4055977 := by
    simpa [prefixWord, tailWord_4055977, baseEnd_4055977] using wordTrace_append hprefix tailTrace_4055977
  have hstable : (prefixWord ++ tailWord_4055977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4055977).length < 2 ^ (prefixWord ++ tailWord_4055977).sum := by decide
  have hdescent : baseEnd_4055977 < baseStart_4055977 := by decide
  rcases family_descends (prefixWord ++ tailWord_4055977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4055985 : List Nat := [1, 2, 2, 4, 3, 2, 1, 2, 1, 3, 2]
def baseStart_4055985 : Nat := 118140960795 + 4055985 * 2 ^ 59
def prefixEnd_4055985 : Nat := 4983230072969 + 3 ^ 40 * 4055985 * 2
def baseEnd_4055985 : Nat := 2082669832426418673734371

theorem tailTrace_4055985 : CollatzResearch.WordTrace tailWord_4055985 prefixEnd_4055985 2082669832426418673734371 := by
  unfold tailWord_4055985
  simp only [CollatzResearch.WordTrace]
  refine ⟨147933926210866526933881409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98622617473911017955920939 147933926210866526933881409)
  ·
    refine ⟨110950444658149895200411057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147933926210866526933881409 110950444658149895200411057)
    ·
      refine ⟨83212833493612421400308293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110950444658149895200411057 83212833493612421400308293)
      ·
        refine ⟨15602406280052329012557805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83212833493612421400308293 15602406280052329012557805)
        ·
          refine ⟨5850902355019623379709177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15602406280052329012557805 5850902355019623379709177)
          ·
            refine ⟨4388176766264717534781883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5850902355019623379709177 4388176766264717534781883)
            ·
              refine ⟨6582265149397076302172825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4388176766264717534781883 6582265149397076302172825)
              ·
                refine ⟨4936698862047807226629619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6582265149397076302172825 4936698862047807226629619)
                ·
                  refine ⟨7405048293071710839944429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4936698862047807226629619 7405048293071710839944429)
                  ·
                    refine ⟨2776893109901891564979161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7405048293071710839944429 2776893109901891564979161)
                    ·
                      refine ⟨2082669832426418673734371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2776893109901891564979161 2082669832426418673734371)
                      ·
                        rfl

theorem cell23_4055985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 1, 2, 1, 3, 2].length) (baseStart_4055985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4055985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4055985 prefixEnd_4055985 := by exact prefixLift 4055985
  have htrace : WordTrace (prefixWord ++ tailWord_4055985) baseStart_4055985 baseEnd_4055985 := by
    simpa [prefixWord, tailWord_4055985, baseEnd_4055985] using wordTrace_append hprefix tailTrace_4055985
  have hstable : (prefixWord ++ tailWord_4055985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4055985).length < 2 ^ (prefixWord ++ tailWord_4055985).sum := by decide
  have hdescent : baseEnd_4055985 < baseStart_4055985 := by decide
  rcases family_descends (prefixWord ++ tailWord_4055985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4056031 : List Nat := [1, 1, 2, 3, 5, 1, 1, 1, 2, 3, 3]
def baseStart_4056031 : Nat := 118140960795 + 4056031 * 2 ^ 59
def prefixEnd_4056031 : Nat := 4983230072969 + 3 ^ 40 * 4056031 * 2
def baseEnd_4056031 : Nat := 2082693452536525493759159

theorem tailTrace_4056031 : CollatzResearch.WordTrace tailWord_4056031 prefixEnd_4056031 2082693452536525493759159 := by
  unfold tailWord_4056031
  simp only [CollatzResearch.WordTrace]
  refine ⟨147935603968699876790055947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98623735979133251193370631 147935603968699876790055947)
  ·
    refine ⟨221903405953049815185083921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147935603968699876790055947 221903405953049815185083921)
    ·
      refine ⟨166427554464787361388812941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221903405953049815185083921 166427554464787361388812941)
      ·
        refine ⟨62410332924295260520804853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166427554464787361388812941 62410332924295260520804853)
        ·
          refine ⟨5850968711652680673825455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62410332924295260520804853 5850968711652680673825455)
          ·
            refine ⟨8776453067479021010738183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5850968711652680673825455 8776453067479021010738183)
            ·
              refine ⟨13164679601218531516107275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8776453067479021010738183 13164679601218531516107275)
              ·
                refine ⟨19747019401827797274160913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13164679601218531516107275 19747019401827797274160913)
                ·
                  refine ⟨14810264551370847955620685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19747019401827797274160913 14810264551370847955620685)
                  ·
                    refine ⟨5553849206764067983357757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14810264551370847955620685 5553849206764067983357757)
                    ·
                      refine ⟨2082693452536525493759159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5553849206764067983357757 2082693452536525493759159)
                      ·
                        rfl

theorem cell23_4056031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 1, 2, 3, 3].length) (baseStart_4056031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4056031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4056031 prefixEnd_4056031 := by exact prefixLift 4056031
  have htrace : WordTrace (prefixWord ++ tailWord_4056031) baseStart_4056031 baseEnd_4056031 := by
    simpa [prefixWord, tailWord_4056031, baseEnd_4056031] using wordTrace_append hprefix tailTrace_4056031
  have hstable : (prefixWord ++ tailWord_4056031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4056031).length < 2 ^ (prefixWord ++ tailWord_4056031).sum := by decide
  have hdescent : baseEnd_4056031 < baseStart_4056031 := by decide
  rcases family_descends (prefixWord ++ tailWord_4056031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4056066 : List Nat := [3, 4, 1, 3, 2, 1, 1, 2, 2, 2, 2]
def baseStart_4056066 : Nat := 118140960795 + 4056066 * 2 ^ 59
def prefixEnd_4056066 : Nat := 4983230072969 + 3 ^ 40 * 4056066 * 2
def baseEnd_4056066 : Nat := 2082711424359432856821499

theorem tailTrace_4056066 : CollatzResearch.WordTrace tailWord_4056066 prefixEnd_4056066 2082711424359432856821499 := by
  unfold tailWord_4056066
  simp only [CollatzResearch.WordTrace]
  refine ⟨36984220130893269441895013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98624587015715385178386701 36984220130893269441895013)
  ·
    refine ⟨6934541274542488020355315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36984220130893269441895013 6934541274542488020355315)
    ·
      refine ⟨10401811911813732030532973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6934541274542488020355315 10401811911813732030532973)
      ·
        refine ⟨3900679466930149511449865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10401811911813732030532973 3900679466930149511449865)
        ·
          refine ⟨2925509600197612133587399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3900679466930149511449865 2925509600197612133587399)
          ·
            refine ⟨4388264400296418200381099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2925509600197612133587399 4388264400296418200381099)
            ·
              refine ⟨6582396600444627300571649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4388264400296418200381099 6582396600444627300571649)
              ·
                refine ⟨4936797450333470475428737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6582396600444627300571649 4936797450333470475428737)
                ·
                  refine ⟨3702598087750102856571553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4936797450333470475428737 3702598087750102856571553)
                  ·
                    refine ⟨2776948565812577142428665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3702598087750102856571553 2776948565812577142428665)
                    ·
                      refine ⟨2082711424359432856821499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2776948565812577142428665 2082711424359432856821499)
                      ·
                        rfl

theorem cell23_4056066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_4056066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4056066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4056066 prefixEnd_4056066 := by exact prefixLift 4056066
  have htrace : WordTrace (prefixWord ++ tailWord_4056066) baseStart_4056066 baseEnd_4056066 := by
    simpa [prefixWord, tailWord_4056066, baseEnd_4056066] using wordTrace_append hprefix tailTrace_4056066
  have hstable : (prefixWord ++ tailWord_4056066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4056066).length < 2 ^ (prefixWord ++ tailWord_4056066).sum := by decide
  have hdescent : baseEnd_4056066 < baseStart_4056066 := by decide
  rcases family_descends (prefixWord ++ tailWord_4056066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4056071 : List Nat := [1, 1, 4, 3, 1, 1, 1, 1, 4, 4, 2]
def baseStart_4056071 : Nat := 118140960795 + 4056071 * 2 ^ 59
def prefixEnd_4056071 : Nat := 4983230072969 + 3 ^ 40 * 4056071 * 2
def baseEnd_4056071 : Nat := 2082713991762705337258975

theorem tailTrace_4056071 : CollatzResearch.WordTrace tailWord_4056071 prefixEnd_4056071 2082713991762705337258975 := by
  unfold tailWord_4056071
  simp only [CollatzResearch.WordTrace]
  refine ⟨147937062888554963621512067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98624708592369975747674711 147937062888554963621512067)
  ·
    refine ⟨221905594332832445432268101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147937062888554963621512067 221905594332832445432268101)
    ·
      refine ⟨41607298937406083518550269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 221905594332832445432268101 41607298937406083518550269)
      ·
        refine ⟨15602737101527281319456351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41607298937406083518550269 15602737101527281319456351)
        ·
          refine ⟨23404105652290921979184527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15602737101527281319456351 23404105652290921979184527)
          ·
            refine ⟨35106158478436382968776791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23404105652290921979184527 35106158478436382968776791)
            ·
              refine ⟨52659237717654574453165187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35106158478436382968776791 52659237717654574453165187)
              ·
                refine ⟨78988856576481861679747781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52659237717654574453165187 78988856576481861679747781)
                ·
                  refine ⟨14810410608090349064952709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78988856576481861679747781 14810410608090349064952709)
                  ·
                    refine ⟨2776951989016940449678633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14810410608090349064952709 2776951989016940449678633)
                    ·
                      refine ⟨2082713991762705337258975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2776951989016940449678633 2082713991762705337258975)
                      ·
                        rfl

theorem cell23_4056071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 4, 4, 2].length) (baseStart_4056071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4056071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4056071 prefixEnd_4056071 := by exact prefixLift 4056071
  have htrace : WordTrace (prefixWord ++ tailWord_4056071) baseStart_4056071 baseEnd_4056071 := by
    simpa [prefixWord, tailWord_4056071, baseEnd_4056071] using wordTrace_append hprefix tailTrace_4056071
  have hstable : (prefixWord ++ tailWord_4056071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4056071).length < 2 ^ (prefixWord ++ tailWord_4056071).sum := by decide
  have hdescent : baseEnd_4056071 < baseStart_4056071 := by decide
  rcases family_descends (prefixWord ++ tailWord_4056071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4056138 : List Nat := [3, 1, 2, 1, 1, 2, 5, 1, 3, 1, 3]
def baseStart_4056138 : Nat := 118140960795 + 4056138 * 2 ^ 59
def prefixEnd_4056138 : Nat := 4983230072969 + 3 ^ 40 * 4056138 * 2
def baseEnd_4056138 : Nat := 2082748394966556575121167

theorem tailTrace_4056138 : CollatzResearch.WordTrace tailWord_4056138 prefixEnd_4056138 2082748394966556575121167 := by
  unfold tailWord_4056138
  simp only [CollatzResearch.WordTrace]
  refine ⟨36984876644828058516050267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98626337719541489376134045 36984876644828058516050267)
  ·
    refine ⟨55477314967242087774075401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36984876644828058516050267 55477314967242087774075401)
    ·
      refine ⟨41607986225431565830556551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55477314967242087774075401 41607986225431565830556551)
      ·
        refine ⟨62411979338147348745834827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41607986225431565830556551 62411979338147348745834827)
        ·
          refine ⟨93617969007221023118752241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62411979338147348745834827 93617969007221023118752241)
          ·
            refine ⟨70213476755415767339064181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93617969007221023118752241 70213476755415767339064181)
            ·
              refine ⟨6582513445820228188037267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70213476755415767339064181 6582513445820228188037267)
              ·
                refine ⟨9873770168730342282055901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6582513445820228188037267 9873770168730342282055901)
                ·
                  refine ⟨3702663813273878355770963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9873770168730342282055901 3702663813273878355770963)
                  ·
                    refine ⟨5553995719910817533656445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3702663813273878355770963 5553995719910817533656445)
                    ·
                      refine ⟨2082748394966556575121167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5553995719910817533656445 2082748394966556575121167)
                      ·
                        rfl

theorem cell23_4056138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5, 1, 3, 1, 3].length) (baseStart_4056138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4056138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4056138 prefixEnd_4056138 := by exact prefixLift 4056138
  have htrace : WordTrace (prefixWord ++ tailWord_4056138) baseStart_4056138 baseEnd_4056138 := by
    simpa [prefixWord, tailWord_4056138, baseEnd_4056138] using wordTrace_append hprefix tailTrace_4056138
  have hstable : (prefixWord ++ tailWord_4056138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4056138).length < 2 ^ (prefixWord ++ tailWord_4056138).sum := by decide
  have hdescent : baseEnd_4056138 < baseStart_4056138 := by decide
  rcases family_descends (prefixWord ++ tailWord_4056138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4056161 : List Nat := [1, 2, 3, 1, 1, 2, 2, 1, 2, 6, 2]
def baseStart_4056161 : Nat := 118140960795 + 4056161 * 2 ^ 59
def prefixEnd_4056161 : Nat := 4983230072969 + 3 ^ 40 * 4056161 * 2
def baseEnd_4056161 : Nat := 2082760205021609985133561

theorem tailTrace_4056161 : CollatzResearch.WordTrace tailWord_4056161 prefixEnd_4056161 2082760205021609985133561 := by
  unfold tailWord_4056161
  simp only [CollatzResearch.WordTrace]
  refine ⟨147940345458228908992288337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98626896972152605994858891 147940345458228908992288337)
  ·
    refine ⟨110955259093671681744216253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147940345458228908992288337 110955259093671681744216253)
    ·
      refine ⟨41608222160126880654081095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110955259093671681744216253 41608222160126880654081095)
      ·
        refine ⟨62412333240190320981121643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41608222160126880654081095 62412333240190320981121643)
        ·
          refine ⟨93618499860285481471682465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62412333240190320981121643 93618499860285481471682465)
          ·
            refine ⟨70213874895214111103761849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93618499860285481471682465 70213874895214111103761849)
            ·
              refine ⟨52660406171410583327821387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70213874895214111103761849 52660406171410583327821387)
              ·
                refine ⟨78990609257115874991732081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52660406171410583327821387 78990609257115874991732081)
                ·
                  refine ⟨59242956942836906243799061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78990609257115874991732081 59242956942836906243799061)
                  ·
                    refine ⟨2777013606695479980178081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 59242956942836906243799061 2777013606695479980178081)
                    ·
                      refine ⟨2082760205021609985133561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2777013606695479980178081 2082760205021609985133561)
                      ·
                        rfl

theorem cell23_4056161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 2, 6, 2].length) (baseStart_4056161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4056161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4056161 prefixEnd_4056161 := by exact prefixLift 4056161
  have htrace : WordTrace (prefixWord ++ tailWord_4056161) baseStart_4056161 baseEnd_4056161 := by
    simpa [prefixWord, tailWord_4056161, baseEnd_4056161] using wordTrace_append hprefix tailTrace_4056161
  have hstable : (prefixWord ++ tailWord_4056161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4056161).length < 2 ^ (prefixWord ++ tailWord_4056161).sum := by decide
  have hdescent : baseEnd_4056161 < baseStart_4056161 := by decide
  rcases family_descends (prefixWord ++ tailWord_4056161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4056188 : List Nat := [2, 2, 2, 1, 1, 3, 4, 2, 2, 4]
def baseStart_4056188 : Nat := 118140960795 + 4056188 * 2 ^ 59
def prefixEnd_4056188 : Nat := 4983230072969 + 3 ^ 40 * 4056188 * 2
def baseEnd_4056188 : Nat := 694258022999760459831979

theorem tailTrace_4056188 : CollatzResearch.WordTrace tailWord_4056188 prefixEnd_4056188 694258022999760459831979 := by
  unfold tailWord_4056188
  simp only [CollatzResearch.WordTrace]
  refine ⟨73970665114565546301760609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98627553486087395069014145 73970665114565546301760609)
  ·
    refine ⟨55477998835924159726320457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73970665114565546301760609 55477998835924159726320457)
    ·
      refine ⟨41608499126943119794740343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55477998835924159726320457 41608499126943119794740343)
      ·
        refine ⟨62412748690414679692110515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41608499126943119794740343 62412748690414679692110515)
        ·
          refine ⟨93619123035622019538165773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62412748690414679692110515 93619123035622019538165773)
          ·
            refine ⟨35107171138358257326812165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93619123035622019538165773 35107171138358257326812165)
            ·
              refine ⟨6582594588442173248777281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35107171138358257326812165 6582594588442173248777281)
              ·
                refine ⟨4936945941331629936582961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6582594588442173248777281 4936945941331629936582961)
                ·
                  refine ⟨3702709455998722452437221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4936945941331629936582961 3702709455998722452437221)
                  ·
                    refine ⟨694258022999760459831979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3702709455998722452437221 694258022999760459831979)
                    ·
                      rfl

theorem cell23_4056188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4, 2, 2, 4].length) (baseStart_4056188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4056188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4056188 prefixEnd_4056188 := by exact prefixLift 4056188
  have htrace : WordTrace (prefixWord ++ tailWord_4056188) baseStart_4056188 baseEnd_4056188 := by
    simpa [prefixWord, tailWord_4056188, baseEnd_4056188] using wordTrace_append hprefix tailTrace_4056188
  have hstable : (prefixWord ++ tailWord_4056188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4056188).length < 2 ^ (prefixWord ++ tailWord_4056188).sum := by decide
  have hdescent : baseEnd_4056188 < baseStart_4056188 := by decide
  rcases family_descends (prefixWord ++ tailWord_4056188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4056201 : List Nat := [1, 2, 1, 1, 4, 5, 1, 8]
def baseStart_4056201 : Nat := 118140960795 + 4056201 * 2 ^ 59
def prefixEnd_4056201 : Nat := 4983230072969 + 3 ^ 40 * 4056201 * 2
def baseEnd_4056201 : Nat := 77140027564732956616051

theorem tailTrace_4056201 : CollatzResearch.WordTrace tailWord_4056201 prefixEnd_4056201 77140027564732956616051 := by
  unfold tailWord_4056201
  simp only [CollatzResearch.WordTrace]
  refine ⟨147941804378083995823744457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98627869585389330549162971 147941804378083995823744457)
  ·
    refine ⟨110956353283562996867808343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147941804378083995823744457 110956353283562996867808343)
    ·
      refine ⟨166434529925344495301712515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110956353283562996867808343 166434529925344495301712515)
      ·
        refine ⟨249651794888016742952568773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166434529925344495301712515 249651794888016742952568773)
        ·
          refine ⟨46809711541503139303606645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 249651794888016742952568773 46809711541503139303606645)
          ·
            refine ⟨4388410457015919309713123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46809711541503139303606645 4388410457015919309713123)
            ·
              refine ⟨6582615685523878964569685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4388410457015919309713123 6582615685523878964569685)
              ·
                refine ⟨77140027564732956616051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6582615685523878964569685 77140027564732956616051)
                ·
                  rfl

theorem cell23_4056201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 1, 8].length) (baseStart_4056201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4056201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4056201 prefixEnd_4056201 := by exact prefixLift 4056201
  have htrace : WordTrace (prefixWord ++ tailWord_4056201) baseStart_4056201 baseEnd_4056201 := by
    simpa [prefixWord, tailWord_4056201, baseEnd_4056201] using wordTrace_append hprefix tailTrace_4056201
  have hstable : (prefixWord ++ tailWord_4056201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4056201).length < 2 ^ (prefixWord ++ tailWord_4056201).sum := by decide
  have hdescent : baseEnd_4056201 < baseStart_4056201 := by decide
  rcases family_descends (prefixWord ++ tailWord_4056201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4056204 : List Nat := [2, 2, 1, 2, 1, 1, 1, 3, 2, 2, 6]
def baseStart_4056204 : Nat := 118140960795 + 4056204 * 2 ^ 59
def prefixEnd_4056204 : Nat := 4983230072969 + 3 ^ 40 * 4056204 * 2
def baseEnd_4056204 : Nat := 2082782284689753316895863

theorem tailTrace_4056204 : CollatzResearch.WordTrace tailWord_4056204 prefixEnd_4056204 2082782284689753316895863 := by
  unfold tailWord_4056204
  simp only [CollatzResearch.WordTrace]
  refine ⟨73970956898536563668051833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98627942531382084890735777 73970956898536563668051833)
  ·
    refine ⟨55478217673902422751038875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73970956898536563668051833 55478217673902422751038875)
    ·
      refine ⟨83217326510853634126558313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55478217673902422751038875 83217326510853634126558313)
      ·
        refine ⟨62412994883140225594918735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83217326510853634126558313 62412994883140225594918735)
        ·
          refine ⟨93619492324710338392378103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62412994883140225594918735 93619492324710338392378103)
          ·
            refine ⟨140429238487065507588567155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93619492324710338392378103 140429238487065507588567155)
            ·
              refine ⟨210643857730598261382850733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140429238487065507588567155 210643857730598261382850733)
              ·
                refine ⟨78991446648974348018569025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 210643857730598261382850733 78991446648974348018569025)
                ·
                  refine ⟨59243584986730761013926769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78991446648974348018569025 59243584986730761013926769)
                  ·
                    refine ⟨44432688740048070760445077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59243584986730761013926769 44432688740048070760445077)
                    ·
                      refine ⟨2082782284689753316895863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44432688740048070760445077 2082782284689753316895863)
                      ·
                        rfl

theorem cell23_4056204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 2, 2, 6].length) (baseStart_4056204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4056204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4056204 prefixEnd_4056204 := by exact prefixLift 4056204
  have htrace : WordTrace (prefixWord ++ tailWord_4056204) baseStart_4056204 baseEnd_4056204 := by
    simpa [prefixWord, tailWord_4056204, baseEnd_4056204] using wordTrace_append hprefix tailTrace_4056204
  have hstable : (prefixWord ++ tailWord_4056204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4056204).length < 2 ^ (prefixWord ++ tailWord_4056204).sum := by decide
  have hdescent : baseEnd_4056204 < baseStart_4056204 := by decide
  rcases family_descends (prefixWord ++ tailWord_4056204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4056211 : List Nat := [1, 1, 1, 2, 1, 2, 5, 3, 1, 3, 3]
def baseStart_4056211 : Nat := 118140960795 + 4056211 * 2 ^ 59
def prefixEnd_4056211 : Nat := 4983230072969 + 3 ^ 40 * 4056211 * 2
def baseEnd_4056211 : Nat := 2082785879054334789508331

theorem tailTrace_4056211 : CollatzResearch.WordTrace tailWord_4056211 prefixEnd_4056211 2082785879054334789508331 := by
  unfold tailWord_4056211
  simp only [CollatzResearch.WordTrace]
  refine ⟨147942169108047767531608487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98628112738698511687738991 147942169108047767531608487)
  ·
    refine ⟨221913253662071651297412731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147942169108047767531608487 221913253662071651297412731)
    ·
      refine ⟨332869880493107476946119097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221913253662071651297412731 332869880493107476946119097)
      ·
        refine ⟨249652410369830607709589323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 332869880493107476946119097 249652410369830607709589323)
        ·
          refine ⟨374478615554745911564383985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249652410369830607709589323 374478615554745911564383985)
          ·
            refine ⟨280858961666059433673287989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 374478615554745911564383985 280858961666059433673287989)
            ·
              refine ⟨26330527656193071906870749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 280858961666059433673287989 26330527656193071906870749)
              ·
                refine ⟨9873947871072401965076531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26330527656193071906870749 9873947871072401965076531)
                ·
                  refine ⟨14810921806608602947614797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9873947871072401965076531 14810921806608602947614797)
                  ·
                    refine ⟨5554095677478226105355549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14810921806608602947614797 5554095677478226105355549)
                    ·
                      refine ⟨2082785879054334789508331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5554095677478226105355549 2082785879054334789508331)
                      ·
                        rfl

theorem cell23_4056211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 3, 1, 3, 3].length) (baseStart_4056211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4056211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4056211 prefixEnd_4056211 := by exact prefixLift 4056211
  have htrace : WordTrace (prefixWord ++ tailWord_4056211) baseStart_4056211 baseEnd_4056211 := by
    simpa [prefixWord, tailWord_4056211, baseEnd_4056211] using wordTrace_append hprefix tailTrace_4056211
  have hstable : (prefixWord ++ tailWord_4056211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4056211).length < 2 ^ (prefixWord ++ tailWord_4056211).sum := by decide
  have hdescent : baseEnd_4056211 < baseStart_4056211 := by decide
  rcases family_descends (prefixWord ++ tailWord_4056211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4056218 : List Nat := [3, 1, 1, 5, 1, 2, 3, 7]
def baseStart_4056218 : Nat := 118140960795 + 4056218 * 2 ^ 59
def prefixEnd_4056218 : Nat := 4983230072969 + 3 ^ 40 * 4056218 * 2
def baseEnd_4056218 : Nat := 77140350867367268967437

theorem tailTrace_4056218 : CollatzResearch.WordTrace tailWord_4056218 prefixEnd_4056218 77140350867367268967437 := by
  unfold tailWord_4056218
  simp only [CollatzResearch.WordTrace]
  refine ⟨36985606104755601931778327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98628282946014938484742205 36985606104755601931778327)
  ·
    refine ⟨55478409157133402897667491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36985606104755601931778327 55478409157133402897667491)
    ·
      refine ⟨83217613735700104346501237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55478409157133402897667491 83217613735700104346501237)
      ·
        refine ⟨7801651287721884782484491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 83217613735700104346501237 7801651287721884782484491)
        ·
          refine ⟨11702476931582827173726737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7801651287721884782484491 11702476931582827173726737)
          ·
            refine ⟨8776857698687120380295053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11702476931582827173726737 8776857698687120380295053)
            ·
              refine ⟨3291321637007670142610645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8776857698687120380295053 3291321637007670142610645)
              ·
                refine ⟨77140350867367268967437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3291321637007670142610645 77140350867367268967437)
                ·
                  rfl

theorem cell23_4056218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 3, 7].length) (baseStart_4056218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4056218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4056218 prefixEnd_4056218 := by exact prefixLift 4056218
  have htrace : WordTrace (prefixWord ++ tailWord_4056218) baseStart_4056218 baseEnd_4056218 := by
    simpa [prefixWord, tailWord_4056218, baseEnd_4056218] using wordTrace_append hprefix tailTrace_4056218
  have hstable : (prefixWord ++ tailWord_4056218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4056218).length < 2 ^ (prefixWord ++ tailWord_4056218).sum := by decide
  have hdescent : baseEnd_4056218 < baseStart_4056218 := by decide
  rcases family_descends (prefixWord ++ tailWord_4056218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4056228 : List Nat := [2, 3, 1, 2, 3, 1, 2, 2, 1, 3, 3]
def baseStart_4056228 : Nat := 118140960795 + 4056228 * 2 ^ 59
def prefixEnd_4056228 : Nat := 4983230072969 + 3 ^ 40 * 4056228 * 2
def baseEnd_4056228 : Nat := 2082794608225461222995753

theorem tailTrace_4056228 : CollatzResearch.WordTrace tailWord_4056228 prefixEnd_4056228 2082794608225461222995753 := by
  unfold tailWord_4056228
  simp only [CollatzResearch.WordTrace]
  refine ⟨73971394574493089717488669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98628526099324119623318225 73971394574493089717488669)
  ·
    refine ⟨27739272965434908644058251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73971394574493089717488669 27739272965434908644058251)
    ·
      refine ⟨41608909448152362966087377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27739272965434908644058251 41608909448152362966087377)
      ·
        refine ⟨31206682086114272224565533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41608909448152362966087377 31206682086114272224565533)
        ·
          refine ⟨11702505782292852084212075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31206682086114272224565533 11702505782292852084212075)
          ·
            refine ⟨17553758673439278126318113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11702505782292852084212075 17553758673439278126318113)
            ·
              refine ⟨13165319005079458594738585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17553758673439278126318113 13165319005079458594738585)
              ·
                refine ⟨9873989253809593946053939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13165319005079458594738585 9873989253809593946053939)
                ·
                  refine ⟨14810983880714390919080909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9873989253809593946053939 14810983880714390919080909)
                  ·
                    refine ⟨5554118955267896594655341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14810983880714390919080909 5554118955267896594655341)
                    ·
                      refine ⟨2082794608225461222995753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5554118955267896594655341 2082794608225461222995753)
                      ·
                        rfl

theorem cell23_4056228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 2, 1, 3, 3].length) (baseStart_4056228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4056228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4056228 prefixEnd_4056228 := by exact prefixLift 4056228
  have htrace : WordTrace (prefixWord ++ tailWord_4056228) baseStart_4056228 baseEnd_4056228 := by
    simpa [prefixWord, tailWord_4056228, baseEnd_4056228] using wordTrace_append hprefix tailTrace_4056228
  have hstable : (prefixWord ++ tailWord_4056228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4056228).length < 2 ^ (prefixWord ++ tailWord_4056228).sum := by decide
  have hdescent : baseEnd_4056228 < baseStart_4056228 := by decide
  rcases family_descends (prefixWord ++ tailWord_4056228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4056246 : List Nat := [5, 1, 3, 2, 1, 1, 2, 1, 3, 2, 2]
def baseStart_4056246 : Nat := 118140960795 + 4056246 * 2 ^ 59
def prefixEnd_4056246 : Nat := 4983230072969 + 3 ^ 40 * 4056246 * 2
def baseEnd_4056246 : Nat := 2082803850877242152570671

theorem tailTrace_4056246 : CollatzResearch.WordTrace tailWord_4056246 prefixEnd_4056246 2082803850877242152570671 := by
  unfold tailWord_4056246
  simp only [CollatzResearch.WordTrace]
  refine ⟨9246465353932560531820787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 98628963775280645672755061 9246465353932560531820787)
  ·
    refine ⟨13869698030898840797731181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9246465353932560531820787 13869698030898840797731181)
    ·
      refine ⟨5201136761587065299149193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13869698030898840797731181 5201136761587065299149193)
      ·
        refine ⟨3900852571190298974361895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5201136761587065299149193 3900852571190298974361895)
        ·
          refine ⟨5851278856785448461542843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3900852571190298974361895 5851278856785448461542843)
          ·
            refine ⟨8776918285178172692314265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5851278856785448461542843 8776918285178172692314265)
            ·
              refine ⟨6582688713883629519235699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8776918285178172692314265 6582688713883629519235699)
              ·
                refine ⟨9874033070825444278853549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6582688713883629519235699 9874033070825444278853549)
                ·
                  refine ⟨3702762401559541604570081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9874033070825444278853549 3702762401559541604570081)
                  ·
                    refine ⟨2777071801169656203427561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3702762401559541604570081 2777071801169656203427561)
                    ·
                      refine ⟨2082803850877242152570671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2777071801169656203427561 2082803850877242152570671)
                      ·
                        rfl

theorem cell23_4056246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_4056246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4056246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4056246 prefixEnd_4056246 := by exact prefixLift 4056246
  have htrace : WordTrace (prefixWord ++ tailWord_4056246) baseStart_4056246 baseEnd_4056246 := by
    simpa [prefixWord, tailWord_4056246, baseEnd_4056246] using wordTrace_append hprefix tailTrace_4056246
  have hstable : (prefixWord ++ tailWord_4056246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4056246).length < 2 ^ (prefixWord ++ tailWord_4056246).sum := by decide
  have hdescent : baseEnd_4056246 < baseStart_4056246 := by decide
  rcases family_descends (prefixWord ++ tailWord_4056246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4056269 : List Nat := [1, 6, 2, 2, 2, 1, 2, 7]
def baseStart_4056269 : Nat := 118140960795 + 4056269 * 2 ^ 59
def prefixEnd_4056269 : Nat := 4983230072969 + 3 ^ 40 * 4056269 * 2
def baseEnd_4056269 : Nat := 77141320775270206021595

theorem tailTrace_4056269 : CollatzResearch.WordTrace tailWord_4056269 prefixEnd_4056269 77141320775270206021595 := by
  unfold tailWord_4056269
  simp only [CollatzResearch.WordTrace]
  refine ⟨147944284541837643437219861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98629523027891762291479907 147944284541837643437219861)
  ·
    refine ⟨6934888337898639536119681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 147944284541837643437219861 6934888337898639536119681)
    ·
      refine ⟨5201166253423979652089761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6934888337898639536119681 5201166253423979652089761)
      ·
        refine ⟨3900874690067984739067321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5201166253423979652089761 3900874690067984739067321)
        ·
          refine ⟨2925656017550988554300491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3900874690067984739067321 2925656017550988554300491)
          ·
            refine ⟨4388484026326482831450737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2925656017550988554300491 4388484026326482831450737)
            ·
              refine ⟨3291363019744862123588053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4388484026326482831450737 3291363019744862123588053)
              ·
                refine ⟨77141320775270206021595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3291363019744862123588053 77141320775270206021595)
                ·
                  rfl

theorem cell23_4056269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 2, 7].length) (baseStart_4056269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4056269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4056269 prefixEnd_4056269 := by exact prefixLift 4056269
  have htrace : WordTrace (prefixWord ++ tailWord_4056269) baseStart_4056269 baseEnd_4056269 := by
    simpa [prefixWord, tailWord_4056269, baseEnd_4056269] using wordTrace_append hprefix tailTrace_4056269
  have hstable : (prefixWord ++ tailWord_4056269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4056269).length < 2 ^ (prefixWord ++ tailWord_4056269).sum := by decide
  have hdescent : baseEnd_4056269 < baseStart_4056269 := by decide
  rcases family_descends (prefixWord ++ tailWord_4056269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4056319 : List Nat := [1, 1, 2, 2, 1, 7, 2, 1, 2, 2, 2]
def baseStart_4056319 : Nat := 118140960795 + 4056319 * 2 ^ 59
def prefixEnd_4056319 : Nat := 4983230072969 + 3 ^ 40 * 4056319 * 2
def baseEnd_4056319 : Nat := 2082841334965020366957835

theorem tailTrace_4056319 : CollatzResearch.WordTrace tailWord_4056319 prefixEnd_4056319 2082841334965020366957835 := by
  unfold tailWord_4056319
  simp only [CollatzResearch.WordTrace]
  refine ⟨147946108191656501976540011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98630738794437667984360007 147946108191656501976540011)
  ·
    refine ⟨221919162287484752964810017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147946108191656501976540011 221919162287484752964810017)
    ·
      refine ⟨166439371715613564723607513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221919162287484752964810017 166439371715613564723607513)
      ·
        refine ⟨124829528786710173542705635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166439371715613564723607513 124829528786710173542705635)
        ·
          refine ⟨187244293180065260314058453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124829528786710173542705635 187244293180065260314058453)
          ·
            refine ⟨4388538121407779538610745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 187244293180065260314058453 4388538121407779538610745)
            ·
              refine ⟨3291403591055834653958059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4388538121407779538610745 3291403591055834653958059)
              ·
                refine ⟨4937105386583751980937089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3291403591055834653958059 4937105386583751980937089)
                ·
                  refine ⟨3702829039937813985702817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4937105386583751980937089 3702829039937813985702817)
                  ·
                    refine ⟨2777121779953360489277113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3702829039937813985702817 2777121779953360489277113)
                    ·
                      refine ⟨2082841334965020366957835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2777121779953360489277113 2082841334965020366957835)
                      ·
                        rfl

theorem cell23_4056319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 2, 1, 2, 2, 2].length) (baseStart_4056319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4056319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4056319 prefixEnd_4056319 := by exact prefixLift 4056319
  have htrace : WordTrace (prefixWord ++ tailWord_4056319) baseStart_4056319 baseEnd_4056319 := by
    simpa [prefixWord, tailWord_4056319, baseEnd_4056319] using wordTrace_append hprefix tailTrace_4056319
  have hstable : (prefixWord ++ tailWord_4056319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4056319).length < 2 ^ (prefixWord ++ tailWord_4056319).sum := by decide
  have hdescent : baseEnd_4056319 < baseStart_4056319 := by decide
  rcases family_descends (prefixWord ++ tailWord_4056319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4056365 : List Nat := [1, 5, 3, 1, 1, 1, 2, 1, 1, 2, 5]
def baseStart_4056365 : Nat := 118140960795 + 4056365 * 2 ^ 59
def prefixEnd_4056365 : Nat := 4983230072969 + 3 ^ 40 * 4056365 * 2
def baseEnd_4056365 : Nat := 2082864955075127186982623

theorem tailTrace_4056365 : CollatzResearch.WordTrace tailWord_4056365 prefixEnd_4056365 2082864955075127186982623 := by
  unfold tailWord_4056365
  simp only [CollatzResearch.WordTrace]
  refine ⟨147947785949489851832714549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98631857299659901221809699 147947785949489851832714549)
  ·
    refine ⟨13870104932764673609316989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 147947785949489851832714549 13870104932764673609316989)
    ·
      refine ⟨5201289349786752603493871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13870104932764673609316989 5201289349786752603493871)
      ·
        refine ⟨7801934024680128905240807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5201289349786752603493871 7801934024680128905240807)
        ·
          refine ⟨11702901037020193357861211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7801934024680128905240807 11702901037020193357861211)
          ·
            refine ⟨17554351555530290036791817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11702901037020193357861211 17554351555530290036791817)
            ·
              refine ⟨13165763666647717527593863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17554351555530290036791817 13165763666647717527593863)
              ·
                refine ⟨19748645499971576291390795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13165763666647717527593863 19748645499971576291390795)
                ·
                  refine ⟨29622968249957364437086193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19748645499971576291390795 29622968249957364437086193)
                  ·
                    refine ⟨22217226187468023327814645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29622968249957364437086193 22217226187468023327814645)
                    ·
                      refine ⟨2082864955075127186982623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22217226187468023327814645 2082864955075127186982623)
                      ·
                        rfl

theorem cell23_4056365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_4056365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4056365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4056365 prefixEnd_4056365 := by exact prefixLift 4056365
  have htrace : WordTrace (prefixWord ++ tailWord_4056365) baseStart_4056365 baseEnd_4056365 := by
    simpa [prefixWord, tailWord_4056365, baseEnd_4056365] using wordTrace_append hprefix tailTrace_4056365
  have hstable : (prefixWord ++ tailWord_4056365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4056365).length < 2 ^ (prefixWord ++ tailWord_4056365).sum := by decide
  have hdescent : baseEnd_4056365 < baseStart_4056365 := by decide
  rcases family_descends (prefixWord ++ tailWord_4056365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4056368 : List Nat := [2, 1, 1, 1, 2, 2, 4, 3, 3, 4]
def baseStart_4056368 : Nat := 118140960795 + 4056368 * 2 ^ 59
def prefixEnd_4056368 : Nat := 4983230072969 + 3 ^ 40 * 4056368 * 2
def baseEnd_4056368 : Nat := 694288831839030225081703

theorem tailTrace_4056368 : CollatzResearch.WordTrace tailWord_4056368 prefixEnd_4056368 694288831839030225081703 := by
  unfold tailWord_4056368
  simp only [CollatzResearch.WordTrace]
  refine ⟨73973947684239491672536879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98631930245652655563382505 73973947684239491672536879)
  ·
    refine ⟨110960921526359237508805319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73973947684239491672536879 110960921526359237508805319)
    ·
      refine ⟨166441382289538856263207979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110960921526359237508805319 166441382289538856263207979)
      ·
        refine ⟨249662073434308284394811969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166441382289538856263207979 249662073434308284394811969)
        ·
          refine ⟨187246555075731213296108977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 249662073434308284394811969 187246555075731213296108977)
          ·
            refine ⟨140434916306798409972081733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187246555075731213296108977 140434916306798409972081733)
            ·
              refine ⟨26331546807524701869765325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 140434916306798409972081733 26331546807524701869765325)
              ·
                refine ⟨9874330052821763201161997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26331546807524701869765325 9874330052821763201161997)
                ·
                  refine ⟨3702873769808161200435749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9874330052821763201161997 3702873769808161200435749)
                  ·
                    refine ⟨694288831839030225081703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3702873769808161200435749 694288831839030225081703)
                    ·
                      rfl

theorem cell23_4056368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 3, 3, 4].length) (baseStart_4056368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4056368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4056368 prefixEnd_4056368 := by exact prefixLift 4056368
  have htrace : WordTrace (prefixWord ++ tailWord_4056368) baseStart_4056368 baseEnd_4056368 := by
    simpa [prefixWord, tailWord_4056368, baseEnd_4056368] using wordTrace_append hprefix tailTrace_4056368
  have hstable : (prefixWord ++ tailWord_4056368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4056368).length < 2 ^ (prefixWord ++ tailWord_4056368).sum := by decide
  have hdescent : baseEnd_4056368 < baseStart_4056368 := by decide
  rcases family_descends (prefixWord ++ tailWord_4056368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4056378 : List Nat := [3, 1, 1, 1, 4, 1, 2, 2, 1, 4, 3]
def baseStart_4056378 : Nat := 118140960795 + 4056378 * 2 ^ 59
def prefixEnd_4056378 : Nat := 4983230072969 + 3 ^ 40 * 4056378 * 2
def baseEnd_4056378 : Nat := 2082871630323635636120063

theorem tailTrace_4056378 : CollatzResearch.WordTrace tailWord_4056378 prefixEnd_4056378 2082871630323635636120063 := by
  unfold tailWord_4056378
  simp only [CollatzResearch.WordTrace]
  refine ⟨36987065024610688763234447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98632173398961836701958525 36987065024610688763234447)
  ·
    refine ⟨55480597536916033144851671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36987065024610688763234447 55480597536916033144851671)
    ·
      refine ⟨83220896305374049717277507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55480597536916033144851671 83220896305374049717277507)
      ·
        refine ⟨124831344458061074575916261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83220896305374049717277507 124831344458061074575916261)
        ·
          refine ⟨23405877085886451482984299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124831344458061074575916261 23405877085886451482984299)
          ·
            refine ⟨35108815628829677224476449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23405877085886451482984299 35108815628829677224476449)
            ·
              refine ⟨26331611721622257918357337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35108815628829677224476449 26331611721622257918357337)
              ·
                refine ⟨19748708791216693438768003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26331611721622257918357337 19748708791216693438768003)
                ·
                  refine ⟨29623063186825040158152005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19748708791216693438768003 29623063186825040158152005)
                  ·
                    refine ⟨5554324347529695029653501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29623063186825040158152005 5554324347529695029653501)
                    ·
                      refine ⟨2082871630323635636120063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5554324347529695029653501 2082871630323635636120063)
                      ·
                        rfl

theorem cell23_4056378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 2, 1, 4, 3].length) (baseStart_4056378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4056378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4056378 prefixEnd_4056378 := by exact prefixLift 4056378
  have htrace : WordTrace (prefixWord ++ tailWord_4056378) baseStart_4056378 baseEnd_4056378 := by
    simpa [prefixWord, tailWord_4056378, baseEnd_4056378] using wordTrace_append hprefix tailTrace_4056378
  have hstable : (prefixWord ++ tailWord_4056378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4056378).length < 2 ^ (prefixWord ++ tailWord_4056378).sum := by decide
  have hdescent : baseEnd_4056378 < baseStart_4056378 := by decide
  rcases family_descends (prefixWord ++ tailWord_4056378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4056385 : List Nat := [1, 2, 5, 2, 1, 1, 1, 1, 5, 4]
def baseStart_4056385 : Nat := 118140960795 + 4056385 * 2 ^ 59
def prefixEnd_4056385 : Nat := 4983230072969 + 3 ^ 40 * 4056385 * 2
def baseEnd_4056385 : Nat := 694291741562739036244177

theorem tailTrace_4056385 : CollatzResearch.WordTrace tailWord_4056385 prefixEnd_4056385 694291741562739036244177 := by
  unfold tailWord_4056385
  simp only [CollatzResearch.WordTrace]
  refine ⟨147948515409417395248442609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98632343606278263498961739 147948515409417395248442609)
  ·
    refine ⟨110961386557063046436331957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147948515409417395248442609 110961386557063046436331957)
    ·
      refine ⟨10402629989724660603406121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 110961386557063046436331957 10402629989724660603406121)
      ·
        refine ⟨7801972492293495452554591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10402629989724660603406121 7801972492293495452554591)
        ·
          refine ⟨11702958738440243178831887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7801972492293495452554591 11702958738440243178831887)
          ·
            refine ⟨17554438107660364768247831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11702958738440243178831887 17554438107660364768247831)
            ·
              refine ⟨26331657161490547152371747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17554438107660364768247831 26331657161490547152371747)
              ·
                refine ⟨39497485742235820728557621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26331657161490547152371747 39497485742235820728557621)
                ·
                  refine ⟨3702889288334608193302277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39497485742235820728557621 3702889288334608193302277)
                  ·
                    refine ⟨694291741562739036244177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3702889288334608193302277 694291741562739036244177)
                    ·
                      rfl

theorem cell23_4056385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 1, 5, 4].length) (baseStart_4056385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4056385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4056385 prefixEnd_4056385 := by exact prefixLift 4056385
  have htrace : WordTrace (prefixWord ++ tailWord_4056385) baseStart_4056385 baseEnd_4056385 := by
    simpa [prefixWord, tailWord_4056385, baseEnd_4056385] using wordTrace_append hprefix tailTrace_4056385
  have hstable : (prefixWord ++ tailWord_4056385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4056385).length < 2 ^ (prefixWord ++ tailWord_4056385).sum := by decide
  have hdescent : baseEnd_4056385 < baseStart_4056385 := by decide
  rcases family_descends (prefixWord ++ tailWord_4056385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4056418 : List Nat := [3, 3, 2, 1, 1, 1, 1, 1, 1, 1, 8]
def baseStart_4056418 : Nat := 118140960795 + 4056418 * 2 ^ 59
def prefixEnd_4056418 : Nat := 4983230072969 + 3 ^ 40 * 4056418 * 2
def baseEnd_4056418 : Nat := 2082892169549815479619879

theorem tailTrace_4056418 : CollatzResearch.WordTrace tailWord_4056418 prefixEnd_4056418 2082892169549815479619879 := by
  unfold tailWord_4056418
  simp only [CollatzResearch.WordTrace]
  refine ⟨36987429754574460471098477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98633146012198561256262605 36987429754574460471098477)
  ·
    refine ⟨13870286157965422676661929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36987429754574460471098477 13870286157965422676661929)
    ·
      refine ⟨10402714618474067007496447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13870286157965422676661929 10402714618474067007496447)
      ·
        refine ⟨15604071927711100511244671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10402714618474067007496447 15604071927711100511244671)
        ·
          refine ⟨23406107891566650766867007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15604071927711100511244671 23406107891566650766867007)
          ·
            refine ⟨35109161837349976150300511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23406107891566650766867007 35109161837349976150300511)
            ·
              refine ⟨52663742756024964225450767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35109161837349976150300511 52663742756024964225450767)
              ·
                refine ⟨78995614134037446338176151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52663742756024964225450767 78995614134037446338176151)
                ·
                  refine ⟨118493421201056169507264227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78995614134037446338176151 118493421201056169507264227)
                  ·
                    refine ⟨177740131801584254260896341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 118493421201056169507264227 177740131801584254260896341)
                    ·
                      refine ⟨2082892169549815479619879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 177740131801584254260896341 2082892169549815479619879)
                      ·
                        rfl

theorem cell23_4056418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_4056418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4056418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4056418 prefixEnd_4056418 := by exact prefixLift 4056418
  have htrace : WordTrace (prefixWord ++ tailWord_4056418) baseStart_4056418 baseEnd_4056418 := by
    simpa [prefixWord, tailWord_4056418, baseEnd_4056418] using wordTrace_append hprefix tailTrace_4056418
  have hstable : (prefixWord ++ tailWord_4056418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4056418).length < 2 ^ (prefixWord ++ tailWord_4056418).sum := by decide
  have hdescent : baseEnd_4056418 < baseStart_4056418 := by decide
  rcases family_descends (prefixWord ++ tailWord_4056418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4056445 : List Nat := [1, 4, 1, 1, 2, 2, 4, 2, 1, 5]
def baseStart_4056445 : Nat := 118140960795 + 4056445 * 2 ^ 59
def prefixEnd_4056445 : Nat := 4983230072969 + 3 ^ 40 * 4056445 * 2
def baseEnd_4056445 : Nat := 694302011175828957994085

theorem tailTrace_4056445 : CollatzResearch.WordTrace tailWord_4056445 prefixEnd_4056445 694302011175828957994085 := by
  unfold tailWord_4056445
  simp only [CollatzResearch.WordTrace]
  refine ⟨147950703789200025495626789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98633802526133350330417859 147950703789200025495626789)
  ·
    refine ⟨27740756960475004780430023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147950703789200025495626789 27740756960475004780430023)
    ·
      refine ⟨41611135440712507170645035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27740756960475004780430023 41611135440712507170645035)
      ·
        refine ⟨62416703161068760755967553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41611135440712507170645035 62416703161068760755967553)
        ·
          refine ⟨46812527370801570566975665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62416703161068760755967553 46812527370801570566975665)
          ·
            refine ⟨35109395528101177925231749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46812527370801570566975665 35109395528101177925231749)
            ·
              refine ⟨6583011661518970860980953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35109395528101177925231749 6583011661518970860980953)
              ·
                refine ⟨4937258746139228145735715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6583011661518970860980953 4937258746139228145735715)
                ·
                  refine ⟨7405888119208842218603573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4937258746139228145735715 7405888119208842218603573)
                  ·
                    refine ⟨694302011175828957994085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7405888119208842218603573 694302011175828957994085)
                    ·
                      rfl

theorem cell23_4056445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4, 2, 1, 5].length) (baseStart_4056445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4056445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4056445 prefixEnd_4056445 := by exact prefixLift 4056445
  have htrace : WordTrace (prefixWord ++ tailWord_4056445) baseStart_4056445 baseEnd_4056445 := by
    simpa [prefixWord, tailWord_4056445, baseEnd_4056445] using wordTrace_append hprefix tailTrace_4056445
  have hstable : (prefixWord ++ tailWord_4056445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4056445).length < 2 ^ (prefixWord ++ tailWord_4056445).sum := by decide
  have hdescent : baseEnd_4056445 < baseStart_4056445 := by decide
  rcases family_descends (prefixWord ++ tailWord_4056445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4056448 : List Nat := [2, 1, 1, 2, 1, 2, 1, 5, 3, 1, 4]
def baseStart_4056448 : Nat := 118140960795 + 4056448 * 2 ^ 59
def prefixEnd_4056448 : Nat := 4983230072969 + 3 ^ 40 * 4056448 * 2
def baseEnd_4056448 : Nat := 2082907573969450362244741

theorem tailTrace_4056448 : CollatzResearch.WordTrace tailWord_4056448 prefixEnd_4056448 2082907573969450362244741 := by
  unfold tailWord_4056448
  simp only [CollatzResearch.WordTrace]
  refine ⟨73975406604094578503992999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98633875472126104671990665 73975406604094578503992999)
  ·
    refine ⟨110963109906141867755989499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73975406604094578503992999 110963109906141867755989499)
    ·
      refine ⟨166444664859212801633984249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110963109906141867755989499 166444664859212801633984249)
      ·
        refine ⟨124833498644409601225488187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166444664859212801633984249 124833498644409601225488187)
        ·
          refine ⟨187250247966614401838232281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124833498644409601225488187 187250247966614401838232281)
          ·
            refine ⟨140437685974960801378674211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187250247966614401838232281 140437685974960801378674211)
            ·
              refine ⟨210656528962441202068011317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140437685974960801378674211 210656528962441202068011317)
              ·
                refine ⟨19749049590228862693876061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 210656528962441202068011317 19749049590228862693876061)
                ·
                  refine ⟨7405893596335823510203523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19749049590228862693876061 7405893596335823510203523)
                  ·
                    refine ⟨11108840394503735265305285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7405893596335823510203523 11108840394503735265305285)
                    ·
                      refine ⟨2082907573969450362244741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11108840394503735265305285 2082907573969450362244741)
                      ·
                        rfl

theorem cell23_4056448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 5, 3, 1, 4].length) (baseStart_4056448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4056448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4056448 prefixEnd_4056448 := by exact prefixLift 4056448
  have htrace : WordTrace (prefixWord ++ tailWord_4056448) baseStart_4056448 baseEnd_4056448 := by
    simpa [prefixWord, tailWord_4056448, baseEnd_4056448] using wordTrace_append hprefix tailTrace_4056448
  have hstable : (prefixWord ++ tailWord_4056448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4056448).length < 2 ^ (prefixWord ++ tailWord_4056448).sum := by decide
  have hdescent : baseEnd_4056448 < baseStart_4056448 := by decide
  rcases family_descends (prefixWord ++ tailWord_4056448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
