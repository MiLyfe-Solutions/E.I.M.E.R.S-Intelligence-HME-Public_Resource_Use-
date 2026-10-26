import V185TrunkScan21Chunk120

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_1472583 : List Nat := [1, 1, 4, 1, 3, 1, 1, 3, 6]
def baseStart_1472583 : Nat := 118140960795 + 1472583 * 2 ^ 59
def prefixEnd_1472583 : Nat := 4983230072969 + 3 ^ 40 * 1472583 * 2
def baseEnd_1472583 : Nat := 336063503395518775973431

theorem tailTrace_1472583 : CollatzResearch.WordTrace tailWord_1472583 prefixEnd_1472583 336063503395518775973431 := by
  unfold tailWord_1472583
  simp only [CollatzResearch.WordTrace]
  refine ⟨53709514424090762998798403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35806342949393841999198935 53709514424090762998798403)
  ·
    refine ⟨80564271636136144498197605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53709514424090762998798403 80564271636136144498197605)
    ·
      refine ⟨15105800931775527093412051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80564271636136144498197605 15105800931775527093412051)
      ·
        refine ⟨22658701397663290640118077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15105800931775527093412051 22658701397663290640118077)
        ·
          refine ⟨8497013024123733990044279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22658701397663290640118077 8497013024123733990044279)
          ·
            refine ⟨12745519536185600985066419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8497013024123733990044279 12745519536185600985066419)
            ·
              refine ⟨19118279304278401477599629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12745519536185600985066419 19118279304278401477599629)
              ·
                refine ⟨7169354739104400554099861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19118279304278401477599629 7169354739104400554099861)
                ·
                  refine ⟨336063503395518775973431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7169354739104400554099861 336063503395518775973431)
                  ·
                    rfl

theorem cell21_1472583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 3, 6].length) (baseStart_1472583 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1472583 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1472583 prefixEnd_1472583 := by exact prefixLift 1472583
  have htrace : WordTrace (prefixWord ++ tailWord_1472583) baseStart_1472583 baseEnd_1472583 := by
    simpa [prefixWord, tailWord_1472583, baseEnd_1472583] using wordTrace_append hprefix tailTrace_1472583
  have hstable : (prefixWord ++ tailWord_1472583).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1472583).length < 2 ^ (prefixWord ++ tailWord_1472583).sum := by decide
  have hdescent : baseEnd_1472583 < baseStart_1472583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1472583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1472600 : List Nat := [2, 1, 2, 2, 1, 5, 1, 3, 4]
def baseStart_1472600 : Nat := 118140960795 + 1472600 * 2 ^ 59
def prefixEnd_1472600 : Nat := 4983230072969 + 3 ^ 40 * 1472600 * 2
def baseEnd_1472600 : Nat := 336067383027130524190063

theorem tailTrace_1472600 : CollatzResearch.WordTrace tailWord_1472600 prefixEnd_1472600 336067383027130524190063 := by
  unfold tailWord_1472600
  simp only [CollatzResearch.WordTrace]
  refine ⟨26855067232514587451083627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35806756310019449934778169 26855067232514587451083627)
  ·
    refine ⟨40282600848771881176625441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26855067232514587451083627 40282600848771881176625441)
    ·
      refine ⟨30211950636578910882469081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40282600848771881176625441 30211950636578910882469081)
      ·
        refine ⟨22658962977434183161851811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30211950636578910882469081 22658962977434183161851811)
        ·
          refine ⟨33988444466151274742777717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22658962977434183161851811 33988444466151274742777717)
          ·
            refine ⟨3186416668701682007135411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 33988444466151274742777717 3186416668701682007135411)
            ·
              refine ⟨4779625003052523010703117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3186416668701682007135411 4779625003052523010703117)
              ·
                refine ⟨1792359376144696129013669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4779625003052523010703117 1792359376144696129013669)
                ·
                  refine ⟨336067383027130524190063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1792359376144696129013669 336067383027130524190063)
                  ·
                    rfl

theorem cell21_1472600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 3, 4].length) (baseStart_1472600 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1472600 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1472600 prefixEnd_1472600 := by exact prefixLift 1472600
  have htrace : WordTrace (prefixWord ++ tailWord_1472600) baseStart_1472600 baseEnd_1472600 := by
    simpa [prefixWord, tailWord_1472600, baseEnd_1472600] using wordTrace_append hprefix tailTrace_1472600
  have hstable : (prefixWord ++ tailWord_1472600).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1472600).length < 2 ^ (prefixWord ++ tailWord_1472600).sum := by decide
  have hdescent : baseEnd_1472600 < baseStart_1472600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1472600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1472693 : List Nat := [1, 3, 3, 4, 1, 1, 1, 1, 6]
def baseStart_1472693 : Nat := 118140960795 + 1472693 * 2 ^ 59
def prefixEnd_1472693 : Nat := 4983230072969 + 3 ^ 40 * 1472693 * 2
def baseEnd_1472693 : Nat := 336088606894183029139873

theorem tailTrace_1472693 : CollatzResearch.WordTrace tailWord_1472693 prefixEnd_1472693 336088606894183029139873 := by
  unfold tailWord_1472693
  simp only [CollatzResearch.WordTrace]
  refine ⟨53713526453692251785302733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35809017635794834523535155 53713526453692251785302733)
  ·
    refine ⟨20142572420134594419488525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53713526453692251785302733 20142572420134594419488525)
    ·
      refine ⟨7553464657550472907308197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20142572420134594419488525 7553464657550472907308197)
      ·
        refine ⟨1416274623290713670120287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7553464657550472907308197 1416274623290713670120287)
        ·
          refine ⟨2124411934936070505180431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1416274623290713670120287 2124411934936070505180431)
          ·
            refine ⟨3186617902404105757770647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2124411934936070505180431 3186617902404105757770647)
            ·
              refine ⟨4779926853606158636655971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3186617902404105757770647 4779926853606158636655971)
              ·
                refine ⟨7169890280409237954983957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4779926853606158636655971 7169890280409237954983957)
                ·
                  refine ⟨336088606894183029139873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7169890280409237954983957 336088606894183029139873)
                  ·
                    rfl

theorem cell21_1472693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 1, 6].length) (baseStart_1472693 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1472693 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1472693 prefixEnd_1472693 := by exact prefixLift 1472693
  have htrace : WordTrace (prefixWord ++ tailWord_1472693) baseStart_1472693 baseEnd_1472693 := by
    simpa [prefixWord, tailWord_1472693, baseEnd_1472693] using wordTrace_append hprefix tailTrace_1472693
  have hstable : (prefixWord ++ tailWord_1472693).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1472693).length < 2 ^ (prefixWord ++ tailWord_1472693).sum := by decide
  have hdescent : baseEnd_1472693 < baseStart_1472693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1472693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1472780 : List Nat := [2, 2, 1, 2, 2, 2, 2, 1, 7]
def baseStart_1472780 : Nat := 118140960795 + 1472780 * 2 ^ 59
def prefixEnd_1472780 : Nat := 4983230072969 + 3 ^ 40 * 1472780 * 2
def baseEnd_1472780 : Nat := 336108461479490211189695

theorem tailTrace_1472780 : CollatzResearch.WordTrace tailWord_1472780 prefixEnd_1472780 336108461479490211189695 := by
  unfold tailWord_1472780
  simp only [CollatzResearch.WordTrace]
  refine ⟨26858349802188532821859897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35811133069584710429146529 26858349802188532821859897)
  ·
    refine ⟨20143762351641399616394923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26858349802188532821859897 20143762351641399616394923)
    ·
      refine ⟨30215643527462099424592385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20143762351641399616394923 30215643527462099424592385)
      ·
        refine ⟨22661732645596574568444289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30215643527462099424592385 22661732645596574568444289)
        ·
          refine ⟨16996299484197430926333217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22661732645596574568444289 16996299484197430926333217)
          ·
            refine ⟨12747224613148073194749913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16996299484197430926333217 12747224613148073194749913)
            ·
              refine ⟨9560418459861054896062435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12747224613148073194749913 9560418459861054896062435)
              ·
                refine ⟨14340627689791582344093653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9560418459861054896062435 14340627689791582344093653)
                ·
                  refine ⟨336108461479490211189695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14340627689791582344093653 336108461479490211189695)
                  ·
                    rfl

theorem cell21_1472780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 1, 7].length) (baseStart_1472780 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1472780 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1472780 prefixEnd_1472780 := by exact prefixLift 1472780
  have htrace : WordTrace (prefixWord ++ tailWord_1472780) baseStart_1472780 baseEnd_1472780 := by
    simpa [prefixWord, tailWord_1472780, baseEnd_1472780] using wordTrace_append hprefix tailTrace_1472780
  have hstable : (prefixWord ++ tailWord_1472780).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1472780).length < 2 ^ (prefixWord ++ tailWord_1472780).sum := by decide
  have hdescent : baseEnd_1472780 < baseStart_1472780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1472780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1472873 : List Nat := [1, 2, 1, 1, 1, 3, 3, 6, 3]
def baseStart_1472873 : Nat := 118140960795 + 1472873 * 2 ^ 59
def prefixEnd_1472873 : Nat := 4983230072969 + 3 ^ 40 * 1472873 * 2
def baseEnd_1472873 : Nat := 336129685346542716139505

theorem tailTrace_1472873 : CollatzResearch.WordTrace tailWord_1472873 prefixEnd_1472873 336129685346542716139505 := by
  unfold tailWord_1472873
  simp only [CollatzResearch.WordTrace]
  refine ⟨53720091593040142526855273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35813394395360095017903515 53720091593040142526855273)
  ·
    refine ⟨40290068694780106895141455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53720091593040142526855273 40290068694780106895141455)
    ·
      refine ⟨60435103042170160342712183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40290068694780106895141455 60435103042170160342712183)
      ·
        refine ⟨90652654563255240514068275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60435103042170160342712183 90652654563255240514068275)
        ·
          refine ⟨135978981844882860771102413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90652654563255240514068275 135978981844882860771102413)
          ·
            refine ⟨50992118191831072789163405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 135978981844882860771102413 50992118191831072789163405)
            ·
              refine ⟨19122044321936652295936277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50992118191831072789163405 19122044321936652295936277)
              ·
                refine ⟨896345827590780576372013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 19122044321936652295936277 896345827590780576372013)
                ·
                  refine ⟨336129685346542716139505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 896345827590780576372013 336129685346542716139505)
                  ·
                    rfl

theorem cell21_1472873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 6, 3].length) (baseStart_1472873 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1472873 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1472873 prefixEnd_1472873 := by exact prefixLift 1472873
  have htrace : WordTrace (prefixWord ++ tailWord_1472873) baseStart_1472873 baseEnd_1472873 := by
    simpa [prefixWord, tailWord_1472873, baseEnd_1472873] using wordTrace_append hprefix tailTrace_1472873
  have hstable : (prefixWord ++ tailWord_1472873).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1472873).length < 2 ^ (prefixWord ++ tailWord_1472873).sum := by decide
  have hdescent : baseEnd_1472873 < baseStart_1472873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1472873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1472980 : List Nat := [2, 4, 1, 2, 2, 1, 1, 4, 4]
def baseStart_1472980 : Nat := 118140960795 + 1472980 * 2 ^ 59
def prefixEnd_1472980 : Nat := 4983230072969 + 3 ^ 40 * 1472980 * 2
def baseEnd_1472980 : Nat := 336154104204334307855953

theorem tailTrace_1472980 : CollatzResearch.WordTrace tailWord_1472980 prefixEnd_1472980 336154104204334307855953 := by
  unfold tailWord_1472980
  simp only [CollatzResearch.WordTrace]
  refine ⟨26861997101826249900500197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35815996135768333200666929 26861997101826249900500197)
  ·
    refine ⟨5036624456592421856343787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26861997101826249900500197 5036624456592421856343787)
    ·
      refine ⟨7554936684888632784515681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5036624456592421856343787 7554936684888632784515681)
      ·
        refine ⟨5666202513666474588386761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7554936684888632784515681 5666202513666474588386761)
        ·
          refine ⟨4249651885249855941290071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5666202513666474588386761 4249651885249855941290071)
          ·
            refine ⟨6374477827874783911935107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4249651885249855941290071 6374477827874783911935107)
            ·
              refine ⟨9561716741812175867902661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6374477827874783911935107 9561716741812175867902661)
              ·
                refine ⟨1792821889089782975231749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9561716741812175867902661 1792821889089782975231749)
                ·
                  refine ⟨336154104204334307855953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1792821889089782975231749 336154104204334307855953)
                  ·
                    rfl

theorem cell21_1472980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 4, 4].length) (baseStart_1472980 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1472980 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1472980 prefixEnd_1472980 := by exact prefixLift 1472980
  have htrace : WordTrace (prefixWord ++ tailWord_1472980) baseStart_1472980 baseEnd_1472980 := by
    simpa [prefixWord, tailWord_1472980, baseEnd_1472980] using wordTrace_append hprefix tailTrace_1472980
  have hstable : (prefixWord ++ tailWord_1472980).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1472980).length < 2 ^ (prefixWord ++ tailWord_1472980).sum := by decide
  have hdescent : baseEnd_1472980 < baseStart_1472980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1472980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473008 : List Nat := [2, 1, 1, 1, 3, 3, 3, 2, 5]
def baseStart_1473008 : Nat := 118140960795 + 1473008 * 2 ^ 59
def prefixEnd_1473008 : Nat := 4983230072969 + 3 ^ 40 * 1473008 * 2
def baseEnd_1473008 : Nat := 336160494185812481389229

theorem tailTrace_1473008 : CollatzResearch.WordTrace tailWord_1473008 prefixEnd_1473008 336160494185812481389229 := by
  unfold tailWord_1473008
  simp only [CollatzResearch.WordTrace]
  refine ⟨26862507723775530291509839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35816676965034040388679785 26862507723775530291509839)
  ·
    refine ⟨40293761585663295437264759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26862507723775530291509839 40293761585663295437264759)
    ·
      refine ⟨60440642378494943155897139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40293761585663295437264759 60440642378494943155897139)
      ·
        refine ⟨90660963567742414733845709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60440642378494943155897139 90660963567742414733845709)
        ·
          refine ⟨33997861337903405525192141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90660963567742414733845709 33997861337903405525192141)
          ·
            refine ⟨12749198001713777071947053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33997861337903405525192141 12749198001713777071947053)
            ·
              refine ⟨4780949250642666401980145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12749198001713777071947053 4780949250642666401980145)
              ·
                refine ⟨3585711937981999801485109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4780949250642666401980145 3585711937981999801485109)
                ·
                  refine ⟨336160494185812481389229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3585711937981999801485109 336160494185812481389229)
                  ·
                    rfl

theorem cell21_1473008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 2, 5].length) (baseStart_1473008 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1473008 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1473008 prefixEnd_1473008 := by exact prefixLift 1473008
  have htrace : WordTrace (prefixWord ++ tailWord_1473008) baseStart_1473008 baseEnd_1473008 := by
    simpa [prefixWord, tailWord_1473008, baseEnd_1473008] using wordTrace_append hprefix tailTrace_1473008
  have hstable : (prefixWord ++ tailWord_1473008).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473008).length < 2 ^ (prefixWord ++ tailWord_1473008).sum := by decide
  have hdescent : baseEnd_1473008 < baseStart_1473008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473295 : List Nat := [1, 1, 2, 1, 1, 1, 6, 1, 7]
def baseStart_1473295 : Nat := 118140960795 + 1473295 * 2 ^ 59
def prefixEnd_1473295 : Nat := 4983230072969 + 3 ^ 40 * 1473295 * 2
def baseEnd_1473295 : Nat := 336225991495963760105309

theorem tailTrace_1473295 : CollatzResearch.WordTrace tailWord_1473295 prefixEnd_1473295 336225991495963760105309 := by
  unfold tailWord_1473295
  simp only [CollatzResearch.WordTrace]
  refine ⟨53735483197511308598717339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35823655465007539065811559 53735483197511308598717339)
  ·
    refine ⟨80603224796266962898076009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53735483197511308598717339 80603224796266962898076009)
    ·
      refine ⟨60452418597200222173557007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80603224796266962898076009 60452418597200222173557007)
      ·
        refine ⟨90678627895800333260335511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60452418597200222173557007 90678627895800333260335511)
        ·
          refine ⟨136017941843700499890503267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90678627895800333260335511 136017941843700499890503267)
          ·
            refine ⟨204026912765550749835754901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136017941843700499890503267 204026912765550749835754901)
            ·
              refine ⟨9563761535885191398551011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 204026912765550749835754901 9563761535885191398551011)
              ·
                refine ⟨14345642303827787097826517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9563761535885191398551011 14345642303827787097826517)
                ·
                  refine ⟨336225991495963760105309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14345642303827787097826517 336225991495963760105309)
                  ·
                    rfl

theorem cell21_1473295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 1, 7].length) (baseStart_1473295 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1473295 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1473295 prefixEnd_1473295 := by exact prefixLift 1473295
  have htrace : WordTrace (prefixWord ++ tailWord_1473295) baseStart_1473295 baseEnd_1473295 := by
    simpa [prefixWord, tailWord_1473295, baseEnd_1473295] using wordTrace_append hprefix tailTrace_1473295
  have hstable : (prefixWord ++ tailWord_1473295).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473295).length < 2 ^ (prefixWord ++ tailWord_1473295).sum := by decide
  have hdescent : baseEnd_1473295 < baseStart_1473295 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473329 : List Nat := [1, 2, 2, 3, 2, 1, 3, 4, 3]
def baseStart_1473329 : Nat := 118140960795 + 1473329 * 2 ^ 59
def prefixEnd_1473329 : Nat := 4983230072969 + 3 ^ 40 * 1473329 * 2
def baseEnd_1473329 : Nat := 336233750759187256538573

theorem tailTrace_1473329 : CollatzResearch.WordTrace tailWord_1473329 prefixEnd_1473329 336233750759187256538573 := by
  unfold tailWord_1473329
  simp only [CollatzResearch.WordTrace]
  refine ⟨53736723279388132405455041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35824482186258754936970027 53736723279388132405455041)
  ·
    refine ⟨40302542459541099304091281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53736723279388132405455041 40302542459541099304091281)
    ·
      refine ⟨30226906844655824478068461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40302542459541099304091281 30226906844655824478068461)
      ·
        refine ⟨11335090066745934179275673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30226906844655824478068461 11335090066745934179275673)
        ·
          refine ⟨8501317550059450634456755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11335090066745934179275673 8501317550059450634456755)
          ·
            refine ⟨12751976325089175951685133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8501317550059450634456755 12751976325089175951685133)
            ·
              refine ⟨4781991121908440981881925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12751976325089175951685133 4781991121908440981881925)
              ·
                refine ⟨896623335357832684102861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4781991121908440981881925 896623335357832684102861)
                ·
                  refine ⟨336233750759187256538573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 896623335357832684102861 336233750759187256538573)
                  ·
                    rfl

theorem cell21_1473329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 4, 3].length) (baseStart_1473329 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1473329 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1473329 prefixEnd_1473329 := by exact prefixLift 1473329
  have htrace : WordTrace (prefixWord ++ tailWord_1473329) baseStart_1473329 baseEnd_1473329 := by
    simpa [prefixWord, tailWord_1473329, baseEnd_1473329] using wordTrace_append hprefix tailTrace_1473329
  have hstable : (prefixWord ++ tailWord_1473329).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473329).length < 2 ^ (prefixWord ++ tailWord_1473329).sum := by decide
  have hdescent : baseEnd_1473329 < baseStart_1473329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473332 : List Nat := [2, 5, 1, 1, 4, 1, 1, 6]
def baseStart_1473332 : Nat := 118140960795 + 1473332 * 2 ^ 59
def prefixEnd_1473332 : Nat := 4983230072969 + 3 ^ 40 * 1473332 * 2
def baseEnd_1473332 : Nat := 112078145133353305996189

theorem tailTrace_1473332 : CollatzResearch.WordTrace tailWord_1473332 prefixEnd_1473332 112078145133353305996189 := by
  unfold tailWord_1473332
  simp only [CollatzResearch.WordTrace]
  refine ⟨26868416349188631958907125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35824555132251509278542833 26868416349188631958907125)
  ·
    refine ⟨2518914032736434246147543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26868416349188631958907125 2518914032736434246147543)
    ·
      refine ⟨3778371049104651369221315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2518914032736434246147543 3778371049104651369221315)
      ·
        refine ⟨5667556573656977053831973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3778371049104651369221315 5667556573656977053831973)
        ·
          refine ⟨1062666857560683197593495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5667556573656977053831973 1062666857560683197593495)
          ·
            refine ⟨1594000286341024796390243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1062666857560683197593495 1594000286341024796390243)
            ·
              refine ⟨2391000429511537194585365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1594000286341024796390243 2391000429511537194585365)
              ·
                refine ⟨112078145133353305996189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2391000429511537194585365 112078145133353305996189)
                ·
                  rfl

theorem cell21_1473332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 1, 6].length) (baseStart_1473332 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1473332 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1473332 prefixEnd_1473332 := by exact prefixLift 1473332
  have htrace : WordTrace (prefixWord ++ tailWord_1473332) baseStart_1473332 baseEnd_1473332 := by
    simpa [prefixWord, tailWord_1473332, baseEnd_1473332] using wordTrace_append hprefix tailTrace_1473332
  have hstable : (prefixWord ++ tailWord_1473332).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473332).length < 2 ^ (prefixWord ++ tailWord_1473332).sum := by decide
  have hdescent : baseEnd_1473332 < baseStart_1473332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473343 : List Nat := [1, 1, 2, 2, 5, 1, 2, 3, 4]
def baseStart_1473343 : Nat := 118140960795 + 1473343 * 2 ^ 59
def prefixEnd_1473343 : Nat := 4983230072969 + 3 ^ 40 * 1473343 * 2
def baseEnd_1473343 : Nat := 336236945749926343305211

theorem tailTrace_1473343 : CollatzResearch.WordTrace tailWord_1473343 prefixEnd_1473343 336236945749926343305211 := by
  unfold tailWord_1473343
  simp only [CollatzResearch.WordTrace]
  refine ⟨53737233901337412796464683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35824822600891608530976455 53737233901337412796464683)
  ·
    refine ⟨80605850852006119194697025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53737233901337412796464683 80605850852006119194697025)
    ·
      refine ⟨60454388139004589396022769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80605850852006119194697025 60454388139004589396022769)
      ·
        refine ⟨45340791104253442047017077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60454388139004589396022769 45340791104253442047017077)
        ·
          refine ⟨4250699166023760191907851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45340791104253442047017077 4250699166023760191907851)
          ·
            refine ⟨6376048749035640287861777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4250699166023760191907851 6376048749035640287861777)
            ·
              refine ⟨4782036561776730215896333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6376048749035640287861777 4782036561776730215896333)
              ·
                refine ⟨1793263710666273830961125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4782036561776730215896333 1793263710666273830961125)
                ·
                  refine ⟨336236945749926343305211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1793263710666273830961125 336236945749926343305211)
                  ·
                    rfl

theorem cell21_1473343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 3, 4].length) (baseStart_1473343 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1473343 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1473343 prefixEnd_1473343 := by exact prefixLift 1473343
  have htrace : WordTrace (prefixWord ++ tailWord_1473343) baseStart_1473343 baseEnd_1473343 := by
    simpa [prefixWord, tailWord_1473343, baseEnd_1473343] using wordTrace_append hprefix tailTrace_1473343
  have hstable : (prefixWord ++ tailWord_1473343).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473343).length < 2 ^ (prefixWord ++ tailWord_1473343).sum := by decide
  have hdescent : baseEnd_1473343 < baseStart_1473343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473388 : List Nat := [2, 2, 1, 1, 4, 1, 4, 1, 5]
def baseStart_1473388 : Nat := 118140960795 + 1473388 * 2 ^ 59
def prefixEnd_1473388 : Nat := 4983230072969 + 3 ^ 40 * 1473388 * 2
def baseEnd_1473388 : Nat := 336247215363016265055119

theorem tailTrace_1473388 : CollatzResearch.WordTrace tailWord_1473388 prefixEnd_1473388 336247215363016265055119 := by
  unfold tailWord_1473388
  simp only [CollatzResearch.WordTrace]
  refine ⟨26869437593087192740926409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35825916790782923654568545 26869437593087192740926409)
  ·
    refine ⟨20152078194815394555694807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26869437593087192740926409 20152078194815394555694807)
    ·
      refine ⟨30228117292223091833542211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20152078194815394555694807 30228117292223091833542211)
      ·
        refine ⟨45342175938334637750313317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30228117292223091833542211 45342175938334637750313317)
        ·
          refine ⟨8501657988437744578183747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45342175938334637750313317 8501657988437744578183747)
          ·
            refine ⟨12752486982656616867275621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8501657988437744578183747 12752486982656616867275621)
            ·
              refine ⟨2391091309248115662614179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12752486982656616867275621 2391091309248115662614179)
              ·
                refine ⟨3586636963872173493921269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2391091309248115662614179 3586636963872173493921269)
                ·
                  refine ⟨336247215363016265055119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3586636963872173493921269 336247215363016265055119)
                  ·
                    rfl

theorem cell21_1473388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 5].length) (baseStart_1473388 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1473388 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1473388 prefixEnd_1473388 := by exact prefixLift 1473388
  have htrace : WordTrace (prefixWord ++ tailWord_1473388) baseStart_1473388 baseEnd_1473388 := by
    simpa [prefixWord, tailWord_1473388, baseEnd_1473388] using wordTrace_append hprefix tailTrace_1473388
  have hstable : (prefixWord ++ tailWord_1473388).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473388).length < 2 ^ (prefixWord ++ tailWord_1473388).sum := by decide
  have hdescent : baseEnd_1473388 < baseStart_1473388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473453 : List Nat := [1, 5, 2, 3, 1, 1, 1, 3, 4]
def baseStart_1473453 : Nat := 118140960795 + 1473453 * 2 ^ 59
def prefixEnd_1473453 : Nat := 4983230072969 + 3 ^ 40 * 1473453 * 2
def baseEnd_1473453 : Nat := 336262049248590596471653

theorem tailTrace_1473453 : CollatzResearch.WordTrace tailWord_1473453 prefixEnd_1473453 336262049248590596471653 := by
  unfold tailWord_1473453
  simp only [CollatzResearch.WordTrace]
  refine ⟨53741245930938901582969013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35827497287292601055312675 53741245930938901582969013)
  ·
    refine ⟨5038241806025522023403345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 53741245930938901582969013 5038241806025522023403345)
    ·
      refine ⟨3778681354519141517552509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5038241806025522023403345 3778681354519141517552509)
      ·
        refine ⟨1417005507944678069082191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3778681354519141517552509 1417005507944678069082191)
        ·
          refine ⟨2125508261917017103623287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1417005507944678069082191 2125508261917017103623287)
          ·
            refine ⟨3188262392875525655434931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2125508261917017103623287 3188262392875525655434931)
            ·
              refine ⟨4782393589313288483152397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3188262392875525655434931 4782393589313288483152397)
              ·
                refine ⟨1793397595992483181182149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4782393589313288483152397 1793397595992483181182149)
                ·
                  refine ⟨336262049248590596471653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1793397595992483181182149 336262049248590596471653)
                  ·
                    rfl

theorem cell21_1473453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 3, 4].length) (baseStart_1473453 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1473453 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1473453 prefixEnd_1473453 := by exact prefixLift 1473453
  have htrace : WordTrace (prefixWord ++ tailWord_1473453) baseStart_1473453 baseEnd_1473453 := by
    simpa [prefixWord, tailWord_1473453, baseEnd_1473453] using wordTrace_append hprefix tailTrace_1473453
  have hstable : (prefixWord ++ tailWord_1473453).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473453).length < 2 ^ (prefixWord ++ tailWord_1473453).sum := by decide
  have hdescent : baseEnd_1473453 < baseStart_1473453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473498 : List Nat := [3, 1, 1, 2, 4, 1, 4, 2, 3]
def baseStart_1473498 : Nat := 118140960795 + 1473498 * 2 ^ 59
def prefixEnd_1473498 : Nat := 4983230072969 + 3 ^ 40 * 1473498 * 2
def baseEnd_1473498 : Nat := 336272318861680518221561

theorem tailTrace_1473498 : CollatzResearch.WordTrace tailWord_1473498 prefixEnd_1473498 336272318861680518221561 := by
  unfold tailWord_1473498
  simp only [CollatzResearch.WordTrace]
  refine ⟨13435721803943968567089287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35828591477183916178904765 13435721803943968567089287)
  ·
    refine ⟨20153582705915952850633931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13435721803943968567089287 20153582705915952850633931)
    ·
      refine ⟨30230374058873929275950897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20153582705915952850633931 30230374058873929275950897)
      ·
        refine ⟨22672780544155446956963173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30230374058873929275950897 22672780544155446956963173)
        ·
          refine ⟨4251146352029146304430595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22672780544155446956963173 4251146352029146304430595)
          ·
            refine ⟨6376719528043719456645893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4251146352029146304430595 6376719528043719456645893)
            ·
              refine ⟨1195634911508197398121105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6376719528043719456645893 1195634911508197398121105)
              ·
                refine ⟨896726183631148048590829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1195634911508197398121105 896726183631148048590829)
                ·
                  refine ⟨336272318861680518221561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 896726183631148048590829 336272318861680518221561)
                  ·
                    rfl

theorem cell21_1473498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 4, 2, 3].length) (baseStart_1473498 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1473498 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1473498 prefixEnd_1473498 := by exact prefixLift 1473498
  have htrace : WordTrace (prefixWord ++ tailWord_1473498) baseStart_1473498 baseEnd_1473498 := by
    simpa [prefixWord, tailWord_1473498, baseEnd_1473498] using wordTrace_append hprefix tailTrace_1473498
  have hstable : (prefixWord ++ tailWord_1473498).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473498).length < 2 ^ (prefixWord ++ tailWord_1473498).sum := by decide
  have hdescent : baseEnd_1473498 < baseStart_1473498 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473557 : List Nat := [1, 3, 2, 1, 4, 1, 2, 4, 3]
def baseStart_1473557 : Nat := 118140960795 + 1473557 * 2 ^ 59
def prefixEnd_1473557 : Nat := 4983230072969 + 3 ^ 40 * 1473557 * 2
def baseEnd_1473557 : Nat := 336285783465509526738107

theorem tailTrace_1473557 : CollatzResearch.WordTrace tailWord_1473557 prefixEnd_1473557 336285783465509526738107 := by
  unfold tailWord_1473557
  simp only [CollatzResearch.WordTrace]
  refine ⟨53745039122562127344754925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35830026081708084896503283 53745039122562127344754925)
  ·
    refine ⟨20154389670960797754283097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53745039122562127344754925 20154389670960797754283097)
    ·
      refine ⟨15115792253220598315712323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20154389670960797754283097 15115792253220598315712323)
      ·
        refine ⟨22673688379830897473568485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15115792253220598315712323 22673688379830897473568485)
        ·
          refine ⟨4251316571218293276294091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22673688379830897473568485 4251316571218293276294091)
          ·
            refine ⟨6376974856827439914441137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4251316571218293276294091 6376974856827439914441137)
            ·
              refine ⟨4782731142620579935830853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6376974856827439914441137 4782731142620579935830853)
              ·
                refine ⟨896762089241358737968285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4782731142620579935830853 896762089241358737968285)
                ·
                  refine ⟨336285783465509526738107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 896762089241358737968285 336285783465509526738107)
                  ·
                    rfl

theorem cell21_1473557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 4, 3].length) (baseStart_1473557 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1473557 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1473557 prefixEnd_1473557 := by exact prefixLift 1473557
  have htrace : WordTrace (prefixWord ++ tailWord_1473557) baseStart_1473557 baseEnd_1473557 := by
    simpa [prefixWord, tailWord_1473557, baseEnd_1473557] using wordTrace_append hprefix tailTrace_1473557
  have hstable : (prefixWord ++ tailWord_1473557).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473557).length < 2 ^ (prefixWord ++ tailWord_1473557).sum := by decide
  have hdescent : baseEnd_1473557 < baseStart_1473557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473616 : List Nat := [2, 1, 1, 1, 1, 3, 1, 8, 3]
def baseStart_1473616 : Nat := 118140960795 + 1473616 * 2 ^ 59
def prefixEnd_1473616 : Nat := 4983230072969 + 3 ^ 40 * 1473616 * 2
def baseEnd_1473616 : Nat := 336299248069338535254653

theorem tailTrace_1473616 : CollatzResearch.WordTrace tailWord_1473616 prefixEnd_1473616 336299248069338535254653 := by
  unfold tailWord_1473616
  simp only [CollatzResearch.WordTrace]
  refine ⟨26873595514674190210576351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35831460686232253614101801 26873595514674190210576351)
  ·
    refine ⟨40310393272011285315864527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26873595514674190210576351 40310393272011285315864527)
    ·
      refine ⟨60465589908016927973796791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40310393272011285315864527 60465589908016927973796791)
      ·
        refine ⟨90698384862025391960695187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60465589908016927973796791 90698384862025391960695187)
        ·
          refine ⟨136047577293038087941042781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90698384862025391960695187 136047577293038087941042781)
          ·
            refine ⟨51017841484889282977891043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 136047577293038087941042781 51017841484889282977891043)
            ·
              refine ⟨76526762227333924466836565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51017841484889282977891043 76526762227333924466836565)
              ·
                refine ⟨896797994851569427345741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 76526762227333924466836565 896797994851569427345741)
                ·
                  refine ⟨336299248069338535254653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 896797994851569427345741 336299248069338535254653)
                  ·
                    rfl

theorem cell21_1473616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 8, 3].length) (baseStart_1473616 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1473616 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1473616 prefixEnd_1473616 := by exact prefixLift 1473616
  have htrace : WordTrace (prefixWord ++ tailWord_1473616) baseStart_1473616 baseEnd_1473616 := by
    simpa [prefixWord, tailWord_1473616, baseEnd_1473616] using wordTrace_append hprefix tailTrace_1473616
  have hstable : (prefixWord ++ tailWord_1473616).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473616).length < 2 ^ (prefixWord ++ tailWord_1473616).sum := by decide
  have hdescent : baseEnd_1473616 < baseStart_1473616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473644 : List Nat := [2, 2, 1, 1, 3, 2, 1, 9]
def baseStart_1473644 : Nat := 118140960795 + 1473644 * 2 ^ 59
def prefixEnd_1473644 : Nat := 4983230072969 + 3 ^ 40 * 1473644 * 2
def baseEnd_1473644 : Nat := 112101879350272236262643

theorem tailTrace_1473644 : CollatzResearch.WordTrace tailWord_1473644 prefixEnd_1473644 112101879350272236262643 := by
  unfold tailWord_1473644
  simp only [CollatzResearch.WordTrace]
  refine ⟨26874106136623470601585993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35832141515497960802114657 26874106136623470601585993)
  ·
    refine ⟨20155579602467602951189495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26874106136623470601585993 20155579602467602951189495)
    ·
      refine ⟨30233369403701404426784243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20155579602467602951189495 30233369403701404426784243)
      ·
        refine ⟨45350054105552106640176365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30233369403701404426784243 45350054105552106640176365)
        ·
          refine ⟨17006270289582039990066137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45350054105552106640176365 17006270289582039990066137)
          ·
            refine ⟨12754702717186529992549603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17006270289582039990066137 12754702717186529992549603)
            ·
              refine ⟨19132054075779794988824405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12754702717186529992549603 19132054075779794988824405)
              ·
                refine ⟨112101879350272236262643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19132054075779794988824405 112101879350272236262643)
                ·
                  rfl

theorem cell21_1473644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 9].length) (baseStart_1473644 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1473644 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1473644 prefixEnd_1473644 := by exact prefixLift 1473644
  have htrace : WordTrace (prefixWord ++ tailWord_1473644) baseStart_1473644 baseEnd_1473644 := by
    simpa [prefixWord, tailWord_1473644, baseEnd_1473644] using wordTrace_append hprefix tailTrace_1473644
  have hstable : (prefixWord ++ tailWord_1473644).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473644).length < 2 ^ (prefixWord ++ tailWord_1473644).sum := by decide
  have hdescent : baseEnd_1473644 < baseStart_1473644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473678 : List Nat := [4, 1, 1, 3, 2, 3, 1, 6]
def baseStart_1473678 : Nat := 118140960795 + 1473678 * 2 ^ 59
def prefixEnd_1473678 : Nat := 4983230072969 + 3 ^ 40 * 1473678 * 2
def baseEnd_1473678 : Nat := 112104465771346735073731

theorem tailTrace_1473678 : CollatzResearch.WordTrace tailWord_1473678 prefixEnd_1473678 112104465771346735073731 := by
  unfold tailWord_1473678
  simp only [CollatzResearch.WordTrace]
  refine ⟨6718681544390470626238711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35832968236749176673273125 6718681544390470626238711)
  ·
    refine ⟨10078022316585705939358067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6718681544390470626238711 10078022316585705939358067)
    ·
      refine ⟨15117033474878558909037101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10078022316585705939358067 15117033474878558909037101)
      ·
        refine ⟨5668887553079459590888913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15117033474878558909037101 5668887553079459590888913)
        ·
          refine ⟨4251665664809594693166685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5668887553079459590888913 4251665664809594693166685)
          ·
            refine ⟨1594374624303598009937507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4251665664809594693166685 1594374624303598009937507)
            ·
              refine ⟨2391561936455397014906261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1594374624303598009937507 2391561936455397014906261)
              ·
                refine ⟨112104465771346735073731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2391561936455397014906261 112104465771346735073731)
                ·
                  rfl

theorem cell21_1473678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 1, 6].length) (baseStart_1473678 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1473678 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1473678 prefixEnd_1473678 := by exact prefixLift 1473678
  have htrace : WordTrace (prefixWord ++ tailWord_1473678) baseStart_1473678 baseEnd_1473678 := by
    simpa [prefixWord, tailWord_1473678, baseEnd_1473678] using wordTrace_append hprefix tailTrace_1473678
  have hstable : (prefixWord ++ tailWord_1473678).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473678).length < 2 ^ (prefixWord ++ tailWord_1473678).sum := by decide
  have hdescent : baseEnd_1473678 < baseStart_1473678 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473689 : List Nat := [1, 2, 1, 2, 1, 2, 1, 1, 10]
def baseStart_1473689 : Nat := 118140960795 + 1473689 * 2 ^ 59
def prefixEnd_1473689 : Nat := 4983230072969 + 3 ^ 40 * 1473689 * 2
def baseEnd_1473689 : Nat := 336315907663906630537837

theorem tailTrace_1473689 : CollatzResearch.WordTrace tailWord_1473689 prefixEnd_1473689 336315907663906630537837 := by
  unfold tailWord_1473689
  simp only [CollatzResearch.WordTrace]
  refine ⟨53749853558083913888560121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35833235705389275925706747 53749853558083913888560121)
  ·
    refine ⟨40312390168562935416420091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53749853558083913888560121 40312390168562935416420091)
    ·
      refine ⟨60468585252844403124630137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40312390168562935416420091 60468585252844403124630137)
      ·
        refine ⟨45351438939633302343472603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60468585252844403124630137 45351438939633302343472603)
        ·
          refine ⟨68027158409449953515208905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45351438939633302343472603 68027158409449953515208905)
          ·
            refine ⟨51020368807087465136406679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68027158409449953515208905 51020368807087465136406679)
            ·
              refine ⟨76530553210631197704610019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51020368807087465136406679 76530553210631197704610019)
              ·
                refine ⟨114795829815946796556915029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76530553210631197704610019 114795829815946796556915029)
                ·
                  refine ⟨336315907663906630537837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 114795829815946796556915029 336315907663906630537837)
                  ·
                    rfl

theorem cell21_1473689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 10].length) (baseStart_1473689 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1473689 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1473689 prefixEnd_1473689 := by exact prefixLift 1473689
  have htrace : WordTrace (prefixWord ++ tailWord_1473689) baseStart_1473689 baseEnd_1473689 := by
    simpa [prefixWord, tailWord_1473689, baseEnd_1473689] using wordTrace_append hprefix tailTrace_1473689
  have hstable : (prefixWord ++ tailWord_1473689).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473689).length < 2 ^ (prefixWord ++ tailWord_1473689).sum := by decide
  have hdescent : baseEnd_1473689 < baseStart_1473689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473692 : List Nat := [2, 2, 3, 2, 1, 3, 1, 2, 5]
def baseStart_1473692 : Nat := 118140960795 + 1473692 * 2 ^ 59
def prefixEnd_1473692 : Nat := 4983230072969 + 3 ^ 40 * 1473692 * 2
def baseEnd_1473692 : Nat := 336316592304779291987831

theorem tailTrace_1473692 : CollatzResearch.WordTrace tailWord_1473692 prefixEnd_1473692 336316592304779291987831 := by
  unfold tailWord_1473692
  simp only [CollatzResearch.WordTrace]
  refine ⟨26874981488536522700459665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35833308651382030267279553 26874981488536522700459665)
  ·
    refine ⟨20156236116402392025344749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26874981488536522700459665 20156236116402392025344749)
    ·
      refine ⟨7558588543650897009504281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20156236116402392025344749 7558588543650897009504281)
      ·
        refine ⟨5668941407738172757128211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7558588543650897009504281 5668941407738172757128211)
        ·
          refine ⟨8503412111607259135692317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5668941407738172757128211 8503412111607259135692317)
          ·
            refine ⟨3188779541852722175884619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8503412111607259135692317 3188779541852722175884619)
            ·
              refine ⟨4783169312779083263826929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3188779541852722175884619 4783169312779083263826929)
              ·
                refine ⟨3587376984584312447870197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4783169312779083263826929 3587376984584312447870197)
                ·
                  refine ⟨336316592304779291987831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3587376984584312447870197 336316592304779291987831)
                  ·
                    rfl

theorem cell21_1473692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 2, 5].length) (baseStart_1473692 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1473692 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1473692 prefixEnd_1473692 := by exact prefixLift 1473692
  have htrace : WordTrace (prefixWord ++ tailWord_1473692) baseStart_1473692 baseEnd_1473692 := by
    simpa [prefixWord, tailWord_1473692, baseEnd_1473692] using wordTrace_append hprefix tailTrace_1473692
  have hstable : (prefixWord ++ tailWord_1473692).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473692).length < 2 ^ (prefixWord ++ tailWord_1473692).sum := by decide
  have hdescent : baseEnd_1473692 < baseStart_1473692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473751 : List Nat := [1, 1, 3, 2, 1, 2, 4, 2, 5]
def baseStart_1473751 : Nat := 118140960795 + 1473751 * 2 ^ 59
def prefixEnd_1473751 : Nat := 4983230072969 + 3 ^ 40 * 1473751 * 2
def baseEnd_1473751 : Nat := 336330056908608300504377

theorem tailTrace_1473751 : CollatzResearch.WordTrace tailWord_1473751 prefixEnd_1473751 336330056908608300504377 := by
  unfold tailWord_1473751
  simp only [CollatzResearch.WordTrace]
  refine ⟨53752114883859298477317107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35834743255906198984878071 53752114883859298477317107)
  ·
    refine ⟨80628172325788947715975661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53752114883859298477317107 80628172325788947715975661)
    ·
      refine ⟨30235564622170855393490873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80628172325788947715975661 30235564622170855393490873)
      ·
        refine ⟨22676673466628141545118155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30235564622170855393490873 22676673466628141545118155)
        ·
          refine ⟨34015010199942212317677233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22676673466628141545118155 34015010199942212317677233)
          ·
            refine ⟨25511257649956659238257925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34015010199942212317677233 25511257649956659238257925)
            ·
              refine ⟨4783360809366873607173361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25511257649956659238257925 4783360809366873607173361)
              ·
                refine ⟨3587520607025155205380021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4783360809366873607173361 3587520607025155205380021)
                ·
                  refine ⟨336330056908608300504377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3587520607025155205380021 336330056908608300504377)
                  ·
                    rfl

theorem cell21_1473751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 2, 5].length) (baseStart_1473751 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1473751 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1473751 prefixEnd_1473751 := by exact prefixLift 1473751
  have htrace : WordTrace (prefixWord ++ tailWord_1473751) baseStart_1473751 baseEnd_1473751 := by
    simpa [prefixWord, tailWord_1473751, baseEnd_1473751] using wordTrace_append hprefix tailTrace_1473751
  have hstable : (prefixWord ++ tailWord_1473751).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473751).length < 2 ^ (prefixWord ++ tailWord_1473751).sum := by decide
  have hdescent : baseEnd_1473751 < baseStart_1473751 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473785 : List Nat := [1, 2, 1, 3, 1, 1, 7, 2, 3]
def baseStart_1473785 : Nat := 118140960795 + 1473785 * 2 ^ 59
def prefixEnd_1473785 : Nat := 4983230072969 + 3 ^ 40 * 1473785 * 2
def baseEnd_1473785 : Nat := 336337816171831796937641

theorem tailTrace_1473785 : CollatzResearch.WordTrace tailWord_1473785 prefixEnd_1473785 336337816171831796937641 := by
  unfold tailWord_1473785
  simp only [CollatzResearch.WordTrace]
  refine ⟨53753354965736122284054809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35835569977157414856036539 53753354965736122284054809)
  ·
    refine ⟨40315016224302091713041107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53753354965736122284054809 40315016224302091713041107)
    ·
      refine ⟨60472524336453137569561661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40315016224302091713041107 60472524336453137569561661)
      ·
        refine ⟨22677196626169926588585623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60472524336453137569561661 22677196626169926588585623)
        ·
          refine ⟨34015794939254889882878435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22677196626169926588585623 34015794939254889882878435)
          ·
            refine ⟨51023692408882334824317653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34015794939254889882878435 51023692408882334824317653)
            ·
              refine ⟨1195867790833179722444945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 51023692408882334824317653 1195867790833179722444945)
              ·
                refine ⟨896900843124884791833709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1195867790833179722444945 896900843124884791833709)
                ·
                  refine ⟨336337816171831796937641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 896900843124884791833709 336337816171831796937641)
                  ·
                    rfl

theorem cell21_1473785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 7, 2, 3].length) (baseStart_1473785 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1473785 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1473785 prefixEnd_1473785 := by exact prefixLift 1473785
  have htrace : WordTrace (prefixWord ++ tailWord_1473785) baseStart_1473785 baseEnd_1473785 := by
    simpa [prefixWord, tailWord_1473785, baseEnd_1473785] using wordTrace_append hprefix tailTrace_1473785
  have hstable : (prefixWord ++ tailWord_1473785).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473785).length < 2 ^ (prefixWord ++ tailWord_1473785).sum := by decide
  have hdescent : baseEnd_1473785 < baseStart_1473785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473844 : List Nat := [2, 5, 1, 1, 1, 1, 2, 3, 5]
def baseStart_1473844 : Nat := 118140960795 + 1473844 * 2 ^ 59
def prefixEnd_1473844 : Nat := 4983230072969 + 3 ^ 40 * 1473844 * 2
def baseEnd_1473844 : Nat := 336351280775660805454187

theorem tailTrace_1473844 : CollatzResearch.WordTrace tailWord_1473844 prefixEnd_1473844 336351280775660805454187 := by
  unfold tailWord_1473844
  simp only [CollatzResearch.WordTrace]
  refine ⟨26877753436261187680226293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35837004581681583573635057 26877753436261187680226293)
  ·
    refine ⟨2519789384649486345021215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26877753436261187680226293 2519789384649486345021215)
    ·
      refine ⟨3779684076974229517531823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2519789384649486345021215 3779684076974229517531823)
      ·
        refine ⟨5669526115461344276297735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3779684076974229517531823 5669526115461344276297735)
        ·
          refine ⟨8504289173192016414446603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5669526115461344276297735 8504289173192016414446603)
          ·
            refine ⟨12756433759788024621669905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8504289173192016414446603 12756433759788024621669905)
            ·
              refine ⟨9567325319841018466252429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12756433759788024621669905 9567325319841018466252429)
              ·
                refine ⟨3587746994940381924844661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9567325319841018466252429 3587746994940381924844661)
                ·
                  refine ⟨336351280775660805454187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3587746994940381924844661 336351280775660805454187)
                  ·
                    rfl

theorem cell21_1473844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_1473844 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1473844 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1473844 prefixEnd_1473844 := by exact prefixLift 1473844
  have htrace : WordTrace (prefixWord ++ tailWord_1473844) baseStart_1473844 baseEnd_1473844 := by
    simpa [prefixWord, tailWord_1473844, baseEnd_1473844] using wordTrace_append hprefix tailTrace_1473844
  have hstable : (prefixWord ++ tailWord_1473844).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473844).length < 2 ^ (prefixWord ++ tailWord_1473844).sum := by decide
  have hdescent : baseEnd_1473844 < baseStart_1473844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473903 : List Nat := [1, 1, 2, 1, 3, 1, 6, 1, 5]
def baseStart_1473903 : Nat := 118140960795 + 1473903 * 2 ^ 59
def prefixEnd_1473903 : Nat := 4983230072969 + 3 ^ 40 * 1473903 * 2
def baseEnd_1473903 : Nat := 336364745379489813970733

theorem tailTrace_1473903 : CollatzResearch.WordTrace tailWord_1473903 prefixEnd_1473903 336364745379489813970733 := by
  unfold tailWord_1473903
  simp only [CollatzResearch.WordTrace]
  refine ⟨53757658779308628436850363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35838439186205752291233575 53757658779308628436850363)
  ·
    refine ⟨80636488168962942655275545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53757658779308628436850363 80636488168962942655275545)
    ·
      refine ⟨60477366126722206991456659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80636488168962942655275545 60477366126722206991456659)
      ·
        refine ⟨90716049190083310487184989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60477366126722206991456659 90716049190083310487184989)
        ·
          refine ⟨34018518446281241432694371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90716049190083310487184989 34018518446281241432694371)
          ·
            refine ⟨51027777669421862149041557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34018518446281241432694371 51027777669421862149041557)
            ·
              refine ⟨2391927078254149788236323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 51027777669421862149041557 2391927078254149788236323)
              ·
                refine ⟨3587890617381224682354485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2391927078254149788236323 3587890617381224682354485)
                ·
                  refine ⟨336364745379489813970733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3587890617381224682354485 336364745379489813970733)
                  ·
                    rfl

theorem cell21_1473903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6, 1, 5].length) (baseStart_1473903 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1473903 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1473903 prefixEnd_1473903 := by exact prefixLift 1473903
  have htrace : WordTrace (prefixWord ++ tailWord_1473903) baseStart_1473903 baseEnd_1473903 := by
    simpa [prefixWord, tailWord_1473903, baseEnd_1473903] using wordTrace_append hprefix tailTrace_1473903
  have hstable : (prefixWord ++ tailWord_1473903).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473903).length < 2 ^ (prefixWord ++ tailWord_1473903).sum := by decide
  have hdescent : baseEnd_1473903 < baseStart_1473903 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473954 : List Nat := [3, 3, 1, 2, 1, 3, 3, 2, 3]
def baseStart_1473954 : Nat := 118140960795 + 1473954 * 2 ^ 59
def prefixEnd_1473954 : Nat := 4983230072969 + 3 ^ 40 * 1473954 * 2
def baseEnd_1473954 : Nat := 336376384274325058620629

theorem tailTrace_1473954 : CollatzResearch.WordTrace tailWord_1473954 prefixEnd_1473954 336376384274325058620629 := by
  unfold tailWord_1473954
  simp only [CollatzResearch.WordTrace]
  refine ⟨13439879725530966036739229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35839679268082576097971277 13439879725530966036739229)
  ·
    refine ⟨5039954897074112263777211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13439879725530966036739229 5039954897074112263777211)
    ·
      refine ⟨7559932345611168395665817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5039954897074112263777211 7559932345611168395665817)
      ·
        refine ⟨5669949259208376296749363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7559932345611168395665817 5669949259208376296749363)
        ·
          refine ⟨8504923888812564445124045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5669949259208376296749363 8504923888812564445124045)
          ·
            refine ⟨3189346458304711666921517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8504923888812564445124045 3189346458304711666921517)
            ·
              refine ⟨1196004921864266875095569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3189346458304711666921517 1196004921864266875095569)
              ·
                refine ⟨897003691398200156321677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1196004921864266875095569 897003691398200156321677)
                ·
                  refine ⟨336376384274325058620629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 897003691398200156321677 336376384274325058620629)
                  ·
                    rfl

theorem cell21_1473954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 3, 2, 3].length) (baseStart_1473954 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1473954 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1473954 prefixEnd_1473954 := by exact prefixLift 1473954
  have htrace : WordTrace (prefixWord ++ tailWord_1473954) baseStart_1473954 baseEnd_1473954 := by
    simpa [prefixWord, tailWord_1473954, baseEnd_1473954] using wordTrace_append hprefix tailTrace_1473954
  have hstable : (prefixWord ++ tailWord_1473954).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473954).length < 2 ^ (prefixWord ++ tailWord_1473954).sum := by decide
  have hdescent : baseEnd_1473954 < baseStart_1473954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473965 : List Nat := [1, 5, 2, 2, 1, 1, 1, 8]
def baseStart_1473965 : Nat := 118140960795 + 1473965 * 2 ^ 59
def prefixEnd_1473965 : Nat := 4983230072969 + 3 ^ 40 * 1473965 * 2
def baseEnd_1473965 : Nat := 112126298208063827979091

theorem tailTrace_1473965 : CollatzResearch.WordTrace tailWord_1473965 prefixEnd_1473965 112126298208063827979091 := by
  unfold tailWord_1473965
  simp only [CollatzResearch.WordTrace]
  refine ⟨53759920105084013025607349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35839946736722675350404899 53759920105084013025607349)
  ·
    refine ⟨5039992509851626221150689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 53759920105084013025607349 5039992509851626221150689)
    ·
      refine ⟨3779994382388719665863017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5039992509851626221150689 3779994382388719665863017)
      ·
        refine ⟨2834995786791539749397263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3779994382388719665863017 2834995786791539749397263)
        ·
          refine ⟨4252493680187309624095895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2834995786791539749397263 4252493680187309624095895)
          ·
            refine ⟨6378740520280964436143843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4252493680187309624095895 6378740520280964436143843)
            ·
              refine ⟨9568110780421446654215765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6378740520280964436143843 9568110780421446654215765)
              ·
                refine ⟨112126298208063827979091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9568110780421446654215765 112126298208063827979091)
                ·
                  rfl

theorem cell21_1473965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 8].length) (baseStart_1473965 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1473965 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1473965 prefixEnd_1473965 := by exact prefixLift 1473965
  have htrace : WordTrace (prefixWord ++ tailWord_1473965) baseStart_1473965 baseEnd_1473965 := by
    simpa [prefixWord, tailWord_1473965, baseEnd_1473965] using wordTrace_append hprefix tailTrace_1473965
  have hstable : (prefixWord ++ tailWord_1473965).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473965).length < 2 ^ (prefixWord ++ tailWord_1473965).sum := by decide
  have hdescent : baseEnd_1473965 < baseStart_1473965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1474010 : List Nat := [3, 1, 1, 2, 3, 2, 1, 4, 4]
def baseStart_1474010 : Nat := 118140960795 + 1474010 * 2 ^ 59
def prefixEnd_1474010 : Nat := 4983230072969 + 3 ^ 40 * 1474010 * 2
def baseEnd_1474010 : Nat := 336389164237281405687181

theorem tailTrace_1474010 : CollatzResearch.WordTrace tailWord_1474010 prefixEnd_1474010 336389164237281405687181 := by
  unfold tailWord_1474010
  simp only [CollatzResearch.WordTrace]
  refine ⟨13440390347480246427748871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35841040926613990473996989 13440390347480246427748871)
  ·
    refine ⟨20160585521220369641623307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13440390347480246427748871 20160585521220369641623307)
    ·
      refine ⟨30240878281830554462434961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20160585521220369641623307 30240878281830554462434961)
      ·
        refine ⟨22680658711372915846826221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30240878281830554462434961 22680658711372915846826221)
        ·
          refine ⟨8505247016764843442559833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22680658711372915846826221 8505247016764843442559833)
          ·
            refine ⟨6378935262573632581919875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8505247016764843442559833 6378935262573632581919875)
            ·
              refine ⟨9568402893860448872879813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6378935262573632581919875 9568402893860448872879813)
              ·
                refine ⟨1794075542598834163664965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9568402893860448872879813 1794075542598834163664965)
                ·
                  refine ⟨336389164237281405687181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1794075542598834163664965 336389164237281405687181)
                  ·
                    rfl

theorem cell21_1474010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 4, 4].length) (baseStart_1474010 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1474010 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1474010 prefixEnd_1474010 := by exact prefixLift 1474010
  have htrace : WordTrace (prefixWord ++ tailWord_1474010) baseStart_1474010 baseEnd_1474010 := by
    simpa [prefixWord, tailWord_1474010, baseEnd_1474010] using wordTrace_append hprefix tailTrace_1474010
  have hstable : (prefixWord ++ tailWord_1474010).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1474010).length < 2 ^ (prefixWord ++ tailWord_1474010).sum := by decide
  have hdescent : baseEnd_1474010 < baseStart_1474010 := by decide
  rcases family_descends (prefixWord ++ tailWord_1474010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1474013 : List Nat := [1, 4, 3, 1, 1, 3, 1, 4, 3]
def baseStart_1474013 : Nat := 118140960795 + 1474013 * 2 ^ 59
def prefixEnd_1474013 : Nat := 4983230072969 + 3 ^ 40 * 1474013 * 2
def baseEnd_1474013 : Nat := 336389848878154067137175

theorem tailTrace_1474013 : CollatzResearch.WordTrace tailWord_1474013 prefixEnd_1474013 336389848878154067137175 := by
  unfold tailWord_1474013
  simp only [CollatzResearch.WordTrace]
  refine ⟨53761670808910117223354693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35841113872606744815569795 53761670808910117223354693)
  ·
    refine ⟨10080313276670646979379005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53761670808910117223354693 10080313276670646979379005)
    ·
      refine ⟨3780117478751492617267127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10080313276670646979379005 3780117478751492617267127)
      ·
        refine ⟨5670176218127238925900691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3780117478751492617267127 5670176218127238925900691)
        ·
          refine ⟨8505264327190858388851037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5670176218127238925900691 8505264327190858388851037)
          ·
            refine ⟨3189474122696571895819139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8505264327190858388851037 3189474122696571895819139)
            ·
              refine ⟨4784211184044857843728709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3189474122696571895819139 4784211184044857843728709)
              ·
                refine ⟨897039597008410845699133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4784211184044857843728709 897039597008410845699133)
                ·
                  refine ⟨336389848878154067137175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 897039597008410845699133 336389848878154067137175)
                  ·
                    rfl

theorem cell21_1474013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 4, 3].length) (baseStart_1474013 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1474013 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1474013 prefixEnd_1474013 := by exact prefixLift 1474013
  have htrace : WordTrace (prefixWord ++ tailWord_1474013) baseStart_1474013 baseEnd_1474013 := by
    simpa [prefixWord, tailWord_1474013, baseEnd_1474013] using wordTrace_append hprefix tailTrace_1474013
  have hstable : (prefixWord ++ tailWord_1474013).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1474013).length < 2 ^ (prefixWord ++ tailWord_1474013).sum := by decide
  have hdescent : baseEnd_1474013 < baseStart_1474013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1474013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1474072 : List Nat := [2, 1, 2, 3, 4, 1, 2, 1, 5]
def baseStart_1474072 : Nat := 118140960795 + 1474072 * 2 ^ 59
def prefixEnd_1474072 : Nat := 4983230072969 + 3 ^ 40 * 1474072 * 2
def baseEnd_1474072 : Nat := 336403313481983075653721

theorem tailTrace_1474072 : CollatzResearch.WordTrace tailWord_1474072 prefixEnd_1474072 336403313481983075653721 := by
  unfold tailWord_1474072
  simp only [CollatzResearch.WordTrace]
  refine ⟨26881911357848185149876235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35842548477130913533168313 26881911357848185149876235)
  ·
    refine ⟨40322867036772277724814353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26881911357848185149876235 40322867036772277724814353)
    ·
      refine ⟨30242150277579208293610765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40322867036772277724814353 30242150277579208293610765)
      ·
        refine ⟨11340806354092203110104037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30242150277579208293610765 11340806354092203110104037)
        ·
          refine ⟨2126401191392288083144507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11340806354092203110104037 2126401191392288083144507)
          ·
            refine ⟨3189601787088432124716761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2126401191392288083144507 3189601787088432124716761)
            ·
              refine ⟨2392201340316324093537571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3189601787088432124716761 2392201340316324093537571)
              ·
                refine ⟨3588302010474486140306357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2392201340316324093537571 3588302010474486140306357)
                ·
                  refine ⟨336403313481983075653721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3588302010474486140306357 336403313481983075653721)
                  ·
                    rfl

theorem cell21_1474072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 2, 1, 5].length) (baseStart_1474072 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1474072 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1474072 prefixEnd_1474072 := by exact prefixLift 1474072
  have htrace : WordTrace (prefixWord ++ tailWord_1474072) baseStart_1474072 baseEnd_1474072 := by
    simpa [prefixWord, tailWord_1474072, baseEnd_1474072] using wordTrace_append hprefix tailTrace_1474072
  have hstable : (prefixWord ++ tailWord_1474072).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1474072).length < 2 ^ (prefixWord ++ tailWord_1474072).sum := by decide
  have hdescent : baseEnd_1474072 < baseStart_1474072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1474072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1474238 : List Nat := [4, 2, 1, 1, 2, 3, 1, 1, 6]
def baseStart_1474238 : Nat := 118140960795 + 1474238 * 2 ^ 59
def prefixEnd_1474238 : Nat := 4983230072969 + 3 ^ 40 * 1474238 * 2
def baseEnd_1474238 : Nat := 336441196943603675886715

theorem tailTrace_1474238 : CollatzResearch.WordTrace tailWord_1474238 prefixEnd_1474238 336441196943603675886715 := by
  unfold tailWord_1474238
  simp only [CollatzResearch.WordTrace]
  refine ⟨6721234654136872581286921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35846584822063320433530245 6721234654136872581286921)
  ·
    refine ⟨5040925990602654435965191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6721234654136872581286921 5040925990602654435965191)
    ·
      refine ⟨7561388985903981653947787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5040925990602654435965191 7561388985903981653947787)
      ·
        refine ⟨11342083478855972480921681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7561388985903981653947787 11342083478855972480921681)
        ·
          refine ⟨8506562609141979360691261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11342083478855972480921681 8506562609141979360691261)
          ·
            refine ⟨3189960978428242260259223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8506562609141979360691261 3189960978428242260259223)
            ·
              refine ⟨4784941467642363390388835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3189960978428242260259223 4784941467642363390388835)
              ·
                refine ⟨7177412201463545085583253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4784941467642363390388835 7177412201463545085583253)
                ·
                  refine ⟨336441196943603675886715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7177412201463545085583253 336441196943603675886715)
                  ·
                    rfl

theorem cell21_1474238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 1, 6].length) (baseStart_1474238 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1474238 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1474238 prefixEnd_1474238 := by exact prefixLift 1474238
  have htrace : WordTrace (prefixWord ++ tailWord_1474238) baseStart_1474238 baseEnd_1474238 := by
    simpa [prefixWord, tailWord_1474238, baseEnd_1474238] using wordTrace_append hprefix tailTrace_1474238
  have hstable : (prefixWord ++ tailWord_1474238).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1474238).length < 2 ^ (prefixWord ++ tailWord_1474238).sum := by decide
  have hdescent : baseEnd_1474238 < baseStart_1474238 := by decide
  rcases family_descends (prefixWord ++ tailWord_1474238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1474314 : List Nat := [3, 1, 2, 2, 1, 4, 1, 3, 4]
def baseStart_1474314 : Nat := 118140960795 + 1474314 * 2 ^ 59
def prefixEnd_1474314 : Nat := 4983230072969 + 3 ^ 40 * 1474314 * 2
def baseEnd_1474314 : Nat := 336458541179044432619893

theorem tailTrace_1474314 : CollatzResearch.WordTrace tailWord_1474314 prefixEnd_1474314 336458541179044432619893 := by
  unfold tailWord_1474314
  simp only [CollatzResearch.WordTrace]
  refine ⟨13443162295204911407515499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35848432787213097086707997 13443162295204911407515499)
  ·
    refine ⟨20164743442807367111273249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13443162295204911407515499 20164743442807367111273249)
    ·
      refine ⟨15123557582105525333454937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20164743442807367111273249 15123557582105525333454937)
      ·
        refine ⟨11342668186579144000091203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15123557582105525333454937 11342668186579144000091203)
        ·
          refine ⟨17014002279868716000136805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11342668186579144000091203 17014002279868716000136805)
          ·
            refine ⟨3190125427475384250025651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17014002279868716000136805 3190125427475384250025651)
            ·
              refine ⟨4785188141213076375038477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3190125427475384250025651 4785188141213076375038477)
              ·
                refine ⟨1794445552954903640639429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4785188141213076375038477 1794445552954903640639429)
                ·
                  refine ⟨336458541179044432619893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1794445552954903640639429 336458541179044432619893)
                  ·
                    rfl

theorem cell21_1474314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 3, 4].length) (baseStart_1474314 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1474314 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1474314 prefixEnd_1474314 := by exact prefixLift 1474314
  have htrace : WordTrace (prefixWord ++ tailWord_1474314) baseStart_1474314 baseEnd_1474314 := by
    simpa [prefixWord, tailWord_1474314, baseEnd_1474314] using wordTrace_append hprefix tailTrace_1474314
  have hstable : (prefixWord ++ tailWord_1474314).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1474314).length < 2 ^ (prefixWord ++ tailWord_1474314).sum := by decide
  have hdescent : baseEnd_1474314 < baseStart_1474314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1474314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1474373 : List Nat := [1, 3, 1, 1, 1, 2, 3, 5, 4]
def baseStart_1474373 : Nat := 118140960795 + 1474373 * 2 ^ 59
def prefixEnd_1474373 : Nat := 4983230072969 + 3 ^ 40 * 1474373 * 2
def baseEnd_1474373 : Nat := 336472005782873441136439

theorem tailTrace_1474373 : CollatzResearch.WordTrace tailWord_1474373 prefixEnd_1474373 336472005782873441136439 := by
  unfold tailWord_1474373
  simp only [CollatzResearch.WordTrace]
  refine ⟨53774801087605898706459773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35849867391737265804306515 53774801087605898706459773)
  ·
    refine ⟨20165550407852212014922415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53774801087605898706459773 20165550407852212014922415)
    ·
      refine ⟨30248325611778318022383623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20165550407852212014922415 30248325611778318022383623)
      ·
        refine ⟨45372488417667477033575435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30248325611778318022383623 45372488417667477033575435)
        ·
          refine ⟨68058732626501215550363153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45372488417667477033575435 68058732626501215550363153)
          ·
            refine ⟨51044049469875911662772365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68058732626501215550363153 51044049469875911662772365)
            ·
              refine ⟨19141518551203466873539637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51044049469875911662772365 19141518551203466873539637)
              ·
                refine ⟨1794517364175325019394341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19141518551203466873539637 1794517364175325019394341)
                ·
                  refine ⟨336472005782873441136439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1794517364175325019394341 336472005782873441136439)
                  ·
                    rfl

theorem cell21_1474373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 5, 4].length) (baseStart_1474373 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1474373 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1474373 prefixEnd_1474373 := by exact prefixLift 1474373
  have htrace : WordTrace (prefixWord ++ tailWord_1474373) baseStart_1474373 baseEnd_1474373 := by
    simpa [prefixWord, tailWord_1474373, baseEnd_1474373] using wordTrace_append hprefix tailTrace_1474373
  have hstable : (prefixWord ++ tailWord_1474373).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1474373).length < 2 ^ (prefixWord ++ tailWord_1474373).sum := by decide
  have hdescent : baseEnd_1474373 < baseStart_1474373 := by decide
  rcases family_descends (prefixWord ++ tailWord_1474373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1474404 : List Nat := [2, 3, 1, 1, 5, 1, 8]
def baseStart_1474404 : Nat := 118140960795 + 1474404 * 2 ^ 59
def prefixEnd_1474404 : Nat := 4983230072969 + 3 ^ 40 * 1474404 * 2
def baseEnd_1474404 : Nat := 37386564489469364013301

theorem tailTrace_1474404 : CollatzResearch.WordTrace tailWord_1474404 prefixEnd_1474404 37386564489469364013301 := by
  unfold tailWord_1474404
  simp only [CollatzResearch.WordTrace]
  refine ⟨26887965875246795500419133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35850621166995727333892177 26887965875246795500419133)
  ·
    refine ⟨10082987203217548312657175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26887965875246795500419133 10082987203217548312657175)
    ·
      refine ⟨15124480804826322468985763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10082987203217548312657175 15124480804826322468985763)
      ·
        refine ⟨22686721207239483703478645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15124480804826322468985763 22686721207239483703478645)
        ·
          refine ⟨2126880113178701597201123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22686721207239483703478645 2126880113178701597201123)
          ·
            refine ⟨3190320169768052395801685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2126880113178701597201123 3190320169768052395801685)
            ·
              refine ⟨37386564489469364013301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3190320169768052395801685 37386564489469364013301)
              ·
                rfl

theorem cell21_1474404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 8].length) (baseStart_1474404 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1474404 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1474404 prefixEnd_1474404 := by exact prefixLift 1474404
  have htrace : WordTrace (prefixWord ++ tailWord_1474404) baseStart_1474404 baseEnd_1474404 := by
    simpa [prefixWord, tailWord_1474404, baseEnd_1474404] using wordTrace_append hprefix tailTrace_1474404
  have hstable : (prefixWord ++ tailWord_1474404).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1474404).length < 2 ^ (prefixWord ++ tailWord_1474404).sum := by decide
  have hdescent : baseEnd_1474404 < baseStart_1474404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1474404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1474511 : List Nat := [1, 1, 2, 1, 1, 5, 2, 5, 3]
def baseStart_1474511 : Nat := 118140960795 + 1474511 * 2 ^ 59
def prefixEnd_1474511 : Nat := 4983230072969 + 3 ^ 40 * 1474511 * 2
def baseEnd_1474511 : Nat := 336503499263015867836157

theorem tailTrace_1474511 : CollatzResearch.WordTrace tailWord_1474511 prefixEnd_1474511 336503499263015867836157 := by
  unfold tailWord_1474511
  simp only [CollatzResearch.WordTrace]
  refine ⟨53779834361105948274983387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35853222907403965516655591 53779834361105948274983387)
  ·
    refine ⟨80669751541658922412475081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53779834361105948274983387 80669751541658922412475081)
    ·
      refine ⟨60502313656244191809356311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80669751541658922412475081 60502313656244191809356311)
      ·
        refine ⟨90753470484366287714034467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60502313656244191809356311 90753470484366287714034467)
        ·
          refine ⟨136130205726549431571051701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90753470484366287714034467 136130205726549431571051701)
          ·
            refine ⟨12762206786864009209786097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 136130205726549431571051701 12762206786864009209786097)
            ·
              refine ⟨9571655090148006907339573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12762206786864009209786097 9571655090148006907339573)
              ·
                refine ⟨897342664701375647563085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9571655090148006907339573 897342664701375647563085)
                ·
                  refine ⟨336503499263015867836157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 897342664701375647563085 336503499263015867836157)
                  ·
                    rfl

theorem cell21_1474511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 5, 3].length) (baseStart_1474511 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1474511 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1474511 prefixEnd_1474511 := by exact prefixLift 1474511
  have htrace : WordTrace (prefixWord ++ tailWord_1474511) baseStart_1474511 baseEnd_1474511 := by
    simpa [prefixWord, tailWord_1474511, baseEnd_1474511] using wordTrace_append hprefix tailTrace_1474511
  have hstable : (prefixWord ++ tailWord_1474511).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1474511).length < 2 ^ (prefixWord ++ tailWord_1474511).sum := by decide
  have hdescent : baseEnd_1474511 < baseStart_1474511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1474511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1474542 : List Nat := [4, 1, 2, 1, 3, 1, 2, 3, 4]
def baseStart_1474542 : Nat := 118140960795 + 1474542 * 2 ^ 59
def prefixEnd_1474542 : Nat := 4983230072969 + 3 ^ 40 * 1474542 * 2
def baseEnd_1474542 : Nat := 336510573885366702819427

theorem tailTrace_1474542 : CollatzResearch.WordTrace tailWord_1474542 prefixEnd_1474542 336510573885366702819427 := by
  unfold tailWord_1474542
  simp only [CollatzResearch.WordTrace]
  refine ⟨6722620627999205071170235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35853976682662427046241253 6722620627999205071170235)
  ·
    refine ⟨10083930941998807606755353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6722620627999205071170235 10083930941998807606755353)
    ·
      refine ⟨7562948206499105705066515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10083930941998807606755353 7562948206499105705066515)
      ·
        refine ⟨11344422309748658557599773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7562948206499105705066515 11344422309748658557599773)
        ·
          refine ⟨4254158366155746959099915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11344422309748658557599773 4254158366155746959099915)
          ·
            refine ⟨6381237549233620438649873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4254158366155746959099915 6381237549233620438649873)
            ·
              refine ⟨4785928161925215328987405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6381237549233620438649873 4785928161925215328987405)
              ·
                refine ⟨1794723060721955748370277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4785928161925215328987405 1794723060721955748370277)
                ·
                  refine ⟨336510573885366702819427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1794723060721955748370277 336510573885366702819427)
                  ·
                    rfl

theorem cell21_1474542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 3, 4].length) (baseStart_1474542 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1474542 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1474542 prefixEnd_1474542 := by exact prefixLift 1474542
  have htrace : WordTrace (prefixWord ++ tailWord_1474542) baseStart_1474542 baseEnd_1474542 := by
    simpa [prefixWord, tailWord_1474542, baseEnd_1474542] using wordTrace_append hprefix tailTrace_1474542
  have hstable : (prefixWord ++ tailWord_1474542).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1474542).length < 2 ^ (prefixWord ++ tailWord_1474542).sum := by decide
  have hdescent : baseEnd_1474542 < baseStart_1474542 := by decide
  rcases family_descends (prefixWord ++ tailWord_1474542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1474556 : List Nat := [2, 2, 2, 1, 2, 2, 5, 5]
def baseStart_1474556 : Nat := 118140960795 + 1474556 * 2 ^ 59
def prefixEnd_1474556 : Nat := 4983230072969 + 3 ^ 40 * 1474556 * 2
def baseEnd_1474556 : Nat := 112171256292035263195355

theorem tailTrace_1474556 : CollatzResearch.WordTrace tailWord_1474556 prefixEnd_1474556 112171256292035263195355 := by
  unfold tailWord_1474556
  simp only [CollatzResearch.WordTrace]
  refine ⟨26890737822971460480185761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35854317097295280640247681 26890737822971460480185761)
  ·
    refine ⟨20168053367228595360139321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26890737822971460480185761 20168053367228595360139321)
    ·
      refine ⟨15126040025421446520104491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20168053367228595360139321 15126040025421446520104491)
      ·
        refine ⟨22689060038132169780156737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15126040025421446520104491 22689060038132169780156737)
        ·
          refine ⟨17016795028599127335117553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22689060038132169780156737 17016795028599127335117553)
          ·
            refine ⟨12762596271449345501338165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17016795028599127335117553 12762596271449345501338165)
            ·
              refine ⟨1196493400448376140750453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12762596271449345501338165 1196493400448376140750453)
              ·
                refine ⟨112171256292035263195355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1196493400448376140750453 112171256292035263195355)
                ·
                  rfl

theorem cell21_1474556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 5, 5].length) (baseStart_1474556 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1474556 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1474556 prefixEnd_1474556 := by exact prefixLift 1474556
  have htrace : WordTrace (prefixWord ++ tailWord_1474556) baseStart_1474556 baseEnd_1474556 := by
    simpa [prefixWord, tailWord_1474556, baseEnd_1474556] using wordTrace_append hprefix tailTrace_1474556
  have hstable : (prefixWord ++ tailWord_1474556).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1474556).length < 2 ^ (prefixWord ++ tailWord_1474556).sum := by decide
  have hdescent : baseEnd_1474556 < baseStart_1474556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1474556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1474705 : List Nat := [1, 2, 2, 1, 1, 1, 1, 1, 11]
def baseStart_1474705 : Nat := 118140960795 + 1474705 * 2 ^ 59
def prefixEnd_1474705 : Nat := 4983230072969 + 3 ^ 40 * 1474705 * 2
def baseEnd_1474705 : Nat := 336547772706114641602427

theorem tailTrace_1474705 : CollatzResearch.WordTrace tailWord_1474705 prefixEnd_1474705 336547772706114641602427 := by
  unfold tailWord_1474705
  simp only [CollatzResearch.WordTrace]
  refine ⟨53786910122403119407545569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35857940081602079605030379 53786910122403119407545569)
  ·
    refine ⟨40340182591802339555659177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53786910122403119407545569 40340182591802339555659177)
    ·
      refine ⟨30255136943851754666744383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40340182591802339555659177 30255136943851754666744383)
      ·
        refine ⟨45382705415777632000116575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30255136943851754666744383 45382705415777632000116575)
        ·
          refine ⟨68074058123666448000174863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45382705415777632000116575 68074058123666448000174863)
          ·
            refine ⟨102111087185499672000262295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68074058123666448000174863 102111087185499672000262295)
            ·
              refine ⟨153166630778249508000393443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102111087185499672000262295 153166630778249508000393443)
              ·
                refine ⟨229749946167374262000590165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 153166630778249508000393443 229749946167374262000590165)
                ·
                  refine ⟨336547772706114641602427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 229749946167374262000590165 336547772706114641602427)
                  ·
                    rfl

theorem cell21_1474705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 11].length) (baseStart_1474705 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1474705 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1474705 prefixEnd_1474705 := by exact prefixLift 1474705
  have htrace : WordTrace (prefixWord ++ tailWord_1474705) baseStart_1474705 baseEnd_1474705 := by
    simpa [prefixWord, tailWord_1474705, baseEnd_1474705] using wordTrace_append hprefix tailTrace_1474705
  have hstable : (prefixWord ++ tailWord_1474705).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1474705).length < 2 ^ (prefixWord ++ tailWord_1474705).sum := by decide
  have hdescent : baseEnd_1474705 < baseStart_1474705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1474705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1474756 : List Nat := [2, 3, 3, 1, 2, 1, 2, 4, 3]
def baseStart_1474756 : Nat := 118140960795 + 1474756 * 2 ^ 59
def prefixEnd_1474756 : Nat := 4983230072969 + 3 ^ 40 * 1474756 * 2
def baseEnd_1474756 : Nat := 336559411600949886252323

theorem tailTrace_1474756 : CollatzResearch.WordTrace tailWord_1474756 prefixEnd_1474756 336559411600949886252323 := by
  unfold tailWord_1474756
  simp only [CollatzResearch.WordTrace]
  refine ⟨26894385122609177558826061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35859180163478903411768081 26894385122609177558826061)
  ·
    refine ⟨10085394420978441584559773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26894385122609177558826061 10085394420978441584559773)
    ·
      refine ⟨3782022907866915594209915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10085394420978441584559773 3782022907866915594209915)
      ·
        refine ⟨5673034361800373391314873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3782022907866915594209915 5673034361800373391314873)
        ·
          refine ⟨4254775771350280043486155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5673034361800373391314873 4254775771350280043486155)
          ·
            refine ⟨6382163657025420065229233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4254775771350280043486155 6382163657025420065229233)
            ·
              refine ⟨4786622742769065048921925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6382163657025420065229233 4786622742769065048921925)
              ·
                refine ⟨897491764269199696672861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4786622742769065048921925 897491764269199696672861)
                ·
                  refine ⟨336559411600949886252323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 897491764269199696672861 336559411600949886252323)
                  ·
                    rfl

theorem cell21_1474756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 4, 3].length) (baseStart_1474756 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1474756 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1474756 prefixEnd_1474756 := by exact prefixLift 1474756
  have htrace : WordTrace (prefixWord ++ tailWord_1474756) baseStart_1474756 baseEnd_1474756 := by
    simpa [prefixWord, tailWord_1474756, baseEnd_1474756] using wordTrace_append hprefix tailTrace_1474756
  have hstable : (prefixWord ++ tailWord_1474756).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1474756).length < 2 ^ (prefixWord ++ tailWord_1474756).sum := by decide
  have hdescent : baseEnd_1474756 < baseStart_1474756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1474756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1474866 : List Nat := [3, 2, 1, 1, 6, 1, 2, 2, 3]
def baseStart_1474866 : Nat := 118140960795 + 1474866 * 2 ^ 59
def prefixEnd_1474866 : Nat := 4983230072969 + 3 ^ 40 * 1474866 * 2
def baseEnd_1474866 : Nat := 336584515099614139418765

theorem tailTrace_1474866 : CollatzResearch.WordTrace tailWord_1474866 prefixEnd_1474866 336584515099614139418765 := by
  unfold tailWord_1474866
  simp only [CollatzResearch.WordTrace]
  refine ⟨13448195568704960976039113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35861854849879895936104301 13448195568704960976039113)
  ·
    refine ⟨10086146676528720732029335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13448195568704960976039113 10086146676528720732029335)
    ·
      refine ⟨15129220014793081098044003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10086146676528720732029335 15129220014793081098044003)
      ·
        refine ⟨22693830022189621647066005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15129220014793081098044003 22693830022189621647066005)
        ·
          refine ⟨1063773282290138514706219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 22693830022189621647066005 1063773282290138514706219)
          ·
            refine ⟨1595659923435207772059329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1063773282290138514706219 1595659923435207772059329)
            ·
              refine ⟨1196744942576405829044497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1595659923435207772059329 1196744942576405829044497)
              ·
                refine ⟨897558706932304371783373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1196744942576405829044497 897558706932304371783373)
                ·
                  refine ⟨336584515099614139418765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 897558706932304371783373 336584515099614139418765)
                  ·
                    rfl

theorem cell21_1474866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 2, 2, 3].length) (baseStart_1474866 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1474866 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1474866 prefixEnd_1474866 := by exact prefixLift 1474866
  have htrace : WordTrace (prefixWord ++ tailWord_1474866) baseStart_1474866 baseEnd_1474866 := by
    simpa [prefixWord, tailWord_1474866, baseEnd_1474866] using wordTrace_append hprefix tailTrace_1474866
  have hstable : (prefixWord ++ tailWord_1474866).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1474866).length < 2 ^ (prefixWord ++ tailWord_1474866).sum := by decide
  have hdescent : baseEnd_1474866 < baseStart_1474866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1474866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1474919 : List Nat := [1, 1, 5, 1, 3, 2, 8]
def baseStart_1474919 : Nat := 118140960795 + 1474919 * 2 ^ 59
def prefixEnd_1474919 : Nat := 4983230072969 + 3 ^ 40 * 1474919 * 2
def baseEnd_1474919 : Nat := 37399623380188647226147

theorem tailTrace_1474919 : CollatzResearch.WordTrace tailWord_1474919 prefixEnd_1474919 37399623380188647226147 := by
  unfold tailWord_1474919
  simp only [CollatzResearch.WordTrace]
  refine ⟨53794715343627833955835811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35863143562418555970557207 53794715343627833955835811)
  ·
    refine ⟨80692073015441750933753717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53794715343627833955835811 80692073015441750933753717)
    ·
      refine ⟨7564881845197664150039411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 80692073015441750933753717 7564881845197664150039411)
      ·
        refine ⟨11347322767796496225059117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7564881845197664150039411 11347322767796496225059117)
        ·
          refine ⟨4255246037923686084397169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11347322767796496225059117 4255246037923686084397169)
          ·
            refine ⟨3191434528442764563297877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4255246037923686084397169 3191434528442764563297877)
            ·
              refine ⟨37399623380188647226147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3191434528442764563297877 37399623380188647226147)
              ·
                rfl

theorem cell21_1474919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 8].length) (baseStart_1474919 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1474919 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1474919 prefixEnd_1474919 := by exact prefixLift 1474919
  have htrace : WordTrace (prefixWord ++ tailWord_1474919) baseStart_1474919 baseEnd_1474919 := by
    simpa [prefixWord, tailWord_1474919, baseEnd_1474919] using wordTrace_append hprefix tailTrace_1474919
  have hstable : (prefixWord ++ tailWord_1474919).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1474919).length < 2 ^ (prefixWord ++ tailWord_1474919).sum := by decide
  have hdescent : baseEnd_1474919 < baseStart_1474919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1474919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1474922 : List Nat := [3, 1, 3, 3, 1, 1, 3, 2, 4]
def baseStart_1474922 : Nat := 118140960795 + 1474922 * 2 ^ 59
def prefixEnd_1474922 : Nat := 4983230072969 + 3 ^ 40 * 1474922 * 2
def baseEnd_1474922 : Nat := 336597295062570486485317

theorem tailTrace_1474922 : CollatzResearch.WordTrace tailWord_1474922 prefixEnd_1474922 336597295062570486485317 := by
  unfold tailWord_1474922
  simp only [CollatzResearch.WordTrace]
  refine ⟨13448706190654241367048755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35863216508411310312130013 13448706190654241367048755)
  ·
    refine ⟨20173059285981362050573133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13448706190654241367048755 20173059285981362050573133)
    ·
      refine ⟨7564897232243010768964925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20173059285981362050573133 7564897232243010768964925)
      ·
        refine ⟨2836836462091129038361847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7564897232243010768964925 2836836462091129038361847)
        ·
          refine ⟨4255254693136693557542771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2836836462091129038361847 4255254693136693557542771)
          ·
            refine ⟨6382882039705040336314157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4255254693136693557542771 6382882039705040336314157)
            ·
              refine ⟨2393580764889390126117809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6382882039705040336314157 2393580764889390126117809)
              ·
                refine ⟨1795185573667042594588357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2393580764889390126117809 1795185573667042594588357)
                ·
                  refine ⟨336597295062570486485317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1795185573667042594588357 336597295062570486485317)
                  ·
                    rfl

theorem cell21_1474922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3, 2, 4].length) (baseStart_1474922 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1474922 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1474922 prefixEnd_1474922 := by exact prefixLift 1474922
  have htrace : WordTrace (prefixWord ++ tailWord_1474922) baseStart_1474922 baseEnd_1474922 := by
    simpa [prefixWord, tailWord_1474922, baseEnd_1474922] using wordTrace_append hprefix tailTrace_1474922
  have hstable : (prefixWord ++ tailWord_1474922).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1474922).length < 2 ^ (prefixWord ++ tailWord_1474922).sum := by decide
  have hdescent : baseEnd_1474922 < baseStart_1474922 := by decide
  rcases family_descends (prefixWord ++ tailWord_1474922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1474967 : List Nat := [1, 1, 3, 3, 1, 1, 5, 3, 3]
def baseStart_1474967 : Nat := 118140960795 + 1474967 * 2 ^ 59
def prefixEnd_1474967 : Nat := 4983230072969 + 3 ^ 40 * 1474967 * 2
def baseEnd_1474967 : Nat := 336607564675660408235225

theorem tailTrace_1474967 : CollatzResearch.WordTrace tailWord_1474967 prefixEnd_1474967 336607564675660408235225 := by
  unfold tailWord_1474967
  simp only [CollatzResearch.WordTrace]
  refine ⟨53796466047453938153583155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35864310698302625435722103 53796466047453938153583155)
  ·
    refine ⟨80694699071180907230374733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53796466047453938153583155 80694699071180907230374733)
    ·
      refine ⟨30260512151692840211390525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80694699071180907230374733 30260512151692840211390525)
      ·
        refine ⟨11347692056884815079271447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30260512151692840211390525 11347692056884815079271447)
        ·
          refine ⟨17021538085327222618907171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11347692056884815079271447 17021538085327222618907171)
          ·
            refine ⟨25532307127990833928360757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17021538085327222618907171 25532307127990833928360757)
            ·
              refine ⟨2393653793249140680783821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25532307127990833928360757 2393653793249140680783821)
              ·
                refine ⟨897620172468427755293933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2393653793249140680783821 897620172468427755293933)
                ·
                  refine ⟨336607564675660408235225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 897620172468427755293933 336607564675660408235225)
                  ·
                    rfl

theorem cell21_1474967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5, 3, 3].length) (baseStart_1474967 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1474967 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1474967 prefixEnd_1474967 := by exact prefixLift 1474967
  have htrace : WordTrace (prefixWord ++ tailWord_1474967) baseStart_1474967 baseEnd_1474967 := by
    simpa [prefixWord, tailWord_1474967, baseEnd_1474967] using wordTrace_append hprefix tailTrace_1474967
  have hstable : (prefixWord ++ tailWord_1474967).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1474967).length < 2 ^ (prefixWord ++ tailWord_1474967).sum := by decide
  have hdescent : baseEnd_1474967 < baseStart_1474967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1474967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1474984 : List Nat := [2, 1, 6, 1, 1, 3, 1, 1, 5]
def baseStart_1474984 : Nat := 118140960795 + 1474984 * 2 ^ 59
def prefixEnd_1474984 : Nat := 4983230072969 + 3 ^ 40 * 1474984 * 2
def baseEnd_1474984 : Nat := 336611444307272156451857

theorem tailTrace_1474984 : CollatzResearch.WordTrace tailWord_1474984 prefixEnd_1474984 336611444307272156451857 := by
  unfold tailWord_1474984
  simp only [CollatzResearch.WordTrace]
  refine ⟨26898543044196175028476003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35864724058928233371301337 26898543044196175028476003)
  ·
    refine ⟨40347814566294262542714005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26898543044196175028476003 40347814566294262542714005)
    ·
      refine ⟨1891303807795043556689719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 40347814566294262542714005 1891303807795043556689719)
      ·
        refine ⟨2836955711692565335034579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1891303807795043556689719 2836955711692565335034579)
        ·
          refine ⟨4255433567538848002551869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2836955711692565335034579 4255433567538848002551869)
          ·
            refine ⟨1595787587827068000956951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4255433567538848002551869 1595787587827068000956951)
            ·
              refine ⟨2393681381740602001435427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1595787587827068000956951 2393681381740602001435427)
              ·
                refine ⟨3590522072610903002153141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2393681381740602001435427 3590522072610903002153141)
                ·
                  refine ⟨336611444307272156451857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3590522072610903002153141 336611444307272156451857)
                  ·
                    rfl

theorem cell21_1474984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 1, 5].length) (baseStart_1474984 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1474984 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1474984 prefixEnd_1474984 := by exact prefixLift 1474984
  have htrace : WordTrace (prefixWord ++ tailWord_1474984) baseStart_1474984 baseEnd_1474984 := by
    simpa [prefixWord, tailWord_1474984, baseEnd_1474984] using wordTrace_append hprefix tailTrace_1474984
  have hstable : (prefixWord ++ tailWord_1474984).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1474984).length < 2 ^ (prefixWord ++ tailWord_1474984).sum := by decide
  have hdescent : baseEnd_1474984 < baseStart_1474984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1474984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475071 : List Nat := [1, 1, 2, 2, 1, 2, 7, 5]
def baseStart_1475071 : Nat := 118140960795 + 1475071 * 2 ^ 59
def prefixEnd_1475071 : Nat := 4983230072969 + 3 ^ 40 * 1475071 * 2
def baseEnd_1475071 : Nat := 112210432964193112833893

theorem tailTrace_1475071 : CollatzResearch.WordTrace tailWord_1475071 prefixEnd_1475071 112210432964193112833893 := by
  unfold tailWord_1475071
  simp only [CollatzResearch.WordTrace]
  refine ⟨53800259239077163915369067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35866839492718109276912711 53800259239077163915369067)
  ·
    refine ⟨80700388858615745873053601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53800259239077163915369067 80700388858615745873053601)
    ·
      refine ⟨60525291643961809404790201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80700388858615745873053601 60525291643961809404790201)
      ·
        refine ⟨45393968732971357053592651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60525291643961809404790201 45393968732971357053592651)
        ·
          refine ⟨68090953099457035580388977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45393968732971357053592651 68090953099457035580388977)
          ·
            refine ⟨51068214824592776685291733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68090953099457035580388977 51068214824592776685291733)
            ·
              refine ⟨1196911284951393203561525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 51068214824592776685291733 1196911284951393203561525)
              ·
                refine ⟨112210432964193112833893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1196911284951393203561525 112210432964193112833893)
                ·
                  rfl

theorem cell21_1475071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 7, 5].length) (baseStart_1475071 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1475071 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1475071 prefixEnd_1475071 := by exact prefixLift 1475071
  have htrace : WordTrace (prefixWord ++ tailWord_1475071) baseStart_1475071 baseEnd_1475071 := by
    simpa [prefixWord, tailWord_1475071, baseEnd_1475071] using wordTrace_append hprefix tailTrace_1475071
  have hstable : (prefixWord ++ tailWord_1475071).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475071).length < 2 ^ (prefixWord ++ tailWord_1475071).sum := by decide
  have hdescent : baseEnd_1475071 < baseStart_1475071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475116 : List Nat := [2, 2, 1, 1, 1, 2, 1, 7, 4]
def baseStart_1475116 : Nat := 118140960795 + 1475116 * 2 ^ 59
def prefixEnd_1475116 : Nat := 4983230072969 + 3 ^ 40 * 1475116 * 2
def baseEnd_1475116 : Nat := 336641568505669260251587

theorem tailTrace_1475116 : CollatzResearch.WordTrace tailWord_1475116 prefixEnd_1475116 336641568505669260251587 := by
  unfold tailWord_1475116
  simp only [CollatzResearch.WordTrace]
  refine ⟨26900950261957068300378601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35867933682609424400504801 26900950261957068300378601)
  ·
    refine ⟨20175712696467801225283951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26900950261957068300378601 20175712696467801225283951)
    ·
      refine ⟨30263569044701701837925927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20175712696467801225283951 30263569044701701837925927)
      ·
        refine ⟨45395353567052552756888891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30263569044701701837925927 45395353567052552756888891)
        ·
          refine ⟨68093030350578829135333337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45395353567052552756888891 68093030350578829135333337)
          ·
            refine ⟨51069772762934121851500003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68093030350578829135333337 51069772762934121851500003)
            ·
              refine ⟨76604659144401182777250005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51069772762934121851500003 76604659144401182777250005)
              ·
                refine ⟨1795421698696902721341797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 76604659144401182777250005 1795421698696902721341797)
                ·
                  refine ⟨336641568505669260251587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1795421698696902721341797 336641568505669260251587)
                  ·
                    rfl

theorem cell21_1475116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 4].length) (baseStart_1475116 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1475116 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1475116 prefixEnd_1475116 := by exact prefixLift 1475116
  have htrace : WordTrace (prefixWord ++ tailWord_1475116) baseStart_1475116 baseEnd_1475116 := by
    simpa [prefixWord, tailWord_1475116, baseEnd_1475116] using wordTrace_append hprefix tailTrace_1475116
  have hstable : (prefixWord ++ tailWord_1475116).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475116).length < 2 ^ (prefixWord ++ tailWord_1475116).sum := by decide
  have hdescent : baseEnd_1475116 < baseStart_1475116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475164 : List Nat := [2, 2, 4, 1, 3, 1, 2, 6]
def baseStart_1475164 : Nat := 118140960795 + 1475164 * 2 ^ 59
def prefixEnd_1475164 : Nat := 4983230072969 + 3 ^ 40 * 1475164 * 2
def baseEnd_1475164 : Nat := 112217507586543947817163

theorem tailTrace_1475164 : CollatzResearch.WordTrace tailWord_1475164 prefixEnd_1475164 112217507586543947817163 := by
  unfold tailWord_1475164
  simp only [CollatzResearch.WordTrace]
  refine ⟨26901825613870120399252273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35869100818493493865669697 26901825613870120399252273)
  ·
    refine ⟨20176369210402590299439205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26901825613870120399252273 20176369210402590299439205)
    ·
      refine ⟨3783069226950485681144851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20176369210402590299439205 3783069226950485681144851)
      ·
        refine ⟨5674603840425728521717277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3783069226950485681144851 5674603840425728521717277)
        ·
          refine ⟨2127976440159648195643979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5674603840425728521717277 2127976440159648195643979)
          ·
            refine ⟨3191964660239472293465969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2127976440159648195643979 3191964660239472293465969)
            ·
              refine ⟨2393973495179604220099477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3191964660239472293465969 2393973495179604220099477)
              ·
                refine ⟨112217507586543947817163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2393973495179604220099477 112217507586543947817163)
                ·
                  rfl

theorem cell21_1475164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 2, 6].length) (baseStart_1475164 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1475164 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1475164 prefixEnd_1475164 := by exact prefixLift 1475164
  have htrace : WordTrace (prefixWord ++ tailWord_1475164) baseStart_1475164 baseEnd_1475164 := by
    simpa [prefixWord, tailWord_1475164, baseEnd_1475164] using wordTrace_append hprefix tailTrace_1475164
  have hstable : (prefixWord ++ tailWord_1475164).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475164).length < 2 ^ (prefixWord ++ tailWord_1475164).sum := by decide
  have hdescent : baseEnd_1475164 < baseStart_1475164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475299 : List Nat := [1, 1, 1, 7, 1, 2, 1, 7]
def baseStart_1475299 : Nat := 118140960795 + 1475299 * 2 ^ 59
def prefixEnd_1475299 : Nat := 4983230072969 + 3 ^ 40 * 1475299 * 2
def baseEnd_1475299 : Nat := 112227777199633869567071

theorem tailTrace_1475299 : CollatzResearch.WordTrace tailWord_1475299 prefixEnd_1475299 112227777199633869567071 := by
  unfold tailWord_1475299
  simp only [CollatzResearch.WordTrace]
  refine ⟨53808575082251158854668951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35872383388167439236445967 53808575082251158854668951)
  ·
    refine ⟨80712862623376738282003427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53808575082251158854668951 80712862623376738282003427)
    ·
      refine ⟨121069293935065107423005141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80712862623376738282003427 121069293935065107423005141)
      ·
        refine ⟨2837561576603088455226683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 121069293935065107423005141 2837561576603088455226683)
        ·
          refine ⟨4256342364904632682840025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2837561576603088455226683 4256342364904632682840025)
          ·
            refine ⟨3192256773678474512130019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4256342364904632682840025 3192256773678474512130019)
            ·
              refine ⟨4788385160517711768195029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3192256773678474512130019 4788385160517711768195029)
              ·
                refine ⟨112227777199633869567071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4788385160517711768195029 112227777199633869567071)
                ·
                  rfl

theorem cell21_1475299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 7].length) (baseStart_1475299 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1475299 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1475299 prefixEnd_1475299 := by exact prefixLift 1475299
  have htrace : WordTrace (prefixWord ++ tailWord_1475299) baseStart_1475299 baseEnd_1475299 := by
    simpa [prefixWord, tailWord_1475299, baseEnd_1475299] using wordTrace_append hprefix tailTrace_1475299
  have hstable : (prefixWord ++ tailWord_1475299).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475299).length < 2 ^ (prefixWord ++ tailWord_1475299).sum := by decide
  have hdescent : baseEnd_1475299 < baseStart_1475299 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475465 : List Nat := [1, 2, 1, 1, 5, 2, 2, 2, 5]
def baseStart_1475465 : Nat := 118140960795 + 1475465 * 2 ^ 59
def prefixEnd_1475465 : Nat := 4983230072969 + 3 ^ 40 * 1475465 * 2
def baseEnd_1475465 : Nat := 336721215060522208934207

theorem tailTrace_1475465 : CollatzResearch.WordTrace tailWord_1475465 prefixEnd_1475465 336721215060522208934207 := by
  unfold tailWord_1475465
  simp only [CollatzResearch.WordTrace]
  refine ⟨53814629599649769205211849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35876419733099846136807899 53814629599649769205211849)
  ·
    refine ⟨40360972199737326903908887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53814629599649769205211849 40360972199737326903908887)
    ·
      refine ⟨60541458299605990355863331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40360972199737326903908887 60541458299605990355863331)
      ·
        refine ⟨90812187449408985533794997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60541458299605990355863331 90812187449408985533794997)
        ·
          refine ⟨8513642573382092393793281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 90812187449408985533794997 8513642573382092393793281)
          ·
            refine ⟨6385231930036569295344961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8513642573382092393793281 6385231930036569295344961)
            ·
              refine ⟨4788923947527426971508721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6385231930036569295344961 4788923947527426971508721)
              ·
                refine ⟨3591692960645570228631541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4788923947527426971508721 3591692960645570228631541)
                ·
                  refine ⟨336721215060522208934207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3591692960645570228631541 336721215060522208934207)
                  ·
                    rfl

theorem cell21_1475465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 2, 5].length) (baseStart_1475465 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1475465 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1475465 prefixEnd_1475465 := by exact prefixLift 1475465
  have htrace : WordTrace (prefixWord ++ tailWord_1475465) baseStart_1475465 baseEnd_1475465 := by
    simpa [prefixWord, tailWord_1475465, baseEnd_1475465] using wordTrace_append hprefix tailTrace_1475465
  have hstable : (prefixWord ++ tailWord_1475465).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475465).length < 2 ^ (prefixWord ++ tailWord_1475465).sum := by decide
  have hdescent : baseEnd_1475465 < baseStart_1475465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475479 : List Nat := [1, 1, 3, 3, 1, 2, 1, 1, 8]
def baseStart_1475479 : Nat := 118140960795 + 1475479 * 2 ^ 59
def prefixEnd_1475479 : Nat := 4983230072969 + 3 ^ 40 * 1475479 * 2
def baseEnd_1475479 : Nat := 336724410051261295700845

theorem tailTrace_1475479 : CollatzResearch.WordTrace tailWord_1475479 prefixEnd_1475479 336724410051261295700845 := by
  unfold tailWord_1475479
  simp only [CollatzResearch.WordTrace]
  refine ⟨53815140221599049596221491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35876760147732699730814327 53815140221599049596221491)
  ·
    refine ⟨80722710332398574394332237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53815140221599049596221491 80722710332398574394332237)
    ·
      refine ⟨30271016374649465397874589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80722710332398574394332237 30271016374649465397874589)
      ·
        refine ⟨11351631140493549524202971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30271016374649465397874589 11351631140493549524202971)
        ·
          refine ⟨17027446710740324286304457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11351631140493549524202971 17027446710740324286304457)
          ·
            refine ⟨12770585033055243214728343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17027446710740324286304457 12770585033055243214728343)
            ·
              refine ⟨19155877549582864822092515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12770585033055243214728343 19155877549582864822092515)
              ·
                refine ⟨28733816324374297233138773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19155877549582864822092515 28733816324374297233138773)
                ·
                  refine ⟨336724410051261295700845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28733816324374297233138773 336724410051261295700845)
                  ·
                    rfl

theorem cell21_1475479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 8].length) (baseStart_1475479 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1475479 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1475479 prefixEnd_1475479 := by exact prefixLift 1475479
  have htrace : WordTrace (prefixWord ++ tailWord_1475479) baseStart_1475479 baseEnd_1475479 := by
    simpa [prefixWord, tailWord_1475479, baseEnd_1475479] using wordTrace_append hprefix tailTrace_1475479
  have hstable : (prefixWord ++ tailWord_1475479).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475479).length < 2 ^ (prefixWord ++ tailWord_1475479).sum := by decide
  have hdescent : baseEnd_1475479 < baseStart_1475479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475513 : List Nat := [1, 2, 1, 4, 2, 2, 4, 1, 4]
def baseStart_1475513 : Nat := 118140960795 + 1475513 * 2 ^ 59
def prefixEnd_1475513 : Nat := 4983230072969 + 3 ^ 40 * 1475513 * 2
def baseEnd_1475513 : Nat := 336732169314484792134109

theorem tailTrace_1475513 : CollatzResearch.WordTrace tailWord_1475513 prefixEnd_1475513 336732169314484792134109 := by
  unfold tailWord_1475513
  simp only [CollatzResearch.WordTrace]
  refine ⟨53816380303475873402959193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35877586868983915601972795 53816380303475873402959193)
  ·
    refine ⟨40362285227606905052219395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53816380303475873402959193 40362285227606905052219395)
    ·
      refine ⟨60543427841410357578329093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40362285227606905052219395 60543427841410357578329093)
      ·
        refine ⟨11351892720264442045936705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60543427841410357578329093 11351892720264442045936705)
        ·
          refine ⟨8513919540198331534452529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11351892720264442045936705 8513919540198331534452529)
          ·
            refine ⟨6385439655148748650839397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8513919540198331534452529 6385439655148748650839397)
            ·
              refine ⟨1197269935340390372032387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6385439655148748650839397 1197269935340390372032387)
              ·
                refine ⟨1795904903010585558048581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1197269935340390372032387 1795904903010585558048581)
                ·
                  refine ⟨336732169314484792134109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1795904903010585558048581 336732169314484792134109)
                  ·
                    rfl

theorem cell21_1475513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 4, 1, 4].length) (baseStart_1475513 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1475513 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1475513 prefixEnd_1475513 := by exact prefixLift 1475513
  have htrace : WordTrace (prefixWord ++ tailWord_1475513) baseStart_1475513 baseEnd_1475513 := by
    simpa [prefixWord, tailWord_1475513, baseEnd_1475513] using wordTrace_append hprefix tailTrace_1475513
  have hstable : (prefixWord ++ tailWord_1475513).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475513).length < 2 ^ (prefixWord ++ tailWord_1475513).sum := by decide
  have hdescent : baseEnd_1475513 < baseStart_1475513 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475617 : List Nat := [1, 2, 3, 2, 3, 1, 1, 3, 5]
def baseStart_1475617 : Nat := 118140960795 + 1475617 * 2 ^ 59
def prefixEnd_1475617 : Nat := 4983230072969 + 3 ^ 40 * 1475617 * 2
def baseEnd_1475617 : Nat := 336755903531403722400563

theorem tailTrace_1475617 : CollatzResearch.WordTrace tailWord_1475617 prefixEnd_1475617 336755903531403722400563 := by
  unfold tailWord_1475617
  simp only [CollatzResearch.WordTrace]
  refine ⟨53820173495099099164745105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35880115663399399443163403 53820173495099099164745105)
  ·
    refine ⟨40365130121324324373558829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53820173495099099164745105 40365130121324324373558829)
    ·
      refine ⟨15136923795496621640084561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40365130121324324373558829 15136923795496621640084561)
      ·
        refine ⟨11352692846622466230063421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15136923795496621640084561 11352692846622466230063421)
        ·
          refine ⟨4257259817483424836273783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11352692846622466230063421 4257259817483424836273783)
          ·
            refine ⟨6385889726225137254410675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4257259817483424836273783 6385889726225137254410675)
            ·
              refine ⟨9578834589337705881616013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6385889726225137254410675 9578834589337705881616013)
              ·
                refine ⟨3592062971001639705606005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9578834589337705881616013 3592062971001639705606005)
                ·
                  refine ⟨336755903531403722400563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3592062971001639705606005 336755903531403722400563)
                  ·
                    rfl

theorem cell21_1475617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 3, 5].length) (baseStart_1475617 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1475617 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1475617 prefixEnd_1475617 := by exact prefixLift 1475617
  have htrace : WordTrace (prefixWord ++ tailWord_1475617) baseStart_1475617 baseEnd_1475617 := by
    simpa [prefixWord, tailWord_1475617, baseEnd_1475617] using wordTrace_append hprefix tailTrace_1475617
  have hstable : (prefixWord ++ tailWord_1475617).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475617).length < 2 ^ (prefixWord ++ tailWord_1475617).sum := by decide
  have hdescent : baseEnd_1475617 < baseStart_1475617 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475682 : List Nat := [3, 3, 2, 2, 1, 1, 4, 1, 4]
def baseStart_1475682 : Nat := 118140960795 + 1475682 * 2 ^ 59
def prefixEnd_1475682 : Nat := 4983230072969 + 3 ^ 40 * 1475682 * 2
def baseEnd_1475682 : Nat := 336770737416978053817097

theorem tailTrace_1475682 : CollatzResearch.WordTrace tailWord_1475682 prefixEnd_1475682 336770737416978053817097 := by
  unfold tailWord_1475682
  simp only [CollatzResearch.WordTrace]
  refine ⟨13455636059965903816465325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35881696159909076843907533 13455636059965903816465325)
  ·
    refine ⟨5045863522487213931174497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13455636059965903816465325 5045863522487213931174497)
    ·
      refine ⟨3784397641865410448380873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5045863522487213931174497 3784397641865410448380873)
      ·
        refine ⟨2838298231399057836285655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3784397641865410448380873 2838298231399057836285655)
        ·
          refine ⟨4257447347098586754428483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2838298231399057836285655 4257447347098586754428483)
          ·
            refine ⟨6386171020647880131642725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4257447347098586754428483 6386171020647880131642725)
            ·
              refine ⟨1197407066371477524683011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6386171020647880131642725 1197407066371477524683011)
              ·
                refine ⟨1796110599557216287024517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1197407066371477524683011 1796110599557216287024517)
                ·
                  refine ⟨336770737416978053817097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1796110599557216287024517 336770737416978053817097)
                  ·
                    rfl

theorem cell21_1475682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 4, 1, 4].length) (baseStart_1475682 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1475682 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1475682 prefixEnd_1475682 := by exact prefixLift 1475682
  have htrace : WordTrace (prefixWord ++ tailWord_1475682) baseStart_1475682 baseEnd_1475682 := by
    simpa [prefixWord, tailWord_1475682, baseEnd_1475682] using wordTrace_append hprefix tailTrace_1475682
  have hstable : (prefixWord ++ tailWord_1475682).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475682).length < 2 ^ (prefixWord ++ tailWord_1475682).sum := by decide
  have hdescent : baseEnd_1475682 < baseStart_1475682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475721 : List Nat := [1, 2, 1, 1, 4, 12]
def baseStart_1475721 : Nat := 118140960795 + 1475721 * 2 ^ 59
def prefixEnd_1475721 : Nat := 4983230072969 + 3 ^ 40 * 1475721 * 2
def baseEnd_1475721 : Nat := 12473319916604542691371

theorem tailTrace_1475721 : CollatzResearch.WordTrace tailWord_1475721 prefixEnd_1475721 12473319916604542691371 := by
  unfold tailWord_1475721
  simp only [CollatzResearch.WordTrace]
  refine ⟨53823966686722324926531017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35882644457814883284354011 53823966686722324926531017)
  ·
    refine ⟨40367975015041743694898263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53823966686722324926531017 40367975015041743694898263)
    ·
      refine ⟨60551962522562615542347395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40367975015041743694898263 60551962522562615542347395)
      ·
        refine ⟨90827943783843923313521093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60551962522562615542347395 90827943783843923313521093)
        ·
          refine ⟨17030239459470735621285205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 90827943783843923313521093 17030239459470735621285205)
          ·
            refine ⟨12473319916604542691371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 17030239459470735621285205 12473319916604542691371)
            ·
              rfl

theorem cell21_1475721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 12].length) (baseStart_1475721 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1475721 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1475721 prefixEnd_1475721 := by exact prefixLift 1475721
  have htrace : WordTrace (prefixWord ++ tailWord_1475721) baseStart_1475721 baseEnd_1475721 := by
    simpa [prefixWord, tailWord_1475721, baseEnd_1475721] using wordTrace_append hprefix tailTrace_1475721
  have hstable : (prefixWord ++ tailWord_1475721).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475721).length < 2 ^ (prefixWord ++ tailWord_1475721).sum := by decide
  have hdescent : baseEnd_1475721 < baseStart_1475721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475786 : List Nat := [3, 1, 2, 1, 3, 2, 2, 4, 3]
def baseStart_1475786 : Nat := 118140960795 + 1475786 * 2 ^ 59
def prefixEnd_1475786 : Nat := 4983230072969 + 3 ^ 40 * 1475786 * 2
def baseEnd_1475786 : Nat := 336794471633896984083551

theorem tailTrace_1475786 : CollatzResearch.WordTrace tailWord_1475786 prefixEnd_1475786 336794471633896984083551 := by
  unfold tailWord_1475786
  simp only [CollatzResearch.WordTrace]
  refine ⟨13456584357871710256911803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35884224954324560685098141 13456584357871710256911803)
  ·
    refine ⟨20184876536807565385367705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13456584357871710256911803 20184876536807565385367705)
    ·
      refine ⟨15138657402605674039025779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20184876536807565385367705 15138657402605674039025779)
      ·
        refine ⟨22707986103908511058538669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15138657402605674039025779 22707986103908511058538669)
        ·
          refine ⟨8515494788965691646952001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22707986103908511058538669 8515494788965691646952001)
          ·
            refine ⟨6386621091724268735214001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8515494788965691646952001 6386621091724268735214001)
            ·
              refine ⟨4789965818793201551410501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6386621091724268735214001 4789965818793201551410501)
              ·
                refine ⟨898118591023725290889469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4789965818793201551410501 898118591023725290889469)
                ·
                  refine ⟨336794471633896984083551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 898118591023725290889469 336794471633896984083551)
                  ·
                    rfl

theorem cell21_1475786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 4, 3].length) (baseStart_1475786 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1475786 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1475786 prefixEnd_1475786 := by exact prefixLift 1475786
  have htrace : WordTrace (prefixWord ++ tailWord_1475786) baseStart_1475786 baseEnd_1475786 := by
    simpa [prefixWord, tailWord_1475786, baseEnd_1475786] using wordTrace_append hprefix tailTrace_1475786
  have hstable : (prefixWord ++ tailWord_1475786).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475786).length < 2 ^ (prefixWord ++ tailWord_1475786).sum := by decide
  have hdescent : baseEnd_1475786 < baseStart_1475786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475904 : List Nat := [2, 1, 1, 2, 2, 1, 4, 3, 5]
def baseStart_1475904 : Nat := 118140960795 + 1475904 * 2 ^ 59
def prefixEnd_1475904 : Nat := 4983230072969 + 3 ^ 40 * 1475904 * 2
def baseEnd_1475904 : Nat := 336821400841555001116643

theorem tailTrace_1475904 : CollatzResearch.WordTrace tailWord_1475904 prefixEnd_1475904 336821400841555001116643 := by
  unfold tailWord_1475904
  simp only [CollatzResearch.WordTrace]
  refine ⟨26915320622529673590221383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35887094163372898120295177 26915320622529673590221383)
  ·
    refine ⟨40372980933794510385332075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26915320622529673590221383 40372980933794510385332075)
    ·
      refine ⟨60559471400691765577998113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40372980933794510385332075 60559471400691765577998113)
      ·
        refine ⟨45419603550518824183498585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60559471400691765577998113 45419603550518824183498585)
        ·
          refine ⟨34064702662889118137623939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45419603550518824183498585 34064702662889118137623939)
          ·
            refine ⟨51097053994333677206435909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34064702662889118137623939 51097053994333677206435909)
            ·
              refine ⟨9580697623937564476206733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51097053994333677206435909 9580697623937564476206733)
              ·
                refine ⟨3592761608976586678577525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9580697623937564476206733 3592761608976586678577525)
                ·
                  refine ⟨336821400841555001116643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3592761608976586678577525 336821400841555001116643)
                  ·
                    rfl

theorem cell21_1475904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 3, 5].length) (baseStart_1475904 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1475904 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1475904 prefixEnd_1475904 := by exact prefixLift 1475904
  have htrace : WordTrace (prefixWord ++ tailWord_1475904) baseStart_1475904 baseEnd_1475904 := by
    simpa [prefixWord, tailWord_1475904, baseEnd_1475904] using wordTrace_append hprefix tailTrace_1475904
  have hstable : (prefixWord ++ tailWord_1475904).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475904).length < 2 ^ (prefixWord ++ tailWord_1475904).sum := by decide
  have hdescent : baseEnd_1475904 < baseStart_1475904 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475980 : List Nat := [2, 2, 1, 2, 1, 3, 1, 4, 5]
def baseStart_1475980 : Nat := 118140960795 + 1475980 * 2 ^ 59
def prefixEnd_1475980 : Nat := 4983230072969 + 3 ^ 40 * 1475980 * 2
def baseEnd_1475980 : Nat := 336838745076995757849821

theorem tailTrace_1475980 : CollatzResearch.WordTrace tailWord_1475980 prefixEnd_1475980 336838745076995757849821 := by
  unfold tailWord_1475980
  simp only [CollatzResearch.WordTrace]
  refine ⟨26916706596392006080104697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35888942128522674773472929 26916706596392006080104697)
  ·
    refine ⟨20187529947294004560078523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26916706596392006080104697 20187529947294004560078523)
    ·
      refine ⟨30281294920941006840117785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20187529947294004560078523 30281294920941006840117785)
      ·
        refine ⟨22710971190705755130088339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30281294920941006840117785 22710971190705755130088339)
        ·
          refine ⟨34066456786058632695132509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22710971190705755130088339 34066456786058632695132509)
          ·
            refine ⟨12774921294771987260674691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34066456786058632695132509 12774921294771987260674691)
            ·
              refine ⟨19162381942157980891012037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12774921294771987260674691 19162381942157980891012037)
              ·
                refine ⟨3592946614154621417064757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19162381942157980891012037 3592946614154621417064757)
                ·
                  refine ⟨336838745076995757849821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3592946614154621417064757 336838745076995757849821)
                  ·
                    rfl

theorem cell21_1475980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 4, 5].length) (baseStart_1475980 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1475980 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1475980 prefixEnd_1475980 := by exact prefixLift 1475980
  have htrace : WordTrace (prefixWord ++ tailWord_1475980) baseStart_1475980 baseEnd_1475980 := by
    simpa [prefixWord, tailWord_1475980, baseEnd_1475980] using wordTrace_append hprefix tailTrace_1475980
  have hstable : (prefixWord ++ tailWord_1475980).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475980).length < 2 ^ (prefixWord ++ tailWord_1475980).sum := by decide
  have hdescent : baseEnd_1475980 < baseStart_1475980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476197 : List Nat := [1, 3, 1, 3, 3, 3, 2, 1, 4]
def baseStart_1476197 : Nat := 118140960795 + 1476197 * 2 ^ 59
def prefixEnd_1476197 : Nat := 4983230072969 + 3 ^ 40 * 1476197 * 2
def baseEnd_1476197 : Nat := 336888267433451602732711

theorem tailTrace_1476197 : CollatzResearch.WordTrace tailWord_1476197 prefixEnd_1476197 336888267433451602732711 := by
  unfold tailWord_1476197
  simp only [CollatzResearch.WordTrace]
  refine ⟨53841327832997858220858845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35894218555331905480572563 53841327832997858220858845)
  ·
    refine ⟨20190497937374196832822067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53841327832997858220858845 20190497937374196832822067)
    ·
      refine ⟨30285746906061295249233101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20190497937374196832822067 30285746906061295249233101)
      ·
        refine ⟨11357155089772985718462413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30285746906061295249233101 11357155089772985718462413)
        ·
          refine ⟨4258933158664869644423405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11357155089772985718462413 4258933158664869644423405)
          ·
            refine ⟨1597099934499326116658777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4258933158664869644423405 1597099934499326116658777)
            ·
              refine ⟨1197824950874494587494083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1597099934499326116658777 1197824950874494587494083)
              ·
                refine ⟨1796737426311741881241125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1197824950874494587494083 1796737426311741881241125)
                ·
                  refine ⟨336888267433451602732711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1796737426311741881241125 336888267433451602732711)
                  ·
                    rfl

theorem cell21_1476197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 2, 1, 4].length) (baseStart_1476197 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1476197 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1476197 prefixEnd_1476197 := by exact prefixLift 1476197
  have htrace : WordTrace (prefixWord ++ tailWord_1476197) baseStart_1476197 baseEnd_1476197 := by
    simpa [prefixWord, tailWord_1476197, baseEnd_1476197] using wordTrace_append hprefix tailTrace_1476197
  have hstable : (prefixWord ++ tailWord_1476197).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476197).length < 2 ^ (prefixWord ++ tailWord_1476197).sum := by decide
  have hdescent : baseEnd_1476197 < baseStart_1476197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476290 : List Nat := [3, 5, 1, 2, 1, 1, 1, 1, 6]
def baseStart_1476290 : Nat := 118140960795 + 1476290 * 2 ^ 59
def prefixEnd_1476290 : Nat := 4983230072969 + 3 ^ 40 * 1476290 * 2
def baseEnd_1476290 : Nat := 336909491300504107682521

theorem tailTrace_1476290 : CollatzResearch.WordTrace tailWord_1476290 prefixEnd_1476290 336909491300504107682521 := by
  unfold tailWord_1476290
  simp only [CollatzResearch.WordTrace]
  refine ⟨13461179955415233775998581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35896479881107290069329549 13461179955415233775998581)
  ·
    refine ⟨1261985620820178166499867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13461179955415233775998581 1261985620820178166499867)
    ·
      refine ⟨1892978431230267249749801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1261985620820178166499867 1892978431230267249749801)
      ·
        refine ⟨1419733823422700437312351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1892978431230267249749801 1419733823422700437312351)
        ·
          refine ⟨2129600735134050655968527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1419733823422700437312351 2129600735134050655968527)
          ·
            refine ⟨3194401102701075983952791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2129600735134050655968527 3194401102701075983952791)
            ·
              refine ⟨4791601654051613975929187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3194401102701075983952791 4791601654051613975929187)
              ·
                refine ⟨7187402481077420963893781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4791601654051613975929187 7187402481077420963893781)
                ·
                  refine ⟨336909491300504107682521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7187402481077420963893781 336909491300504107682521)
                  ·
                    rfl

theorem cell21_1476290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_1476290 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1476290 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1476290 prefixEnd_1476290 := by exact prefixLift 1476290
  have htrace : WordTrace (prefixWord ++ tailWord_1476290) baseStart_1476290 baseEnd_1476290 := by
    simpa [prefixWord, tailWord_1476290, baseEnd_1476290] using wordTrace_append hprefix tailTrace_1476290
  have hstable : (prefixWord ++ tailWord_1476290).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476290).length < 2 ^ (prefixWord ++ tailWord_1476290).sum := by decide
  have hdescent : baseEnd_1476290 < baseStart_1476290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476343 : List Nat := [1, 1, 3, 1, 1, 1, 4, 2, 7]
def baseStart_1476343 : Nat := 118140960795 + 1476343 * 2 ^ 59
def prefixEnd_1476343 : Nat := 4983230072969 + 3 ^ 40 * 1476343 * 2
def baseEnd_1476343 : Nat := 336921586622587793299079

theorem tailTrace_1476343 : CollatzResearch.WordTrace tailWord_1476343 prefixEnd_1476343 336921586622587793299079 := by
  unfold tailWord_1476343
  simp only [CollatzResearch.WordTrace]
  refine ⟨53846652890468925155673683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35897768593645950103782455 53846652890468925155673683)
  ·
    refine ⟨80769979335703387733510525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53846652890468925155673683 80769979335703387733510525)
    ·
      refine ⟨30288742250888770400066447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80769979335703387733510525 30288742250888770400066447)
      ·
        refine ⟨45433113376333155600099671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30288742250888770400066447 45433113376333155600099671)
        ·
          refine ⟨68149670064499733400149507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45433113376333155600099671 68149670064499733400149507)
          ·
            refine ⟨102224505096749600100224261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68149670064499733400149507 102224505096749600100224261)
            ·
              refine ⟨19167094705640550018792049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 102224505096749600100224261 19167094705640550018792049)
              ·
                refine ⟨14375321029230412514094037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19167094705640550018792049 14375321029230412514094037)
                ·
                  refine ⟨336921586622587793299079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14375321029230412514094037 336921586622587793299079)
                  ·
                    rfl

theorem cell21_1476343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 2, 7].length) (baseStart_1476343 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1476343 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1476343 prefixEnd_1476343 := by exact prefixLift 1476343
  have htrace : WordTrace (prefixWord ++ tailWord_1476343) baseStart_1476343 baseEnd_1476343 := by
    simpa [prefixWord, tailWord_1476343, baseEnd_1476343] using wordTrace_append hprefix tailTrace_1476343
  have hstable : (prefixWord ++ tailWord_1476343).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476343).length < 2 ^ (prefixWord ++ tailWord_1476343).sum := by decide
  have hdescent : baseEnd_1476343 < baseStart_1476343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476358 : List Nat := [6, 2, 2, 1, 2, 1, 2, 1, 4]
def baseStart_1476358 : Nat := 118140960795 + 1476358 * 2 ^ 59
def prefixEnd_1476358 : Nat := 4983230072969 + 3 ^ 40 * 1476358 * 2
def baseEnd_1476358 : Nat := 336925009826951100549049

theorem tailTrace_1476358 : CollatzResearch.WordTrace tailWord_1476358 prefixEnd_1476358 336925009826951100549049 := by
  unfold tailWord_1476358
  simp only [CollatzResearch.WordTrace]
  refine ⟨1682724999544205709920929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 35898133323609721811646485 1682724999544205709920929)
  ·
    refine ⟨1262043749658154282440697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1682724999544205709920929 1262043749658154282440697)
    ·
      refine ⟨946532812243615711830523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1262043749658154282440697 946532812243615711830523)
      ·
        refine ⟨1419799218365423567745785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 946532812243615711830523 1419799218365423567745785)
        ·
          refine ⟨1064849413774067675809339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1419799218365423567745785 1064849413774067675809339)
          ·
            refine ⟨1597274120661101513714009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1064849413774067675809339 1597274120661101513714009)
            ·
              refine ⟨1197955590495826135285507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1597274120661101513714009 1197955590495826135285507)
              ·
                refine ⟨1796933385743739202928261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1197955590495826135285507 1796933385743739202928261)
                ·
                  refine ⟨336925009826951100549049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1796933385743739202928261 336925009826951100549049)
                  ·
                    rfl

theorem cell21_1476358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_1476358 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1476358 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1476358 prefixEnd_1476358 := by exact prefixLift 1476358
  have htrace : WordTrace (prefixWord ++ tailWord_1476358) baseStart_1476358 baseEnd_1476358 := by
    simpa [prefixWord, tailWord_1476358, baseEnd_1476358] using wordTrace_append hprefix tailTrace_1476358
  have hstable : (prefixWord ++ tailWord_1476358).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476358).length < 2 ^ (prefixWord ++ tailWord_1476358).sum := by decide
  have hdescent : baseEnd_1476358 < baseStart_1476358 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476405 : List Nat := [1, 3, 3, 1, 4, 9]
def baseStart_1476405 : Nat := 118140960795 + 1476405 * 2 ^ 59
def prefixEnd_1476405 : Nat := 4983230072969 + 3 ^ 40 * 1476405 * 2
def baseEnd_1476405 : Nat := 12479101328418128269097

theorem tailTrace_1476405 : CollatzResearch.WordTrace tailWord_1476405 prefixEnd_1476405 12479101328418128269097 := by
  unfold tailWord_1476405
  simp only [CollatzResearch.WordTrace]
  refine ⟨53848914216244309744430669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35899276144162873162953779 53848914216244309744430669)
  ·
    refine ⟨20193342831091616154161501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53848914216244309744430669 20193342831091616154161501)
    ·
      refine ⟨7572503561659356057810563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20193342831091616154161501 7572503561659356057810563)
      ·
        refine ⟨11358755342489034086715845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7572503561659356057810563 11358755342489034086715845)
        ·
          refine ⟨2129766626716693891259221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11358755342489034086715845 2129766626716693891259221)
          ·
            refine ⟨12479101328418128269097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2129766626716693891259221 12479101328418128269097)
            ·
              rfl

theorem cell21_1476405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 9].length) (baseStart_1476405 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1476405 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1476405 prefixEnd_1476405 := by exact prefixLift 1476405
  have htrace : WordTrace (prefixWord ++ tailWord_1476405) baseStart_1476405 baseEnd_1476405 := by
    simpa [prefixWord, tailWord_1476405, baseEnd_1476405] using wordTrace_append hprefix tailTrace_1476405
  have hstable : (prefixWord ++ tailWord_1476405).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476405).length < 2 ^ (prefixWord ++ tailWord_1476405).sum := by decide
  have hdescent : baseEnd_1476405 < baseStart_1476405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476436 : List Nat := [2, 4, 1, 1, 3, 1, 1, 1, 7]
def baseStart_1476436 : Nat := 118140960795 + 1476436 * 2 ^ 59
def prefixEnd_1476436 : Nat := 4983230072969 + 3 ^ 40 * 1476436 * 2
def baseEnd_1476436 : Nat := 336942810489640298248889

theorem tailTrace_1476436 : CollatzResearch.WordTrace tailWord_1476436 prefixEnd_1476436 336942810489640298248889 := by
  unfold tailWord_1476436
  simp only [CollatzResearch.WordTrace]
  refine ⟨26925022439566001019404581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35900029919421334692539441 26925022439566001019404581)
  ·
    refine ⟨5048441707418625191138359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26925022439566001019404581 5048441707418625191138359)
    ·
      refine ⟨7572662561127937786707539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5048441707418625191138359 7572662561127937786707539)
      ·
        refine ⟨11358993841691906680061309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7572662561127937786707539 11358993841691906680061309)
        ·
          refine ⟨4259622690634465005022991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11358993841691906680061309 4259622690634465005022991)
          ·
            refine ⟨6389434035951697507534487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4259622690634465005022991 6389434035951697507534487)
            ·
              refine ⟨9584151053927546261301731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6389434035951697507534487 9584151053927546261301731)
              ·
                refine ⟨14376226580891319391952597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9584151053927546261301731 14376226580891319391952597)
                ·
                  refine ⟨336942810489640298248889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14376226580891319391952597 336942810489640298248889)
                  ·
                    rfl

theorem cell21_1476436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_1476436 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1476436 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1476436 prefixEnd_1476436 := by exact prefixLift 1476436
  have htrace : WordTrace (prefixWord ++ tailWord_1476436) baseStart_1476436 baseEnd_1476436 := by
    simpa [prefixWord, tailWord_1476436, baseEnd_1476436] using wordTrace_append hprefix tailTrace_1476436
  have hstable : (prefixWord ++ tailWord_1476436).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476436).length < 2 ^ (prefixWord ++ tailWord_1476436).sum := by decide
  have hdescent : baseEnd_1476436 < baseStart_1476436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476470 : List Nat := [5, 1, 1, 3, 2, 1, 2, 1, 5]
def baseStart_1476470 : Nat := 118140960795 + 1476470 * 2 ^ 59
def prefixEnd_1476470 : Nat := 4983230072969 + 3 ^ 40 * 1476470 * 2
def baseEnd_1476470 : Nat := 336950569752863794682153

theorem tailTrace_1476470 : CollatzResearch.WordTrace tailWord_1476470 prefixEnd_1476470 336950569752863794682153 := by
  unfold tailWord_1476470
  simp only [CollatzResearch.WordTrace]
  refine ⟨3365705310063051615346679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 35900856640672550563697909 3365705310063051615346679)
  ·
    refine ⟨5048557965094577423020019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3365705310063051615346679 5048557965094577423020019)
    ·
      refine ⟨7572836947641866134530029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5048557965094577423020019 7572836947641866134530029)
      ·
        refine ⟨2839813855365699800448761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7572836947641866134530029 2839813855365699800448761)
        ·
          refine ⟨2129860391524274850336571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2839813855365699800448761 2129860391524274850336571)
          ·
            refine ⟨3194790587286412275504857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2129860391524274850336571 3194790587286412275504857)
            ·
              refine ⟨2396092940464809206628643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3194790587286412275504857 2396092940464809206628643)
              ·
                refine ⟨3594139410697213809942965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2396092940464809206628643 3594139410697213809942965)
                ·
                  refine ⟨336950569752863794682153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3594139410697213809942965 336950569752863794682153)
                  ·
                    rfl

theorem cell21_1476470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 2, 1, 5].length) (baseStart_1476470 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1476470 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1476470 prefixEnd_1476470 := by exact prefixLift 1476470
  have htrace : WordTrace (prefixWord ++ tailWord_1476470) baseStart_1476470 baseEnd_1476470 := by
    simpa [prefixWord, tailWord_1476470, baseEnd_1476470] using wordTrace_append hprefix tailTrace_1476470
  have hstable : (prefixWord ++ tailWord_1476470).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476470).length < 2 ^ (prefixWord ++ tailWord_1476470).sum := by decide
  have hdescent : baseEnd_1476470 < baseStart_1476470 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476498 : List Nat := [3, 2, 3, 2, 1, 2, 1, 7]
def baseStart_1476498 : Nat := 118140960795 + 1476498 * 2 ^ 59
def prefixEnd_1476498 : Nat := 4983230072969 + 3 ^ 40 * 1476498 * 2
def baseEnd_1476498 : Nat := 112318986578113989405143

theorem tailTrace_1476498 : CollatzResearch.WordTrace tailWord_1476498 prefixEnd_1476498 112318986578113989405143 := by
  unfold tailWord_1476498
  simp only [CollatzResearch.WordTrace]
  refine ⟨13463076551226846656891537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35901537469938257751710765 13463076551226846656891537)
  ·
    refine ⟨10097307413420134992668653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13463076551226846656891537 10097307413420134992668653)
    ·
      refine ⟨3786490280032550622250745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10097307413420134992668653 3786490280032550622250745)
      ·
        refine ⟨2839867710024412966688059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3786490280032550622250745 2839867710024412966688059)
        ·
          refine ⟨4259801565036619450032089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2839867710024412966688059 4259801565036619450032089)
          ·
            refine ⟨3194851173777464587524067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4259801565036619450032089 3194851173777464587524067)
            ·
              refine ⟨4792276760666196881286101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3194851173777464587524067 4792276760666196881286101)
              ·
                refine ⟨112318986578113989405143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4792276760666196881286101 112318986578113989405143)
                ·
                  rfl

theorem cell21_1476498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 7].length) (baseStart_1476498 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1476498 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1476498 prefixEnd_1476498 := by exact prefixLift 1476498
  have htrace : WordTrace (prefixWord ++ tailWord_1476498) baseStart_1476498 baseEnd_1476498 := by
    simpa [prefixWord, tailWord_1476498, baseEnd_1476498] using wordTrace_append hprefix tailTrace_1476498
  have hstable : (prefixWord ++ tailWord_1476498).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476498).length < 2 ^ (prefixWord ++ tailWord_1476498).sum := by decide
  have hdescent : baseEnd_1476498 < baseStart_1476498 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476504 : List Nat := [2, 1, 2, 6, 2, 1, 1, 3, 3]
def baseStart_1476504 : Nat := 118140960795 + 1476504 * 2 ^ 59
def prefixEnd_1476504 : Nat := 4983230072969 + 3 ^ 40 * 1476504 * 2
def baseEnd_1476504 : Nat := 336958329016087291115417

theorem tailTrace_1476504 : CollatzResearch.WordTrace tailWord_1476504 prefixEnd_1476504 336958329016087291115417 := by
  unfold tailWord_1476504
  simp only [CollatzResearch.WordTrace]
  refine ⟨26926262521442824826142283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35901683361923766434856377 26926262521442824826142283)
  ·
    refine ⟨40389393782164237239213425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26926262521442824826142283 40389393782164237239213425)
    ·
      refine ⟨30292045336623177929410069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40389393782164237239213425 30292045336623177929410069)
      ·
        refine ⟨1419939625154211465441097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 30292045336623177929410069 1419939625154211465441097)
        ·
          refine ⟨1064954718865658599080823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1419939625154211465441097 1064954718865658599080823)
          ·
            refine ⟨1597432078298487898621235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1064954718865658599080823 1597432078298487898621235)
            ·
              refine ⟨2396148117447731847931853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1597432078298487898621235 2396148117447731847931853)
              ·
                refine ⟨898555544042899442974445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2396148117447731847931853 898555544042899442974445)
                ·
                  refine ⟨336958329016087291115417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 898555544042899442974445 336958329016087291115417)
                  ·
                    rfl

theorem cell21_1476504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 1, 3, 3].length) (baseStart_1476504 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1476504 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1476504 prefixEnd_1476504 := by exact prefixLift 1476504
  have htrace : WordTrace (prefixWord ++ tailWord_1476504) baseStart_1476504 baseEnd_1476504 := by
    simpa [prefixWord, tailWord_1476504, baseEnd_1476504] using wordTrace_append hprefix tailTrace_1476504
  have hstable : (prefixWord ++ tailWord_1476504).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476504).length < 2 ^ (prefixWord ++ tailWord_1476504).sum := by decide
  have hdescent : baseEnd_1476504 < baseStart_1476504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476529 : List Nat := [1, 2, 2, 4, 2, 3, 1, 1, 5]
def baseStart_1476529 : Nat := 118140960795 + 1476529 * 2 ^ 59
def prefixEnd_1476529 : Nat := 4983230072969 + 3 ^ 40 * 1476529 * 2
def baseEnd_1476529 : Nat := 336964034356692803198699

theorem tailTrace_1476529 : CollatzResearch.WordTrace tailWord_1476529 prefixEnd_1476529 336964034356692803198699 := by
  unfold tailWord_1476529
  simp only [CollatzResearch.WordTrace]
  refine ⟨53853436867795078921944641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35902291245196719281296427 53853436867795078921944641)
  ·
    refine ⟨40390077650846309191458481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53853436867795078921944641 40390077650846309191458481)
    ·
      refine ⟨30292558238134731893593861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40390077650846309191458481 30292558238134731893593861)
      ·
        refine ⟨5679854669650262230048849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30292558238134731893593861 5679854669650262230048849)
        ·
          refine ⟨4259891002237696672536637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5679854669650262230048849 4259891002237696672536637)
          ·
            refine ⟨1597459125839136252201239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4259891002237696672536637 1597459125839136252201239)
            ·
              refine ⟨2396188688758704378301859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1597459125839136252201239 2396188688758704378301859)
              ·
                refine ⟨3594283033138056567452789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2396188688758704378301859 3594283033138056567452789)
                ·
                  refine ⟨336964034356692803198699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3594283033138056567452789 336964034356692803198699)
                  ·
                    rfl

theorem cell21_1476529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 1, 1, 5].length) (baseStart_1476529 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1476529 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1476529 prefixEnd_1476529 := by exact prefixLift 1476529
  have htrace : WordTrace (prefixWord ++ tailWord_1476529) baseStart_1476529 baseEnd_1476529 := by
    simpa [prefixWord, tailWord_1476529, baseEnd_1476529] using wordTrace_append hprefix tailTrace_1476529
  have hstable : (prefixWord ++ tailWord_1476529).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476529).length < 2 ^ (prefixWord ++ tailWord_1476529).sum := by decide
  have hdescent : baseEnd_1476529 < baseStart_1476529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476636 : List Nat := [2, 2, 3, 1, 3, 3, 1, 2, 4]
def baseStart_1476636 : Nat := 118140960795 + 1476636 * 2 ^ 59
def prefixEnd_1476636 : Nat := 4983230072969 + 3 ^ 40 * 1476636 * 2
def baseEnd_1476636 : Nat := 336988453214484394915147

theorem tailTrace_1476636 : CollatzResearch.WordTrace tailWord_1476636 prefixEnd_1476636 336988453214484394915147 := by
  unfold tailWord_1476636
  simp only [CollatzResearch.WordTrace]
  refine ⟨26928669739203718098044881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35904892985604957464059841 26928669739203718098044881)
  ·
    refine ⟨20196502304402788573533661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26928669739203718098044881 20196502304402788573533661)
    ·
      refine ⟨7573688364151045715075123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20196502304402788573533661 7573688364151045715075123)
      ·
        refine ⟨11360532546226568572612685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7573688364151045715075123 11360532546226568572612685)
        ·
          refine ⟨4260199704834963214729757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11360532546226568572612685 4260199704834963214729757)
          ·
            refine ⟨1597574889313111205523659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4260199704834963214729757 1597574889313111205523659)
            ·
              refine ⟨2396362333969666808285489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1597574889313111205523659 2396362333969666808285489)
              ·
                refine ⟨1797271750477250106214117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2396362333969666808285489 1797271750477250106214117)
                ·
                  refine ⟨336988453214484394915147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1797271750477250106214117 336988453214484394915147)
                  ·
                    rfl

theorem cell21_1476636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 1, 2, 4].length) (baseStart_1476636 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1476636 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1476636 prefixEnd_1476636 := by exact prefixLift 1476636
  have htrace : WordTrace (prefixWord ++ tailWord_1476636) baseStart_1476636 baseEnd_1476636 := by
    simpa [prefixWord, tailWord_1476636, baseEnd_1476636] using wordTrace_append hprefix tailTrace_1476636
  have hstable : (prefixWord ++ tailWord_1476636).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476636).length < 2 ^ (prefixWord ++ tailWord_1476636).sum := by decide
  have hdescent : baseEnd_1476636 < baseStart_1476636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476709 : List Nat := [1, 3, 1, 3, 2, 3, 2, 6]
def baseStart_1476709 : Nat := 118140960795 + 1476709 * 2 ^ 59
def prefixEnd_1476709 : Nat := 4983230072969 + 3 ^ 40 * 1476709 * 2
def baseEnd_1476709 : Nat := 112335037603017496732777

theorem tailTrace_1476709 : CollatzResearch.WordTrace tailWord_1476709 prefixEnd_1476709 112335037603017496732777 := by
  unfold tailWord_1476709
  simp only [CollatzResearch.WordTrace]
  refine ⟨53860002007142969663497181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35906668004761979775664787 53860002007142969663497181)
  ·
    refine ⟨20197500752678613623811443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53860002007142969663497181 20197500752678613623811443)
    ·
      refine ⟨30296251129017920435717165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20197500752678613623811443 30296251129017920435717165)
      ·
        refine ⟨11361094173381720163393937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30296251129017920435717165 11361094173381720163393937)
        ·
          refine ⟨8520820630036290122545453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11361094173381720163393937 8520820630036290122545453)
          ·
            refine ⟨3195307736263608795954545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8520820630036290122545453 3195307736263608795954545)
            ·
              refine ⟨2396480802197706596965909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3195307736263608795954545 2396480802197706596965909)
              ·
                refine ⟨112335037603017496732777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2396480802197706596965909 112335037603017496732777)
                ·
                  rfl

theorem cell21_1476709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2, 6].length) (baseStart_1476709 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1476709 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1476709 prefixEnd_1476709 := by exact prefixLift 1476709
  have htrace : WordTrace (prefixWord ++ tailWord_1476709) baseStart_1476709 baseEnd_1476709 := by
    simpa [prefixWord, tailWord_1476709, baseEnd_1476709] using wordTrace_append hprefix tailTrace_1476709
  have hstable : (prefixWord ++ tailWord_1476709).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476709).length < 2 ^ (prefixWord ++ tailWord_1476709).sum := by decide
  have hdescent : baseEnd_1476709 < baseStart_1476709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476844 : List Nat := [2, 2, 1, 1, 2, 3, 3, 7]
def baseStart_1476844 : Nat := 118140960795 + 1476844 * 2 ^ 59
def prefixEnd_1476844 : Nat := 4983230072969 + 3 ^ 40 * 1476844 * 2
def baseEnd_1476844 : Nat := 112345307216107418482685

theorem tailTrace_1476844 : CollatzResearch.WordTrace tailWord_1476844 prefixEnd_1476844 112345307216107418482685 := by
  unfold tailWord_1476844
  simp only [CollatzResearch.WordTrace]
  refine ⟨26932462930826943859830793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35909950574435925146441057 26932462930826943859830793)
  ·
    refine ⟨20199347198120207894873095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26932462930826943859830793 20199347198120207894873095)
    ·
      refine ⟨30299020797180311842309643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20199347198120207894873095 30299020797180311842309643)
      ·
        refine ⟨45448531195770467763464465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30299020797180311842309643 45448531195770467763464465)
        ·
          refine ⟨34086398396827850822598349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45448531195770467763464465 34086398396827850822598349)
          ·
            refine ⟨12782399398810444058474381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34086398396827850822598349 12782399398810444058474381)
            ·
              refine ⟨4793399774553916521927893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12782399398810444058474381 4793399774553916521927893)
              ·
                refine ⟨112345307216107418482685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4793399774553916521927893 112345307216107418482685)
                ·
                  rfl

theorem cell21_1476844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 7].length) (baseStart_1476844 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1476844 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1476844 prefixEnd_1476844 := by exact prefixLift 1476844
  have htrace : WordTrace (prefixWord ++ tailWord_1476844) baseStart_1476844 baseEnd_1476844 := by
    simpa [prefixWord, tailWord_1476844, baseEnd_1476844] using wordTrace_append hprefix tailTrace_1476844
  have hstable : (prefixWord ++ tailWord_1476844).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476844).length < 2 ^ (prefixWord ++ tailWord_1476844).sum := by decide
  have hdescent : baseEnd_1476844 < baseStart_1476844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476850 : List Nat := [3, 2, 1, 3, 2, 3, 1, 3, 3]
def baseStart_1476850 : Nat := 118140960795 + 1476850 * 2 ^ 59
def prefixEnd_1476850 : Nat := 4983230072969 + 3 ^ 40 * 1476850 * 2
def baseEnd_1476850 : Nat := 337037290930067578348043

theorem tailTrace_1476850 : CollatzResearch.WordTrace tailWord_1476850 prefixEnd_1476850 337037290930067578348043 := by
  unfold tailWord_1476850
  simp only [CollatzResearch.WordTrace]
  refine ⟨13466286174908037686095001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35910096466421433829586669 13466286174908037686095001)
  ·
    refine ⟨10099714631181028264571251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13466286174908037686095001 10099714631181028264571251)
    ·
      refine ⟨15149571946771542396856877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10099714631181028264571251 15149571946771542396856877)
      ·
        refine ⟨5681089480039328398821329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15149571946771542396856877 5681089480039328398821329)
        ·
          refine ⟨4260817110029496299115997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5681089480039328398821329 4260817110029496299115997)
          ·
            refine ⟨1597806416261061112168499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4260817110029496299115997 1597806416261061112168499)
            ·
              refine ⟨2396709624391591668252749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1597806416261061112168499 2396709624391591668252749)
              ·
                refine ⟨898766109146846875594781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2396709624391591668252749 898766109146846875594781)
                ·
                  refine ⟨337037290930067578348043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 898766109146846875594781 337037290930067578348043)
                  ·
                    rfl

theorem cell21_1476850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 1, 3, 3].length) (baseStart_1476850 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1476850 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1476850 prefixEnd_1476850 := by exact prefixLift 1476850
  have htrace : WordTrace (prefixWord ++ tailWord_1476850) baseStart_1476850 baseEnd_1476850 := by
    simpa [prefixWord, tailWord_1476850, baseEnd_1476850] using wordTrace_append hprefix tailTrace_1476850
  have hstable : (prefixWord ++ tailWord_1476850).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476850).length < 2 ^ (prefixWord ++ tailWord_1476850).sum := by decide
  have hdescent : baseEnd_1476850 < baseStart_1476850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476926 : List Nat := [4, 2, 1, 2, 1, 2, 4, 2, 3]
def baseStart_1476926 : Nat := 118140960795 + 1476926 * 2 ^ 59
def prefixEnd_1476926 : Nat := 4983230072969 + 3 ^ 40 * 1476926 * 2
def baseEnd_1476926 : Nat := 337054635165508335081221

theorem tailTrace_1476926 : CollatzResearch.WordTrace tailWord_1476926 prefixEnd_1476926 337054635165508335081221 := by
  unfold tailWord_1476926
  simp only [CollatzResearch.WordTrace]
  refine ⟨6733489580919601965518329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35911944431571210482764421 6733489580919601965518329)
  ·
    refine ⟨5050117185689701474138747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6733489580919601965518329 5050117185689701474138747)
    ·
      refine ⟨7575175778534552211208121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5050117185689701474138747 7575175778534552211208121)
      ·
        refine ⟨5681381833900914158406091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7575175778534552211208121 5681381833900914158406091)
        ·
          refine ⟨8522072750851371237609137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5681381833900914158406091 8522072750851371237609137)
          ·
            refine ⟨6391554563138528428206853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8522072750851371237609137 6391554563138528428206853)
            ·
              refine ⟨1198416480588474080288785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6391554563138528428206853 1198416480588474080288785)
              ·
                refine ⟨898812360441355560216589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1198416480588474080288785 898812360441355560216589)
                ·
                  refine ⟨337054635165508335081221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 898812360441355560216589 337054635165508335081221)
                  ·
                    rfl

theorem cell21_1476926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 4, 2, 3].length) (baseStart_1476926 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1476926 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1476926 prefixEnd_1476926 := by exact prefixLift 1476926
  have htrace : WordTrace (prefixWord ++ tailWord_1476926) baseStart_1476926 baseEnd_1476926 := by
    simpa [prefixWord, tailWord_1476926, baseEnd_1476926] using wordTrace_append hprefix tailTrace_1476926
  have hstable : (prefixWord ++ tailWord_1476926).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476926).length < 2 ^ (prefixWord ++ tailWord_1476926).sum := by decide
  have hdescent : baseEnd_1476926 < baseStart_1476926 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476951 : List Nat := [1, 1, 3, 2, 3, 1, 3, 2, 5]
def baseStart_1476951 : Nat := 118140960795 + 1476951 * 2 ^ 59
def prefixEnd_1476951 : Nat := 4983230072969 + 3 ^ 40 * 1476951 * 2
def baseEnd_1476951 : Nat := 337060340506113847164503

theorem tailTrace_1476951 : CollatzResearch.WordTrace tailWord_1476951 prefixEnd_1476951 337060340506113847164503 := by
  unfold tailWord_1476951
  simp only [CollatzResearch.WordTrace]
  refine ⟨53868828472266244993806707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35912552314844163329204471 53868828472266244993806707)
  ·
    refine ⟨80803242708399367490710061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53868828472266244993806707 80803242708399367490710061)
    ·
      refine ⟨30301216015649762809016273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80803242708399367490710061 30301216015649762809016273)
      ·
        refine ⟨22725912011737322106762205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30301216015649762809016273 22725912011737322106762205)
        ·
          refine ⟨8522217004401495790035827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22725912011737322106762205 8522217004401495790035827)
          ·
            refine ⟨12783325506602243685053741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8522217004401495790035827 12783325506602243685053741)
            ·
              refine ⟨4793747064975841381895153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12783325506602243685053741 4793747064975841381895153)
              ·
                refine ⟨3595310298731881036421365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4793747064975841381895153 3595310298731881036421365)
                ·
                  refine ⟨337060340506113847164503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3595310298731881036421365 337060340506113847164503)
                  ·
                    rfl

theorem cell21_1476951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 2, 5].length) (baseStart_1476951 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1476951 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1476951 prefixEnd_1476951 := by exact prefixLift 1476951
  have htrace : WordTrace (prefixWord ++ tailWord_1476951) baseStart_1476951 baseEnd_1476951 := by
    simpa [prefixWord, tailWord_1476951, baseEnd_1476951] using wordTrace_append hprefix tailTrace_1476951
  have hstable : (prefixWord ++ tailWord_1476951).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476951).length < 2 ^ (prefixWord ++ tailWord_1476951).sum := by decide
  have hdescent : baseEnd_1476951 < baseStart_1476951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476996 : List Nat := [2, 3, 2, 1, 1, 2, 2, 8]
def baseStart_1476996 : Nat := 118140960795 + 1476996 * 2 ^ 59
def prefixEnd_1476996 : Nat := 4983230072969 + 3 ^ 40 * 1476996 * 2
def baseEnd_1476996 : Nat := 112356870039734589638137

theorem tailTrace_1476996 : CollatzResearch.WordTrace tailWord_1476996 prefixEnd_1476996 112356870039734589638137 := by
  unfold tailWord_1476996
  simp only [CollatzResearch.WordTrace]
  refine ⟨26935234878551608839597421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35913646504735478452796561 26935234878551608839597421)
  ·
    refine ⟨10100713079456853314849033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26935234878551608839597421 10100713079456853314849033)
    ·
      refine ⟨7575534809592639986136775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10100713079456853314849033 7575534809592639986136775)
      ·
        refine ⟨11363302214388959979205163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7575534809592639986136775 11363302214388959979205163)
        ·
          refine ⟨17044953321583439968807745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11363302214388959979205163 17044953321583439968807745)
          ·
            refine ⟨12783714991187579976605809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17044953321583439968807745 12783714991187579976605809)
            ·
              refine ⟨9587786243390684982454357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12783714991187579976605809 9587786243390684982454357)
              ·
                refine ⟨112356870039734589638137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9587786243390684982454357 112356870039734589638137)
                ·
                  rfl

theorem cell21_1476996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 8].length) (baseStart_1476996 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1476996 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1476996 prefixEnd_1476996 := by exact prefixLift 1476996
  have htrace : WordTrace (prefixWord ++ tailWord_1476996) baseStart_1476996 baseEnd_1476996 := by
    simpa [prefixWord, tailWord_1476996, baseEnd_1476996] using wordTrace_append hprefix tailTrace_1476996
  have hstable : (prefixWord ++ tailWord_1476996).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476996).length < 2 ^ (prefixWord ++ tailWord_1476996).sum := by decide
  have hdescent : baseEnd_1476996 < baseStart_1476996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476999 : List Nat := [1, 1, 4, 2, 2, 1, 5, 1, 4]
def baseStart_1476999 : Nat := 118140960795 + 1476999 * 2 ^ 59
def prefixEnd_1476999 : Nat := 4983230072969 + 3 ^ 40 * 1476999 * 2
def baseEnd_1476999 : Nat := 337071294760076430364405

theorem tailTrace_1476999 : CollatzResearch.WordTrace tailWord_1476999 prefixEnd_1476999 337071294760076430364405 := by
  unfold tailWord_1476999
  simp only [CollatzResearch.WordTrace]
  refine ⟨53870579176092349191554051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35913719450728232794369367 53870579176092349191554051)
  ·
    refine ⟨80805868764138523787331077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53870579176092349191554051 80805868764138523787331077)
    ·
      refine ⟨15151100393275973210124577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80805868764138523787331077 15151100393275973210124577)
      ·
        refine ⟨11363325294956979907593433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15151100393275973210124577 11363325294956979907593433)
        ·
          refine ⟨8522493971217734930695075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11363325294956979907593433 8522493971217734930695075)
          ·
            refine ⟨12783740956826602396042613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8522493971217734930695075 12783740956826602396042613)
            ·
              refine ⟨1198475714702493974628995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12783740956826602396042613 1198475714702493974628995)
              ·
                refine ⟨1797713572053740961943493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1198475714702493974628995 1797713572053740961943493)
                ·
                  refine ⟨337071294760076430364405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1797713572053740961943493 337071294760076430364405)
                  ·
                    rfl

theorem cell21_1476999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 5, 1, 4].length) (baseStart_1476999 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1476999 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1476999 prefixEnd_1476999 := by exact prefixLift 1476999
  have htrace : WordTrace (prefixWord ++ tailWord_1476999) baseStart_1476999 baseEnd_1476999 := by
    simpa [prefixWord, tailWord_1476999, baseEnd_1476999] using wordTrace_append hprefix tailTrace_1476999
  have hstable : (prefixWord ++ tailWord_1476999).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476999).length < 2 ^ (prefixWord ++ tailWord_1476999).sum := by decide
  have hdescent : baseEnd_1476999 < baseStart_1476999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477106 : List Nat := [3, 2, 1, 4, 2, 2, 1, 6]
def baseStart_1477106 : Nat := 118140960795 + 1477106 * 2 ^ 59
def prefixEnd_1477106 : Nat := 4983230072969 + 3 ^ 40 * 1477106 * 2
def baseEnd_1477106 : Nat := 112365237872622674026951

theorem tailTrace_1477106 : CollatzResearch.WordTrace tailWord_1477106 prefixEnd_1477106 112365237872622674026951 := by
  unfold tailWord_1477106
  simp only [CollatzResearch.WordTrace]
  refine ⟨13468620446676176616424793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35916321191136470977132781 13468620446676176616424793)
  ·
    refine ⟨10101465335007132462318595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13468620446676176616424793 10101465335007132462318595)
    ·
      refine ⟨15152198002510698693477893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10101465335007132462318595 15152198002510698693477893)
      ·
        refine ⟨2841037125470756005027105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15152198002510698693477893 2841037125470756005027105)
        ·
          refine ⟨2130777844103067003770329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2841037125470756005027105 2130777844103067003770329)
          ·
            refine ⟨1598083383077300252827747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2130777844103067003770329 1598083383077300252827747)
            ·
              refine ⟨2397125074615950379241621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1598083383077300252827747 2397125074615950379241621)
              ·
                refine ⟨112365237872622674026951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2397125074615950379241621 112365237872622674026951)
                ·
                  rfl

theorem cell21_1477106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 1, 6].length) (baseStart_1477106 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1477106 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1477106 prefixEnd_1477106 := by exact prefixLift 1477106
  have htrace : WordTrace (prefixWord ++ tailWord_1477106) baseStart_1477106 baseEnd_1477106 := by
    simpa [prefixWord, tailWord_1477106, baseEnd_1477106] using wordTrace_append hprefix tailTrace_1477106
  have hstable : (prefixWord ++ tailWord_1477106).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477106).length < 2 ^ (prefixWord ++ tailWord_1477106).sum := by decide
  have hdescent : baseEnd_1477106 < baseStart_1477106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477148 : List Nat := [2, 2, 3, 1, 2, 3, 8]
def baseStart_1477148 : Nat := 118140960795 + 1477148 * 2 ^ 59
def prefixEnd_1477148 : Nat := 4983230072969 + 3 ^ 40 * 1477148 * 2
def baseEnd_1477148 : Nat := 37456144287787253597863

theorem tailTrace_1477148 : CollatzResearch.WordTrace tailWord_1477148 prefixEnd_1477148 37456144287787253597863 := by
  unfold tailWord_1477148
  simp only [CollatzResearch.WordTrace]
  refine ⟨26938006826276273819364049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35917342435035031759152065 26938006826276273819364049)
  ·
    refine ⟨20203505119707205364523037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26938006826276273819364049 20203505119707205364523037)
    ·
      refine ⟨7576314419890202011696139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20203505119707205364523037 7576314419890202011696139)
      ·
        refine ⟨11364471629835303017544209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7576314419890202011696139 11364471629835303017544209)
        ·
          refine ⟨8523353722376477263158157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11364471629835303017544209 8523353722376477263158157)
          ·
            refine ⟨3196257645891178973684309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8523353722376477263158157 3196257645891178973684309)
            ·
              refine ⟨37456144287787253597863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3196257645891178973684309 37456144287787253597863)
              ·
                rfl

theorem cell21_1477148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 8].length) (baseStart_1477148 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1477148 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1477148 prefixEnd_1477148 := by exact prefixLift 1477148
  have htrace : WordTrace (prefixWord ++ tailWord_1477148) baseStart_1477148 baseEnd_1477148 := by
    simpa [prefixWord, tailWord_1477148, baseEnd_1477148] using wordTrace_append hprefix tailTrace_1477148
  have hstable : (prefixWord ++ tailWord_1477148).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477148).length < 2 ^ (prefixWord ++ tailWord_1477148).sum := by decide
  have hdescent : baseEnd_1477148 < baseStart_1477148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477182 : List Nat := [4, 2, 1, 4, 1, 1, 1, 7]
def baseStart_1477182 : Nat := 118140960795 + 1477182 * 2 ^ 59
def prefixEnd_1477182 : Nat := 4983230072969 + 3 ^ 40 * 1477182 * 2
def baseEnd_1477182 : Nat := 112371019284436259604677

theorem tailTrace_1477182 : CollatzResearch.WordTrace tailWord_1477182 prefixEnd_1477182 112371019284436259604677 := by
  unfold tailWord_1477182
  simp only [CollatzResearch.WordTrace]
  refine ⟨6734656716803671430683225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35918169156286247630310533 6734656716803671430683225)
  ·
    refine ⟨5050992537602753573012419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6734656716803671430683225 5050992537602753573012419)
    ·
      refine ⟨7576488806404130359518629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5050992537602753573012419 7576488806404130359518629)
      ·
        refine ⟨1420591651200774442409743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7576488806404130359518629 1420591651200774442409743)
        ·
          refine ⟨2130887476801161663614615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1420591651200774442409743 2130887476801161663614615)
          ·
            refine ⟨3196331215201742495421923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2130887476801161663614615 3196331215201742495421923)
            ·
              refine ⟨4794496822802613743132885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3196331215201742495421923 4794496822802613743132885)
              ·
                refine ⟨112371019284436259604677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4794496822802613743132885 112371019284436259604677)
                ·
                  rfl

theorem cell21_1477182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 7].length) (baseStart_1477182 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1477182 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1477182 prefixEnd_1477182 := by exact prefixLift 1477182
  have htrace : WordTrace (prefixWord ++ tailWord_1477182) baseStart_1477182 baseEnd_1477182 := by
    simpa [prefixWord, tailWord_1477182, baseEnd_1477182] using wordTrace_append hprefix tailTrace_1477182
  have hstable : (prefixWord ++ tailWord_1477182).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477182).length < 2 ^ (prefixWord ++ tailWord_1477182).sum := by decide
  have hdescent : baseEnd_1477182 < baseStart_1477182 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477188 : List Nat := [2, 3, 5, 1, 1, 2, 1, 3, 3]
def baseStart_1477188 : Nat := 118140960795 + 1477188 * 2 ^ 59
def prefixEnd_1477188 : Nat := 4983230072969 + 3 ^ 40 * 1477188 * 2
def baseEnd_1477188 : Nat := 337114427135054101714019

theorem tailTrace_1477188 : CollatzResearch.WordTrace tailWord_1477188 prefixEnd_1477188 337114427135054101714019 := by
  unfold tailWord_1477188
  simp only [CollatzResearch.WordTrace]
  refine ⟨26938736286203817235092109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35918315048271756313456145 26938736286203817235092109)
  ·
    refine ⟨10102026107326431463159541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26938736286203817235092109 10102026107326431463159541)
    ·
      refine ⟨947064947561852949671207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10102026107326431463159541 947064947561852949671207)
      ·
        refine ⟨1420597421342779424506811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 947064947561852949671207 1420597421342779424506811)
        ·
          refine ⟨2130896132014169136760217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1420597421342779424506811 2130896132014169136760217)
          ·
            refine ⟨1598172099010626852570163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2130896132014169136760217 1598172099010626852570163)
            ·
              refine ⟨2397258148515940278855245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1598172099010626852570163 2397258148515940278855245)
              ·
                refine ⟨898971805693477604570717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2397258148515940278855245 898971805693477604570717)
                ·
                  refine ⟨337114427135054101714019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 898971805693477604570717 337114427135054101714019)
                  ·
                    rfl

theorem cell21_1477188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 1, 3, 3].length) (baseStart_1477188 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1477188 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1477188 prefixEnd_1477188 := by exact prefixLift 1477188
  have htrace : WordTrace (prefixWord ++ tailWord_1477188) baseStart_1477188 baseEnd_1477188 := by
    simpa [prefixWord, tailWord_1477188, baseEnd_1477188] using wordTrace_append hprefix tailTrace_1477188
  have hstable : (prefixWord ++ tailWord_1477188).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477188).length < 2 ^ (prefixWord ++ tailWord_1477188).sum := by decide
  have hdescent : baseEnd_1477188 < baseStart_1477188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477272 : List Nat := [2, 1, 2, 4, 1, 1, 3, 4, 3]
def baseStart_1477272 : Nat := 118140960795 + 1477272 * 2 ^ 59
def prefixEnd_1477272 : Nat := 4983230072969 + 3 ^ 40 * 1477272 * 2
def baseEnd_1477272 : Nat := 337133597079488622313847

theorem tailTrace_1477272 : CollatzResearch.WordTrace tailWord_1477272 prefixEnd_1477272 337133597079488622313847 := by
  unfold tailWord_1477272
  simp only [CollatzResearch.WordTrace]
  refine ⟨26940268152051658408121035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35920357536068877877494713 26940268152051658408121035)
  ·
    refine ⟨40410402228077487612181553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26940268152051658408121035 40410402228077487612181553)
    ·
      refine ⟨30307801671058115709136165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40410402228077487612181553 30307801671058115709136165)
      ·
        refine ⟨5682712813323396695463031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30307801671058115709136165 5682712813323396695463031)
        ·
          refine ⟨8524069219985095043194547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5682712813323396695463031 8524069219985095043194547)
          ·
            refine ⟨12786103829977642564791821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8524069219985095043194547 12786103829977642564791821)
            ·
              refine ⟨4794788936241615961796933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12786103829977642564791821 4794788936241615961796933)
              ·
                refine ⟨899022925545302992836925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4794788936241615961796933 899022925545302992836925)
                ·
                  refine ⟨337133597079488622313847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 899022925545302992836925 337133597079488622313847)
                  ·
                    rfl

theorem cell21_1477272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 4, 3].length) (baseStart_1477272 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1477272 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1477272 prefixEnd_1477272 := by exact prefixLift 1477272
  have htrace : WordTrace (prefixWord ++ tailWord_1477272) baseStart_1477272 baseEnd_1477272 := by
    simpa [prefixWord, tailWord_1477272, baseEnd_1477272] using wordTrace_append hprefix tailTrace_1477272
  have hstable : (prefixWord ++ tailWord_1477272).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477272).length < 2 ^ (prefixWord ++ tailWord_1477272).sum := by decide
  have hdescent : baseEnd_1477272 < baseStart_1477272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477283 : List Nat := [1, 1, 1, 4, 1, 1, 2, 10]
def baseStart_1477283 : Nat := 118140960795 + 1477283 * 2 ^ 59
def prefixEnd_1477283 : Nat := 4983230072969 + 3 ^ 40 * 1477283 * 2
def baseEnd_1477283 : Nat := 112378702476451682543497

theorem tailTrace_1477283 : CollatzResearch.WordTrace tailWord_1477283 prefixEnd_1477283 112378702476451682543497 := by
  unfold tailWord_1477283
  simp only [CollatzResearch.WordTrace]
  refine ⟨53880937507063465694892503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35920625004708977129928335 53880937507063465694892503)
  ·
    refine ⟨80821406260595198542338755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53880937507063465694892503 80821406260595198542338755)
    ·
      refine ⟨121232109390892797813508133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80821406260595198542338755 121232109390892797813508133)
      ·
        refine ⟨22731020510792399590032775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 121232109390892797813508133 22731020510792399590032775)
        ·
          refine ⟨34096530766188599385049163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22731020510792399590032775 34096530766188599385049163)
          ·
            refine ⟨51144796149282899077573745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34096530766188599385049163 51144796149282899077573745)
            ·
              refine ⟨38358597111962174308180309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51144796149282899077573745 38358597111962174308180309)
              ·
                refine ⟨112378702476451682543497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 38358597111962174308180309 112378702476451682543497)
                ·
                  rfl

theorem cell21_1477283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 10].length) (baseStart_1477283 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1477283 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1477283 prefixEnd_1477283 := by exact prefixLift 1477283
  have htrace : WordTrace (prefixWord ++ tailWord_1477283) baseStart_1477283 baseEnd_1477283 := by
    simpa [prefixWord, tailWord_1477283, baseEnd_1477283] using wordTrace_append hprefix tailTrace_1477283
  have hstable : (prefixWord ++ tailWord_1477283).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477283).length < 2 ^ (prefixWord ++ tailWord_1477283).sum := by decide
  have hdescent : baseEnd_1477283 < baseStart_1477283 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477452 : List Nat := [2, 2, 1, 3, 3, 1, 3, 6]
def baseStart_1477452 : Nat := 118140960795 + 1477452 * 2 ^ 59
def prefixEnd_1477452 : Nat := 4983230072969 + 3 ^ 40 * 1477452 * 2
def baseEnd_1477452 : Nat := 112391558510616103104493

theorem tailTrace_1477452 : CollatzResearch.WordTrace tailWord_1477452 prefixEnd_1477452 112391558510616103104493 := by
  unfold tailWord_1477452
  simp only [CollatzResearch.WordTrace]
  refine ⟨26943550721725603778897305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35924734295634138371863073 26943550721725603778897305)
  ·
    refine ⟨20207663041294202834172979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26943550721725603778897305 20207663041294202834172979)
    ·
      refine ⟨30311494561941304251259469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20207663041294202834172979 30311494561941304251259469)
      ·
        refine ⟨11366810460727989094222301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30311494561941304251259469 11366810460727989094222301)
        ·
          refine ⟨4262553922772995910333363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11366810460727989094222301 4262553922772995910333363)
          ·
            refine ⟨6393830884159493865500045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4262553922772995910333363 6393830884159493865500045)
            ·
              refine ⟨2397686581559810199562517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6393830884159493865500045 2397686581559810199562517)
              ·
                refine ⟨112391558510616103104493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2397686581559810199562517 112391558510616103104493)
                ·
                  rfl

theorem cell21_1477452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3, 6].length) (baseStart_1477452 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1477452 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1477452 prefixEnd_1477452 := by exact prefixLift 1477452
  have htrace : WordTrace (prefixWord ++ tailWord_1477452) baseStart_1477452 baseEnd_1477452 := by
    simpa [prefixWord, tailWord_1477452, baseEnd_1477452] using wordTrace_append hprefix tailTrace_1477452
  have hstable : (prefixWord ++ tailWord_1477452).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477452).length < 2 ^ (prefixWord ++ tailWord_1477452).sum := by decide
  have hdescent : baseEnd_1477452 < baseStart_1477452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477466 : List Nat := [3, 1, 1, 2, 1, 4, 1, 1, 7]
def baseStart_1477466 : Nat := 118140960795 + 1477466 * 2 ^ 59
def prefixEnd_1477466 : Nat := 4983230072969 + 3 ^ 40 * 1477466 * 2
def baseEnd_1477466 : Nat := 337177870522587396080117

theorem tailTrace_1477466 : CollatzResearch.WordTrace tailWord_1477466 prefixEnd_1477466 337177870522587396080117 := by
  unfold tailWord_1477466
  simp only [CollatzResearch.WordTrace]
  refine ⟨13471903016350121987201063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35925074710266991965869501 13471903016350121987201063)
  ·
    refine ⟨20207854524525182980801595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13471903016350121987201063 20207854524525182980801595)
    ·
      refine ⟨30311781786787774471202393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20207854524525182980801595 30311781786787774471202393)
      ·
        refine ⟨22733836340090830853401795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30311781786787774471202393 22733836340090830853401795)
        ·
          refine ⟨34100754510136246280102693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22733836340090830853401795 34100754510136246280102693)
          ·
            refine ⟨6393891470650546177519255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34100754510136246280102693 6393891470650546177519255)
            ·
              refine ⟨9590837205975819266278883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6393891470650546177519255 9590837205975819266278883)
              ·
                refine ⟨14386255808963728899418325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9590837205975819266278883 14386255808963728899418325)
                ·
                  refine ⟨337177870522587396080117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14386255808963728899418325 337177870522587396080117)
                  ·
                    rfl

theorem cell21_1477466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 1, 7].length) (baseStart_1477466 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1477466 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1477466 prefixEnd_1477466 := by exact prefixLift 1477466
  have htrace : WordTrace (prefixWord ++ tailWord_1477466) baseStart_1477466 baseEnd_1477466 := by
    simpa [prefixWord, tailWord_1477466, baseEnd_1477466] using wordTrace_append hprefix tailTrace_1477466
  have hstable : (prefixWord ++ tailWord_1477466).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477466).length < 2 ^ (prefixWord ++ tailWord_1477466).sum := by decide
  have hdescent : baseEnd_1477466 < baseStart_1477466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477483 : List Nat := [1, 1, 1, 1, 2, 2, 5, 5, 3]
def baseStart_1477483 : Nat := 118140960795 + 1477483 * 2 ^ 59
def prefixEnd_1477483 : Nat := 4983230072969 + 3 ^ 40 * 1477483 * 2
def baseEnd_1477483 : Nat := 337181750154199144296749

theorem tailTrace_1477483 : CollatzResearch.WordTrace tailWord_1477483 prefixEnd_1477483 337181750154199144296749 := by
  unfold tailWord_1477483
  simp only [CollatzResearch.WordTrace]
  refine ⟨53888232106338899852173103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35925488070892599901448735 53888232106338899852173103)
  ·
    refine ⟨80832348159508349778259655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53888232106338899852173103 80832348159508349778259655)
    ·
      refine ⟨121248522239262524667389483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80832348159508349778259655 121248522239262524667389483)
      ·
        refine ⟨181872783358893787001084225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121248522239262524667389483 181872783358893787001084225)
        ·
          refine ⟨136404587519170340250813169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181872783358893787001084225 136404587519170340250813169)
          ·
            refine ⟨102303440639377755188109877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136404587519170340250813169 102303440639377755188109877)
            ·
              refine ⟨9590947559941664548885301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 102303440639377755188109877 9590947559941664548885301)
              ·
                refine ⟨899151333744531051457997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9590947559941664548885301 899151333744531051457997)
                ·
                  refine ⟨337181750154199144296749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 899151333744531051457997 337181750154199144296749)
                  ·
                    rfl

theorem cell21_1477483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 5, 3].length) (baseStart_1477483 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1477483 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1477483 prefixEnd_1477483 := by exact prefixLift 1477483
  have htrace : WordTrace (prefixWord ++ tailWord_1477483) baseStart_1477483 baseEnd_1477483 := by
    simpa [prefixWord, tailWord_1477483, baseEnd_1477483] using wordTrace_append hprefix tailTrace_1477483
  have hstable : (prefixWord ++ tailWord_1477483).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477483).length < 2 ^ (prefixWord ++ tailWord_1477483).sum := by decide
  have hdescent : baseEnd_1477483 < baseStart_1477483 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477497 : List Nat := [1, 2, 1, 3, 2, 4, 1, 1, 6]
def baseStart_1477497 : Nat := 118140960795 + 1477497 * 2 ^ 59
def prefixEnd_1477497 : Nat := 4983230072969 + 3 ^ 40 * 1477497 * 2
def baseEnd_1477497 : Nat := 337184945144938231063387

theorem tailTrace_1477497 : CollatzResearch.WordTrace tailWord_1477497 prefixEnd_1477497 337184945144938231063387 := by
  unfold tailWord_1477497
  simp only [CollatzResearch.WordTrace]
  refine ⟨53888742728288180243182745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35925828485525453495455163 53888742728288180243182745)
  ·
    refine ⟨40416557046216135182387059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53888742728288180243182745 40416557046216135182387059)
    ·
      refine ⟨60624835569324202773580589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40416557046216135182387059 60624835569324202773580589)
      ·
        refine ⟨22734313338496576040092721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60624835569324202773580589 22734313338496576040092721)
        ·
          refine ⟨17050735003872432030069541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22734313338496576040092721 17050735003872432030069541)
          ·
            refine ⟨3197012813226081005638039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17050735003872432030069541 3197012813226081005638039)
            ·
              refine ⟨4795519219839121508457059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3197012813226081005638039 4795519219839121508457059)
              ·
                refine ⟨7193278829758682262685589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4795519219839121508457059 7193278829758682262685589)
                ·
                  refine ⟨337184945144938231063387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7193278829758682262685589 337184945144938231063387)
                  ·
                    rfl

theorem cell21_1477497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 1, 6].length) (baseStart_1477497 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1477497 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1477497 prefixEnd_1477497 := by exact prefixLift 1477497
  have htrace : WordTrace (prefixWord ++ tailWord_1477497) baseStart_1477497 baseEnd_1477497 := by
    simpa [prefixWord, tailWord_1477497, baseEnd_1477497] using wordTrace_append hprefix tailTrace_1477497
  have hstable : (prefixWord ++ tailWord_1477497).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477497).length < 2 ^ (prefixWord ++ tailWord_1477497).sum := by decide
  have hdescent : baseEnd_1477497 < baseStart_1477497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477559 : List Nat := [1, 1, 3, 1, 3, 1, 2, 6, 3]
def baseStart_1477559 : Nat := 118140960795 + 1477559 * 2 ^ 59
def prefixEnd_1477559 : Nat := 4983230072969 + 3 ^ 40 * 1477559 * 2
def baseEnd_1477559 : Nat := 337199094389639901029927

theorem tailTrace_1477559 : CollatzResearch.WordTrace tailWord_1477559 prefixEnd_1477559 337199094389639901029927 := by
  unfold tailWord_1477559
  simp only [CollatzResearch.WordTrace]
  refine ⟨53891004054063564831939731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35927336036042376554626487 53891004054063564831939731)
  ·
    refine ⟨80836506081095347247909597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53891004054063564831939731 80836506081095347247909597)
    ·
      refine ⟨30313689780410755217966099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80836506081095347247909597 30313689780410755217966099)
      ·
        refine ⟨45470534670616132826949149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30313689780410755217966099 45470534670616132826949149)
        ·
          refine ⟨17051450501481049810105931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45470534670616132826949149 17051450501481049810105931)
          ·
            refine ⟨25577175752221574715158897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17051450501481049810105931 25577175752221574715158897)
            ·
              refine ⟨19182881814166181036369173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25577175752221574715158897 19182881814166181036369173)
              ·
                refine ⟨899197585039039736079805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 19182881814166181036369173 899197585039039736079805)
                ·
                  refine ⟨337199094389639901029927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 899197585039039736079805 337199094389639901029927)
                  ·
                    rfl

theorem cell21_1477559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 6, 3].length) (baseStart_1477559 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1477559 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1477559 prefixEnd_1477559 := by exact prefixLift 1477559
  have htrace : WordTrace (prefixWord ++ tailWord_1477559) baseStart_1477559 baseEnd_1477559 := by
    simpa [prefixWord, tailWord_1477559, baseEnd_1477559] using wordTrace_append hprefix tailTrace_1477559
  have hstable : (prefixWord ++ tailWord_1477559).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477559).length < 2 ^ (prefixWord ++ tailWord_1477559).sum := by decide
  have hdescent : baseEnd_1477559 < baseStart_1477559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477663 : List Nat := [1, 1, 2, 4, 1, 4, 8]
def baseStart_1477663 : Nat := 118140960795 + 1477663 * 2 ^ 59
def prefixEnd_1477663 : Nat := 4983230072969 + 3 ^ 40 * 1477663 * 2
def baseEnd_1477663 : Nat := 37469203178506536810709

theorem tailTrace_1477663 : CollatzResearch.WordTrace tailWord_1477663 prefixEnd_1477663 37469203178506536810709 := by
  unfold tailWord_1477663
  simp only [CollatzResearch.WordTrace]
  refine ⟨53894797245686790593725643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35929864830457860395817095 53894797245686790593725643)
  ·
    refine ⟨80842195868530185890588465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53894797245686790593725643 80842195868530185890588465)
    ·
      refine ⟨60631646901397639417941349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80842195868530185890588465 60631646901397639417941349)
      ·
        refine ⟨11368433794012057390864003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60631646901397639417941349 11368433794012057390864003)
        ·
          refine ⟨17052650691018086086296005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11368433794012057390864003 17052650691018086086296005)
          ·
            refine ⟨3197372004565891141180501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17052650691018086086296005 3197372004565891141180501)
            ·
              refine ⟨37469203178506536810709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3197372004565891141180501 37469203178506536810709)
              ·
                rfl

theorem cell21_1477663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 8].length) (baseStart_1477663 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1477663 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1477663 prefixEnd_1477663 := by exact prefixLift 1477663
  have htrace : WordTrace (prefixWord ++ tailWord_1477663) baseStart_1477663 baseEnd_1477663 := by
    simpa [prefixWord, tailWord_1477663, baseEnd_1477663] using wordTrace_append hprefix tailTrace_1477663
  have hstable : (prefixWord ++ tailWord_1477663).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477663).length < 2 ^ (prefixWord ++ tailWord_1477663).sum := by decide
  have hdescent : baseEnd_1477663 < baseStart_1477663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477666 : List Nat := [3, 3, 1, 1, 1, 3, 3, 2, 4]
def baseStart_1477666 : Nat := 118140960795 + 1477666 * 2 ^ 59
def prefixEnd_1477666 : Nat := 4983230072969 + 3 ^ 40 * 1477666 * 2
def baseEnd_1477666 : Nat := 337223513247431492746375

theorem tailTrace_1477666 : CollatzResearch.WordTrace tailWord_1477666 prefixEnd_1477666 337223513247431492746375 := by
  unfold tailWord_1477666
  simp only [CollatzResearch.WordTrace]
  refine ⟨13473726666168980526521213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35929937776450614737389901 13473726666168980526521213)
  ·
    refine ⟨5052647499813367697445455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13473726666168980526521213 5052647499813367697445455)
    ·
      refine ⟨7578971249720051546168183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5052647499813367697445455 7578971249720051546168183)
      ·
        refine ⟨11368456874580077319252275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7578971249720051546168183 11368456874580077319252275)
        ·
          refine ⟨17052685311870115978878413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11368456874580077319252275 17052685311870115978878413)
          ·
            refine ⟨6394756991951293492079405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17052685311870115978878413 6394756991951293492079405)
            ·
              refine ⟨2398033871981735059529777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6394756991951293492079405 2398033871981735059529777)
              ·
                refine ⟨1798525403986301294647333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2398033871981735059529777 1798525403986301294647333)
                ·
                  refine ⟨337223513247431492746375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1798525403986301294647333 337223513247431492746375)
                  ·
                    rfl

theorem cell21_1477666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3, 2, 4].length) (baseStart_1477666 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1477666 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1477666 prefixEnd_1477666 := by exact prefixLift 1477666
  have htrace : WordTrace (prefixWord ++ tailWord_1477666) baseStart_1477666 baseEnd_1477666 := by
    simpa [prefixWord, tailWord_1477666, baseEnd_1477666] using wordTrace_append hprefix tailTrace_1477666
  have hstable : (prefixWord ++ tailWord_1477666).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477666).length < 2 ^ (prefixWord ++ tailWord_1477666).sum := by decide
  have hdescent : baseEnd_1477666 < baseStart_1477666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477728 : List Nat := [2, 1, 1, 3, 2, 2, 5, 2, 3]
def baseStart_1477728 : Nat := 118140960795 + 1477728 * 2 ^ 59
def prefixEnd_1477728 : Nat := 4983230072969 + 3 ^ 40 * 1477728 * 2
def baseEnd_1477728 : Nat := 337237662492133162712915

theorem tailTrace_1477728 : CollatzResearch.WordTrace tailWord_1477728 prefixEnd_1477728 337237662492133162712915 := by
  unfold tailWord_1477728
  simp only [CollatzResearch.WordTrace]
  refine ⟨26948583995225653347420919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35931445326967537796561225 26948583995225653347420919)
  ·
    refine ⟨40422875992838480021131379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26948583995225653347420919 40422875992838480021131379)
    ·
      refine ⟨60634313989257720031697069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40422875992838480021131379 60634313989257720031697069)
      ·
        refine ⟨22737867745971645011886401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60634313989257720031697069 22737867745971645011886401)
        ·
          refine ⟨17053400809478733758914801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22737867745971645011886401 17053400809478733758914801)
          ·
            refine ⟨12790050607109050319186101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17053400809478733758914801 12790050607109050319186101)
            ·
              refine ⟨1199067244416473467423697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12790050607109050319186101 1199067244416473467423697)
              ·
                refine ⟨899300433312355100567773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1199067244416473467423697 899300433312355100567773)
                ·
                  refine ⟨337237662492133162712915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 899300433312355100567773 337237662492133162712915)
                  ·
                    rfl

theorem cell21_1477728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 5, 2, 3].length) (baseStart_1477728 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1477728 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1477728 prefixEnd_1477728 := by exact prefixLift 1477728
  have htrace : WordTrace (prefixWord ++ tailWord_1477728) baseStart_1477728 baseEnd_1477728 := by
    simpa [prefixWord, tailWord_1477728, baseEnd_1477728] using wordTrace_append hprefix tailTrace_1477728
  have hstable : (prefixWord ++ tailWord_1477728).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477728).length < 2 ^ (prefixWord ++ tailWord_1477728).sum := by decide
  have hdescent : baseEnd_1477728 < baseStart_1477728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477742 : List Nat := [4, 1, 2, 2, 1, 3, 1, 3, 4]
def baseStart_1477742 : Nat := 118140960795 + 1477742 * 2 ^ 59
def prefixEnd_1477742 : Nat := 4983230072969 + 3 ^ 40 * 1477742 * 2
def baseEnd_1477742 : Nat := 337240857482872249479553

theorem tailTrace_1477742 : CollatzResearch.WordTrace tailWord_1477742 prefixEnd_1477742 337240857482872249479553 := by
  unfold tailWord_1477742
  simp only [CollatzResearch.WordTrace]
  refine ⟨6737209826550073385731435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35931785741600391390567653 6737209826550073385731435)
  ·
    refine ⟨10105814739825110078597153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6737209826550073385731435 10105814739825110078597153)
    ·
      refine ⟨7579361054868832558947865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10105814739825110078597153 7579361054868832558947865)
      ·
        refine ⟨5684520791151624419210899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7579361054868832558947865 5684520791151624419210899)
        ·
          refine ⟨8526781186727436628816349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5684520791151624419210899 8526781186727436628816349)
          ·
            refine ⟨3197542945022788735806131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8526781186727436628816349 3197542945022788735806131)
            ·
              refine ⟨4796314417534183103709197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3197542945022788735806131 4796314417534183103709197)
              ·
                refine ⟨1798617906575318663890949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4796314417534183103709197 1798617906575318663890949)
                ·
                  refine ⟨337240857482872249479553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1798617906575318663890949 337240857482872249479553)
                  ·
                    rfl

theorem cell21_1477742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 3, 4].length) (baseStart_1477742 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1477742 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1477742 prefixEnd_1477742 := by exact prefixLift 1477742
  have htrace : WordTrace (prefixWord ++ tailWord_1477742) baseStart_1477742 baseEnd_1477742 := by
    simpa [prefixWord, tailWord_1477742, baseEnd_1477742] using wordTrace_append hprefix tailTrace_1477742
  have hstable : (prefixWord ++ tailWord_1477742).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477742).length < 2 ^ (prefixWord ++ tailWord_1477742).sum := by decide
  have hdescent : baseEnd_1477742 < baseStart_1477742 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477829 : List Nat := [1, 3, 1, 1, 1, 1, 3, 1, 9]
def baseStart_1477829 : Nat := 118140960795 + 1477829 * 2 ^ 59
def prefixEnd_1477829 : Nat := 4983230072969 + 3 ^ 40 * 1477829 * 2
def baseEnd_1477829 : Nat := 337260712068179431529375

theorem tailTrace_1477829 : CollatzResearch.WordTrace tailWord_1477829 prefixEnd_1477829 337260712068179431529375 := by
  unfold tailWord_1477829
  simp only [CollatzResearch.WordTrace]
  refine ⟨53900851763085400944268541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35933901175390267296179027 53900851763085400944268541)
  ·
    refine ⟨20212819411157025354100703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53900851763085400944268541 20212819411157025354100703)
    ·
      refine ⟨30319229116735538031151055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20212819411157025354100703 30319229116735538031151055)
      ·
        refine ⟨45478843675103307046726583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30319229116735538031151055 45478843675103307046726583)
        ·
          refine ⟨68218265512654960570089875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45478843675103307046726583 68218265512654960570089875)
          ·
            refine ⟨102327398268982440855134813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68218265512654960570089875 102327398268982440855134813)
            ·
              refine ⟨38372774350868415320675555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 102327398268982440855134813 38372774350868415320675555)
              ·
                refine ⟨57559161526302622981013333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38372774350868415320675555 57559161526302622981013333)
                ·
                  refine ⟨337260712068179431529375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 57559161526302622981013333 337260712068179431529375)
                  ·
                    rfl

theorem cell21_1477829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 9].length) (baseStart_1477829 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1477829 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1477829 prefixEnd_1477829 := by exact prefixLift 1477829
  have htrace : WordTrace (prefixWord ++ tailWord_1477829) baseStart_1477829 baseEnd_1477829 := by
    simpa [prefixWord, tailWord_1477829, baseEnd_1477829] using wordTrace_append hprefix tailTrace_1477829
  have hstable : (prefixWord ++ tailWord_1477829).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477829).length < 2 ^ (prefixWord ++ tailWord_1477829).sum := by decide
  have hdescent : baseEnd_1477829 < baseStart_1477829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477891 : List Nat := [1, 1, 1, 3, 2, 6, 7]
def baseStart_1477891 : Nat := 118140960795 + 1477891 * 2 ^ 59
def prefixEnd_1477891 : Nat := 4983230072969 + 3 ^ 40 * 1477891 * 2
def baseEnd_1477891 : Nat := 37474984590320122388435

theorem tailTrace_1477891 : CollatzResearch.WordTrace tailWord_1477891 prefixEnd_1477891 37474984590320122388435 := by
  unfold tailWord_1477891
  simp only [CollatzResearch.WordTrace]
  refine ⟨53903113088860785533025527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35935408725907190355350351 53903113088860785533025527)
  ·
    refine ⟨80854669633291178299538291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53903113088860785533025527 80854669633291178299538291)
    ·
      refine ⟨121282004449936767449307437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80854669633291178299538291 121282004449936767449307437)
      ·
        refine ⟨45480751668726287793490289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121282004449936767449307437 45480751668726287793490289)
        ·
          refine ⟨34110563751544715845117717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45480751668726287793490289 34110563751544715845117717)
          ·
            refine ⟨1598932675853658555239893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 34110563751544715845117717 1598932675853658555239893)
            ·
              refine ⟨37474984590320122388435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1598932675853658555239893 37474984590320122388435)
              ·
                rfl

theorem cell21_1477891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 7].length) (baseStart_1477891 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1477891 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1477891 prefixEnd_1477891 := by exact prefixLift 1477891
  have htrace : WordTrace (prefixWord ++ tailWord_1477891) baseStart_1477891 baseEnd_1477891 := by
    simpa [prefixWord, tailWord_1477891, baseEnd_1477891] using wordTrace_append hprefix tailTrace_1477891
  have hstable : (prefixWord ++ tailWord_1477891).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477891).length < 2 ^ (prefixWord ++ tailWord_1477891).sum := by decide
  have hdescent : baseEnd_1477891 < baseStart_1477891 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477984 : List Nat := [2, 1, 1, 3, 4, 2, 3, 5]
def baseStart_1477984 : Nat := 118140960795 + 1477984 * 2 ^ 59
def prefixEnd_1477984 : Nat := 4983230072969 + 3 ^ 40 * 1477984 * 2
def baseEnd_1477984 : Nat := 112432028393311202148575

theorem tailTrace_1477984 : CollatzResearch.WordTrace tailWord_1477984 prefixEnd_1477984 112432028393311202148575 := by
  unfold tailWord_1477984
  simp only [CollatzResearch.WordTrace]
  refine ⟨26953252538761931208080503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35937670051682574944107337 26953252538761931208080503)
  ·
    refine ⟨40429878808142896812120755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26953252538761931208080503 40429878808142896812120755)
    ·
      refine ⟨60644818212214345218181133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40429878808142896812120755 60644818212214345218181133)
      ·
        refine ⟨22741806829580379456817925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60644818212214345218181133 22741806829580379456817925)
        ·
          refine ⟨4264088780546321148153361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22741806829580379456817925 4264088780546321148153361)
          ·
            refine ⟨3198066585409740861115021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4264088780546321148153361 3198066585409740861115021)
            ·
              refine ⟨1199274969528652822918133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3198066585409740861115021 1199274969528652822918133)
              ·
                refine ⟨112432028393311202148575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1199274969528652822918133 112432028393311202148575)
                ·
                  rfl

theorem cell21_1477984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 3, 5].length) (baseStart_1477984 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1477984 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1477984 prefixEnd_1477984 := by exact prefixLift 1477984
  have htrace : WordTrace (prefixWord ++ tailWord_1477984) baseStart_1477984 baseEnd_1477984 := by
    simpa [prefixWord, tailWord_1477984, baseEnd_1477984] using wordTrace_append hprefix tailTrace_1477984
  have hstable : (prefixWord ++ tailWord_1477984).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477984).length < 2 ^ (prefixWord ++ tailWord_1477984).sum := by decide
  have hdescent : baseEnd_1477984 < baseStart_1477984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1478012 : List Nat := [2, 2, 2, 1, 1, 1, 5, 1, 6]
def baseStart_1478012 : Nat := 118140960795 + 1478012 * 2 ^ 59
def prefixEnd_1478012 : Nat := 4983230072969 + 3 ^ 40 * 1478012 * 2
def baseEnd_1478012 : Nat := 337302475161411779979001

theorem tailTrace_1478012 : CollatzResearch.WordTrace tailWord_1478012 prefixEnd_1478012 337302475161411779979001 := by
  unfold tailWord_1478012
  simp only [CollatzResearch.WordTrace]
  refine ⟨26953763160711211599090145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35938350880948282132120193 26953763160711211599090145)
  ·
    refine ⟨20215322370533408699317609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26953763160711211599090145 20215322370533408699317609)
    ·
      refine ⟨15161491777900056524488207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20215322370533408699317609 15161491777900056524488207)
      ·
        refine ⟨22742237666850084786732311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15161491777900056524488207 22742237666850084786732311)
        ·
          refine ⟨34113356500275127180098467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22742237666850084786732311 34113356500275127180098467)
          ·
            refine ⟨51170034750412690770147701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34113356500275127180098467 51170034750412690770147701)
            ·
              refine ⟨4797190757851189759701347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51170034750412690770147701 4797190757851189759701347)
              ·
                refine ⟨7195786136776784639552021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4797190757851189759701347 7195786136776784639552021)
                ·
                  refine ⟨337302475161411779979001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7195786136776784639552021 337302475161411779979001)
                  ·
                    rfl

theorem cell21_1478012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 1, 6].length) (baseStart_1478012 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1478012 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1478012 prefixEnd_1478012 := by exact prefixLift 1478012
  have htrace : WordTrace (prefixWord ++ tailWord_1478012) baseStart_1478012 baseEnd_1478012 := by
    simpa [prefixWord, tailWord_1478012, baseEnd_1478012] using wordTrace_append hprefix tailTrace_1478012
  have hstable : (prefixWord ++ tailWord_1478012).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1478012).length < 2 ^ (prefixWord ++ tailWord_1478012).sum := by decide
  have hdescent : baseEnd_1478012 < baseStart_1478012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1478012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1478122 : List Nat := [3, 1, 3, 1, 4, 1, 2, 2, 4]
def baseStart_1478122 : Nat := 118140960795 + 1478122 * 2 ^ 59
def prefixEnd_1478122 : Nat := 4983230072969 + 3 ^ 40 * 1478122 * 2
def baseEnd_1478122 : Nat := 337327578660076033145443

theorem tailTrace_1478122 : CollatzResearch.WordTrace tailWord_1478122 prefixEnd_1478122 337327578660076033145443 := by
  unfold tailWord_1478122
  simp only [CollatzResearch.WordTrace]
  refine ⟨13477884587755977996171155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35941025567349274656456413 13477884587755977996171155)
  ·
    refine ⟨20216826881633966994256733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13477884587755977996171155 20216826881633966994256733)
    ·
      refine ⟨7581310080612737622846275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20216826881633966994256733 7581310080612737622846275)
      ·
        refine ⟨11371965120919106434269413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7581310080612737622846275 11371965120919106434269413)
        ·
          refine ⟨2132243460172332456425515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11371965120919106434269413 2132243460172332456425515)
          ·
            refine ⟨3198365190258498684638273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2132243460172332456425515 3198365190258498684638273)
            ·
              refine ⟨2398773892693874013478705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3198365190258498684638273 2398773892693874013478705)
              ·
                refine ⟨1799080419520405510109029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2398773892693874013478705 1799080419520405510109029)
                ·
                  refine ⟨337327578660076033145443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1799080419520405510109029 337327578660076033145443)
                  ·
                    rfl

theorem cell21_1478122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 2, 2, 4].length) (baseStart_1478122 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1478122 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1478122 prefixEnd_1478122 := by exact prefixLift 1478122
  have htrace : WordTrace (prefixWord ++ tailWord_1478122) baseStart_1478122 baseEnd_1478122 := by
    simpa [prefixWord, tailWord_1478122, baseEnd_1478122] using wordTrace_append hprefix tailTrace_1478122
  have hstable : (prefixWord ++ tailWord_1478122).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1478122).length < 2 ^ (prefixWord ++ tailWord_1478122).sum := by decide
  have hdescent : baseEnd_1478122 < baseStart_1478122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1478122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1478240 : List Nat := [2, 1, 1, 3, 2, 1, 1, 6, 4]
def baseStart_1478240 : Nat := 118140960795 + 1478240 * 2 ^ 59
def prefixEnd_1478240 : Nat := 4983230072969 + 3 ^ 40 * 1478240 * 2
def baseEnd_1478240 : Nat := 337354507867734050178535

theorem tailTrace_1478240 : CollatzResearch.WordTrace tailWord_1478240 prefixEnd_1478240 337354507867734050178535 := by
  unfold tailWord_1478240
  simp only [CollatzResearch.WordTrace]
  refine ⟨26957921082298209068740087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35943894776397612091653449 26957921082298209068740087)
  ·
    refine ⟨40436881623447313603110131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26957921082298209068740087 40436881623447313603110131)
    ·
      refine ⟨60655322435170970404665197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40436881623447313603110131 60655322435170970404665197)
      ·
        refine ⟨22745745913189113901749449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60655322435170970404665197 22745745913189113901749449)
        ·
          refine ⟨17059309434891835426312087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22745745913189113901749449 17059309434891835426312087)
          ·
            refine ⟨25588964152337753139468131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17059309434891835426312087 25588964152337753139468131)
            ·
              refine ⟨38383446228506629709202197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25588964152337753139468131 38383446228506629709202197)
              ·
                refine ⟨1799224041961248267618853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 38383446228506629709202197 1799224041961248267618853)
                ·
                  refine ⟨337354507867734050178535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1799224041961248267618853 337354507867734050178535)
                  ·
                    rfl

theorem cell21_1478240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 6, 4].length) (baseStart_1478240 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1478240 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1478240 prefixEnd_1478240 := by exact prefixLift 1478240
  have htrace : WordTrace (prefixWord ++ tailWord_1478240) baseStart_1478240 baseEnd_1478240 := by
    simpa [prefixWord, tailWord_1478240, baseEnd_1478240] using wordTrace_append hprefix tailTrace_1478240
  have hstable : (prefixWord ++ tailWord_1478240).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1478240).length < 2 ^ (prefixWord ++ tailWord_1478240).sum := by decide
  have hdescent : baseEnd_1478240 < baseStart_1478240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1478240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1478361 : List Nat := [1, 2, 1, 2, 3, 3, 1, 3, 5]
def baseStart_1478361 : Nat := 118140960795 + 1478361 * 2 ^ 59
def prefixEnd_1478361 : Nat := 4983230072969 + 3 ^ 40 * 1478361 * 2
def baseEnd_1478361 : Nat := 337382121716264728661621

theorem tailTrace_1478361 : CollatzResearch.WordTrace tailWord_1478361 prefixEnd_1478361 337382121716264728661621 := by
  unfold tailWord_1478361
  simp only [CollatzResearch.WordTrace]
  refine ⟨53920255397158055802634937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35946836931438703868423291 53920255397158055802634937)
  ·
    refine ⟨40440191547868541851976203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53920255397158055802634937 40440191547868541851976203)
    ·
      refine ⟨60660287321802812777964305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40440191547868541851976203 60660287321802812777964305)
      ·
        refine ⟨45495215491352109583473229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60660287321802812777964305 45495215491352109583473229)
        ·
          refine ⟨17060705809257041093802461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45495215491352109583473229 17060705809257041093802461)
          ·
            refine ⟨6397764678471390410175923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17060705809257041093802461 6397764678471390410175923)
            ·
              refine ⟨9596647017707085615263885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6397764678471390410175923 9596647017707085615263885)
              ·
                refine ⟨3598742631640157105723957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9596647017707085615263885 3598742631640157105723957)
                ·
                  refine ⟨337382121716264728661621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3598742631640157105723957 337382121716264728661621)
                  ·
                    rfl

theorem cell21_1478361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 3, 5].length) (baseStart_1478361 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1478361 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1478361 prefixEnd_1478361 := by exact prefixLift 1478361
  have htrace : WordTrace (prefixWord ++ tailWord_1478361) baseStart_1478361 baseEnd_1478361 := by
    simpa [prefixWord, tailWord_1478361, baseEnd_1478361] using wordTrace_append hprefix tailTrace_1478361
  have hstable : (prefixWord ++ tailWord_1478361).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1478361).length < 2 ^ (prefixWord ++ tailWord_1478361).sum := by decide
  have hdescent : baseEnd_1478361 < baseStart_1478361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1478361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1478423 : List Nat := [1, 1, 3, 4, 2, 2, 2, 6]
def baseStart_1478423 : Nat := 118140960795 + 1478423 * 2 ^ 59
def prefixEnd_1478423 : Nat := 4983230072969 + 3 ^ 40 * 1478423 * 2
def baseEnd_1478423 : Nat := 112465423653655466209387

theorem tailTrace_1478423 : CollatzResearch.WordTrace tailWord_1478423 prefixEnd_1478423 112465423653655466209387 := by
  unfold tailWord_1478423
  simp only [CollatzResearch.WordTrace]
  refine ⟨53922516722933440391391923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35948344481955626927594615 53922516722933440391391923)
  ·
    refine ⟨80883775084400160587087885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53922516722933440391391923 80883775084400160587087885)
    ·
      refine ⟨30331415656650060220157957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80883775084400160587087885 30331415656650060220157957)
      ·
        refine ⟨5687140435621886291279617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30331415656650060220157957 5687140435621886291279617)
        ·
          refine ⟨4265355326716414718459713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5687140435621886291279617 4265355326716414718459713)
          ·
            refine ⟨3199016495037311038844785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4265355326716414718459713 3199016495037311038844785)
            ·
              refine ⟨2399262371277983279133589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3199016495037311038844785 2399262371277983279133589)
              ·
                refine ⟨112465423653655466209387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2399262371277983279133589 112465423653655466209387)
                ·
                  rfl

theorem cell21_1478423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2, 6].length) (baseStart_1478423 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1478423 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1478423 prefixEnd_1478423 := by exact prefixLift 1478423
  have htrace : WordTrace (prefixWord ++ tailWord_1478423) baseStart_1478423 baseEnd_1478423 := by
    simpa [prefixWord, tailWord_1478423, baseEnd_1478423] using wordTrace_append hprefix tailTrace_1478423
  have hstable : (prefixWord ++ tailWord_1478423).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1478423).length < 2 ^ (prefixWord ++ tailWord_1478423).sum := by decide
  have hdescent : baseEnd_1478423 < baseStart_1478423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1478423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1478426 : List Nat := [3, 1, 1, 3, 2, 4, 2, 1, 4]
def baseStart_1478426 : Nat := 118140960795 + 1478426 * 2 ^ 59
def prefixEnd_1478426 : Nat := 4983230072969 + 3 ^ 40 * 1478426 * 2
def baseEnd_1478426 : Nat := 337396955601839060078155

theorem tailTrace_1478426 : CollatzResearch.WordTrace tailWord_1478426 prefixEnd_1478426 337396955601839060078155 := by
  unfold tailWord_1478426
  simp only [CollatzResearch.WordTrace]
  refine ⟨13480656535480642975937783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35948417427948381269167421 13480656535480642975937783)
  ·
    refine ⟨20220984803220964463906675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13480656535480642975937783 20220984803220964463906675)
    ·
      refine ⟨30331477204831446695860013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20220984803220964463906675 30331477204831446695860013)
      ·
        refine ⟨11374303951811792510947505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30331477204831446695860013 11374303951811792510947505)
        ·
          refine ⟨8530727963858844383210629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11374303951811792510947505 8530727963858844383210629)
          ·
            refine ⟨1599511493223533321851993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8530727963858844383210629 1599511493223533321851993)
            ·
              refine ⟨1199633619917649991388995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1599511493223533321851993 1199633619917649991388995)
              ·
                refine ⟨1799450429876474987083493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1199633619917649991388995 1799450429876474987083493)
                ·
                  refine ⟨337396955601839060078155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1799450429876474987083493 337396955601839060078155)
                  ·
                    rfl

theorem cell21_1478426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 2, 1, 4].length) (baseStart_1478426 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1478426 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1478426 prefixEnd_1478426 := by exact prefixLift 1478426
  have htrace : WordTrace (prefixWord ++ tailWord_1478426) baseStart_1478426 baseEnd_1478426 := by
    simpa [prefixWord, tailWord_1478426, baseEnd_1478426] using wordTrace_append hprefix tailTrace_1478426
  have hstable : (prefixWord ++ tailWord_1478426).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1478426).length < 2 ^ (prefixWord ++ tailWord_1478426).sum := by decide
  have hdescent : baseEnd_1478426 < baseStart_1478426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1478426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1478471 : List Nat := [1, 1, 4, 1, 2, 1, 6, 2, 3]
def baseStart_1478471 : Nat := 118140960795 + 1478471 * 2 ^ 59
def prefixEnd_1478471 : Nat := 4983230072969 + 3 ^ 40 * 1478471 * 2
def baseEnd_1478471 : Nat := 337407225214928981828063

theorem tailTrace_1478471 : CollatzResearch.WordTrace tailWord_1478471 prefixEnd_1478471 337407225214928981828063 := by
  unfold tailWord_1478471
  simp only [CollatzResearch.WordTrace]
  refine ⟨53924267426759544589139267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35949511617839696392759511 53924267426759544589139267)
  ·
    refine ⟨80886401140139316883708901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53924267426759544589139267 80886401140139316883708901)
    ·
      refine ⟨15166200213776121915695419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80886401140139316883708901 15166200213776121915695419)
      ·
        refine ⟨22749300320664182873543129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15166200213776121915695419 22749300320664182873543129)
        ·
          refine ⟨17061975240498137155157347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22749300320664182873543129 17061975240498137155157347)
          ·
            refine ⟨25592962860747205732736021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17061975240498137155157347 25592962860747205732736021)
            ·
              refine ⟨1199670134097525268722001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 25592962860747205732736021 1199670134097525268722001)
              ·
                refine ⟨899752600573143951541501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1199670134097525268722001 899752600573143951541501)
                ·
                  refine ⟨337407225214928981828063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 899752600573143951541501 337407225214928981828063)
                  ·
                    rfl

theorem cell21_1478471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 6, 2, 3].length) (baseStart_1478471 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1478471 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1478471 prefixEnd_1478471 := by exact prefixLift 1478471
  have htrace : WordTrace (prefixWord ++ tailWord_1478471) baseStart_1478471 baseEnd_1478471 := by
    simpa [prefixWord, tailWord_1478471, baseEnd_1478471] using wordTrace_append hprefix tailTrace_1478471
  have hstable : (prefixWord ++ tailWord_1478471).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1478471).length < 2 ^ (prefixWord ++ tailWord_1478471).sum := by decide
  have hdescent : baseEnd_1478471 < baseStart_1478471 := by decide
  rcases family_descends (prefixWord ++ tailWord_1478471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1478682 : List Nat := [3, 1, 1, 3, 1, 3, 1, 5, 3]
def baseStart_1478682 : Nat := 118140960795 + 1478682 * 2 ^ 59
def prefixEnd_1478682 : Nat := 4983230072969 + 3 ^ 40 * 1478682 * 2
def baseEnd_1478682 : Nat := 337455378289639503810965

theorem tailTrace_1478682 : CollatzResearch.WordTrace tailWord_1478682 prefixEnd_1478682 337455378289639503810965 := by
  unfold tailWord_1478682
  simp only [CollatzResearch.WordTrace]
  refine ⟨13482990807248781906267575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35954642152663418416713533 13482990807248781906267575)
  ·
    refine ⟨20224486210873172859401363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13482990807248781906267575 20224486210873172859401363)
    ·
      refine ⟨30336729316309759289102045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20224486210873172859401363 30336729316309759289102045)
      ·
        refine ⟨11376273493616159733413267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30336729316309759289102045 11376273493616159733413267)
        ·
          refine ⟨17064410240424239600119901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11376273493616159733413267 17064410240424239600119901)
          ·
            refine ⟨6399153840159089850044963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17064410240424239600119901 6399153840159089850044963)
            ·
              refine ⟨9598730760238634775067445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6399153840159089850044963 9598730760238634775067445)
              ·
                refine ⟨899881008772372010162573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9598730760238634775067445 899881008772372010162573)
                ·
                  refine ⟨337455378289639503810965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 899881008772372010162573 337455378289639503810965)
                  ·
                    rfl

theorem cell21_1478682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 5, 3].length) (baseStart_1478682 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1478682 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1478682 prefixEnd_1478682 := by exact prefixLift 1478682
  have htrace : WordTrace (prefixWord ++ tailWord_1478682) baseStart_1478682 baseEnd_1478682 := by
    simpa [prefixWord, tailWord_1478682, baseEnd_1478682] using wordTrace_append hprefix tailTrace_1478682
  have hstable : (prefixWord ++ tailWord_1478682).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1478682).length < 2 ^ (prefixWord ++ tailWord_1478682).sum := by decide
  have hdescent : baseEnd_1478682 < baseStart_1478682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1478682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1478750 : List Nat := [4, 4, 1, 1, 2, 1, 3, 2, 3]
def baseStart_1478750 : Nat := 118140960795 + 1478750 * 2 ^ 59
def prefixEnd_1478750 : Nat := 4983230072969 + 3 ^ 40 * 1478750 * 2
def baseEnd_1478750 : Nat := 337470896816086496677493

theorem tailTrace_1478750 : CollatzResearch.WordTrace tailWord_1478750 prefixEnd_1478750 337470896816086496677493 := by
  unfold tailWord_1478750
  simp only [CollatzResearch.WordTrace]
  refine ⟨6741805424093596904818213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35956295595165850159030469 6741805424093596904818213)
  ·
    refine ⟨1264088517017549419653415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6741805424093596904818213 1264088517017549419653415)
    ·
      refine ⟨1896132775526324129480123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1264088517017549419653415 1896132775526324129480123)
      ·
        refine ⟨2844199163289486194220185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1896132775526324129480123 2844199163289486194220185)
        ·
          refine ⟨2133149372467114645665139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2844199163289486194220185 2133149372467114645665139)
          ·
            refine ⟨3199724058700671968497709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2133149372467114645665139 3199724058700671968497709)
            ·
              refine ⟨1199896522012751988186641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3199724058700671968497709 1199896522012751988186641)
              ·
                refine ⟨899922391509563991139981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1199896522012751988186641 899922391509563991139981)
                ·
                  refine ⟨337470896816086496677493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 899922391509563991139981 337470896816086496677493)
                  ·
                    rfl

theorem cell21_1478750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_1478750 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1478750 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1478750 prefixEnd_1478750 := by exact prefixLift 1478750
  have htrace : WordTrace (prefixWord ++ tailWord_1478750) baseStart_1478750 baseEnd_1478750 := by
    simpa [prefixWord, tailWord_1478750, baseEnd_1478750] using wordTrace_append hprefix tailTrace_1478750
  have hstable : (prefixWord ++ tailWord_1478750).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1478750).length < 2 ^ (prefixWord ++ tailWord_1478750).sum := by decide
  have hdescent : baseEnd_1478750 < baseStart_1478750 := by decide
  rcases family_descends (prefixWord ++ tailWord_1478750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1478755 : List Nat := [1, 1, 1, 5, 1, 1, 4, 1, 6]
def baseStart_1478755 : Nat := 118140960795 + 1478755 * 2 ^ 59
def prefixEnd_1478755 : Nat := 4983230072969 + 3 ^ 40 * 1478755 * 2
def baseEnd_1478755 : Nat := 337472037884207599094149

theorem tailTrace_1478755 : CollatzResearch.WordTrace tailWord_1478755 prefixEnd_1478755 337472037884207599094149 := by
  unfold tailWord_1478755
  simp only [CollatzResearch.WordTrace]
  refine ⟨53934625757730661092477719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35956417171820440728318479 53934625757730661092477719)
  ·
    refine ⟨80901938636595991638716579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53934625757730661092477719 80901938636595991638716579)
    ·
      refine ⟨121352907954893987458074869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80901938636595991638716579 121352907954893987458074869)
      ·
        refine ⟨11376835120771311324194519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 121352907954893987458074869 11376835120771311324194519)
        ·
          refine ⟨17065252681156966986291779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11376835120771311324194519 17065252681156966986291779)
          ·
            refine ⟨25597879021735450479437669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17065252681156966986291779 25597879021735450479437669)
            ·
              refine ⟨4799602316575396964894563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25597879021735450479437669 4799602316575396964894563)
              ·
                refine ⟨7199403474863095447341845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4799602316575396964894563 7199403474863095447341845)
                ·
                  refine ⟨337472037884207599094149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7199403474863095447341845 337472037884207599094149)
                  ·
                    rfl

theorem cell21_1478755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 1, 6].length) (baseStart_1478755 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1478755 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1478755 prefixEnd_1478755 := by exact prefixLift 1478755
  have htrace : WordTrace (prefixWord ++ tailWord_1478755) baseStart_1478755 baseEnd_1478755 := by
    simpa [prefixWord, tailWord_1478755, baseEnd_1478755] using wordTrace_append hprefix tailTrace_1478755
  have hstable : (prefixWord ++ tailWord_1478755).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1478755).length < 2 ^ (prefixWord ++ tailWord_1478755).sum := by decide
  have hdescent : baseEnd_1478755 < baseStart_1478755 := by decide
  rcases family_descends (prefixWord ++ tailWord_1478755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1478820 : List Nat := [2, 3, 1, 2, 5, 1, 1, 6]
def baseStart_1478820 : Nat := 118140960795 + 1478820 * 2 ^ 59
def prefixEnd_1478820 : Nat := 4983230072969 + 3 ^ 40 * 1478820 * 2
def baseEnd_1478820 : Nat := 112495623923260643503561

theorem tailTrace_1478820 : CollatzResearch.WordTrace tailWord_1478820 prefixEnd_1478820 112495623923260643503561 := by
  unfold tailWord_1478820
  simp only [CollatzResearch.WordTrace]
  refine ⟨26968498251247588596796957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35957997668330118129062609 26968498251247588596796957)
  ·
    refine ⟨10113186844217845723798859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26968498251247588596796957 10113186844217845723798859)
    ·
      refine ⟨15169780266326768585698289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10113186844217845723798859 15169780266326768585698289)
      ·
        refine ⟨11377335199745076439273717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15169780266326768585698289 11377335199745076439273717)
        ·
          refine ⟨1066625174976100916181911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11377335199745076439273717 1066625174976100916181911)
          ·
            refine ⟨1599937762464151374272867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1066625174976100916181911 1599937762464151374272867)
            ·
              refine ⟨2399906643696227061409301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1599937762464151374272867 2399906643696227061409301)
              ·
                refine ⟨112495623923260643503561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2399906643696227061409301 112495623923260643503561)
                ·
                  rfl

theorem cell21_1478820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 1, 6].length) (baseStart_1478820 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1478820 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1478820 prefixEnd_1478820 := by exact prefixLift 1478820
  have htrace : WordTrace (prefixWord ++ tailWord_1478820) baseStart_1478820 baseEnd_1478820 := by
    simpa [prefixWord, tailWord_1478820, baseEnd_1478820] using wordTrace_append hprefix tailTrace_1478820
  have hstable : (prefixWord ++ tailWord_1478820).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1478820).length < 2 ^ (prefixWord ++ tailWord_1478820).sum := by decide
  have hdescent : baseEnd_1478820 < baseStart_1478820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1478820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1478862 : List Nat := [4, 1, 1, 1, 4, 2, 8]
def baseStart_1478862 : Nat := 118140960795 + 1478862 * 2 ^ 59
def prefixEnd_1478862 : Nat := 4983230072969 + 3 ^ 40 * 1478862 * 2
def baseEnd_1478862 : Nat := 37499606304666576756733

theorem tailTrace_1478862 : CollatzResearch.WordTrace tailWord_1478862 prefixEnd_1478862 37499606304666576756733 := by
  unfold tailWord_1478862
  simp only [CollatzResearch.WordTrace]
  refine ⟨6742316046042877295827855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35959018912228678911081893 6742316046042877295827855)
  ·
    refine ⟨10113474069064315943741783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6742316046042877295827855 10113474069064315943741783)
    ·
      refine ⟨15170211103596473915612675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10113474069064315943741783 15170211103596473915612675)
      ·
        refine ⟨22755316655394710873419013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15170211103596473915612675 22755316655394710873419013)
        ·
          refine ⟨4266621872886508288766065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22755316655394710873419013 4266621872886508288766065)
          ·
            refine ⟨3199966404664881216574549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4266621872886508288766065 3199966404664881216574549)
            ·
              refine ⟨37499606304666576756733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3199966404664881216574549 37499606304666576756733)
              ·
                rfl

theorem cell21_1478862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 8].length) (baseStart_1478862 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1478862 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1478862 prefixEnd_1478862 := by exact prefixLift 1478862
  have htrace : WordTrace (prefixWord ++ tailWord_1478862) baseStart_1478862 baseEnd_1478862 := by
    simpa [prefixWord, tailWord_1478862, baseEnd_1478862] using wordTrace_append hprefix tailTrace_1478862
  have hstable : (prefixWord ++ tailWord_1478862).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1478862).length < 2 ^ (prefixWord ++ tailWord_1478862).sum := by decide
  have hdescent : baseEnd_1478862 < baseStart_1478862 := by decide
  rcases family_descends (prefixWord ++ tailWord_1478862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1478921 : List Nat := [1, 2, 1, 1, 3, 4, 9]
def baseStart_1478921 : Nat := 118140960795 + 1478921 * 2 ^ 59
def prefixEnd_1478921 : Nat := 4983230072969 + 3 ^ 40 * 1478921 * 2
def baseEnd_1478921 : Nat := 37501102371758688814127

theorem tailTrace_1478921 : CollatzResearch.WordTrace tailWord_1478921 prefixEnd_1478921 37501102371758688814127 := by
  unfold tailWord_1478921
  simp only [CollatzResearch.WordTrace]
  refine ⟨53940680275129271443020617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35960453516752847628680411 53940680275129271443020617)
  ·
    refine ⟨40455510206346953582265463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53940680275129271443020617 40455510206346953582265463)
    ·
      refine ⟨60683265309520430373398195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40455510206346953582265463 60683265309520430373398195)
      ·
        refine ⟨91024897964280645560097293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60683265309520430373398195 91024897964280645560097293)
        ·
          refine ⟨34134336736605242085036485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91024897964280645560097293 34134336736605242085036485)
          ·
            refine ⟨6400188138113482890944341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34134336736605242085036485 6400188138113482890944341)
            ·
              refine ⟨37501102371758688814127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6400188138113482890944341 37501102371758688814127)
              ·
                rfl

theorem cell21_1478921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 9].length) (baseStart_1478921 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1478921 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1478921 prefixEnd_1478921 := by exact prefixLift 1478921
  have htrace : WordTrace (prefixWord ++ tailWord_1478921) baseStart_1478921 baseEnd_1478921 := by
    simpa [prefixWord, tailWord_1478921, baseEnd_1478921] using wordTrace_append hprefix tailTrace_1478921
  have hstable : (prefixWord ++ tailWord_1478921).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1478921).length < 2 ^ (prefixWord ++ tailWord_1478921).sum := by decide
  have hdescent : baseEnd_1478921 < baseStart_1478921 := by decide
  rcases family_descends (prefixWord ++ tailWord_1478921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1478941 : List Nat := [1, 4, 2, 3, 2, 1, 1, 3, 4]
def baseStart_1478941 : Nat := 118140960795 + 1478941 * 2 ^ 59
def prefixEnd_1478941 : Nat := 4983230072969 + 3 ^ 40 * 1478941 * 2
def baseEnd_1478941 : Nat := 337514485618312608993769

theorem tailTrace_1478941 : CollatzResearch.WordTrace tailWord_1478941 prefixEnd_1478941 337514485618312608993769 := by
  unfold tailWord_1478941
  simp only [CollatzResearch.WordTrace]
  refine ⟨53941409735056814858748677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35960939823371209905832451 53941409735056814858748677)
  ·
    refine ⟨10114014325323152786015377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53941409735056814858748677 10114014325323152786015377)
    ·
      refine ⟨7585510743992364589511533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10114014325323152786015377 7585510743992364589511533)
      ·
        refine ⟨2844566528997136721066825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7585510743992364589511533 2844566528997136721066825)
        ·
          refine ⟨2133424896747852540800119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2844566528997136721066825 2133424896747852540800119)
          ·
            refine ⟨3200137345121778811200179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2133424896747852540800119 3200137345121778811200179)
            ·
              refine ⟨4800206017682668216800269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3200137345121778811200179 4800206017682668216800269)
              ·
                refine ⟨1800077256631000581300101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4800206017682668216800269 1800077256631000581300101)
                ·
                  refine ⟨337514485618312608993769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1800077256631000581300101 337514485618312608993769)
                  ·
                    rfl

theorem cell21_1478941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 3, 4].length) (baseStart_1478941 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1478941 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1478941 prefixEnd_1478941 := by exact prefixLift 1478941
  have htrace : WordTrace (prefixWord ++ tailWord_1478941) baseStart_1478941 baseEnd_1478941 := by
    simpa [prefixWord, tailWord_1478941, baseEnd_1478941] using wordTrace_append hprefix tailTrace_1478941
  have hstable : (prefixWord ++ tailWord_1478941).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1478941).length < 2 ^ (prefixWord ++ tailWord_1478941).sum := by decide
  have hdescent : baseEnd_1478941 < baseStart_1478941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1478941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479079 : List Nat := [1, 1, 6, 1, 1, 4, 1, 3, 3]
def baseStart_1479079 : Nat := 118140960795 + 1479079 * 2 ^ 59
def prefixEnd_1479079 : Nat := 4983230072969 + 3 ^ 40 * 1479079 * 2
def baseEnd_1479079 : Nat := 337545979098455035693487

theorem tailTrace_1479079 : CollatzResearch.WordTrace tailWord_1479079 prefixEnd_1479079 337545979098455035693487 := by
  unfold tailWord_1479079
  simp only [CollatzResearch.WordTrace]
  refine ⟨53946443008556864427272291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35964295339037909618181527 53946443008556864427272291)
  ·
    refine ⟨80919664512835296640908437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53946443008556864427272291 80919664512835296640908437)
    ·
      refine ⟨3793109274039154530042583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 80919664512835296640908437 3793109274039154530042583)
      ·
        refine ⟨5689663911058731795063875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3793109274039154530042583 5689663911058731795063875)
        ·
          refine ⟨8534495866588097692595813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5689663911058731795063875 8534495866588097692595813)
          ·
            refine ⟨1600217974985268317361715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8534495866588097692595813 1600217974985268317361715)
            ·
              refine ⟨2400326962477902476042573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1600217974985268317361715 2400326962477902476042573)
              ·
                refine ⟨900122610929213428515965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2400326962477902476042573 900122610929213428515965)
                ·
                  refine ⟨337545979098455035693487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 900122610929213428515965 337545979098455035693487)
                  ·
                    rfl

theorem cell21_1479079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 1, 3, 3].length) (baseStart_1479079 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1479079 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1479079 prefixEnd_1479079 := by exact prefixLift 1479079
  have htrace : WordTrace (prefixWord ++ tailWord_1479079) baseStart_1479079 baseEnd_1479079 := by
    simpa [prefixWord, tailWord_1479079, baseEnd_1479079] using wordTrace_append hprefix tailTrace_1479079
  have hstable : (prefixWord ++ tailWord_1479079).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479079).length < 2 ^ (prefixWord ++ tailWord_1479079).sum := by decide
  have hdescent : baseEnd_1479079 < baseStart_1479079 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479180 : List Nat := [2, 2, 1, 2, 4, 1, 1, 1, 7]
def baseStart_1479180 : Nat := 118140960795 + 1479180 * 2 ^ 59
def prefixEnd_1479180 : Nat := 4983230072969 + 3 ^ 40 * 1479180 * 2
def baseEnd_1479180 : Nat := 337569028674501304509947

theorem tailTrace_1479180 : CollatzResearch.WordTrace tailWord_1479180 prefixEnd_1479180 337569028674501304509947 := by
  unfold tailWord_1479180
  simp only [CollatzResearch.WordTrace]
  refine ⟨26975063390595479338349497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35966751187460639117799329 26975063390595479338349497)
  ·
    refine ⟨20231297542946609503762123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26975063390595479338349497 20231297542946609503762123)
    ·
      refine ⟨30346946314419914255643185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20231297542946609503762123 30346946314419914255643185)
      ·
        refine ⟨22760209735814935691732389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30346946314419914255643185 22760209735814935691732389)
        ·
          refine ⟨4267539325465300442199823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22760209735814935691732389 4267539325465300442199823)
          ·
            refine ⟨6401308988197950663299735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4267539325465300442199823 6401308988197950663299735)
            ·
              refine ⟨9601963482296925994949603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6401308988197950663299735 9601963482296925994949603)
              ·
                refine ⟨14402945223445388992424405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9601963482296925994949603 14402945223445388992424405)
                ·
                  refine ⟨337569028674501304509947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14402945223445388992424405 337569028674501304509947)
                  ·
                    rfl

theorem cell21_1479180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 1, 7].length) (baseStart_1479180 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1479180 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1479180 prefixEnd_1479180 := by exact prefixLift 1479180
  have htrace : WordTrace (prefixWord ++ tailWord_1479180) baseStart_1479180 baseEnd_1479180 := by
    simpa [prefixWord, tailWord_1479180, baseEnd_1479180] using wordTrace_append hprefix tailTrace_1479180
  have hstable : (prefixWord ++ tailWord_1479180).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479180).length < 2 ^ (prefixWord ++ tailWord_1479180).sum := by decide
  have hdescent : baseEnd_1479180 < baseStart_1479180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479214 : List Nat := [4, 1, 3, 1, 3, 1, 2, 1, 5]
def baseStart_1479214 : Nat := 118140960795 + 1479214 * 2 ^ 59
def prefixEnd_1479214 : Nat := 4983230072969 + 3 ^ 40 * 1479214 * 2
def baseEnd_1479214 : Nat := 337576787937724800943211

theorem tailTrace_1479214 : CollatzResearch.WordTrace tailWord_1479214 prefixEnd_1479214 337576787937724800943211 := by
  unfold tailWord_1479214
  simp only [CollatzResearch.WordTrace]
  refine ⟨6743920857883472810429587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35967577908711854988957797 6743920857883472810429587)
  ·
    refine ⟨10115881286825209215644381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6743920857883472810429587 10115881286825209215644381)
    ·
      refine ⟨3793455482559453455866643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10115881286825209215644381 3793455482559453455866643)
      ·
        refine ⟨5690183223839180183799965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3793455482559453455866643 5690183223839180183799965)
        ·
          refine ⟨2133818708939692568924987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5690183223839180183799965 2133818708939692568924987)
          ·
            refine ⟨3200728063409538853387481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2133818708939692568924987 3200728063409538853387481)
            ·
              refine ⟨2400546047557154140040611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3200728063409538853387481 2400546047557154140040611)
              ·
                refine ⟨3600819071335731210060917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2400546047557154140040611 3600819071335731210060917)
                ·
                  refine ⟨337576787937724800943211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3600819071335731210060917 337576787937724800943211)
                  ·
                    rfl

theorem cell21_1479214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 2, 1, 5].length) (baseStart_1479214 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1479214 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1479214 prefixEnd_1479214 := by exact prefixLift 1479214
  have htrace : WordTrace (prefixWord ++ tailWord_1479214) baseStart_1479214 baseEnd_1479214 := by
    simpa [prefixWord, tailWord_1479214, baseEnd_1479214] using wordTrace_append hprefix tailTrace_1479214
  have hstable : (prefixWord ++ tailWord_1479214).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479214).length < 2 ^ (prefixWord ++ tailWord_1479214).sum := by decide
  have hdescent : baseEnd_1479214 < baseStart_1479214 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479225 : List Nat := [1, 2, 1, 5, 1, 1, 2, 8]
def baseStart_1479225 : Nat := 118140960795 + 1479225 * 2 ^ 59
def prefixEnd_1479225 : Nat := 4983230072969 + 3 ^ 40 * 1479225 * 2
def baseEnd_1479225 : Nat := 112526432762530408753285

theorem tailTrace_1479225 : CollatzResearch.WordTrace tailWord_1479225 prefixEnd_1479225 112526432762530408753285 := by
  unfold tailWord_1479225
  simp only [CollatzResearch.WordTrace]
  refine ⟨53951768066027931362087129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35967845377351954241391419 53951768066027931362087129)
  ·
    refine ⟨40463826049520948521565347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53951768066027931362087129 40463826049520948521565347)
    ·
      refine ⟨60695739074281422782348021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40463826049520948521565347 60695739074281422782348021)
      ·
        refine ⟨5690225538213883385845127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 60695739074281422782348021 5690225538213883385845127)
        ·
          refine ⟨8535338307320825078767691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5690225538213883385845127 8535338307320825078767691)
          ·
            refine ⟨12803007460981237618151537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8535338307320825078767691 12803007460981237618151537)
            ·
              refine ⟨9602255595735928213613653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12803007460981237618151537 9602255595735928213613653)
              ·
                refine ⟨112526432762530408753285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9602255595735928213613653 112526432762530408753285)
                ·
                  rfl

theorem cell21_1479225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 8].length) (baseStart_1479225 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1479225 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1479225 prefixEnd_1479225 := by exact prefixLift 1479225
  have htrace : WordTrace (prefixWord ++ tailWord_1479225) baseStart_1479225 baseEnd_1479225 := by
    simpa [prefixWord, tailWord_1479225, baseEnd_1479225] using wordTrace_append hprefix tailTrace_1479225
  have hstable : (prefixWord ++ tailWord_1479225).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479225).length < 2 ^ (prefixWord ++ tailWord_1479225).sum := by decide
  have hdescent : baseEnd_1479225 < baseStart_1479225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479242 : List Nat := [3, 1, 2, 1, 1, 4, 4, 5]
def baseStart_1479242 : Nat := 118140960795 + 1479242 * 2 ^ 59
def prefixEnd_1479242 : Nat := 4983230072969 + 3 ^ 40 * 1479242 * 2
def baseEnd_1479242 : Nat := 112527725973067658158829

theorem tailTrace_1479242 : CollatzResearch.WordTrace tailWord_1479242 prefixEnd_1479242 112527725973067658158829 := by
  unfold tailWord_1479242
  simp only [CollatzResearch.WordTrace]
  refine ⟨13488097026741585816363995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35968258737977562176970653 13488097026741585816363995)
  ·
    refine ⟨20232145540112378724545993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13488097026741585816363995 20232145540112378724545993)
    ·
      refine ⟨15174109155084284043409495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20232145540112378724545993 15174109155084284043409495)
      ·
        refine ⟨22761163732626426065114243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15174109155084284043409495 22761163732626426065114243)
        ·
          refine ⟨34141745598939639097671365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22761163732626426065114243 34141745598939639097671365)
          ·
            refine ⟨6401577299801182330813381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34141745598939639097671365 6401577299801182330813381)
            ·
              refine ⟨1200295743712721687027509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6401577299801182330813381 1200295743712721687027509)
              ·
                refine ⟨112527725973067658158829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1200295743712721687027509 112527725973067658158829)
                ·
                  rfl

theorem cell21_1479242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 4, 5].length) (baseStart_1479242 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1479242 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1479242 prefixEnd_1479242 := by exact prefixLift 1479242
  have htrace : WordTrace (prefixWord ++ tailWord_1479242) baseStart_1479242 baseEnd_1479242 := by
    simpa [prefixWord, tailWord_1479242, baseEnd_1479242] using wordTrace_append hprefix tailTrace_1479242
  have hstable : (prefixWord ++ tailWord_1479242).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479242).length < 2 ^ (prefixWord ++ tailWord_1479242).sum := by decide
  have hdescent : baseEnd_1479242 < baseStart_1479242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479301 : List Nat := [1, 3, 1, 1, 4, 2, 2, 7]
def baseStart_1479301 : Nat := 118140960795 + 1479301 * 2 ^ 59
def prefixEnd_1479301 : Nat := 4983230072969 + 3 ^ 40 * 1479301 * 2
def baseEnd_1479301 : Nat := 112532214174343994331011

theorem tailTrace_1479301 : CollatzResearch.WordTrace tailWord_1479301 prefixEnd_1479301 112532214174343994331011 := by
  unfold tailWord_1479301
  simp only [CollatzResearch.WordTrace]
  refine ⟨53954540013752596341853757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35969693342501730894569171 53954540013752596341853757)
  ·
    refine ⟨20232952505157223628195159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53954540013752596341853757 20232952505157223628195159)
    ·
      refine ⟨30349428757735835442292739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20232952505157223628195159 30349428757735835442292739)
      ·
        refine ⟨45524143136603753163439109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30349428757735835442292739 45524143136603753163439109)
        ·
          refine ⟨8535776838113203718144833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45524143136603753163439109 8535776838113203718144833)
          ·
            refine ⟨6401832628584902788608625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8535776838113203718144833 6401832628584902788608625)
            ·
              refine ⟨4801374471438677091456469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6401832628584902788608625 4801374471438677091456469)
              ·
                refine ⟨112532214174343994331011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4801374471438677091456469 112532214174343994331011)
                ·
                  rfl

theorem cell21_1479301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 7].length) (baseStart_1479301 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1479301 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1479301 prefixEnd_1479301 := by exact prefixLift 1479301
  have htrace : WordTrace (prefixWord ++ tailWord_1479301) baseStart_1479301 baseEnd_1479301 := by
    simpa [prefixWord, tailWord_1479301, baseEnd_1479301] using wordTrace_append hprefix tailTrace_1479301
  have hstable : (prefixWord ++ tailWord_1479301).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479301).length < 2 ^ (prefixWord ++ tailWord_1479301).sum := by decide
  have hdescent : baseEnd_1479301 < baseStart_1479301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479315 : List Nat := [1, 1, 1, 2, 1, 2, 2, 4, 7]
def baseStart_1479315 : Nat := 118140960795 + 1479315 * 2 ^ 59
def prefixEnd_1479315 : Nat := 4983230072969 + 3 ^ 40 * 1479315 * 2
def baseEnd_1479315 : Nat := 337599837513771069759671

theorem tailTrace_1479315 : CollatzResearch.WordTrace tailWord_1479315 prefixEnd_1479315 337599837513771069759671 := by
  unfold tailWord_1479315
  simp only [CollatzResearch.WordTrace]
  refine ⟨53955050635701876732863399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35970033757134584488575599 53955050635701876732863399)
  ·
    refine ⟨80932575953552815099295099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53955050635701876732863399 80932575953552815099295099)
    ·
      refine ⟨121398863930329222648942649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80932575953552815099295099 121398863930329222648942649)
      ·
        refine ⟨91049147947746916986706987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121398863930329222648942649 91049147947746916986706987)
        ·
          refine ⟨136573721921620375480060481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91049147947746916986706987 136573721921620375480060481)
          ·
            refine ⟨102430291441215281610045361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136573721921620375480060481 102430291441215281610045361)
            ·
              refine ⟨76822718580911461207534021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102430291441215281610045361 76822718580911461207534021)
              ·
                refine ⟨14404259733920898976412629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76822718580911461207534021 14404259733920898976412629)
                ·
                  refine ⟨337599837513771069759671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14404259733920898976412629 337599837513771069759671)
                  ·
                    rfl

theorem cell21_1479315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 4, 7].length) (baseStart_1479315 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1479315 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1479315 prefixEnd_1479315 := by exact prefixLift 1479315
  have htrace : WordTrace (prefixWord ++ tailWord_1479315) baseStart_1479315 baseEnd_1479315 := by
    simpa [prefixWord, tailWord_1479315, baseEnd_1479315] using wordTrace_append hprefix tailTrace_1479315
  have hstable : (prefixWord ++ tailWord_1479315).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479315).length < 2 ^ (prefixWord ++ tailWord_1479315).sum := by decide
  have hdescent : baseEnd_1479315 < baseStart_1479315 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479332 : List Nat := [2, 3, 1, 2, 2, 1, 2, 3, 5]
def baseStart_1479332 : Nat := 118140960795 + 1479332 * 2 ^ 59
def prefixEnd_1479332 : Nat := 4983230072969 + 3 ^ 40 * 1479332 * 2
def baseEnd_1479332 : Nat := 337603717145382817976303

theorem tailTrace_1479332 : CollatzResearch.WordTrace tailWord_1479332 prefixEnd_1479332 337603717145382817976303 := by
  unfold tailWord_1479332
  simp only [CollatzResearch.WordTrace]
  refine ⟨26977835338320144318116125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35970447117760192424154833 26977835338320144318116125)
  ·
    refine ⟨10116688251870054119293547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26977835338320144318116125 10116688251870054119293547)
    ·
      refine ⟨15175032377805081178940321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10116688251870054119293547 15175032377805081178940321)
      ·
        refine ⟨11381274283353810884205241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15175032377805081178940321 11381274283353810884205241)
        ·
          refine ⟨8535955712515358163153931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11381274283353810884205241 8535955712515358163153931)
          ·
            refine ⟨12803933568773037244730897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8535955712515358163153931 12803933568773037244730897)
            ·
              refine ⟨9602950176579777933548173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12803933568773037244730897 9602950176579777933548173)
              ·
                refine ⟨3601106316217416725080565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9602950176579777933548173 3601106316217416725080565)
                ·
                  refine ⟨337603717145382817976303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3601106316217416725080565 337603717145382817976303)
                  ·
                    rfl

theorem cell21_1479332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 3, 5].length) (baseStart_1479332 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1479332 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1479332 prefixEnd_1479332 := by exact prefixLift 1479332
  have htrace : WordTrace (prefixWord ++ tailWord_1479332) baseStart_1479332 baseEnd_1479332 := by
    simpa [prefixWord, tailWord_1479332, baseEnd_1479332] using wordTrace_append hprefix tailTrace_1479332
  have hstable : (prefixWord ++ tailWord_1479332).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479332).length < 2 ^ (prefixWord ++ tailWord_1479332).sum := by decide
  have hdescent : baseEnd_1479332 < baseStart_1479332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479346 : List Nat := [3, 2, 1, 1, 1, 2, 1, 2, 8]
def baseStart_1479346 : Nat := 118140960795 + 1479346 * 2 ^ 59
def prefixEnd_1479346 : Nat := 4983230072969 + 3 ^ 40 * 1479346 * 2
def baseEnd_1479346 : Nat := 337606912136121904742941

theorem tailTrace_1479346 : CollatzResearch.WordTrace tailWord_1479346 prefixEnd_1479346 337606912136121904742941 := by
  unfold tailWord_1479346
  simp only [CollatzResearch.WordTrace]
  refine ⟨13489045324647392256810473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35970787532393046018161261 13489045324647392256810473)
  ·
    refine ⟨10116783993485544192607855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13489045324647392256810473 10116783993485544192607855)
    ·
      refine ⟨15175175990228316288911783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10116783993485544192607855 15175175990228316288911783)
      ·
        refine ⟨22762763985342474433367675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15175175990228316288911783 22762763985342474433367675)
        ·
          refine ⟨34144145978013711650051513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22762763985342474433367675 34144145978013711650051513)
          ·
            refine ⟨25608109483510283737538635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34144145978013711650051513 25608109483510283737538635)
            ·
              refine ⟨38412164225265425606307953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25608109483510283737538635 38412164225265425606307953)
              ·
                refine ⟨28809123168949069204730965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38412164225265425606307953 28809123168949069204730965)
                ·
                  refine ⟨337606912136121904742941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28809123168949069204730965 337606912136121904742941)
                  ·
                    rfl

theorem cell21_1479346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 8].length) (baseStart_1479346 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1479346 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1479346 prefixEnd_1479346 := by exact prefixLift 1479346
  have htrace : WordTrace (prefixWord ++ tailWord_1479346) baseStart_1479346 baseEnd_1479346 := by
    simpa [prefixWord, tailWord_1479346, baseEnd_1479346] using wordTrace_append hprefix tailTrace_1479346
  have hstable : (prefixWord ++ tailWord_1479346).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479346).length < 2 ^ (prefixWord ++ tailWord_1479346).sum := by decide
  have hdescent : baseEnd_1479346 < baseStart_1479346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479349 : List Nat := [1, 3, 3, 3, 1, 2, 1, 2, 5]
def baseStart_1479349 : Nat := 118140960795 + 1479349 * 2 ^ 59
def prefixEnd_1479349 : Nat := 4983230072969 + 3 ^ 40 * 1479349 * 2
def baseEnd_1479349 : Nat := 337607596776994566192935

theorem tailTrace_1479349 : CollatzResearch.WordTrace tailWord_1479349 prefixEnd_1479349 337607596776994566192935 := by
  unfold tailWord_1479349
  simp only [CollatzResearch.WordTrace]
  refine ⟨53956290717578700539601101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35970860478385800359734067 53956290717578700539601101)
  ·
    refine ⟨20233609019092012702350413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53956290717578700539601101 20233609019092012702350413)
    ·
      refine ⟨7587603382159504763381405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20233609019092012702350413 7587603382159504763381405)
      ·
        refine ⟨2845351268309814286268027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7587603382159504763381405 2845351268309814286268027)
        ·
          refine ⟨4268026902464721429402041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2845351268309814286268027 4268026902464721429402041)
          ·
            refine ⟨3201020176848541072051531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4268026902464721429402041 3201020176848541072051531)
            ·
              refine ⟨4801530265272811608077297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3201020176848541072051531 4801530265272811608077297)
              ·
                refine ⟨3601147698954608706057973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4801530265272811608077297 3601147698954608706057973)
                ·
                  refine ⟨337607596776994566192935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3601147698954608706057973 337607596776994566192935)
                  ·
                    rfl

theorem cell21_1479349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 2, 5].length) (baseStart_1479349 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1479349 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1479349 prefixEnd_1479349 := by exact prefixLift 1479349
  have htrace : WordTrace (prefixWord ++ tailWord_1479349) baseStart_1479349 baseEnd_1479349 := by
    simpa [prefixWord, tailWord_1479349, baseEnd_1479349] using wordTrace_append hprefix tailTrace_1479349
  have hstable : (prefixWord ++ tailWord_1479349).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479349).length < 2 ^ (prefixWord ++ tailWord_1479349).sum := by decide
  have hdescent : baseEnd_1479349 < baseStart_1479349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479380 : List Nat := [2, 4, 1, 3, 2, 1, 1, 1, 6]
def baseStart_1479380 : Nat := 118140960795 + 1479380 * 2 ^ 59
def prefixEnd_1479380 : Nat := 4983230072969 + 3 ^ 40 * 1479380 * 2
def baseEnd_1479380 : Nat := 337614671399345401176205

theorem tailTrace_1479380 : CollatzResearch.WordTrace tailWord_1479380 prefixEnd_1479380 337614671399345401176205 := by
  unfold tailWord_1479380
  simp only [CollatzResearch.WordTrace]
  refine ⟨26978710690233196416989797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35971614253644261889319729 26978710690233196416989797)
  ·
    refine ⟨5058508254418724328185587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26978710690233196416989797 5058508254418724328185587)
    ·
      refine ⟨7587762381628086492278381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5058508254418724328185587 7587762381628086492278381)
      ·
        refine ⟨2845410893110532434604393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7587762381628086492278381 2845410893110532434604393)
        ·
          refine ⟨2134058169832899325953295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2845410893110532434604393 2134058169832899325953295)
          ·
            refine ⟨3201087254749348988929943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2134058169832899325953295 3201087254749348988929943)
            ·
              refine ⟨4801630882124023483394915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3201087254749348988929943 4801630882124023483394915)
              ·
                refine ⟨7202446323186035225092373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4801630882124023483394915 7202446323186035225092373)
                ·
                  refine ⟨337614671399345401176205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7202446323186035225092373 337614671399345401176205)
                  ·
                    rfl

theorem cell21_1479380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 1, 6].length) (baseStart_1479380 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1479380 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1479380 prefixEnd_1479380 := by exact prefixLift 1479380
  have htrace : WordTrace (prefixWord ++ tailWord_1479380) baseStart_1479380 baseEnd_1479380 := by
    simpa [prefixWord, tailWord_1479380, baseEnd_1479380] using wordTrace_append hprefix tailTrace_1479380
  have hstable : (prefixWord ++ tailWord_1479380).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479380).length < 2 ^ (prefixWord ++ tailWord_1479380).sum := by decide
  have hdescent : baseEnd_1479380 < baseStart_1479380 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479456 : List Nat := [2, 1, 1, 5, 1, 2, 4, 1, 4]
def baseStart_1479456 : Nat := 118140960795 + 1479456 * 2 ^ 59
def prefixEnd_1479456 : Nat := 4983230072969 + 3 ^ 40 * 1479456 * 2
def baseEnd_1479456 : Nat := 337632015634786157909383

theorem tailTrace_1479456 : CollatzResearch.WordTrace tailWord_1479456 prefixEnd_1479456 337632015634786157909383 := by
  unfold tailWord_1479456
  simp only [CollatzResearch.WordTrace]
  refine ⟨26980096664095528906873111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35973462218794038542497481 26980096664095528906873111)
  ·
    refine ⟨40470144996143293360309667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26980096664095528906873111 40470144996143293360309667)
    ·
      refine ⟨60705217494214940040464501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40470144996143293360309667 60705217494214940040464501)
      ·
        refine ⟨5691114140082650628793547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 60705217494214940040464501 5691114140082650628793547)
        ·
          refine ⟨8536671210123975943190321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5691114140082650628793547 8536671210123975943190321)
          ·
            refine ⟨6402503407592981957392741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8536671210123975943190321 6402503407592981957392741)
            ·
              refine ⟨1200469388923684117011139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6402503407592981957392741 1200469388923684117011139)
              ·
                refine ⟨1800704083385526175516709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1200469388923684117011139 1800704083385526175516709)
                ·
                  refine ⟨337632015634786157909383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1800704083385526175516709 337632015634786157909383)
                  ·
                    rfl

theorem cell21_1479456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 4, 1, 4].length) (baseStart_1479456 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1479456 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1479456 prefixEnd_1479456 := by exact prefixLift 1479456
  have htrace : WordTrace (prefixWord ++ tailWord_1479456) baseStart_1479456 baseEnd_1479456 := by
    simpa [prefixWord, tailWord_1479456, baseEnd_1479456] using wordTrace_append hprefix tailTrace_1479456
  have hstable : (prefixWord ++ tailWord_1479456).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479456).length < 2 ^ (prefixWord ++ tailWord_1479456).sum := by decide
  have hdescent : baseEnd_1479456 < baseStart_1479456 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479470 : List Nat := [4, 1, 3, 2, 1, 1, 2, 7]
def baseStart_1479470 : Nat := 118140960795 + 1479470 * 2 ^ 59
def prefixEnd_1479470 : Nat := 4983230072969 + 3 ^ 40 * 1479470 * 2
def baseEnd_1479470 : Nat := 112545070208508414892007

theorem tailTrace_1479470 : CollatzResearch.WordTrace tailWord_1479470 prefixEnd_1479470 112545070208508414892007 := by
  unfold tailWord_1479470
  simp only [CollatzResearch.WordTrace]
  refine ⟨6745087993767542275594483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35973802633426892136503909 6745087993767542275594483)
  ·
    refine ⟨10117631990651313413391725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6745087993767542275594483 10117631990651313413391725)
    ·
      refine ⟨3794111996494242530021897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10117631990651313413391725 3794111996494242530021897)
      ·
        refine ⟨2845583997370681897516423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3794111996494242530021897 2845583997370681897516423)
        ·
          refine ⟨4268375996056022846274635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2845583997370681897516423 4268375996056022846274635)
          ·
            refine ⟨6402563994084034269411953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4268375996056022846274635 6402563994084034269411953)
            ·
              refine ⟨4801922995563025702058965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6402563994084034269411953 4801922995563025702058965)
              ·
                refine ⟨112545070208508414892007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4801922995563025702058965 112545070208508414892007)
                ·
                  rfl

theorem cell21_1479470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 7].length) (baseStart_1479470 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1479470 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1479470 prefixEnd_1479470 := by exact prefixLift 1479470
  have htrace : WordTrace (prefixWord ++ tailWord_1479470) baseStart_1479470 baseEnd_1479470 := by
    simpa [prefixWord, tailWord_1479470, baseEnd_1479470] using wordTrace_append hprefix tailTrace_1479470
  have hstable : (prefixWord ++ tailWord_1479470).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479470).length < 2 ^ (prefixWord ++ tailWord_1479470).sum := by decide
  have hdescent : baseEnd_1479470 < baseStart_1479470 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479560 : List Nat := [2, 1, 3, 3, 2, 1, 1, 3, 5]
def baseStart_1479560 : Nat := 118140960795 + 1479560 * 2 ^ 59
def prefixEnd_1479560 : Nat := 4983230072969 + 3 ^ 40 * 1479560 * 2
def baseEnd_1479560 : Nat := 337655749851705088175837

theorem tailTrace_1479560 : CollatzResearch.WordTrace tailWord_1479560 prefixEnd_1479560 337655749851705088175837 := by
  unfold tailWord_1479560
  simp only [CollatzResearch.WordTrace]
  refine ⟨26981993259907141787766067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35975991013209522383688089 26981993259907141787766067)
  ·
    refine ⟨40472989889860712681649101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26981993259907141787766067 40472989889860712681649101)
    ·
      refine ⟨15177371208697767255618413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40472989889860712681649101 15177371208697767255618413)
      ·
        refine ⟨5691514203261662720856905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15177371208697767255618413 5691514203261662720856905)
        ·
          refine ⟨4268635652446247040642679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5691514203261662720856905 4268635652446247040642679)
          ·
            refine ⟨6402953478669370560964019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4268635652446247040642679 6402953478669370560964019)
            ·
              refine ⟨9604430218004055841446029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6402953478669370560964019 9604430218004055841446029)
              ·
                refine ⟨3601661331751520940542261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9604430218004055841446029 3601661331751520940542261)
                ·
                  refine ⟨337655749851705088175837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3601661331751520940542261 337655749851705088175837)
                  ·
                    rfl

theorem cell21_1479560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 3, 5].length) (baseStart_1479560 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1479560 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1479560 prefixEnd_1479560 := by exact prefixLift 1479560
  have htrace : WordTrace (prefixWord ++ tailWord_1479560) baseStart_1479560 baseEnd_1479560 := by
    simpa [prefixWord, tailWord_1479560, baseEnd_1479560] using wordTrace_append hprefix tailTrace_1479560
  have hstable : (prefixWord ++ tailWord_1479560).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479560).length < 2 ^ (prefixWord ++ tailWord_1479560).sum := by decide
  have hdescent : baseEnd_1479560 < baseStart_1479560 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479580 : List Nat := [2, 2, 3, 3, 3, 1, 2, 5]
def baseStart_1479580 : Nat := 118140960795 + 1479580 * 2 ^ 59
def prefixEnd_1479580 : Nat := 4983230072969 + 3 ^ 40 * 1479580 * 2
def baseEnd_1479580 : Nat := 112553438041396499280821

theorem tailTrace_1479580 : CollatzResearch.WordTrace tailWord_1479580 prefixEnd_1479580 112553438041396499280821 := by
  unfold tailWord_1479580
  simp only [CollatzResearch.WordTrace]
  refine ⟨26982357989870913495630097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35976477319827884660840129 26982357989870913495630097)
  ·
    refine ⟨20236768492403185121722573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26982357989870913495630097 20236768492403185121722573)
    ·
      refine ⟨7588788184651194420645965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20236768492403185121722573 7588788184651194420645965)
      ·
        refine ⟨2845795569244197907742237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7588788184651194420645965 2845795569244197907742237)
        ·
          refine ⟨1067173338466574215403339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2845795569244197907742237 1067173338466574215403339)
          ·
            refine ⟨1600760007699861323105009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1067173338466574215403339 1600760007699861323105009)
            ·
              refine ⟨1200570005774895992328757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1600760007699861323105009 1200570005774895992328757)
              ·
                refine ⟨112553438041396499280821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1200570005774895992328757 112553438041396499280821)
                ·
                  rfl

theorem cell21_1479580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 2, 5].length) (baseStart_1479580 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1479580 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1479580 prefixEnd_1479580 := by exact prefixLift 1479580
  have htrace : WordTrace (prefixWord ++ tailWord_1479580) baseStart_1479580 baseEnd_1479580 := by
    simpa [prefixWord, tailWord_1479580, baseEnd_1479580] using wordTrace_append hprefix tailTrace_1479580
  have hstable : (prefixWord ++ tailWord_1479580).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479580).length < 2 ^ (prefixWord ++ tailWord_1479580).sum := by decide
  have hdescent : baseEnd_1479580 < baseStart_1479580 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479670 : List Nat := [5, 1, 1, 1, 3, 2, 1, 4, 3]
def baseStart_1479670 : Nat := 118140960795 + 1479670 * 2 ^ 59
def prefixEnd_1479670 : Nat := 4983230072969 + 3 ^ 40 * 1479670 * 2
def baseEnd_1479670 : Nat := 337680853350369341342279

theorem tailTrace_1479670 : CollatzResearch.WordTrace tailWord_1479670 prefixEnd_1479670 337680853350369341342279 := by
  unfold tailWord_1479670
  simp only [CollatzResearch.WordTrace]
  refine ⟨3372999909338485772627279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 35978665699610514908024309 3372999909338485772627279)
  ·
    refine ⟨5059499864007728658940919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3372999909338485772627279 5059499864007728658940919)
    ·
      refine ⟨7589249796011592988411379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5059499864007728658940919 7589249796011592988411379)
      ·
        refine ⟨11383874694017389482617069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7589249796011592988411379 11383874694017389482617069)
        ·
          refine ⟨4268953010256521055981401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11383874694017389482617069 4268953010256521055981401)
          ·
            refine ⟨3201714757692390791986051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4268953010256521055981401 3201714757692390791986051)
            ·
              refine ⟨4802572136538586187979077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3201714757692390791986051 4802572136538586187979077)
              ·
                refine ⟨900482275600984910246077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4802572136538586187979077 900482275600984910246077)
                ·
                  refine ⟨337680853350369341342279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 900482275600984910246077 337680853350369341342279)
                  ·
                    rfl

theorem cell21_1479670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 4, 3].length) (baseStart_1479670 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1479670 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1479670 prefixEnd_1479670 := by exact prefixLift 1479670
  have htrace : WordTrace (prefixWord ++ tailWord_1479670) baseStart_1479670 baseEnd_1479670 := by
    simpa [prefixWord, tailWord_1479670, baseEnd_1479670] using wordTrace_append hprefix tailTrace_1479670
  have hstable : (prefixWord ++ tailWord_1479670).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479670).length < 2 ^ (prefixWord ++ tailWord_1479670).sum := by decide
  have hdescent : baseEnd_1479670 < baseStart_1479670 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479681 : List Nat := [1, 2, 4, 1, 2, 2, 3, 6]
def baseStart_1479681 : Nat := 118140960795 + 1479681 * 2 ^ 59
def prefixEnd_1479681 : Nat := 4983230072969 + 3 ^ 40 * 1479681 * 2
def baseEnd_1479681 : Nat := 112561121233411922219641

theorem tailTrace_1479681 : CollatzResearch.WordTrace tailWord_1479681 prefixEnd_1479681 112561121233411922219641 := by
  unfold tailWord_1479681
  simp only [CollatzResearch.WordTrace]
  refine ⟨53968399752375921240686897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35978933168250614160457931 53968399752375921240686897)
  ·
    refine ⟨40476299814281940930515173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53968399752375921240686897 40476299814281940930515173)
    ·
      refine ⟨7589306215177863924471595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40476299814281940930515173 7589306215177863924471595)
      ·
        refine ⟨11383959322766795886707393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7589306215177863924471595 11383959322766795886707393)
        ·
          refine ⟨8537969492075096915030545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11383959322766795886707393 8537969492075096915030545)
          ·
            refine ⟨6403477119056322686272909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8537969492075096915030545 6403477119056322686272909)
            ·
              refine ⟨2401303919646121007352341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6403477119056322686272909 2401303919646121007352341)
              ·
                refine ⟨112561121233411922219641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2401303919646121007352341 112561121233411922219641)
                ·
                  rfl

theorem cell21_1479681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3, 6].length) (baseStart_1479681 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1479681 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1479681 prefixEnd_1479681 := by exact prefixLift 1479681
  have htrace : WordTrace (prefixWord ++ tailWord_1479681) baseStart_1479681 baseEnd_1479681 := by
    simpa [prefixWord, tailWord_1479681, baseEnd_1479681] using wordTrace_append hprefix tailTrace_1479681
  have hstable : (prefixWord ++ tailWord_1479681).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479681).length < 2 ^ (prefixWord ++ tailWord_1479681).sum := by decide
  have hdescent : baseEnd_1479681 < baseStart_1479681 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479839 : List Nat := [1, 1, 2, 6, 2, 2, 2, 2, 3]
def baseStart_1479839 : Nat := 118140960795 + 1479839 * 2 ^ 59
def prefixEnd_1479839 : Nat := 4983230072969 + 3 ^ 40 * 1479839 * 2
def baseEnd_1479839 : Nat := 337719421452862603025267

theorem tailTrace_1479839 : CollatzResearch.WordTrace tailWord_1479839 prefixEnd_1479839 337719421452862603025267 := by
  unfold tailWord_1479839
  simp only [CollatzResearch.WordTrace]
  refine ⟨53974162485803514224938571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35982774990535676149959047 53974162485803514224938571)
  ·
    refine ⟨80961243728705271337407857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53974162485803514224938571 80961243728705271337407857)
    ·
      refine ⟨60720932796528953503055893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80961243728705271337407857 60720932796528953503055893)
      ·
        refine ⟨2846293724837294695455745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 60720932796528953503055893 2846293724837294695455745)
        ·
          refine ⟨2134720293627971021591809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2846293724837294695455745 2134720293627971021591809)
          ·
            refine ⟨1601040220220978266193857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2134720293627971021591809 1601040220220978266193857)
            ·
              refine ⟨1200780165165733699645393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1601040220220978266193857 1200780165165733699645393)
              ·
                refine ⟨900585123874300274734045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1200780165165733699645393 900585123874300274734045)
                ·
                  refine ⟨337719421452862603025267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 900585123874300274734045 337719421452862603025267)
                  ·
                    rfl

theorem cell21_1479839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 2, 2, 3].length) (baseStart_1479839 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1479839 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1479839 prefixEnd_1479839 := by exact prefixLift 1479839
  have htrace : WordTrace (prefixWord ++ tailWord_1479839) baseStart_1479839 baseEnd_1479839 := by
    simpa [prefixWord, tailWord_1479839, baseEnd_1479839] using wordTrace_append hprefix tailTrace_1479839
  have hstable : (prefixWord ++ tailWord_1479839).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479839).length < 2 ^ (prefixWord ++ tailWord_1479839).sum := by decide
  have hdescent : baseEnd_1479839 < baseStart_1479839 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479850 : List Nat := [3, 1, 5, 1, 1, 1, 3, 6]
def baseStart_1479850 : Nat := 118140960795 + 1479850 * 2 ^ 59
def prefixEnd_1479850 : Nat := 4983230072969 + 3 ^ 40 * 1479850 * 2
def baseEnd_1479850 : Nat := 112573977267576342780637

theorem tailTrace_1479850 : CollatzResearch.WordTrace tailWord_1479850 prefixEnd_1479850 112573977267576342780637 := by
  unfold tailWord_1479850
  simp only [CollatzResearch.WordTrace]
  refine ⟨13493640922190915775897251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35983042459175775402392669 13493640922190915775897251)
  ·
    refine ⟨20240461383286373663845877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13493640922190915775897251 20240461383286373663845877)
    ·
      refine ⟨1897543254683097530985551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20240461383286373663845877 1897543254683097530985551)
      ·
        refine ⟨2846314882024646296478327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1897543254683097530985551 2846314882024646296478327)
        ·
          refine ⟨4269472323036969444717491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2846314882024646296478327 4269472323036969444717491)
          ·
            refine ⟨6404208484555454167076237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4269472323036969444717491 6404208484555454167076237)
            ·
              refine ⟨2401578181708295312653589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6404208484555454167076237 2401578181708295312653589)
              ·
                refine ⟨112573977267576342780637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2401578181708295312653589 112573977267576342780637)
                ·
                  rfl

theorem cell21_1479850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 3, 6].length) (baseStart_1479850 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1479850 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1479850 prefixEnd_1479850 := by exact prefixLift 1479850
  have htrace : WordTrace (prefixWord ++ tailWord_1479850) baseStart_1479850 baseEnd_1479850 := by
    simpa [prefixWord, tailWord_1479850, baseEnd_1479850] using wordTrace_append hprefix tailTrace_1479850
  have hstable : (prefixWord ++ tailWord_1479850).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479850).length < 2 ^ (prefixWord ++ tailWord_1479850).sum := by decide
  have hdescent : baseEnd_1479850 < baseStart_1479850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479923 : List Nat := [1, 1, 1, 2, 2, 5, 2, 2, 5]
def baseStart_1479923 : Nat := 118140960795 + 1479923 * 2 ^ 59
def prefixEnd_1479923 : Nat := 4983230072969 + 3 ^ 40 * 1479923 * 2
def baseEnd_1479923 : Nat := 337738591397297123625095

theorem tailTrace_1479923 : CollatzResearch.WordTrace tailWord_1479923 prefixEnd_1479923 337738591397297123625095 := by
  unfold tailWord_1479923
  simp only [CollatzResearch.WordTrace]
  refine ⟨53977226217499196570996423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35984817478332797713997615 53977226217499196570996423)
  ·
    refine ⟨80965839326248794856494635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53977226217499196570996423 80965839326248794856494635)
    ·
      refine ⟨121448758989373192284741953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80965839326248794856494635 121448758989373192284741953)
      ·
        refine ⟨91086569242029894213556465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121448758989373192284741953 91086569242029894213556465)
        ·
          refine ⟨68314926931522420660167349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91086569242029894213556465 68314926931522420660167349)
          ·
            refine ⟨6404524399830226936890689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 68314926931522420660167349 6404524399830226936890689)
            ·
              refine ⟨4803393299872670202668017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6404524399830226936890689 4803393299872670202668017)
              ·
                refine ⟨3602544974904502652001013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4803393299872670202668017 3602544974904502652001013)
                ·
                  refine ⟨337738591397297123625095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3602544974904502652001013 337738591397297123625095)
                  ·
                    rfl

theorem cell21_1479923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 2, 5].length) (baseStart_1479923 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1479923 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1479923 prefixEnd_1479923 := by exact prefixLift 1479923
  have htrace : WordTrace (prefixWord ++ tailWord_1479923) baseStart_1479923 baseEnd_1479923 := by
    simpa [prefixWord, tailWord_1479923, baseEnd_1479923] using wordTrace_append hprefix tailTrace_1479923
  have hstable : (prefixWord ++ tailWord_1479923).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479923).length < 2 ^ (prefixWord ++ tailWord_1479923).sum := by decide
  have hdescent : baseEnd_1479923 < baseStart_1479923 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479971 : List Nat := [1, 1, 1, 4, 2, 3, 4, 1, 4]
def baseStart_1479971 : Nat := 118140960795 + 1479971 * 2 ^ 59
def prefixEnd_1479971 : Nat := 4983230072969 + 3 ^ 40 * 1479971 * 2
def baseEnd_1479971 : Nat := 337749545651259706824997

theorem tailTrace_1479971 : CollatzResearch.WordTrace tailWord_1479971 prefixEnd_1479971 337749545651259706824997 := by
  unfold tailWord_1479971
  simp only [CollatzResearch.WordTrace]
  refine ⟨53978976921325300768743767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35985984614216867179162511 53978976921325300768743767)
  ·
    refine ⟨80968465381987951153115651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53978976921325300768743767 80968465381987951153115651)
    ·
      refine ⟨121452698072981926729673477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80968465381987951153115651 121452698072981926729673477)
      ·
        refine ⟨22772380888684111261813777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 121452698072981926729673477 22772380888684111261813777)
        ·
          refine ⟨17079285666513083446360333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22772380888684111261813777 17079285666513083446360333)
          ·
            refine ⟨6404732124942406292385125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17079285666513083446360333 6404732124942406292385125)
            ·
              refine ⟨1200887273426701179822211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6404732124942406292385125 1200887273426701179822211)
              ·
                refine ⟨1801330910140051769733317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1200887273426701179822211 1801330910140051769733317)
                ·
                  refine ⟨337749545651259706824997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1801330910140051769733317 337749545651259706824997)
                  ·
                    rfl

theorem cell21_1479971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 4, 1, 4].length) (baseStart_1479971 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1479971 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1479971 prefixEnd_1479971 := by exact prefixLift 1479971
  have htrace : WordTrace (prefixWord ++ tailWord_1479971) baseStart_1479971 baseEnd_1479971 := by
    simpa [prefixWord, tailWord_1479971, baseEnd_1479971] using wordTrace_append hprefix tailTrace_1479971
  have hstable : (prefixWord ++ tailWord_1479971).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479971).length < 2 ^ (prefixWord ++ tailWord_1479971).sum := by decide
  have hdescent : baseEnd_1479971 < baseStart_1479971 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480016 : List Nat := [2, 1, 1, 1, 1, 5, 3, 4, 3]
def baseStart_1480016 : Nat := 118140960795 + 1480016 * 2 ^ 59
def prefixEnd_1480016 : Nat := 4983230072969 + 3 ^ 40 * 1480016 * 2
def baseEnd_1480016 : Nat := 337759815264349628574905

theorem tailTrace_1480016 : CollatzResearch.WordTrace tailWord_1480016 prefixEnd_1480016 337759815264349628574905 := by
  unfold tailWord_1480016
  simp only [CollatzResearch.WordTrace]
  refine ⟨26990309103081136727065951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35987078804108182302754601 26990309103081136727065951)
  ·
    refine ⟨40485463654621705090598927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26990309103081136727065951 40485463654621705090598927)
    ·
      refine ⟨60728195481932557635898391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40485463654621705090598927 60728195481932557635898391)
      ·
        refine ⟨91092293222898836453847587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60728195481932557635898391 91092293222898836453847587)
        ·
          refine ⟨136638439834348254680771381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91092293222898836453847587 136638439834348254680771381)
          ·
            refine ⟨12809853734470148876322317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 136638439834348254680771381 12809853734470148876322317)
            ·
              refine ⟨4803695150426305828620869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12809853734470148876322317 4803695150426305828620869)
              ·
                refine ⟨900692840704932342866413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4803695150426305828620869 900692840704932342866413)
                ·
                  refine ⟨337759815264349628574905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 900692840704932342866413 337759815264349628574905)
                  ·
                    rfl

theorem cell21_1480016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 4, 3].length) (baseStart_1480016 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1480016 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1480016 prefixEnd_1480016 := by exact prefixLift 1480016
  have htrace : WordTrace (prefixWord ++ tailWord_1480016) baseStart_1480016 baseEnd_1480016 := by
    simpa [prefixWord, tailWord_1480016, baseEnd_1480016] using wordTrace_append hprefix tailTrace_1480016
  have hstable : (prefixWord ++ tailWord_1480016).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480016).length < 2 ^ (prefixWord ++ tailWord_1480016).sum := by decide
  have hdescent : baseEnd_1480016 < baseStart_1480016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480075 : List Nat := [1, 1, 1, 1, 4, 3, 4, 1, 5]
def baseStart_1480075 : Nat := 118140960795 + 1480075 * 2 ^ 59
def prefixEnd_1480075 : Nat := 4983230072969 + 3 ^ 40 * 1480075 * 2
def baseEnd_1480075 : Nat := 337773279868178637091451

theorem tailTrace_1480075 : CollatzResearch.WordTrace tailWord_1480075 prefixEnd_1480075 337773279868178637091451 := by
  unfold tailWord_1480075
  simp only [CollatzResearch.WordTrace]
  refine ⟨53982770112948526530529679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35988513408632351020353119 53982770112948526530529679)
  ·
    refine ⟨80974155169422789795794519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53982770112948526530529679 80974155169422789795794519)
    ·
      refine ⟨121461232754134184693691779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80974155169422789795794519 121461232754134184693691779)
      ·
        refine ⟨182191849131201277040537669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121461232754134184693691779 182191849131201277040537669)
        ·
          refine ⟨34160971712100239445100813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 182191849131201277040537669 34160971712100239445100813)
          ·
            refine ⟨12810364392037589791912805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34160971712100239445100813 12810364392037589791912805)
            ·
              refine ⟨2401943323507048085983651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12810364392037589791912805 2401943323507048085983651)
              ·
                refine ⟨3602914985260572128975477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2401943323507048085983651 3602914985260572128975477)
                ·
                  refine ⟨337773279868178637091451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3602914985260572128975477 337773279868178637091451)
                  ·
                    rfl

theorem cell21_1480075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4, 1, 5].length) (baseStart_1480075 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1480075 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1480075 prefixEnd_1480075 := by exact prefixLift 1480075
  have htrace : WordTrace (prefixWord ++ tailWord_1480075) baseStart_1480075 baseEnd_1480075 := by
    simpa [prefixWord, tailWord_1480075, baseEnd_1480075] using wordTrace_append hprefix tailTrace_1480075
  have hstable : (prefixWord ++ tailWord_1480075).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480075).length < 2 ^ (prefixWord ++ tailWord_1480075).sum := by decide
  have hdescent : baseEnd_1480075 < baseStart_1480075 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480140 : List Nat := [2, 2, 1, 4, 2, 3, 2, 1, 4]
def baseStart_1480140 : Nat := 118140960795 + 1480140 * 2 ^ 59
def prefixEnd_1480140 : Nat := 4983230072969 + 3 ^ 40 * 1480140 * 2
def baseEnd_1480140 : Nat := 337788113753752968507985

theorem tailTrace_1480140 : CollatzResearch.WordTrace tailWord_1480140 prefixEnd_1480140 337788113753752968507985 := by
  unfold tailWord_1480140
  simp only [CollatzResearch.WordTrace]
  refine ⟨26992570428856521315822937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35990093905142028421097249 26992570428856521315822937)
  ·
    refine ⟨20244427821642390986867203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26992570428856521315822937 20244427821642390986867203)
    ·
      refine ⟨30366641732463586480300805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20244427821642390986867203 30366641732463586480300805)
      ·
        refine ⟨5693745324836922465056401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30366641732463586480300805 5693745324836922465056401)
        ·
          refine ⟨4270308993627691848792301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5693745324836922465056401 4270308993627691848792301)
          ·
            refine ⟨1601365872610384443297113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4270308993627691848792301 1601365872610384443297113)
            ·
              refine ⟨1201024404457788332472835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1601365872610384443297113 1201024404457788332472835)
              ·
                refine ⟨1801536606686682498709253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1201024404457788332472835 1801536606686682498709253)
                ·
                  refine ⟨337788113753752968507985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1801536606686682498709253 337788113753752968507985)
                  ·
                    rfl

theorem cell21_1480140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 2, 1, 4].length) (baseStart_1480140 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1480140 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1480140 prefixEnd_1480140 := by exact prefixLift 1480140
  have htrace : WordTrace (prefixWord ++ tailWord_1480140) baseStart_1480140 baseEnd_1480140 := by
    simpa [prefixWord, tailWord_1480140, baseEnd_1480140] using wordTrace_append hprefix tailTrace_1480140
  have hstable : (prefixWord ++ tailWord_1480140).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480140).length < 2 ^ (prefixWord ++ tailWord_1480140).sum := by decide
  have hdescent : baseEnd_1480140 < baseStart_1480140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480168 : List Nat := [2, 1, 4, 1, 1, 2, 2, 5, 3]
def baseStart_1480168 : Nat := 118140960795 + 1480168 * 2 ^ 59
def prefixEnd_1480168 : Nat := 4983230072969 + 3 ^ 40 * 1480168 * 2
def baseEnd_1480168 : Nat := 337794503735231142041261

theorem tailTrace_1480168 : CollatzResearch.WordTrace tailWord_1480168 prefixEnd_1480168 337794503735231142041261 := by
  unfold tailWord_1480168
  simp only [CollatzResearch.WordTrace]
  refine ⟨26993081050805801706832579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35990774734407735609110105 26993081050805801706832579)
  ·
    refine ⟨40489621576208702560248869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26993081050805801706832579 40489621576208702560248869)
    ·
      refine ⟨7591804045539131730046663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40489621576208702560248869 7591804045539131730046663)
      ·
        refine ⟨11387706068308697595069995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7591804045539131730046663 11387706068308697595069995)
        ·
          refine ⟨17081559102463046392604993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11387706068308697595069995 17081559102463046392604993)
          ·
            refine ⟨12811169326847284794453745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17081559102463046392604993 12811169326847284794453745)
            ·
              refine ⟨9608376995135463595840309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12811169326847284794453745 9608376995135463595840309)
              ·
                refine ⟨900785343293949712110029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9608376995135463595840309 900785343293949712110029)
                ·
                  refine ⟨337794503735231142041261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 900785343293949712110029 337794503735231142041261)
                  ·
                    rfl

theorem cell21_1480168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 5, 3].length) (baseStart_1480168 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1480168 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1480168 prefixEnd_1480168 := by exact prefixLift 1480168
  have htrace : WordTrace (prefixWord ++ tailWord_1480168) baseStart_1480168 baseEnd_1480168 := by
    simpa [prefixWord, tailWord_1480168, baseEnd_1480168] using wordTrace_append hprefix tailTrace_1480168
  have hstable : (prefixWord ++ tailWord_1480168).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480168).length < 2 ^ (prefixWord ++ tailWord_1480168).sum := by decide
  have hdescent : baseEnd_1480168 < baseStart_1480168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480213 : List Nat := [1, 3, 2, 1, 3, 3, 3, 5]
def baseStart_1480213 : Nat := 118140960795 + 1480213 * 2 ^ 59
def prefixEnd_1480213 : Nat := 4983230072969 + 3 ^ 40 * 1480213 * 2
def baseEnd_1480213 : Nat := 112601591116107021263723

theorem tailTrace_1480213 : CollatzResearch.WordTrace tailWord_1480213 prefixEnd_1480213 112601591116107021263723 := by
  unfold tailWord_1480213
  simp only [CollatzResearch.WordTrace]
  refine ⟨53987803386448576099053293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35991868924299050732702195 53987803386448576099053293)
  ·
    refine ⟨20245426269918216037144985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53987803386448576099053293 20245426269918216037144985)
    ·
      refine ⟨15184069702438662027858739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20245426269918216037144985 15184069702438662027858739)
      ·
        refine ⟨22776104553657993041788109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15184069702438662027858739 22776104553657993041788109)
        ·
          refine ⟨8541039207621747390670541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22776104553657993041788109 8541039207621747390670541)
          ·
            refine ⟨3202889702858155271501453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8541039207621747390670541 3202889702858155271501453)
            ·
              refine ⟨1201083638571808226813045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3202889702858155271501453 1201083638571808226813045)
              ·
                refine ⟨112601591116107021263723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1201083638571808226813045 112601591116107021263723)
                ·
                  rfl

theorem cell21_1480213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 3, 5].length) (baseStart_1480213 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1480213 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1480213 prefixEnd_1480213 := by exact prefixLift 1480213
  have htrace : WordTrace (prefixWord ++ tailWord_1480213) baseStart_1480213 baseEnd_1480213 := by
    simpa [prefixWord, tailWord_1480213, baseEnd_1480213] using wordTrace_append hprefix tailTrace_1480213
  have hstable : (prefixWord ++ tailWord_1480213).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480213).length < 2 ^ (prefixWord ++ tailWord_1480213).sum := by decide
  have hdescent : baseEnd_1480213 < baseStart_1480213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480331 : List Nat := [1, 1, 1, 1, 4, 1, 3, 9]
def baseStart_1480331 : Nat := 118140960795 + 1480331 * 2 ^ 59
def prefixEnd_1480331 : Nat := 4983230072969 + 3 ^ 40 * 1480331 * 2
def baseEnd_1480331 : Nat := 112610567518659693608087

theorem tailTrace_1480331 : CollatzResearch.WordTrace tailWord_1480331 prefixEnd_1480331 112610567518659693608087 := by
  unfold tailWord_1480331
  simp only [CollatzResearch.WordTrace]
  refine ⟨53992107200021082251848847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35994738133347388167899231 53992107200021082251848847)
  ·
    refine ⟨80988160800031623377773271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53992107200021082251848847 80988160800031623377773271)
    ·
      refine ⟨121482241200047435066659907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80988160800031623377773271 121482241200047435066659907)
      ·
        refine ⟨182223361800071152599989861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121482241200047435066659907 182223361800071152599989861)
        ·
          refine ⟨34166880337513341112498099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 182223361800071152599989861 34166880337513341112498099)
          ·
            refine ⟨51250320506270011668747149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34166880337513341112498099 51250320506270011668747149)
            ·
              refine ⟨19218870189851254375780181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51250320506270011668747149 19218870189851254375780181)
              ·
                refine ⟨112610567518659693608087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19218870189851254375780181 112610567518659693608087)
                ·
                  rfl

theorem cell21_1480331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 9].length) (baseStart_1480331 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1480331 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1480331 prefixEnd_1480331 := by exact prefixLift 1480331
  have htrace : WordTrace (prefixWord ++ tailWord_1480331) baseStart_1480331 baseEnd_1480331 := by
    simpa [prefixWord, tailWord_1480331, baseEnd_1480331] using wordTrace_append hprefix tailTrace_1480331
  have hstable : (prefixWord ++ tailWord_1480331).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480331).length < 2 ^ (prefixWord ++ tailWord_1480331).sum := by decide
  have hdescent : baseEnd_1480331 < baseStart_1480331 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480348 : List Nat := [2, 2, 3, 2, 3, 9]
def baseStart_1480348 : Nat := 118140960795 + 1480348 * 2 ^ 59
def prefixEnd_1480348 : Nat := 4983230072969 + 3 ^ 40 * 1480348 * 2
def baseEnd_1480348 : Nat := 12512428969910771445959

theorem tailTrace_1480348 : CollatzResearch.WordTrace tailWord_1480348 prefixEnd_1480348 12512428969910771445959 := by
  unfold tailWord_1480348
  simp only [CollatzResearch.WordTrace]
  refine ⟨26996363620479747077608849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35995151493972996103478465 26996363620479747077608849)
  ·
    refine ⟨20247272715359810308206637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26996363620479747077608849 20247272715359810308206637)
    ·
      refine ⟨7592727268259928865577489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20247272715359810308206637 7592727268259928865577489)
      ·
        refine ⟨5694545451194946649183117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7592727268259928865577489 5694545451194946649183117)
        ·
          refine ⟨2135454544198104993443669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5694545451194946649183117 2135454544198104993443669)
          ·
            refine ⟨12512428969910771445959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2135454544198104993443669 12512428969910771445959)
            ·
              rfl

theorem cell21_1480348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 9].length) (baseStart_1480348 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1480348 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1480348 prefixEnd_1480348 := by exact prefixLift 1480348
  have htrace : WordTrace (prefixWord ++ tailWord_1480348) baseStart_1480348 baseEnd_1480348 := by
    simpa [prefixWord, tailWord_1480348, baseEnd_1480348] using wordTrace_append hprefix tailTrace_1480348
  have hstable : (prefixWord ++ tailWord_1480348).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480348).length < 2 ^ (prefixWord ++ tailWord_1480348).sum := by decide
  have hdescent : baseEnd_1480348 < baseStart_1480348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480354 : List Nat := [3, 3, 1, 4, 1, 1, 1, 4, 3]
def baseStart_1480354 : Nat := 118140960795 + 1480354 * 2 ^ 59
def prefixEnd_1480354 : Nat := 4983230072969 + 3 ^ 40 * 1480354 * 2
def baseEnd_1480354 : Nat := 337836951469336151940881

theorem tailTrace_1480354 : CollatzResearch.WordTrace tailWord_1480354 prefixEnd_1480354 337836951469336151940881 := by
  unfold tailWord_1480354
  simp only [CollatzResearch.WordTrace]
  refine ⟨13498236519734439294984029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35995297385958504786624077 13498236519734439294984029)
  ·
    refine ⟨5061838694900414735619011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13498236519734439294984029 5061838694900414735619011)
    ·
      refine ⟨7592758042350622103428517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5061838694900414735619011 7592758042350622103428517)
      ·
        refine ⟨1423642132940741644392847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7592758042350622103428517 1423642132940741644392847)
        ·
          refine ⟨2135463199411112466589271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1423642132940741644392847 2135463199411112466589271)
          ·
            refine ⟨3203194799116668699883907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2135463199411112466589271 3203194799116668699883907)
            ·
              refine ⟨4804792198675003049825861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3203194799116668699883907 4804792198675003049825861)
              ·
                refine ⟨900898537251563071842349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4804792198675003049825861 900898537251563071842349)
                ·
                  refine ⟨337836951469336151940881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 900898537251563071842349 337836951469336151940881)
                  ·
                    rfl

theorem cell21_1480354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 4, 3].length) (baseStart_1480354 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1480354 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1480354 prefixEnd_1480354 := by exact prefixLift 1480354
  have htrace : WordTrace (prefixWord ++ tailWord_1480354) baseStart_1480354 baseEnd_1480354 := by
    simpa [prefixWord, tailWord_1480354, baseEnd_1480354] using wordTrace_append hprefix tailTrace_1480354
  have hstable : (prefixWord ++ tailWord_1480354).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480354).length < 2 ^ (prefixWord ++ tailWord_1480354).sum := by decide
  have hdescent : baseEnd_1480354 < baseStart_1480354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480407 : List Nat := [1, 1, 3, 2, 1, 3, 10]
def baseStart_1480407 : Nat := 118140960795 + 1480407 * 2 ^ 59
def prefixEnd_1480407 : Nat := 4983230072969 + 3 ^ 40 * 1480407 * 2
def baseEnd_1480407 : Nat := 37538782976824426395271

theorem tailTrace_1480407 : CollatzResearch.WordTrace tailWord_1480407 prefixEnd_1480407 37538782976824426395271 := by
  unfold tailWord_1480407
  simp only [CollatzResearch.WordTrace]
  refine ⟨53994879147745747231615475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35996586098497164821076983 53994879147745747231615475)
  ·
    refine ⟨80992318721618620847423213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53994879147745747231615475 80992318721618620847423213)
    ·
      refine ⟨30372119520606982817783705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80992318721618620847423213 30372119520606982817783705)
      ·
        refine ⟨22779089640455237113337779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30372119520606982817783705 22779089640455237113337779)
        ·
          refine ⟨34168634460682855670006669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22779089640455237113337779 34168634460682855670006669)
          ·
            refine ⟨12813237922756070876252501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34168634460682855670006669 12813237922756070876252501)
            ·
              refine ⟨37538782976824426395271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 12813237922756070876252501 37538782976824426395271)
              ·
                rfl

theorem cell21_1480407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 10].length) (baseStart_1480407 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1480407 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1480407 prefixEnd_1480407 := by exact prefixLift 1480407
  have htrace : WordTrace (prefixWord ++ tailWord_1480407) baseStart_1480407 baseEnd_1480407 := by
    simpa [prefixWord, tailWord_1480407, baseEnd_1480407] using wordTrace_append hprefix tailTrace_1480407
  have hstable : (prefixWord ++ tailWord_1480407).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480407).length < 2 ^ (prefixWord ++ tailWord_1480407).sum := by decide
  have hdescent : baseEnd_1480407 < baseStart_1480407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480410 : List Nat := [3, 1, 1, 2, 2, 3, 3, 2, 4]
def baseStart_1480410 : Nat := 118140960795 + 1480410 * 2 ^ 59
def prefixEnd_1480410 : Nat := 4983230072969 + 3 ^ 40 * 1480410 * 2
def baseEnd_1480410 : Nat := 337849731432292499007433

theorem tailTrace_1480410 : CollatzResearch.WordTrace tailWord_1480410 prefixEnd_1480410 337849731432292499007433 := by
  unfold tailWord_1480410
  simp only [CollatzResearch.WordTrace]
  refine ⟨13498747141683719685993671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35996659044489919162649789 13498747141683719685993671)
  ·
    refine ⟨20248120712525579528990507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13498747141683719685993671 20248120712525579528990507)
    ·
      refine ⟨30372181068788369293485761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20248120712525579528990507 30372181068788369293485761)
      ·
        refine ⟨22779135801591276970114321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30372181068788369293485761 22779135801591276970114321)
        ·
          refine ⟨17084351851193457727585741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22779135801591276970114321 17084351851193457727585741)
          ·
            refine ⟨6406631944197546647844653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17084351851193457727585741 6406631944197546647844653)
            ·
              refine ⟨2402486979074079992941745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6406631944197546647844653 2402486979074079992941745)
              ·
                refine ⟨1801865234305559994706309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2402486979074079992941745 1801865234305559994706309)
                ·
                  refine ⟨337849731432292499007433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1801865234305559994706309 337849731432292499007433)
                  ·
                    rfl

theorem cell21_1480410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3, 2, 4].length) (baseStart_1480410 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1480410 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1480410 prefixEnd_1480410 := by exact prefixLift 1480410
  have htrace : WordTrace (prefixWord ++ tailWord_1480410) baseStart_1480410 baseEnd_1480410 := by
    simpa [prefixWord, tailWord_1480410, baseEnd_1480410] using wordTrace_append hprefix tailTrace_1480410
  have hstable : (prefixWord ++ tailWord_1480410).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480410).length < 2 ^ (prefixWord ++ tailWord_1480410).sum := by decide
  have hdescent : baseEnd_1480410 < baseStart_1480410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480413 : List Nat := [1, 4, 3, 3, 1, 1, 2, 1, 5]
def baseStart_1480413 : Nat := 118140960795 + 1480413 * 2 ^ 59
def prefixEnd_1480413 : Nat := 4983230072969 + 3 ^ 40 * 1480413 * 2
def baseEnd_1480413 : Nat := 337850416073165160457427

theorem tailTrace_1480413 : CollatzResearch.WordTrace tailWord_1480413 prefixEnd_1480413 337850416073165160457427 := by
  unfold tailWord_1480413
  simp only [CollatzResearch.WordTrace]
  refine ⟨53995097985724010256333893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35996731990482673504222595 53995097985724010256333893)
  ·
    refine ⟨10124080872323251923062605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53995097985724010256333893 10124080872323251923062605)
    ·
      refine ⟨3796530327121219471148477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10124080872323251923062605 3796530327121219471148477)
      ·
        refine ⟨1423698872670457301680679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3796530327121219471148477 1423698872670457301680679)
        ·
          refine ⟨2135548309005685952521019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1423698872670457301680679 2135548309005685952521019)
          ·
            refine ⟨3203322463508528928781529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2135548309005685952521019 3203322463508528928781529)
            ·
              refine ⟨2402491847631396696586147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3203322463508528928781529 2402491847631396696586147)
              ·
                refine ⟨3603737771447095044879221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2402491847631396696586147 3603737771447095044879221)
                ·
                  refine ⟨337850416073165160457427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3603737771447095044879221 337850416073165160457427)
                  ·
                    rfl

theorem cell21_1480413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 2, 1, 5].length) (baseStart_1480413 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1480413 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1480413 prefixEnd_1480413 := by exact prefixLift 1480413
  have htrace : WordTrace (prefixWord ++ tailWord_1480413) baseStart_1480413 baseEnd_1480413 := by
    simpa [prefixWord, tailWord_1480413, baseEnd_1480413] using wordTrace_append hprefix tailTrace_1480413
  have hstable : (prefixWord ++ tailWord_1480413).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480413).length < 2 ^ (prefixWord ++ tailWord_1480413).sum := by decide
  have hdescent : baseEnd_1480413 < baseStart_1480413 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480469 : List Nat := [1, 3, 2, 1, 2, 3, 2, 1, 6]
def baseStart_1480469 : Nat := 118140960795 + 1480469 * 2 ^ 59
def prefixEnd_1480469 : Nat := 4983230072969 + 3 ^ 40 * 1480469 * 2
def baseEnd_1480469 : Nat := 337863196036121507523979

theorem tailTrace_1480469 : CollatzResearch.WordTrace tailWord_1480469 prefixEnd_1480469 337863196036121507523979 := by
  unfold tailWord_1480469
  simp only [CollatzResearch.WordTrace]
  refine ⟨53997140473521131820372461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35998093649014087880248307 53997140473521131820372461)
  ·
    refine ⟨20248927677570424432639673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53997140473521131820372461 20248927677570424432639673)
    ·
      refine ⟨15186695758177818324479755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20248927677570424432639673 15186695758177818324479755)
      ·
        refine ⟨22780043637266727486719633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15186695758177818324479755 22780043637266727486719633)
        ·
          refine ⟨17085032727950045615039725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22780043637266727486719633 17085032727950045615039725)
          ·
            refine ⟨6406887272981267105639897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17085032727950045615039725 6406887272981267105639897)
            ·
              refine ⟨4805165454735950329229923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6406887272981267105639897 4805165454735950329229923)
              ·
                refine ⟨7207748182103925493844885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4805165454735950329229923 7207748182103925493844885)
                ·
                  refine ⟨337863196036121507523979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7207748182103925493844885 337863196036121507523979)
                  ·
                    rfl

theorem cell21_1480469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 1, 6].length) (baseStart_1480469 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1480469 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1480469 prefixEnd_1480469 := by exact prefixLift 1480469
  have htrace : WordTrace (prefixWord ++ tailWord_1480469) baseStart_1480469 baseEnd_1480469 := by
    simpa [prefixWord, tailWord_1480469, baseEnd_1480469] using wordTrace_append hprefix tailTrace_1480469
  have hstable : (prefixWord ++ tailWord_1480469).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480469).length < 2 ^ (prefixWord ++ tailWord_1480469).sum := by decide
  have hdescent : baseEnd_1480469 < baseStart_1480469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480478 : List Nat := [4, 3, 2, 2, 1, 2, 2, 1, 4]
def baseStart_1480478 : Nat := 118140960795 + 1480478 * 2 ^ 59
def prefixEnd_1480478 : Nat := 4983230072969 + 3 ^ 40 * 1480478 * 2
def baseEnd_1480478 : Nat := 337865249958739491873961

theorem tailTrace_1480478 : CollatzResearch.WordTrace tailWord_1480478 prefixEnd_1480478 337865249958739491873961 := by
  unfold tailWord_1480478
  simp only [CollatzResearch.WordTrace]
  refine ⟨6749683591311065794681261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35998312486992350904966725 6749683591311065794681261)
  ·
    refine ⟨2531131346741649673005473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6749683591311065794681261 2531131346741649673005473)
    ·
      refine ⟨1898348510056237254754105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2531131346741649673005473 1898348510056237254754105)
      ·
        refine ⟨1423761382542177941065579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1898348510056237254754105 1423761382542177941065579)
        ·
          refine ⟨2135642073813266911598369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1423761382542177941065579 2135642073813266911598369)
          ·
            refine ⟨1601731555359950183698777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2135642073813266911598369 1601731555359950183698777)
            ·
              refine ⟨1201298666519962637774083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1601731555359950183698777 1201298666519962637774083)
              ·
                refine ⟨1801947999779943956661125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1201298666519962637774083 1801947999779943956661125)
                ·
                  refine ⟨337865249958739491873961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1801947999779943956661125 337865249958739491873961)
                  ·
                    rfl

theorem cell21_1480478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_1480478 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1480478 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1480478 prefixEnd_1480478 := by exact prefixLift 1480478
  have htrace : WordTrace (prefixWord ++ tailWord_1480478) baseStart_1480478 baseEnd_1480478 := by
    simpa [prefixWord, tailWord_1480478, baseEnd_1480478] using wordTrace_append hprefix tailTrace_1480478
  have hstable : (prefixWord ++ tailWord_1480478).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480478).length < 2 ^ (prefixWord ++ tailWord_1480478).sum := by decide
  have hdescent : baseEnd_1480478 < baseStart_1480478 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480483 : List Nat := [1, 1, 1, 4, 2, 1, 3, 8]
def baseStart_1480483 : Nat := 118140960795 + 1480483 * 2 ^ 59
def prefixEnd_1480483 : Nat := 4983230072969 + 3 ^ 40 * 1480483 * 2
def baseEnd_1480483 : Nat := 112622130342286864763539

theorem tailTrace_1480483 : CollatzResearch.WordTrace tailWord_1480483 prefixEnd_1480483 112622130342286864763539 := by
  unfold tailWord_1480483
  simp only [CollatzResearch.WordTrace]
  refine ⟨53997651095470412211382103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35998434063646941474254735 53997651095470412211382103)
  ·
    refine ⟨80996476643205618317073155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53997651095470412211382103 80996476643205618317073155)
    ·
      refine ⟨121494714964808427475609733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80996476643205618317073155 121494714964808427475609733)
      ·
        refine ⟨22780259055901580151676825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 121494714964808427475609733 22780259055901580151676825)
        ·
          refine ⟨17085194291926185113757619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22780259055901580151676825 17085194291926185113757619)
          ·
            refine ⟨25627791437889277670636429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17085194291926185113757619 25627791437889277670636429)
            ·
              refine ⟨9610421789208479126488661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25627791437889277670636429 9610421789208479126488661)
              ·
                refine ⟨112622130342286864763539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9610421789208479126488661 112622130342286864763539)
                ·
                  rfl

theorem cell21_1480483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 8].length) (baseStart_1480483 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1480483 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1480483 prefixEnd_1480483 := by exact prefixLift 1480483
  have htrace : WordTrace (prefixWord ++ tailWord_1480483) baseStart_1480483 baseEnd_1480483 := by
    simpa [prefixWord, tailWord_1480483, baseEnd_1480483] using wordTrace_append hprefix tailTrace_1480483
  have hstable : (prefixWord ++ tailWord_1480483).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480483).length < 2 ^ (prefixWord ++ tailWord_1480483).sum := by decide
  have hdescent : baseEnd_1480483 < baseStart_1480483 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480545 : List Nat := [1, 2, 3, 1, 1, 1, 3, 5, 4]
def baseStart_1480545 : Nat := 118140960795 + 1480545 * 2 ^ 59
def prefixEnd_1480545 : Nat := 4983230072969 + 3 ^ 40 * 1480545 * 2
def baseEnd_1480545 : Nat := 337880540271562264257157

theorem tailTrace_1480545 : CollatzResearch.WordTrace tailWord_1480545 prefixEnd_1480545 337880540271562264257157 := by
  unfold tailWord_1480545
  simp only [CollatzResearch.WordTrace]
  refine ⟨53999912421245796800139089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35999941614163864533426059 53999912421245796800139089)
  ·
    refine ⟨40499934315934347600104317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53999912421245796800139089 40499934315934347600104317)
    ·
      refine ⟨15187475368475380350039119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40499934315934347600104317 15187475368475380350039119)
      ·
        refine ⟨22781213052713070525058679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15187475368475380350039119 22781213052713070525058679)
        ·
          refine ⟨34171819579069605787588019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22781213052713070525058679 34171819579069605787588019)
          ·
            refine ⟨51257729368604408681382029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34171819579069605787588019 51257729368604408681382029)
            ·
              refine ⟨19221648513226653255518261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51257729368604408681382029 19221648513226653255518261)
              ·
                refine ⟨1802029548114998742704837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19221648513226653255518261 1802029548114998742704837)
                ·
                  refine ⟨337880540271562264257157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1802029548114998742704837 337880540271562264257157)
                  ·
                    rfl

theorem cell21_1480545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 5, 4].length) (baseStart_1480545 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1480545 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1480545 prefixEnd_1480545 := by exact prefixLift 1480545
  have htrace : WordTrace (prefixWord ++ tailWord_1480545) baseStart_1480545 baseEnd_1480545 := by
    simpa [prefixWord, tailWord_1480545, baseEnd_1480545] using wordTrace_append hprefix tailTrace_1480545
  have hstable : (prefixWord ++ tailWord_1480545).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480545).length < 2 ^ (prefixWord ++ tailWord_1480545).sum := by decide
  have hdescent : baseEnd_1480545 < baseStart_1480545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480610 : List Nat := [3, 3, 1, 2, 3, 2, 2, 5]
def baseStart_1480610 : Nat := 118140960795 + 1480610 * 2 ^ 59
def prefixEnd_1480610 : Nat := 4983230072969 + 3 ^ 40 * 1480610 * 2
def baseEnd_1480610 : Nat := 112631791385712198557897

theorem tailTrace_1480610 : CollatzResearch.WordTrace tailWord_1480610 prefixEnd_1480610 112631791385712198557897 := by
  unfold tailWord_1480610
  simp only [CollatzResearch.WordTrace]
  refine ⟨13500570791502578225313821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36001522110673541934170189 13500570791502578225313821)
  ·
    refine ⟨5062714046813466834492683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13500570791502578225313821 5062714046813466834492683)
    ·
      refine ⟨7594071070220200251739025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5062714046813466834492683 7594071070220200251739025)
      ·
        refine ⟨5695553302665150188804269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7594071070220200251739025 5695553302665150188804269)
        ·
          refine ⟨2135832488499431320801601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5695553302665150188804269 2135832488499431320801601)
          ·
            refine ⟨1601874366374573490601201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2135832488499431320801601 1601874366374573490601201)
            ·
              refine ⟨1201405774780930117950901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1601874366374573490601201 1201405774780930117950901)
              ·
                refine ⟨112631791385712198557897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1201405774780930117950901 112631791385712198557897)
                ·
                  rfl

theorem cell21_1480610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 2, 5].length) (baseStart_1480610 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1480610 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1480610 prefixEnd_1480610 := by exact prefixLift 1480610
  have htrace : WordTrace (prefixWord ++ tailWord_1480610) baseStart_1480610 baseEnd_1480610 := by
    simpa [prefixWord, tailWord_1480610, baseEnd_1480610] using wordTrace_append hprefix tailTrace_1480610
  have hstable : (prefixWord ++ tailWord_1480610).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480610).length < 2 ^ (prefixWord ++ tailWord_1480610).sum := by decide
  have hdescent : baseEnd_1480610 < baseStart_1480610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480652 : List Nat := [2, 2, 1, 4, 1, 3, 2, 6]
def baseStart_1480652 : Nat := 118140960795 + 1480652 * 2 ^ 59
def prefixEnd_1480652 : Nat := 4983230072969 + 3 ^ 40 * 1480652 * 2
def baseEnd_1480652 : Nat := 112634986376451285324535

theorem tailTrace_1480652 : CollatzResearch.WordTrace tailWord_1480652 prefixEnd_1480652 112634986376451285324535 := by
  unfold tailWord_1480652
  simp only [CollatzResearch.WordTrace]
  refine ⟨27001907515929077037142105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36002543354572102716189473 27001907515929077037142105)
  ·
    refine ⟨20251430636946807777856579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27001907515929077037142105 20251430636946807777856579)
    ·
      refine ⟨30377145955420211666784869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20251430636946807777856579 30377145955420211666784869)
      ·
        refine ⟨5695714866641289687522163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30377145955420211666784869 5695714866641289687522163)
        ·
          refine ⟨8543572299961934531283245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5695714866641289687522163 8543572299961934531283245)
          ·
            refine ⟨3203839612485725449231217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8543572299961934531283245 3203839612485725449231217)
            ·
              refine ⟨2402879709364294086923413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3203839612485725449231217 2402879709364294086923413)
              ·
                refine ⟨112634986376451285324535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2402879709364294086923413 112634986376451285324535)
                ·
                  rfl

theorem cell21_1480652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2, 6].length) (baseStart_1480652 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1480652 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1480652 prefixEnd_1480652 := by exact prefixLift 1480652
  have htrace : WordTrace (prefixWord ++ tailWord_1480652) baseStart_1480652 baseEnd_1480652 := by
    simpa [prefixWord, tailWord_1480652, baseEnd_1480652] using wordTrace_append hprefix tailTrace_1480652
  have hstable : (prefixWord ++ tailWord_1480652).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480652).length < 2 ^ (prefixWord ++ tailWord_1480652).sum := by decide
  have hdescent : baseEnd_1480652 < baseStart_1480652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480697 : List Nat := [1, 2, 1, 3, 1, 4, 1, 4, 4]
def baseStart_1480697 : Nat := 118140960795 + 1480697 * 2 ^ 59
def prefixEnd_1480697 : Nat := 4983230072969 + 3 ^ 40 * 1480697 * 2
def baseEnd_1480697 : Nat := 337915228742443777723513

theorem tailTrace_1480697 : CollatzResearch.WordTrace tailWord_1480697 prefixEnd_1480697 337915228742443777723513 := by
  unfold tailWord_1480697
  simp only [CollatzResearch.WordTrace]
  refine ⟨54005456316695126759672345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36003637544463417839781563 54005456316695126759672345)
  ·
    refine ⟨40504092237521345069754259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54005456316695126759672345 40504092237521345069754259)
    ·
      refine ⟨60756138356282017604631389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40504092237521345069754259 60756138356282017604631389)
      ·
        refine ⟨22783551883605756601736771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60756138356282017604631389 22783551883605756601736771)
        ·
          refine ⟨34175327825408634902605157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22783551883605756601736771 34175327825408634902605157)
          ·
            refine ⟨6407873967264119044238467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34175327825408634902605157 6407873967264119044238467)
            ·
              refine ⟨9611810950896178566357701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6407873967264119044238467 9611810950896178566357701)
              ·
                refine ⟨1802214553293033481192069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9611810950896178566357701 1802214553293033481192069)
                ·
                  refine ⟨337915228742443777723513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1802214553293033481192069 337915228742443777723513)
                  ·
                    rfl

theorem cell21_1480697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 4, 4].length) (baseStart_1480697 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1480697 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1480697 prefixEnd_1480697 := by exact prefixLift 1480697
  have htrace : WordTrace (prefixWord ++ tailWord_1480697) baseStart_1480697 baseEnd_1480697 := by
    simpa [prefixWord, tailWord_1480697, baseEnd_1480697] using wordTrace_append hprefix tailTrace_1480697
  have hstable : (prefixWord ++ tailWord_1480697).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480697).length < 2 ^ (prefixWord ++ tailWord_1480697).sum := by decide
  have hdescent : baseEnd_1480697 < baseStart_1480697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480728 : List Nat := [2, 1, 2, 3, 2, 1, 5, 5]
def baseStart_1480728 : Nat := 118140960795 + 1480728 * 2 ^ 59
def prefixEnd_1480728 : Nat := 4983230072969 + 3 ^ 40 * 1480728 * 2
def baseEnd_1480728 : Nat := 112640767788264870902261

theorem tailTrace_1480728 : CollatzResearch.WordTrace tailWord_1480728 prefixEnd_1480728 112640767788264870902261 := by
  unfold tailWord_1480728
  simp only [CollatzResearch.WordTrace]
  refine ⟨27003293489791409527025419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36004391319721879369367225 27003293489791409527025419)
  ·
    refine ⟨40504940234687114290538129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27003293489791409527025419 40504940234687114290538129)
    ·
      refine ⟨30378705176015335717903597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40504940234687114290538129 30378705176015335717903597)
      ·
        refine ⟨11392014441005750894213849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30378705176015335717903597 11392014441005750894213849)
        ·
          refine ⟨8544010830754313170660387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11392014441005750894213849 8544010830754313170660387)
          ·
            refine ⟨12816016246131469755990581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8544010830754313170660387 12816016246131469755990581)
            ·
              refine ⟨1201501523074825289624117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12816016246131469755990581 1201501523074825289624117)
              ·
                refine ⟨112640767788264870902261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1201501523074825289624117 112640767788264870902261)
                ·
                  rfl

theorem cell21_1480728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 5, 5].length) (baseStart_1480728 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1480728 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1480728 prefixEnd_1480728 := by exact prefixLift 1480728
  have htrace : WordTrace (prefixWord ++ tailWord_1480728) baseStart_1480728 baseEnd_1480728 := by
    simpa [prefixWord, tailWord_1480728, baseEnd_1480728] using wordTrace_append hprefix tailTrace_1480728
  have hstable : (prefixWord ++ tailWord_1480728).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480728).length < 2 ^ (prefixWord ++ tailWord_1480728).sum := by decide
  have hdescent : baseEnd_1480728 < baseStart_1480728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480759 : List Nat := [1, 1, 3, 1, 2, 2, 4, 4, 3]
def baseStart_1480759 : Nat := 118140960795 + 1480759 * 2 ^ 59
def prefixEnd_1480759 : Nat := 4983230072969 + 3 ^ 40 * 1480759 * 2
def baseEnd_1480759 : Nat := 337929377987145447690053

theorem tailTrace_1480759 : CollatzResearch.WordTrace tailWord_1480759 prefixEnd_1480759 337929377987145447690053 := by
  unfold tailWord_1480759
  simp only [CollatzResearch.WordTrace]
  refine ⟨54007717642470511348429331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36005145094980340898952887 54007717642470511348429331)
  ·
    refine ⟨81011576463705767022643997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54007717642470511348429331 81011576463705767022643997)
    ·
      refine ⟨30379341173889662633491499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81011576463705767022643997 30379341173889662633491499)
      ·
        refine ⟨45569011760834493950237249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30379341173889662633491499 45569011760834493950237249)
        ·
          refine ⟨34176758820625870462677937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45569011760834493950237249 34176758820625870462677937)
          ·
            refine ⟨25632569115469402847008453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34176758820625870462677937 25632569115469402847008453)
            ·
              refine ⟨4806106709150513033814085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25632569115469402847008453 4806106709150513033814085)
              ·
                refine ⟨901145007965721193840141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4806106709150513033814085 901145007965721193840141)
                ·
                  refine ⟨337929377987145447690053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 901145007965721193840141 337929377987145447690053)
                  ·
                    rfl

theorem cell21_1480759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 4, 3].length) (baseStart_1480759 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1480759 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1480759 prefixEnd_1480759 := by exact prefixLift 1480759
  have htrace : WordTrace (prefixWord ++ tailWord_1480759) baseStart_1480759 baseEnd_1480759 := by
    simpa [prefixWord, tailWord_1480759, baseEnd_1480759] using wordTrace_append hprefix tailTrace_1480759
  have hstable : (prefixWord ++ tailWord_1480759).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480759).length < 2 ^ (prefixWord ++ tailWord_1480759).sum := by decide
  have hdescent : baseEnd_1480759 < baseStart_1480759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480863 : List Nat := [1, 1, 2, 6, 1, 10]
def baseStart_1480863 : Nat := 118140960795 + 1480863 * 2 ^ 59
def prefixEnd_1480863 : Nat := 4983230072969 + 3 ^ 40 * 1480863 * 2
def baseEnd_1480863 : Nat := 12516781933483865850241

theorem tailTrace_1480863 : CollatzResearch.WordTrace tailWord_1480863 prefixEnd_1480863 12516781933483865850241 := by
  unfold tailWord_1480863
  simp only [CollatzResearch.WordTrace]
  refine ⟨54011510834093737110215243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36007673889395824740143495 54011510834093737110215243)
  ·
    refine ⟨81017266251140605665322865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54011510834093737110215243 81017266251140605665322865)
    ·
      refine ⟨60762949688355454248992149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81017266251140605665322865 60762949688355454248992149)
      ·
        refine ⟨2848263266641661917921507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 60762949688355454248992149 2848263266641661917921507)
        ·
          refine ⟨4272394899962492876882261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2848263266641661917921507 4272394899962492876882261)
          ·
            refine ⟨12516781933483865850241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4272394899962492876882261 12516781933483865850241)
            ·
              rfl

theorem cell21_1480863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 10].length) (baseStart_1480863 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1480863 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1480863 prefixEnd_1480863 := by exact prefixLift 1480863
  have htrace : WordTrace (prefixWord ++ tailWord_1480863) baseStart_1480863 baseEnd_1480863 := by
    simpa [prefixWord, tailWord_1480863, baseEnd_1480863] using wordTrace_append hprefix tailTrace_1480863
  have hstable : (prefixWord ++ tailWord_1480863).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480863).length < 2 ^ (prefixWord ++ tailWord_1480863).sum := by decide
  have hdescent : baseEnd_1480863 < baseStart_1480863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480866 : List Nat := [3, 3, 1, 3, 1, 1, 1, 4, 4]
def baseStart_1480866 : Nat := 118140960795 + 1480866 * 2 ^ 59
def prefixEnd_1480866 : Nat := 4983230072969 + 3 ^ 40 * 1480866 * 2
def baseEnd_1480866 : Nat := 337953796844937039406501

theorem tailTrace_1480866 : CollatzResearch.WordTrace tailWord_1480866 prefixEnd_1480866 337953796844937039406501 := by
  unfold tailWord_1480866
  simp only [CollatzResearch.WordTrace]
  refine ⟨13502905063270717155643613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36007746835388579081716301 13502905063270717155643613)
  ·
    refine ⟨5063589398726518933366355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13502905063270717155643613 5063589398726518933366355)
    ·
      refine ⟨7595384098089778400049533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5063589398726518933366355 7595384098089778400049533)
      ·
        refine ⟨2848269036783666900018575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7595384098089778400049533 2848269036783666900018575)
        ·
          refine ⟨4272403555175500350027863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2848269036783666900018575 4272403555175500350027863)
          ·
            refine ⟨6408605332763250525041795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4272403555175500350027863 6408605332763250525041795)
            ·
              refine ⟨9612907999144875787562693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6408605332763250525041795 9612907999144875787562693)
              ·
                refine ⟨1802420249839664210168005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9612907999144875787562693 1802420249839664210168005)
                ·
                  refine ⟨337953796844937039406501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1802420249839664210168005 337953796844937039406501)
                  ·
                    rfl

theorem cell21_1480866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 4, 4].length) (baseStart_1480866 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1480866 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1480866 prefixEnd_1480866 := by exact prefixLift 1480866
  have htrace : WordTrace (prefixWord ++ tailWord_1480866) baseStart_1480866 baseEnd_1480866 := by
    simpa [prefixWord, tailWord_1480866, baseEnd_1480866] using wordTrace_append hprefix tailTrace_1480866
  have hstable : (prefixWord ++ tailWord_1480866).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480866).length < 2 ^ (prefixWord ++ tailWord_1480866).sum := by decide
  have hdescent : baseEnd_1480866 < baseStart_1480866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480911 : List Nat := [1, 1, 2, 1, 1, 3, 6, 3, 3]
def baseStart_1480911 : Nat := 118140960795 + 1480911 * 2 ^ 59
def prefixEnd_1480911 : Nat := 4983230072969 + 3 ^ 40 * 1480911 * 2
def baseEnd_1480911 : Nat := 337964066458026961156409

theorem tailTrace_1480911 : CollatzResearch.WordTrace tailWord_1480911 prefixEnd_1480911 337964066458026961156409 := by
  unfold tailWord_1480911
  simp only [CollatzResearch.WordTrace]
  refine ⟨54013261537919841307962587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36008841025279894205308391 54013261537919841307962587)
  ·
    refine ⟨81019892306879761961943881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54013261537919841307962587 81019892306879761961943881)
    ·
      refine ⟨60764919230159821471457911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81019892306879761961943881 60764919230159821471457911)
      ·
        refine ⟨91147378845239732207186867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60764919230159821471457911 91147378845239732207186867)
        ·
          refine ⟨136721068267859598310780301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91147378845239732207186867 136721068267859598310780301)
          ·
            refine ⟨51270400600447349366542613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 136721068267859598310780301 51270400600447349366542613)
            ·
              refine ⟨2403300028145969501556685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 51270400600447349366542613 2403300028145969501556685)
              ·
                refine ⟨901237510554738563083757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2403300028145969501556685 901237510554738563083757)
                ·
                  refine ⟨337964066458026961156409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 901237510554738563083757 337964066458026961156409)
                  ·
                    rfl

theorem cell21_1480911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6, 3, 3].length) (baseStart_1480911 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1480911 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1480911 prefixEnd_1480911 := by exact prefixLift 1480911
  have htrace : WordTrace (prefixWord ++ tailWord_1480911) baseStart_1480911 baseEnd_1480911 := by
    simpa [prefixWord, tailWord_1480911, baseEnd_1480911] using wordTrace_append hprefix tailTrace_1480911
  have hstable : (prefixWord ++ tailWord_1480911).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480911).length < 2 ^ (prefixWord ++ tailWord_1480911).sum := by decide
  have hdescent : baseEnd_1480911 < baseStart_1480911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480953 : List Nat := [1, 2, 1, 3, 1, 1, 2, 3, 7]
def baseStart_1480953 : Nat := 118140960795 + 1480953 * 2 ^ 59
def prefixEnd_1480953 : Nat := 4983230072969 + 3 ^ 40 * 1480953 * 2
def baseEnd_1480953 : Nat := 337973651430244221456323

theorem tailTrace_1480953 : CollatzResearch.WordTrace tailWord_1480953 prefixEnd_1480953 337973651430244221456323 := by
  unfold tailWord_1480953
  simp only [CollatzResearch.WordTrace]
  refine ⟨54014793403767682480991513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36009862269178454987327675 54014793403767682480991513)
  ·
    refine ⟨40511095052825761860743635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54014793403767682480991513 40511095052825761860743635)
    ·
      refine ⟨60766642579238642791115453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40511095052825761860743635 60766642579238642791115453)
      ·
        refine ⟨22787490967214491046668295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60766642579238642791115453 22787490967214491046668295)
        ·
          refine ⟨34181236450821736570002443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22787490967214491046668295 34181236450821736570002443)
          ·
            refine ⟨51271854676232604855003665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34181236450821736570002443 51271854676232604855003665)
            ·
              refine ⟨38453891007174453641252749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51271854676232604855003665 38453891007174453641252749)
              ·
                refine ⟨14420209127690420115469781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38453891007174453641252749 14420209127690420115469781)
                ·
                  refine ⟨337973651430244221456323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14420209127690420115469781 337973651430244221456323)
                  ·
                    rfl

theorem cell21_1480953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 3, 7].length) (baseStart_1480953 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1480953 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1480953 prefixEnd_1480953 := by exact prefixLift 1480953
  have htrace : WordTrace (prefixWord ++ tailWord_1480953) baseStart_1480953 baseEnd_1480953 := by
    simpa [prefixWord, tailWord_1480953, baseEnd_1480953] using wordTrace_append hprefix tailTrace_1480953
  have hstable : (prefixWord ++ tailWord_1480953).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480953).length < 2 ^ (prefixWord ++ tailWord_1480953).sum := by decide
  have hdescent : baseEnd_1480953 < baseStart_1480953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480956 : List Nat := [2, 2, 2, 1, 4, 1, 4, 5]
def baseStart_1480956 : Nat := 118140960795 + 1480956 * 2 ^ 59
def prefixEnd_1480956 : Nat := 4983230072969 + 3 ^ 40 * 1480956 * 2
def baseEnd_1480956 : Nat := 112658112023705627635439

theorem tailTrace_1480956 : CollatzResearch.WordTrace tailWord_1480956 prefixEnd_1480956 112658112023705627635439 := by
  unfold tailWord_1480956
  simp only [CollatzResearch.WordTrace]
  refine ⟨27007451411378406996675361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36009935215171209328900481 27007451411378406996675361)
  ·
    refine ⟨20255588558533805247506521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27007451411378406996675361 20255588558533805247506521)
    ·
      refine ⟨15191691418900353935629891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20255588558533805247506521 15191691418900353935629891)
      ·
        refine ⟨22787537128350530903444837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15191691418900353935629891 22787537128350530903444837)
        ·
          refine ⟨4272663211565724544395907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22787537128350530903444837 4272663211565724544395907)
          ·
            refine ⟨6408994817348586816593861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4272663211565724544395907 6408994817348586816593861)
            ·
              refine ⟨1201686528252860028111349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6408994817348586816593861 1201686528252860028111349)
              ·
                refine ⟨112658112023705627635439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1201686528252860028111349 112658112023705627635439)
                ·
                  rfl

theorem cell21_1480956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 4, 5].length) (baseStart_1480956 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1480956 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1480956 prefixEnd_1480956 := by exact prefixLift 1480956
  have htrace : WordTrace (prefixWord ++ tailWord_1480956) baseStart_1480956 baseEnd_1480956 := by
    simpa [prefixWord, tailWord_1480956, baseEnd_1480956] using wordTrace_append hprefix tailTrace_1480956
  have hstable : (prefixWord ++ tailWord_1480956).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480956).length < 2 ^ (prefixWord ++ tailWord_1480956).sum := by decide
  have hdescent : baseEnd_1480956 < baseStart_1480956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1480984 : List Nat := [2, 1, 2, 3, 1, 2, 1, 3, 6]
def baseStart_1480984 : Nat := 118140960795 + 1480984 * 2 ^ 59
def prefixEnd_1480984 : Nat := 4983230072969 + 3 ^ 40 * 1480984 * 2
def baseEnd_1480984 : Nat := 337980726052595056439593

theorem tailTrace_1480984 : CollatzResearch.WordTrace tailWord_1480984 prefixEnd_1480984 337980726052595056439593 := by
  unfold tailWord_1480984
  simp only [CollatzResearch.WordTrace]
  refine ⟨27007962033327687387685003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36010616044436916516913337 27007962033327687387685003)
  ·
    refine ⟨40511943049991531081527505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27007962033327687387685003 40511943049991531081527505)
    ·
      refine ⟨30383957287493648311145629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40511943049991531081527505 30383957287493648311145629)
      ·
        refine ⟨11393983982810118116679611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30383957287493648311145629 11393983982810118116679611)
        ·
          refine ⟨17090975974215177175019417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11393983982810118116679611 17090975974215177175019417)
          ·
            refine ⟨12818231980661382881264563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17090975974215177175019417 12818231980661382881264563)
            ·
              refine ⟨19227347970992074321896845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12818231980661382881264563 19227347970992074321896845)
              ·
                refine ⟨7210255489122027870711317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19227347970992074321896845 7210255489122027870711317)
                ·
                  refine ⟨337980726052595056439593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7210255489122027870711317 337980726052595056439593)
                  ·
                    rfl

theorem cell21_1480984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 3, 6].length) (baseStart_1480984 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1480984 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1480984 prefixEnd_1480984 := by exact prefixLift 1480984
  have htrace : WordTrace (prefixWord ++ tailWord_1480984) baseStart_1480984 baseEnd_1480984 := by
    simpa [prefixWord, tailWord_1480984, baseEnd_1480984] using wordTrace_append hprefix tailTrace_1480984
  have hstable : (prefixWord ++ tailWord_1480984).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1480984).length < 2 ^ (prefixWord ++ tailWord_1480984).sum := by decide
  have hdescent : baseEnd_1480984 < baseStart_1480984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1480984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481091 : List Nat := [1, 1, 1, 3, 6, 1, 8]
def baseStart_1481091 : Nat := 118140960795 + 1481091 * 2 ^ 59
def prefixEnd_1481091 : Nat := 4983230072969 + 3 ^ 40 * 1481091 * 2
def baseEnd_1481091 : Nat := 37556127212265183128449

theorem tailTrace_1481091 : CollatzResearch.WordTrace tailWord_1481091 prefixEnd_1481091 37556127212265183128449 := by
  unfold tailWord_1481091
  simp only [CollatzResearch.WordTrace]
  refine ⟨54019826677267732049515127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36013217784845154699676751 54019826677267732049515127)
  ·
    refine ⟨81029740015901598074272691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54019826677267732049515127 81029740015901598074272691)
    ·
      refine ⟨121544610023852397111409037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81029740015901598074272691 121544610023852397111409037)
      ·
        refine ⟨45579228758944648916778389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121544610023852397111409037 45579228758944648916778389)
        ·
          refine ⟨2136526348075530417973987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 45579228758944648916778389 2136526348075530417973987)
          ·
            refine ⟨3204789522113295626960981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2136526348075530417973987 3204789522113295626960981)
            ·
              refine ⟨37556127212265183128449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3204789522113295626960981 37556127212265183128449)
              ·
                rfl

theorem cell21_1481091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 8].length) (baseStart_1481091 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1481091 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1481091 prefixEnd_1481091 := by exact prefixLift 1481091
  have htrace : WordTrace (prefixWord ++ tailWord_1481091) baseStart_1481091 baseEnd_1481091 := by
    simpa [prefixWord, tailWord_1481091, baseEnd_1481091] using wordTrace_append hprefix tailTrace_1481091
  have hstable : (prefixWord ++ tailWord_1481091).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481091).length < 2 ^ (prefixWord ++ tailWord_1481091).sum := by decide
  have hdescent : baseEnd_1481091 < baseStart_1481091 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481122 : List Nat := [3, 3, 1, 2, 1, 1, 1, 4, 5]
def baseStart_1481122 : Nat := 118140960795 + 1481122 * 2 ^ 59
def prefixEnd_1481122 : Nat := 4983230072969 + 3 ^ 40 * 1481122 * 2
def baseEnd_1481122 : Nat := 338012219532737483139311

theorem tailTrace_1481122 : CollatzResearch.WordTrace tailWord_1481122 prefixEnd_1481122 338012219532737483139311 := by
  unfold tailWord_1481122
  simp only [CollatzResearch.WordTrace]
  refine ⟨13505239335038856085973405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36013971560103616229262413 13505239335038856085973405)
  ·
    refine ⟨5064464750639571032240027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13505239335038856085973405 5064464750639571032240027)
    ·
      refine ⟨7596697125959356548360041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5064464750639571032240027 7596697125959356548360041)
      ·
        refine ⟨5697522844469517411270031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7596697125959356548360041 5697522844469517411270031)
        ·
          refine ⟨8546284266704276116905047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5697522844469517411270031 8546284266704276116905047)
          ·
            refine ⟨12819426400056414175357571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8546284266704276116905047 12819426400056414175357571)
            ·
              refine ⟨19229139600084621263036357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12819426400056414175357571 19229139600084621263036357)
              ·
                refine ⟨3605463675015866486819317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19229139600084621263036357 3605463675015866486819317)
                ·
                  refine ⟨338012219532737483139311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3605463675015866486819317 338012219532737483139311)
                  ·
                    rfl

theorem cell21_1481122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_1481122 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1481122 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1481122 prefixEnd_1481122 := by exact prefixLift 1481122
  have htrace : WordTrace (prefixWord ++ tailWord_1481122) baseStart_1481122 baseEnd_1481122 := by
    simpa [prefixWord, tailWord_1481122, baseEnd_1481122] using wordTrace_append hprefix tailTrace_1481122
  have hstable : (prefixWord ++ tailWord_1481122).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481122).length < 2 ^ (prefixWord ++ tailWord_1481122).sum := by decide
  have hdescent : baseEnd_1481122 < baseStart_1481122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481156 : List Nat := [2, 3, 3, 2, 2, 2, 1, 1, 5]
def baseStart_1481156 : Nat := 118140960795 + 1481156 * 2 ^ 59
def prefixEnd_1481156 : Nat := 4983230072969 + 3 ^ 40 * 1481156 * 2
def baseEnd_1481156 : Nat := 338019978795960979572575

theorem tailTrace_1481156 : CollatzResearch.WordTrace tailWord_1481156 prefixEnd_1481156 338019978795960979572575 := by
  unfold tailWord_1481156
  simp only [CollatzResearch.WordTrace]
  refine ⟨27011098711016124075315661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36014798281354832100420881 27011098711016124075315661)
  ·
    refine ⟨10129162016631046528243373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27011098711016124075315661 10129162016631046528243373)
    ·
      refine ⟨3798435756236642448091265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10129162016631046528243373 3798435756236642448091265)
      ·
        refine ⟨2848826817177481836068449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3798435756236642448091265 2848826817177481836068449)
        ·
          refine ⟨2136620112883111377051337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2848826817177481836068449 2136620112883111377051337)
          ·
            refine ⟨1602465084662333532788503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2136620112883111377051337 1602465084662333532788503)
            ·
              refine ⟨2403697626993500299182755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1602465084662333532788503 2403697626993500299182755)
              ·
                refine ⟨3605546440490250448774133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2403697626993500299182755 3605546440490250448774133)
                ·
                  refine ⟨338019978795960979572575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3605546440490250448774133 338019978795960979572575)
                  ·
                    rfl

theorem cell21_1481156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 1, 1, 5].length) (baseStart_1481156 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1481156 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1481156 prefixEnd_1481156 := by exact prefixLift 1481156
  have htrace : WordTrace (prefixWord ++ tailWord_1481156) baseStart_1481156 baseEnd_1481156 := by
    simpa [prefixWord, tailWord_1481156, baseEnd_1481156] using wordTrace_append hprefix tailTrace_1481156
  have hstable : (prefixWord ++ tailWord_1481156).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481156).length < 2 ^ (prefixWord ++ tailWord_1481156).sum := by decide
  have hdescent : baseEnd_1481156 < baseStart_1481156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481218 : List Nat := [3, 4, 1, 2, 3, 1, 1, 6]
def baseStart_1481218 : Nat := 118140960795 + 1481218 * 2 ^ 59
def prefixEnd_1481218 : Nat := 4983230072969 + 3 ^ 40 * 1481218 * 2
def baseEnd_1481218 : Nat := 112678042680220883179705

theorem tailTrace_1481218 : CollatzResearch.WordTrace tailWord_1481218 prefixEnd_1481218 112678042680220883179705 := by
  unfold tailWord_1481218
  simp only [CollatzResearch.WordTrace]
  refine ⟨13506114686951908184847077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36016305831871755159592205 13506114686951908184847077)
  ·
    refine ⟨2532396503803482784658827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13506114686951908184847077 2532396503803482784658827)
    ·
      refine ⟨3798594755705224176988241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2532396503803482784658827 3798594755705224176988241)
      ·
        refine ⟨2848946066778918132741181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3798594755705224176988241 2848946066778918132741181)
        ·
          refine ⟨1068354775042094299777943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2848946066778918132741181 1068354775042094299777943)
          ·
            refine ⟨1602532162563141449666915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1068354775042094299777943 1602532162563141449666915)
            ·
              refine ⟨2403798243844712174500373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1602532162563141449666915 2403798243844712174500373)
              ·
                refine ⟨112678042680220883179705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2403798243844712174500373 112678042680220883179705)
                ·
                  rfl

theorem cell21_1481218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 1, 6].length) (baseStart_1481218 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1481218 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1481218 prefixEnd_1481218 := by exact prefixLift 1481218
  have htrace : WordTrace (prefixWord ++ tailWord_1481218) baseStart_1481218 baseEnd_1481218 := by
    simpa [prefixWord, tailWord_1481218, baseEnd_1481218] using wordTrace_append hprefix tailTrace_1481218
  have hstable : (prefixWord ++ tailWord_1481218).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481218).length < 2 ^ (prefixWord ++ tailWord_1481218).sum := by decide
  have hdescent : baseEnd_1481218 < baseStart_1481218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481274 : List Nat := [3, 1, 1, 1, 3, 4, 2, 1, 5]
def baseStart_1481274 : Nat := 118140960795 + 1481274 * 2 ^ 59
def prefixEnd_1481274 : Nat := 4983230072969 + 3 ^ 40 * 1481274 * 2
def baseEnd_1481274 : Nat := 338046908003618996605667

theorem tailTrace_1481274 : CollatzResearch.WordTrace tailWord_1481274 prefixEnd_1481274 338046908003618996605667 := by
  unfold tailWord_1481274
  simp only [CollatzResearch.WordTrace]
  refine ⟨13506625308901188575856719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36017667490403169535617917 13506625308901188575856719)
  ·
    refine ⟨20259937963351782863785079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13506625308901188575856719 20259937963351782863785079)
    ·
      refine ⟨30389906945027674295677619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20259937963351782863785079 30389906945027674295677619)
      ·
        refine ⟨45584860417541511443516429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30389906945027674295677619 45584860417541511443516429)
        ·
          refine ⟨17094322656578066791318661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45584860417541511443516429 17094322656578066791318661)
          ·
            refine ⟨3205185498108387523372249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17094322656578066791318661 3205185498108387523372249)
            ·
              refine ⟨2403889123581290642529187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3205185498108387523372249 2403889123581290642529187)
              ·
                refine ⟨3605833685371935963793781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2403889123581290642529187 3605833685371935963793781)
                ·
                  refine ⟨338046908003618996605667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3605833685371935963793781 338046908003618996605667)
                  ·
                    rfl

theorem cell21_1481274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2, 1, 5].length) (baseStart_1481274 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1481274 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1481274 prefixEnd_1481274 := by exact prefixLift 1481274
  have htrace : WordTrace (prefixWord ++ tailWord_1481274) baseStart_1481274 baseEnd_1481274 := by
    simpa [prefixWord, tailWord_1481274, baseEnd_1481274] using wordTrace_append hprefix tailTrace_1481274
  have hstable : (prefixWord ++ tailWord_1481274).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481274).length < 2 ^ (prefixWord ++ tailWord_1481274).sum := by decide
  have hdescent : baseEnd_1481274 < baseStart_1481274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481288 : List Nat := [2, 1, 3, 1, 1, 1, 1, 7, 4]
def baseStart_1481288 : Nat := 118140960795 + 1481288 * 2 ^ 59
def prefixEnd_1481288 : Nat := 4983230072969 + 3 ^ 40 * 1481288 * 2
def baseEnd_1481288 : Nat := 338050102994358083372305

theorem tailTrace_1481288 : CollatzResearch.WordTrace tailWord_1481288 prefixEnd_1481288 338050102994358083372305 := by
  unfold tailWord_1481288
  simp only [CollatzResearch.WordTrace]
  refine ⟨27013505928777017347218259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36018007905036023129624345 27013505928777017347218259)
  ·
    refine ⟨40520258893165526020827389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27013505928777017347218259 40520258893165526020827389)
    ·
      refine ⟨15195097084937072257810271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40520258893165526020827389 15195097084937072257810271)
      ·
        refine ⟨22792645627405608386715407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15195097084937072257810271 22792645627405608386715407)
        ·
          refine ⟨34188968441108412580073111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22792645627405608386715407 34188968441108412580073111)
          ·
            refine ⟨51283452661662618870109667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34188968441108412580073111 51283452661662618870109667)
            ·
              refine ⟨76925178992493928305164501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51283452661662618870109667 76925178992493928305164501)
              ·
                refine ⟨1802933882636576444652293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 76925178992493928305164501 1802933882636576444652293)
                ·
                  refine ⟨338050102994358083372305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1802933882636576444652293 338050102994358083372305)
                  ·
                    rfl

theorem cell21_1481288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 7, 4].length) (baseStart_1481288 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1481288 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1481288 prefixEnd_1481288 := by exact prefixLift 1481288
  have htrace : WordTrace (prefixWord ++ tailWord_1481288) baseStart_1481288 baseEnd_1481288 := by
    simpa [prefixWord, tailWord_1481288, baseEnd_1481288] using wordTrace_append hprefix tailTrace_1481288
  have hstable : (prefixWord ++ tailWord_1481288).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481288).length < 2 ^ (prefixWord ++ tailWord_1481288).sum := by decide
  have hdescent : baseEnd_1481288 < baseStart_1481288 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481378 : List Nat := [3, 3, 1, 14]
def baseStart_1481378 : Nat := 118140960795 + 1481378 * 2 ^ 59
def prefixEnd_1481378 : Nat := 4983230072969 + 3 ^ 40 * 1481378 * 2
def baseEnd_1481378 : Nat := 1391237210784106694947

theorem tailTrace_1481378 : CollatzResearch.WordTrace tailWord_1481378 prefixEnd_1481378 1391237210784106694947 := by
  unfold tailWord_1481378
  simp only [CollatzResearch.WordTrace]
  refine ⟨13507573606806995016303197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36020196284818653376808525 13507573606806995016303197)
  ·
    refine ⟨5065340102552623131113699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13507573606806995016303197 5065340102552623131113699)
    ·
      refine ⟨7598010153828934696670549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5065340102552623131113699 7598010153828934696670549)
      ·
        refine ⟨1391237210784106694947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 14 7598010153828934696670549 1391237210784106694947)
        ·
          rfl

theorem cell21_1481378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 14].length) (baseStart_1481378 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1481378 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1481378 prefixEnd_1481378 := by exact prefixLift 1481378
  have htrace : WordTrace (prefixWord ++ tailWord_1481378) baseStart_1481378 baseEnd_1481378 := by
    simpa [prefixWord, tailWord_1481378, baseEnd_1481378] using wordTrace_append hprefix tailTrace_1481378
  have hstable : (prefixWord ++ tailWord_1481378).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481378).length < 2 ^ (prefixWord ++ tailWord_1481378).sum := by decide
  have hdescent : baseEnd_1481378 < baseStart_1481378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481395 : List Nat := [1, 1, 1, 2, 3, 6, 1, 6]
def baseStart_1481395 : Nat := 118140960795 + 1481395 * 2 ^ 59
def prefixEnd_1481395 : Nat := 4983230072969 + 3 ^ 40 * 1481395 * 2
def baseEnd_1481395 : Nat := 112691507284049891696251

theorem tailTrace_1481395 : CollatzResearch.WordTrace tailWord_1481395 prefixEnd_1481395 112691507284049891696251 := by
  unfold tailWord_1481395
  simp only [CollatzResearch.WordTrace]
  refine ⟨54030914468166391968581639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36020609645444261312387759 54030914468166391968581639)
  ·
    refine ⟨81046371702249587952872459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54030914468166391968581639 81046371702249587952872459)
    ·
      refine ⟨121569557553374381929308689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81046371702249587952872459 121569557553374381929308689)
      ·
        refine ⟨91177168165030786446981517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121569557553374381929308689 91177168165030786446981517)
        ·
          refine ⟨34191438061886544917618069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91177168165030786446981517 34191438061886544917618069)
          ·
            refine ⟨1602723659150931793013347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 34191438061886544917618069 1602723659150931793013347)
            ·
              refine ⟨2404085488726397689520021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1602723659150931793013347 2404085488726397689520021)
              ·
                refine ⟨112691507284049891696251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2404085488726397689520021 112691507284049891696251)
                ·
                  rfl

theorem cell21_1481395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 1, 6].length) (baseStart_1481395 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1481395 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1481395 prefixEnd_1481395 := by exact prefixLift 1481395
  have htrace : WordTrace (prefixWord ++ tailWord_1481395) baseStart_1481395 baseEnd_1481395 := by
    simpa [prefixWord, tailWord_1481395, baseEnd_1481395] using wordTrace_append hprefix tailTrace_1481395
  have hstable : (prefixWord ++ tailWord_1481395).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481395).length < 2 ^ (prefixWord ++ tailWord_1481395).sum := by decide
  have hdescent : baseEnd_1481395 < baseStart_1481395 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481412 : List Nat := [2, 3, 3, 1, 1, 3, 3, 5]
def baseStart_1481412 : Nat := 118140960795 + 1481412 * 2 ^ 59
def prefixEnd_1481412 : Nat := 4983230072969 + 3 ^ 40 * 1481412 * 2
def baseEnd_1481412 : Nat := 112692800494587141101795

theorem tailTrace_1481412 : CollatzResearch.WordTrace tailWord_1481412 prefixEnd_1481412 112692800494587141101795 := by
  unfold tailWord_1481412
  simp only [CollatzResearch.WordTrace]
  refine ⟨27015767254552401935975245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36021023006069869247966993 27015767254552401935975245)
  ·
    refine ⟨10130912720457150725990717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27015767254552401935975245 10130912720457150725990717)
    ·
      refine ⟨3799092270171431522246519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10130912720457150725990717 3799092270171431522246519)
      ·
        refine ⟨5698638405257147283369779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3799092270171431522246519 5698638405257147283369779)
        ·
          refine ⟨8547957607885720925054669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5698638405257147283369779 8547957607885720925054669)
          ·
            refine ⟨3205484102957145346895501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8547957607885720925054669 3205484102957145346895501)
            ·
              refine ⟨1202056538608929505085813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3205484102957145346895501 1202056538608929505085813)
              ·
                refine ⟨112692800494587141101795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1202056538608929505085813 112692800494587141101795)
                ·
                  rfl

theorem cell21_1481412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 3, 5].length) (baseStart_1481412 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1481412 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1481412 prefixEnd_1481412 := by exact prefixLift 1481412
  have htrace : WordTrace (prefixWord ++ tailWord_1481412) baseStart_1481412 baseEnd_1481412 := by
    simpa [prefixWord, tailWord_1481412, baseEnd_1481412] using wordTrace_append hprefix tailTrace_1481412
  have hstable : (prefixWord ++ tailWord_1481412).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481412).length < 2 ^ (prefixWord ++ tailWord_1481412).sum := by decide
  have hdescent : baseEnd_1481412 < baseStart_1481412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481443 : List Nat := [1, 1, 1, 7, 1, 1, 2, 4, 3]
def baseStart_1481443 : Nat := 118140960795 + 1481443 * 2 ^ 59
def prefixEnd_1481443 : Nat := 4983230072969 + 3 ^ 40 * 1481443 * 2
def baseEnd_1481443 : Nat := 338085476106112258288655

theorem tailTrace_1481443 : CollatzResearch.WordTrace tailWord_1481443 prefixEnd_1481443 338085476106112258288655 := by
  unfold tailWord_1481443
  simp only [CollatzResearch.WordTrace]
  refine ⟨54032665171992496166328983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36021776781328330777552655 54032665171992496166328983)
  ·
    refine ⟨81048997757988744249493475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54032665171992496166328983 81048997757988744249493475)
    ·
      refine ⟨121573496636983116374240213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81048997757988744249493475 121573496636983116374240213)
      ·
        refine ⟨2849378827429291790021255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 121573496636983116374240213 2849378827429291790021255)
        ·
          refine ⟨4274068241143937685031883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2849378827429291790021255 4274068241143937685031883)
          ·
            refine ⟨6411102361715906527547825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4274068241143937685031883 6411102361715906527547825)
            ·
              refine ⟨4808326771286929895660869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6411102361715906527547825 4808326771286929895660869)
              ·
                refine ⟨901561269616299355436413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4808326771286929895660869 901561269616299355436413)
                ·
                  refine ⟨338085476106112258288655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 901561269616299355436413 338085476106112258288655)
                  ·
                    rfl

theorem cell21_1481443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 4, 3].length) (baseStart_1481443 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1481443 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1481443 prefixEnd_1481443 := by exact prefixLift 1481443
  have htrace : WordTrace (prefixWord ++ tailWord_1481443) baseStart_1481443 baseEnd_1481443 := by
    simpa [prefixWord, tailWord_1481443, baseEnd_1481443] using wordTrace_append hprefix tailTrace_1481443
  have hstable : (prefixWord ++ tailWord_1481443).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481443).length < 2 ^ (prefixWord ++ tailWord_1481443).sum := by decide
  have hdescent : baseEnd_1481443 < baseStart_1481443 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481457 : List Nat := [1, 2, 2, 2, 2, 2, 5, 1, 4]
def baseStart_1481457 : Nat := 118140960795 + 1481457 * 2 ^ 59
def prefixEnd_1481457 : Nat := 4983230072969 + 3 ^ 40 * 1481457 * 2
def baseEnd_1481457 : Nat := 338088671096851345055293

theorem tailTrace_1481457 : CollatzResearch.WordTrace tailWord_1481457 prefixEnd_1481457 338088671096851345055293 := by
  unfold tailWord_1481457
  simp only [CollatzResearch.WordTrace]
  refine ⟨54033175793941776557338625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36022117195961184371559083 54033175793941776557338625)
  ·
    refine ⟨40524881845456332418003969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54033175793941776557338625 40524881845456332418003969)
    ·
      refine ⟨30393661384092249313502977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40524881845456332418003969 30393661384092249313502977)
      ·
        refine ⟨22795246038069186985127233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30393661384092249313502977 22795246038069186985127233)
        ·
          refine ⟨17096434528551890238845425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22795246038069186985127233 17096434528551890238845425)
          ·
            refine ⟨12822325896413917679134069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17096434528551890238845425 12822325896413917679134069)
            ·
              refine ⟨1202093052788804782418819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12822325896413917679134069 1202093052788804782418819)
              ·
                refine ⟨1803139579183207173628229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1202093052788804782418819 1803139579183207173628229)
                ·
                  refine ⟨338088671096851345055293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1803139579183207173628229 338088671096851345055293)
                  ·
                    rfl

theorem cell21_1481457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 5, 1, 4].length) (baseStart_1481457 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1481457 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1481457 prefixEnd_1481457 := by exact prefixLift 1481457
  have htrace : WordTrace (prefixWord ++ tailWord_1481457) baseStart_1481457 baseEnd_1481457 := by
    simpa [prefixWord, tailWord_1481457, baseEnd_1481457] using wordTrace_append hprefix tailTrace_1481457
  have hstable : (prefixWord ++ tailWord_1481457).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481457).length < 2 ^ (prefixWord ++ tailWord_1481457).sum := by decide
  have hdescent : baseEnd_1481457 < baseStart_1481457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481516 : List Nat := [2, 2, 1, 1, 1, 4, 3, 3, 4]
def baseStart_1481516 : Nat := 118140960795 + 1481516 * 2 ^ 59
def prefixEnd_1481516 : Nat := 4983230072969 + 3 ^ 40 * 1481516 * 2
def baseEnd_1481516 : Nat := 338102135700680353571839

theorem tailTrace_1481516 : CollatzResearch.WordTrace tailWord_1481516 prefixEnd_1481516 338102135700680353571839 := by
  unfold tailWord_1481516
  simp only [CollatzResearch.WordTrace]
  refine ⟨27017663850364014816868201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36023551800485353089157601 27017663850364014816868201)
  ·
    refine ⟨20263247887773011112651151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27017663850364014816868201 20263247887773011112651151)
    ·
      refine ⟨30394871831659516668976727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20263247887773011112651151 30394871831659516668976727)
      ·
        refine ⟨45592307747489275003465091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30394871831659516668976727 45592307747489275003465091)
        ·
          refine ⟨68388461621233912505197637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45592307747489275003465091 68388461621233912505197637)
          ·
            refine ⟨12822836553981358594724557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68388461621233912505197637 12822836553981358594724557)
            ·
              refine ⟨4808563707743009473021709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12822836553981358594724557 4808563707743009473021709)
              ·
                refine ⟨1803211390403628552383141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4808563707743009473021709 1803211390403628552383141)
                ·
                  refine ⟨338102135700680353571839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1803211390403628552383141 338102135700680353571839)
                  ·
                    rfl

theorem cell21_1481516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 4].length) (baseStart_1481516 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1481516 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1481516 prefixEnd_1481516 := by exact prefixLift 1481516
  have htrace : WordTrace (prefixWord ++ tailWord_1481516) baseStart_1481516 baseEnd_1481516 := by
    simpa [prefixWord, tailWord_1481516, baseEnd_1481516] using wordTrace_append hprefix tailTrace_1481516
  have hstable : (prefixWord ++ tailWord_1481516).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481516).length < 2 ^ (prefixWord ++ tailWord_1481516).sum := by decide
  have hdescent : baseEnd_1481516 < baseStart_1481516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481553 : List Nat := [1, 2, 2, 1, 7, 1, 2, 2, 3]
def baseStart_1481553 : Nat := 118140960795 + 1481553 * 2 ^ 59
def prefixEnd_1481553 : Nat := 4983230072969 + 3 ^ 40 * 1481553 * 2
def baseEnd_1481553 : Nat := 338110579604776511455097

theorem tailTrace_1481553 : CollatzResearch.WordTrace tailWord_1481553 prefixEnd_1481553 338110579604776511455097 := by
  unfold tailWord_1481553
  simp only [CollatzResearch.WordTrace]
  refine ⟨54036677201593984952833313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36024451467729323301888875 54036677201593984952833313)
  ·
    refine ⟨40527507901195488714624985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54036677201593984952833313 40527507901195488714624985)
    ·
      refine ⟨30395630925896616535968739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40527507901195488714624985 30395630925896616535968739)
      ·
        refine ⟨45593446388844924803953109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30395630925896616535968739 45593446388844924803953109)
        ·
          refine ⟨1068596399738552925092651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 45593446388844924803953109 1068596399738552925092651)
          ·
            refine ⟨1602894599607829387638977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1068596399738552925092651 1602894599607829387638977)
            ·
              refine ⟨1202170949705872040729233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1602894599607829387638977 1202170949705872040729233)
              ·
                refine ⟨901628212279404030546925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1202170949705872040729233 901628212279404030546925)
                ·
                  refine ⟨338110579604776511455097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 901628212279404030546925 338110579604776511455097)
                  ·
                    rfl

theorem cell21_1481553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 2, 2, 3].length) (baseStart_1481553 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1481553 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1481553 prefixEnd_1481553 := by exact prefixLift 1481553
  have htrace : WordTrace (prefixWord ++ tailWord_1481553) baseStart_1481553 baseEnd_1481553 := by
    simpa [prefixWord, tailWord_1481553, baseEnd_1481553] using wordTrace_append hprefix tailTrace_1481553
  have hstable : (prefixWord ++ tailWord_1481553).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481553).length < 2 ^ (prefixWord ++ tailWord_1481553).sum := by decide
  have hdescent : baseEnd_1481553 < baseStart_1481553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481564 : List Nat := [2, 2, 4, 2, 1, 3, 1, 6]
def baseStart_1481564 : Nat := 118140960795 + 1481564 * 2 ^ 59
def prefixEnd_1481564 : Nat := 4983230072969 + 3 ^ 40 * 1481564 * 2
def baseEnd_1481564 : Nat := 112704363318214312257247

theorem tailTrace_1481564 : CollatzResearch.WordTrace tailWord_1481564 prefixEnd_1481564 112704363318214312257247 := by
  unfold tailWord_1481564
  simp only [CollatzResearch.WordTrace]
  refine ⟨27018539202277066915741873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36024718936369422554322497 27018539202277066915741873)
  ·
    refine ⟨20263904401707800186806405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27018539202277066915741873 20263904401707800186806405)
    ·
      refine ⟨3799482075320212535026201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20263904401707800186806405 3799482075320212535026201)
      ·
        refine ⟨2849611556490159401269651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3799482075320212535026201 2849611556490159401269651)
        ·
          refine ⟨4274417334735239101904477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2849611556490159401269651 4274417334735239101904477)
          ·
            refine ⟨1602906500525714663214179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4274417334735239101904477 1602906500525714663214179)
            ·
              refine ⟨2404359750788571994821269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1602906500525714663214179 2404359750788571994821269)
              ·
                refine ⟨112704363318214312257247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2404359750788571994821269 112704363318214312257247)
                ·
                  rfl

theorem cell21_1481564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 1, 6].length) (baseStart_1481564 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1481564 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1481564 prefixEnd_1481564 := by exact prefixLift 1481564
  have htrace : WordTrace (prefixWord ++ tailWord_1481564) baseStart_1481564 baseEnd_1481564 := by
    simpa [prefixWord, tailWord_1481564, baseEnd_1481564] using wordTrace_append hprefix tailTrace_1481564
  have hstable : (prefixWord ++ tailWord_1481564).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481564).length < 2 ^ (prefixWord ++ tailWord_1481564).sum := by decide
  have hdescent : baseEnd_1481564 < baseStart_1481564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481609 : List Nat := [1, 2, 1, 1, 5, 4, 1, 2, 4]
def baseStart_1481609 : Nat := 118140960795 + 1481609 * 2 ^ 59
def prefixEnd_1481609 : Nat := 4983230072969 + 3 ^ 40 * 1481609 * 2
def baseEnd_1481609 : Nat := 338123359567732858521649

theorem tailTrace_1481609 : CollatzResearch.WordTrace tailWord_1481609 prefixEnd_1481609 338123359567732858521649 := by
  unfold tailWord_1481609
  simp only [CollatzResearch.WordTrace]
  refine ⟨54038719689391106516871881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36025813126260737677914587 54038719689391106516871881)
  ·
    refine ⟨40529039767043329887653911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54038719689391106516871881 40529039767043329887653911)
    ·
      refine ⟨60793559650564994831480867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40529039767043329887653911 60793559650564994831480867)
      ·
        refine ⟨91190339475847492247221301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60793559650564994831480867 91190339475847492247221301)
        ·
          refine ⟨8549094325860702398176997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 91190339475847492247221301 8549094325860702398176997)
          ·
            refine ⟨1602955186098881699658187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8549094325860702398176997 1602955186098881699658187)
            ·
              refine ⟨2404432779148322549487281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1602955186098881699658187 2404432779148322549487281)
              ·
                refine ⟨1803324584361241912115461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2404432779148322549487281 1803324584361241912115461)
                ·
                  refine ⟨338123359567732858521649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1803324584361241912115461 338123359567732858521649)
                  ·
                    rfl

theorem cell21_1481609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 1, 2, 4].length) (baseStart_1481609 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1481609 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1481609 prefixEnd_1481609 := by exact prefixLift 1481609
  have htrace : WordTrace (prefixWord ++ tailWord_1481609) baseStart_1481609 baseEnd_1481609 := by
    simpa [prefixWord, tailWord_1481609, baseEnd_1481609] using wordTrace_append hprefix tailTrace_1481609
  have hstable : (prefixWord ++ tailWord_1481609).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481609).length < 2 ^ (prefixWord ++ tailWord_1481609).sum := by decide
  have hdescent : baseEnd_1481609 < baseStart_1481609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481626 : List Nat := [3, 1, 1, 4, 3, 1, 3, 1, 4]
def baseStart_1481626 : Nat := 118140960795 + 1481626 * 2 ^ 59
def prefixEnd_1481626 : Nat := 4983230072969 + 3 ^ 40 * 1481626 * 2
def baseEnd_1481626 : Nat := 338127239199344606738281

theorem tailTrace_1481626 : CollatzResearch.WordTrace tailWord_1481626 prefixEnd_1481626 338127239199344606738281 := by
  unfold tailWord_1481626
  simp only [CollatzResearch.WordTrace]
  refine ⟨13509834932582379605060183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36026226486886345613493821 13509834932582379605060183)
  ·
    refine ⟨20264752398873569407590275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13509834932582379605060183 20264752398873569407590275)
    ·
      refine ⟨30397128598310354111385413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20264752398873569407590275 30397128598310354111385413)
      ·
        refine ⟨5699461612183191395884765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30397128598310354111385413 5699461612183191395884765)
        ·
          refine ⟨2137298104568696773456787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5699461612183191395884765 2137298104568696773456787)
          ·
            refine ⟨3205947156853045160185181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2137298104568696773456787 3205947156853045160185181)
            ·
              refine ⟨1202230183819891935069443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3205947156853045160185181 1202230183819891935069443)
              ·
                refine ⟨1803345275729837902604165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1202230183819891935069443 1803345275729837902604165)
                ·
                  refine ⟨338127239199344606738281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1803345275729837902604165 338127239199344606738281)
                  ·
                    rfl

theorem cell21_1481626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 3, 1, 4].length) (baseStart_1481626 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1481626 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1481626 prefixEnd_1481626 := by exact prefixLift 1481626
  have htrace : WordTrace (prefixWord ++ tailWord_1481626) baseStart_1481626 baseEnd_1481626 := by
    simpa [prefixWord, tailWord_1481626, baseEnd_1481626] using wordTrace_append hprefix tailTrace_1481626
  have hstable : (prefixWord ++ tailWord_1481626).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481626).length < 2 ^ (prefixWord ++ tailWord_1481626).sum := by decide
  have hdescent : baseEnd_1481626 < baseStart_1481626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481677 : List Nat := [1, 6, 3, 1, 1, 2, 2, 1, 4]
def baseStart_1481677 : Nat := 118140960795 + 1481677 * 2 ^ 59
def prefixEnd_1481677 : Nat := 4983230072969 + 3 ^ 40 * 1481677 * 2
def baseEnd_1481677 : Nat := 338138878094179851388177

theorem tailTrace_1481677 : CollatzResearch.WordTrace tailWord_1481677 prefixEnd_1481677 338138878094179851388177 := by
  unfold tailWord_1481677
  simp only [CollatzResearch.WordTrace]
  refine ⟨54041199853144754130347285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36027466568763169420231523 54041199853144754130347285)
  ·
    refine ⟨2533181243116160349860029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 54041199853144754130347285 2533181243116160349860029)
    ·
      refine ⟨949942966168560131197511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2533181243116160349860029 949942966168560131197511)
      ·
        refine ⟨1424914449252840196796267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 949942966168560131197511 1424914449252840196796267)
        ·
          refine ⟨2137371673879260295194401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1424914449252840196796267 2137371673879260295194401)
          ·
            refine ⟨1603028755409445221395801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2137371673879260295194401 1603028755409445221395801)
            ·
              refine ⟨1202271566557083916046851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1603028755409445221395801 1202271566557083916046851)
              ·
                refine ⟨1803407349835625874070277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1202271566557083916046851 1803407349835625874070277)
                ·
                  refine ⟨338138878094179851388177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1803407349835625874070277 338138878094179851388177)
                  ·
                    rfl

theorem cell21_1481677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 2, 1, 4].length) (baseStart_1481677 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1481677 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1481677 prefixEnd_1481677 := by exact prefixLift 1481677
  have htrace : WordTrace (prefixWord ++ tailWord_1481677) baseStart_1481677 baseEnd_1481677 := by
    simpa [prefixWord, tailWord_1481677, baseEnd_1481677] using wordTrace_append hprefix tailTrace_1481677
  have hstable : (prefixWord ++ tailWord_1481677).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481677).length < 2 ^ (prefixWord ++ tailWord_1481677).sum := by decide
  have hdescent : baseEnd_1481677 < baseStart_1481677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481685 : List Nat := [1, 3, 2, 3, 3, 1, 1, 3, 4]
def baseStart_1481685 : Nat := 118140960795 + 1481685 * 2 ^ 59
def prefixEnd_1481685 : Nat := 4983230072969 + 3 ^ 40 * 1481685 * 2
def baseEnd_1481685 : Nat := 338140703803173615254827

theorem tailTrace_1481685 : CollatzResearch.WordTrace tailWord_1481685 prefixEnd_1481685 338140703803173615254827 := by
  unfold tailWord_1481685
  simp only [CollatzResearch.WordTrace]
  refine ⟨54041491637115771496638509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36027661091410514331092339 54041491637115771496638509)
  ·
    refine ⟨20265559363918414311239441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54041491637115771496638509 20265559363918414311239441)
    ·
      refine ⟨15199169522938810733429581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20265559363918414311239441 15199169522938810733429581)
      ·
        refine ⟨5699688571102054025036093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15199169522938810733429581 5699688571102054025036093)
        ·
          refine ⟨2137383214163270259388535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5699688571102054025036093 2137383214163270259388535)
          ·
            refine ⟨3206074821244905389082803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2137383214163270259388535 3206074821244905389082803)
            ·
              refine ⟨4809112231867358083624205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3206074821244905389082803 4809112231867358083624205)
              ·
                refine ⟨1803417086950259281359077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4809112231867358083624205 1803417086950259281359077)
                ·
                  refine ⟨338140703803173615254827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1803417086950259281359077 338140703803173615254827)
                  ·
                    rfl

theorem cell21_1481685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 3, 4].length) (baseStart_1481685 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1481685 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1481685 prefixEnd_1481685 := by exact prefixLift 1481685
  have htrace : WordTrace (prefixWord ++ tailWord_1481685) baseStart_1481685 baseEnd_1481685 := by
    simpa [prefixWord, tailWord_1481685, baseEnd_1481685] using wordTrace_append hprefix tailTrace_1481685
  have hstable : (prefixWord ++ tailWord_1481685).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481685).length < 2 ^ (prefixWord ++ tailWord_1481685).sum := by decide
  have hdescent : baseEnd_1481685 < baseStart_1481685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481772 : List Nat := [2, 2, 1, 1, 1, 2, 3, 2, 7]
def baseStart_1481772 : Nat := 118140960795 + 1481772 * 2 ^ 59
def prefixEnd_1481772 : Nat := 4983230072969 + 3 ^ 40 * 1481772 * 2
def baseEnd_1481772 : Nat := 338160558388480797304649

theorem tailTrace_1481772 : CollatzResearch.WordTrace tailWord_1481772 prefixEnd_1481772 338160558388480797304649 := by
  unfold tailWord_1481772
  simp only [CollatzResearch.WordTrace]
  refine ⟨27022332393900292677527785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36029776525200390236703713 27022332393900292677527785)
  ·
    refine ⟨20266749295425219508145839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27022332393900292677527785 20266749295425219508145839)
    ·
      refine ⟨30400123943137829262218759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20266749295425219508145839 30400123943137829262218759)
      ·
        refine ⟨45600185914706743893328139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30400123943137829262218759 45600185914706743893328139)
        ·
          refine ⟨68400278872060115839992209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45600185914706743893328139 68400278872060115839992209)
          ·
            refine ⟨51300209154045086879994157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68400278872060115839992209 51300209154045086879994157)
            ·
              refine ⟨19237578432766907579997809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51300209154045086879994157 19237578432766907579997809)
              ·
                refine ⟨14428183824575180684998357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19237578432766907579997809 14428183824575180684998357)
                ·
                  refine ⟨338160558388480797304649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14428183824575180684998357 338160558388480797304649)
                  ·
                    rfl

theorem cell21_1481772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 7].length) (baseStart_1481772 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1481772 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1481772 prefixEnd_1481772 := by exact prefixLift 1481772
  have htrace : WordTrace (prefixWord ++ tailWord_1481772) baseStart_1481772 baseEnd_1481772 := by
    simpa [prefixWord, tailWord_1481772, baseEnd_1481772] using wordTrace_append hprefix tailTrace_1481772
  have hstable : (prefixWord ++ tailWord_1481772).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481772).length < 2 ^ (prefixWord ++ tailWord_1481772).sum := by decide
  have hdescent : baseEnd_1481772 < baseStart_1481772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481789 : List Nat := [1, 4, 1, 3, 1, 2, 1, 3, 5]
def baseStart_1481789 : Nat := 118140960795 + 1481789 * 2 ^ 59
def prefixEnd_1481789 : Nat := 4983230072969 + 3 ^ 40 * 1481789 * 2
def baseEnd_1481789 : Nat := 338164438020092545521281

theorem tailTrace_1481789 : CollatzResearch.WordTrace tailWord_1481789 prefixEnd_1481789 338164438020092545521281 := by
  unfold tailWord_1481789
  simp only [CollatzResearch.WordTrace]
  refine ⟨54045284828738997258424421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36030189885825998172282947 54045284828738997258424421)
  ·
    refine ⟨10133490905388561985954579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54045284828738997258424421 10133490905388561985954579)
    ·
      refine ⟨15200236358082842978931869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10133490905388561985954579 15200236358082842978931869)
      ·
        refine ⟨5700088634281066117099451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15200236358082842978931869 5700088634281066117099451)
        ·
          refine ⟨8550132951421599175649177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5700088634281066117099451 8550132951421599175649177)
          ·
            refine ⟨6412599713566199381736883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8550132951421599175649177 6412599713566199381736883)
            ·
              refine ⟨9618899570349299072605325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6412599713566199381736883 9618899570349299072605325)
              ·
                refine ⟨3607087338880987152226997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9618899570349299072605325 3607087338880987152226997)
                ·
                  refine ⟨338164438020092545521281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3607087338880987152226997 338164438020092545521281)
                  ·
                    rfl

theorem cell21_1481789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 3, 5].length) (baseStart_1481789 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1481789 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1481789 prefixEnd_1481789 := by exact prefixLift 1481789
  have htrace : WordTrace (prefixWord ++ tailWord_1481789) baseStart_1481789 baseEnd_1481789 := by
    simpa [prefixWord, tailWord_1481789, baseEnd_1481789] using wordTrace_append hprefix tailTrace_1481789
  have hstable : (prefixWord ++ tailWord_1481789).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481789).length < 2 ^ (prefixWord ++ tailWord_1481789).sum := by decide
  have hdescent : baseEnd_1481789 < baseStart_1481789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481834 : List Nat := [3, 1, 3, 2, 2, 1, 9]
def baseStart_1481834 : Nat := 118140960795 + 1481834 * 2 ^ 59
def prefixEnd_1481834 : Nat := 4983230072969 + 3 ^ 40 * 1481834 * 2
def baseEnd_1481834 : Nat := 37574967514798051919021

theorem tailTrace_1481834 : CollatzResearch.WordTrace tailWord_1481834 prefixEnd_1481834 37574967514798051919021 := by
  unfold tailWord_1481834
  simp only [CollatzResearch.WordTrace]
  refine ⟨13511731528393992485953139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36031284075717313295875037 13511731528393992485953139)
  ·
    refine ⟨20267597292590988728929709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13511731528393992485953139 20267597292590988728929709)
    ·
      refine ⟨7600348984721620773348641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20267597292590988728929709 7600348984721620773348641)
      ·
        refine ⟨5700261738541215580011481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7600348984721620773348641 5700261738541215580011481)
        ·
          refine ⟨4275196303905911685008611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5700261738541215580011481 4275196303905911685008611)
          ·
            refine ⟨6412794455858867527512917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4275196303905911685008611 6412794455858867527512917)
            ·
              refine ⟨37574967514798051919021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6412794455858867527512917 37574967514798051919021)
              ·
                rfl

theorem cell21_1481834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 9].length) (baseStart_1481834 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1481834 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1481834 prefixEnd_1481834 := by exact prefixLift 1481834
  have htrace : WordTrace (prefixWord ++ tailWord_1481834) baseStart_1481834 baseEnd_1481834 := by
    simpa [prefixWord, tailWord_1481834, baseEnd_1481834] using wordTrace_append hprefix tailTrace_1481834
  have hstable : (prefixWord ++ tailWord_1481834).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481834).length < 2 ^ (prefixWord ++ tailWord_1481834).sum := by decide
  have hdescent : baseEnd_1481834 < baseStart_1481834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481893 : List Nat := [1, 3, 1, 2, 1, 13]
def baseStart_1481893 : Nat := 118140960795 + 1481893 * 2 ^ 59
def prefixEnd_1481893 : Nat := 4983230072969 + 3 ^ 40 * 1481893 * 2
def baseEnd_1481893 : Nat := 12525487860630054658805

theorem tailTrace_1481893 : CollatzResearch.WordTrace tailWord_1481893 prefixEnd_1481893 12525487860630054658805 := by
  unfold tailWord_1481893
  simp only [CollatzResearch.WordTrace]
  refine ⟨54049078020362223020210333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36032718680241482013473555 54049078020362223020210333)
  ·
    refine ⟨20268404257635833632578875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54049078020362223020210333 20268404257635833632578875)
    ·
      refine ⟨30402606386453750448868313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20268404257635833632578875 30402606386453750448868313)
      ·
        refine ⟨22801954789840312836651235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30402606386453750448868313 22801954789840312836651235)
        ·
          refine ⟨34202932184760469254976853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22801954789840312836651235 34202932184760469254976853)
          ·
            refine ⟨12525487860630054658805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 34202932184760469254976853 12525487860630054658805)
            ·
              rfl

theorem cell21_1481893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 13].length) (baseStart_1481893 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1481893 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1481893 prefixEnd_1481893 := by exact prefixLift 1481893
  have htrace : WordTrace (prefixWord ++ tailWord_1481893) baseStart_1481893 baseEnd_1481893 := by
    simpa [prefixWord, tailWord_1481893, baseEnd_1481893] using wordTrace_append hprefix tailTrace_1481893
  have hstable : (prefixWord ++ tailWord_1481893).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481893).length < 2 ^ (prefixWord ++ tailWord_1481893).sum := by decide
  have hdescent : baseEnd_1481893 < baseStart_1481893 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481933 : List Nat := [1, 6, 2, 2, 1, 1, 2, 3, 3]
def baseStart_1481933 : Nat := 118140960795 + 1481933 * 2 ^ 59
def prefixEnd_1481933 : Nat := 4983230072969 + 3 ^ 40 * 1481933 * 2
def baseEnd_1481933 : Nat := 338197300781980295120987

theorem tailTrace_1481933 : CollatzResearch.WordTrace tailWord_1481933 prefixEnd_1481933 338197300781980295120987 := by
  unfold tailWord_1481933
  simp only [CollatzResearch.WordTrace]
  refine ⟨54050536940217309851666453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36033691293478206567777635 54050536940217309851666453)
  ·
    refine ⟨2533618919072686399296865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 54050536940217309851666453 2533618919072686399296865)
    ·
      refine ⟨1900214189304514799472649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2533618919072686399296865 1900214189304514799472649)
      ·
        refine ⟨1425160641978386099604487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1900214189304514799472649 1425160641978386099604487)
        ·
          refine ⟨2137740962967579149406731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1425160641978386099604487 2137740962967579149406731)
          ·
            refine ⟨3206611444451368724110097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2137740962967579149406731 3206611444451368724110097)
            ·
              refine ⟨2404958583338526543082573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3206611444451368724110097 2404958583338526543082573)
              ·
                refine ⟨901859468751947453655965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2404958583338526543082573 901859468751947453655965)
                ·
                  refine ⟨338197300781980295120987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 901859468751947453655965 338197300781980295120987)
                  ·
                    rfl

theorem cell21_1481933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 2, 3, 3].length) (baseStart_1481933 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1481933 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1481933 prefixEnd_1481933 := by exact prefixLift 1481933
  have htrace : WordTrace (prefixWord ++ tailWord_1481933) baseStart_1481933 baseEnd_1481933 := by
    simpa [prefixWord, tailWord_1481933, baseEnd_1481933] using wordTrace_append hprefix tailTrace_1481933
  have hstable : (prefixWord ++ tailWord_1481933).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481933).length < 2 ^ (prefixWord ++ tailWord_1481933).sum := by decide
  have hdescent : baseEnd_1481933 < baseStart_1481933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481969 : List Nat := [1, 2, 2, 2, 2, 1, 1, 10]
def baseStart_1481969 : Nat := 118140960795 + 1481969 * 2 ^ 59
def prefixEnd_1481969 : Nat := 4983230072969 + 3 ^ 40 * 1481969 * 2
def baseEnd_1481969 : Nat := 112735172157484077506971

theorem tailTrace_1481969 : CollatzResearch.WordTrace tailWord_1481969 prefixEnd_1481969 112735172157484077506971 := by
  unfold tailWord_1481969
  simp only [CollatzResearch.WordTrace]
  refine ⟨54051849968086887999976961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36034566645391258666651307 54051849968086887999976961)
  ·
    refine ⟨40538887476065165999982721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54051849968086887999976961 40538887476065165999982721)
    ·
      refine ⟨30404165607048874499987041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40538887476065165999982721 30404165607048874499987041)
      ·
        refine ⟨22803124205286655874990281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30404165607048874499987041 22803124205286655874990281)
        ·
          refine ⟨17102343153964991906242711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22803124205286655874990281 17102343153964991906242711)
          ·
            refine ⟨25653514730947487859364067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17102343153964991906242711 25653514730947487859364067)
            ·
              refine ⟨38480272096421231789046101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25653514730947487859364067 38480272096421231789046101)
              ·
                refine ⟨112735172157484077506971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 38480272096421231789046101 112735172157484077506971)
                ·
                  rfl

theorem cell21_1481969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 10].length) (baseStart_1481969 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1481969 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1481969 prefixEnd_1481969 := by exact prefixLift 1481969
  have htrace : WordTrace (prefixWord ++ tailWord_1481969) baseStart_1481969 baseEnd_1481969 := by
    simpa [prefixWord, tailWord_1481969, baseEnd_1481969] using wordTrace_append hprefix tailTrace_1481969
  have hstable : (prefixWord ++ tailWord_1481969).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481969).length < 2 ^ (prefixWord ++ tailWord_1481969).sum := by decide
  have hdescent : baseEnd_1481969 < baseStart_1481969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1481992 : List Nat := [2, 1, 3, 2, 5, 1, 1, 3, 3]
def baseStart_1481992 : Nat := 118140960795 + 1481992 * 2 ^ 59
def prefixEnd_1481992 : Nat := 4983230072969 + 3 ^ 40 * 1481992 * 2
def baseEnd_1481992 : Nat := 338210765385809303637533

theorem tailTrace_1481992 : CollatzResearch.WordTrace tailWord_1481992 prefixEnd_1481992 338210765385809303637533 := by
  unfold tailWord_1481992
  simp only [CollatzResearch.WordTrace]
  refine ⟨27026344423501781464032115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36035125898002375285376153 27026344423501781464032115)
  ·
    refine ⟨40539516635252672196048173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27026344423501781464032115 40539516635252672196048173)
    ·
      refine ⟨15202318738219752073518065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40539516635252672196048173 15202318738219752073518065)
      ·
        refine ⟨11401739053664814055138549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15202318738219752073518065 11401739053664814055138549)
        ·
          refine ⟨1068913036281076317669239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11401739053664814055138549 1068913036281076317669239)
          ·
            refine ⟨1603369554421614476503859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1068913036281076317669239 1603369554421614476503859)
            ·
              refine ⟨2405054331632421714755789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1603369554421614476503859 2405054331632421714755789)
              ·
                refine ⟨901895374362158143033421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2405054331632421714755789 901895374362158143033421)
                ·
                  refine ⟨338210765385809303637533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 901895374362158143033421 338210765385809303637533)
                  ·
                    rfl

theorem cell21_1481992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 1, 3, 3].length) (baseStart_1481992 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1481992 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1481992 prefixEnd_1481992 := by exact prefixLift 1481992
  have htrace : WordTrace (prefixWord ++ tailWord_1481992) baseStart_1481992 baseEnd_1481992 := by
    simpa [prefixWord, tailWord_1481992, baseEnd_1481992] using wordTrace_append hprefix tailTrace_1481992
  have hstable : (prefixWord ++ tailWord_1481992).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1481992).length < 2 ^ (prefixWord ++ tailWord_1481992).sum := by decide
  have hdescent : baseEnd_1481992 < baseStart_1481992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1481992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482093 : List Nat := [1, 5, 1, 1, 1, 4, 1, 2, 5]
def baseStart_1482093 : Nat := 118140960795 + 1482093 * 2 ^ 59
def prefixEnd_1482093 : Nat := 4983230072969 + 3 ^ 40 * 1482093 * 2
def baseEnd_1482093 : Nat := 338233814961855572453993

theorem tailTrace_1482093 : CollatzResearch.WordTrace tailWord_1482093 prefixEnd_1482093 338233814961855572453993 := by
  unfold tailWord_1482093
  simp only [CollatzResearch.WordTrace]
  refine ⟨54056372619637657177490933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36037581746425104784993955 54056372619637657177490933)
  ·
    refine ⟨5067784933091030360389775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 54056372619637657177490933 5067784933091030360389775)
    ·
      refine ⟨7601677399636545540584663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5067784933091030360389775 7601677399636545540584663)
      ·
        refine ⟨11402516099454818310876995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7601677399636545540584663 11402516099454818310876995)
        ·
          refine ⟨17103774149182227466315493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11402516099454818310876995 17103774149182227466315493)
          ·
            refine ⟨3206957652971667649934155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17103774149182227466315493 3206957652971667649934155)
            ·
              refine ⟨4810436479457501474901233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3206957652971667649934155 4810436479457501474901233)
              ·
                refine ⟨3607827359593126106175925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4810436479457501474901233 3607827359593126106175925)
                ·
                  refine ⟨338233814961855572453993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3607827359593126106175925 338233814961855572453993)
                  ·
                    rfl

theorem cell21_1482093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 2, 5].length) (baseStart_1482093 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1482093 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1482093 prefixEnd_1482093 := by exact prefixLift 1482093
  have htrace : WordTrace (prefixWord ++ tailWord_1482093) baseStart_1482093 baseEnd_1482093 := by
    simpa [prefixWord, tailWord_1482093, baseEnd_1482093] using wordTrace_append hprefix tailTrace_1482093
  have hstable : (prefixWord ++ tailWord_1482093).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482093).length < 2 ^ (prefixWord ++ tailWord_1482093).sum := by decide
  have hdescent : baseEnd_1482093 < baseStart_1482093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482141 : List Nat := [1, 4, 2, 1, 3, 2, 3, 1, 4]
def baseStart_1482141 : Nat := 118140960795 + 1482141 * 2 ^ 59
def prefixEnd_1482141 : Nat := 4983230072969 + 3 ^ 40 * 1482141 * 2
def baseEnd_1482141 : Nat := 338244769215818155653895

theorem tailTrace_1482141 : CollatzResearch.WordTrace tailWord_1482141 prefixEnd_1482141 338244769215818155653895 := by
  unfold tailWord_1482141
  simp only [CollatzResearch.WordTrace]
  refine ⟨54058123323463761375238277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36038748882309174250158851 54058123323463761375238277)
  ·
    refine ⟨10135898123149455257857177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54058123323463761375238277 10135898123149455257857177)
    ·
      refine ⟨7601923592362091443392883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10135898123149455257857177 7601923592362091443392883)
      ·
        refine ⟨11402885388543137165089325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7601923592362091443392883 11402885388543137165089325)
        ·
          refine ⟨4276082020703676436908497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11402885388543137165089325 4276082020703676436908497)
          ·
            refine ⟨3207061515527757327681373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4276082020703676436908497 3207061515527757327681373)
            ·
              refine ⟨1202648068322908997880515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3207061515527757327681373 1202648068322908997880515)
              ·
                refine ⟨1803972102484363496820773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1202648068322908997880515 1803972102484363496820773)
                ·
                  refine ⟨338244769215818155653895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1803972102484363496820773 338244769215818155653895)
                  ·
                    rfl

theorem cell21_1482141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 3, 1, 4].length) (baseStart_1482141 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1482141 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1482141 prefixEnd_1482141 := by exact prefixLift 1482141
  have htrace : WordTrace (prefixWord ++ tailWord_1482141) baseStart_1482141 baseEnd_1482141 := by
    simpa [prefixWord, tailWord_1482141, baseEnd_1482141] using wordTrace_append hprefix tailTrace_1482141
  have hstable : (prefixWord ++ tailWord_1482141).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482141).length < 2 ^ (prefixWord ++ tailWord_1482141).sum := by decide
  have hdescent : baseEnd_1482141 < baseStart_1482141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482178 : List Nat := [3, 5, 2, 1, 2, 1, 1, 1, 5]
def baseStart_1482178 : Nat := 118140960795 + 1482178 * 2 ^ 59
def prefixEnd_1482178 : Nat := 4983230072969 + 3 ^ 40 * 1482178 * 2
def baseEnd_1482178 : Nat := 338253213119914313537153

theorem tailTrace_1482178 : CollatzResearch.WordTrace tailWord_1482178 prefixEnd_1482178 338253213119914313537153 := by
  unfold tailWord_1482178
  simp only [CollatzResearch.WordTrace]
  refine ⟨13514868206082429173583797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36039648549553144462890125 13514868206082429173583797)
  ·
    refine ⟨1267018894320227735023481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13514868206082429173583797 1267018894320227735023481)
    ·
      refine ⟨950264170740170801267611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1267018894320227735023481 950264170740170801267611)
      ·
        refine ⟨1425396256110256201901417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 950264170740170801267611 1425396256110256201901417)
        ·
          refine ⟨1069047192082692151426063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1425396256110256201901417 1069047192082692151426063)
          ·
            refine ⟨1603570788124038227139095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1069047192082692151426063 1603570788124038227139095)
            ·
              refine ⟨2405356182186057340708643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1603570788124038227139095 2405356182186057340708643)
              ·
                refine ⟨3608034273279086011062965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2405356182186057340708643 3608034273279086011062965)
                ·
                  refine ⟨338253213119914313537153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3608034273279086011062965 338253213119914313537153)
                  ·
                    rfl

theorem cell21_1482178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_1482178 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1482178 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1482178 prefixEnd_1482178 := by exact prefixLift 1482178
  have htrace : WordTrace (prefixWord ++ tailWord_1482178) baseStart_1482178 baseEnd_1482178 := by
    simpa [prefixWord, tailWord_1482178, baseEnd_1482178] using wordTrace_append hprefix tailTrace_1482178
  have hstable : (prefixWord ++ tailWord_1482178).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482178).length < 2 ^ (prefixWord ++ tailWord_1482178).sum := by decide
  have hdescent : baseEnd_1482178 < baseStart_1482178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482183 : List Nat := [1, 1, 4, 1, 1, 3, 2, 4, 4]
def baseStart_1482183 : Nat := 118140960795 + 1482183 * 2 ^ 59
def prefixEnd_1482183 : Nat := 4983230072969 + 3 ^ 40 * 1482183 * 2
def baseEnd_1482183 : Nat := 338254354188035415953809

theorem tailTrace_1482183 : CollatzResearch.WordTrace tailWord_1482183 prefixEnd_1482183 338254354188035415953809 := by
  unfold tailWord_1482183
  simp only [CollatzResearch.WordTrace]
  refine ⟨54059655189311602548267203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36039770126207735032178135 54059655189311602548267203)
  ·
    refine ⟨81089482783967403822400805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54059655189311602548267203 81089482783967403822400805)
    ·
      refine ⟨15204278021993888216700151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81089482783967403822400805 15204278021993888216700151)
      ·
        refine ⟨22806417032990832325050227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15204278021993888216700151 22806417032990832325050227)
        ·
          refine ⟨34209625549486248487575341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22806417032990832325050227 34209625549486248487575341)
          ·
            refine ⟨12828609581057343182840753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34209625549486248487575341 12828609581057343182840753)
            ·
              refine ⟨9621457185793007387130565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12828609581057343182840753 9621457185793007387130565)
              ·
                refine ⟨1804023222336188885086981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9621457185793007387130565 1804023222336188885086981)
                ·
                  refine ⟨338254354188035415953809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1804023222336188885086981 338254354188035415953809)
                  ·
                    rfl

theorem cell21_1482183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 4, 4].length) (baseStart_1482183 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1482183 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1482183 prefixEnd_1482183 := by exact prefixLift 1482183
  have htrace : WordTrace (prefixWord ++ tailWord_1482183) baseStart_1482183 baseEnd_1482183 := by
    simpa [prefixWord, tailWord_1482183, baseEnd_1482183] using wordTrace_append hprefix tailTrace_1482183
  have hstable : (prefixWord ++ tailWord_1482183).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482183).length < 2 ^ (prefixWord ++ tailWord_1482183).sum := by decide
  have hdescent : baseEnd_1482183 < baseStart_1482183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482200 : List Nat := [2, 1, 2, 2, 2, 1, 6, 1, 4]
def baseStart_1482200 : Nat := 118140960795 + 1482200 * 2 ^ 59
def prefixEnd_1482200 : Nat := 4983230072969 + 3 ^ 40 * 1482200 * 2
def baseEnd_1482200 : Nat := 338258233819647164170441

theorem tailTrace_1482200 : CollatzResearch.WordTrace tailWord_1482200 prefixEnd_1482200 338258233819647164170441 := by
  unfold tailWord_1482200
  simp only [CollatzResearch.WordTrace]
  refine ⟨27030137615125007225818027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36040183486833342967757369 27030137615125007225818027)
  ·
    refine ⟨40545206422687510838727041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27030137615125007225818027 40545206422687510838727041)
    ·
      refine ⟨30408904817015633129045281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40545206422687510838727041 30408904817015633129045281)
      ·
        refine ⟨22806678612761724846783961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30408904817015633129045281 22806678612761724846783961)
        ·
          refine ⟨17105008959571293635087971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22806678612761724846783961 17105008959571293635087971)
          ·
            refine ⟨25657513439356940452631957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17105008959571293635087971 25657513439356940452631957)
            ·
              refine ⟨1202695942469856583717123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 25657513439356940452631957 1202695942469856583717123)
              ·
                refine ⟨1804043913704784875575685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1202695942469856583717123 1804043913704784875575685)
                ·
                  refine ⟨338258233819647164170441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1804043913704784875575685 338258233819647164170441)
                  ·
                    rfl

theorem cell21_1482200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 6, 1, 4].length) (baseStart_1482200 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1482200 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1482200 prefixEnd_1482200 := by exact prefixLift 1482200
  have htrace : WordTrace (prefixWord ++ tailWord_1482200) baseStart_1482200 baseEnd_1482200 := by
    simpa [prefixWord, tailWord_1482200, baseEnd_1482200] using wordTrace_append hprefix tailTrace_1482200
  have hstable : (prefixWord ++ tailWord_1482200).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482200).length < 2 ^ (prefixWord ++ tailWord_1482200).sum := by decide
  have hdescent : baseEnd_1482200 < baseStart_1482200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482259 : List Nat := [1, 1, 1, 2, 1, 6, 2, 3, 4]
def baseStart_1482259 : Nat := 118140960795 + 1482259 * 2 ^ 59
def prefixEnd_1482259 : Nat := 4983230072969 + 3 ^ 40 * 1482259 * 2
def baseEnd_1482259 : Nat := 338271698423476172686987

theorem tailTrace_1482259 : CollatzResearch.WordTrace tailWord_1482259 prefixEnd_1482259 338271698423476172686987 := by
  unfold tailWord_1482259
  simp only [CollatzResearch.WordTrace]
  refine ⟨54062427137036267528033831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36041618091357511685355887 54062427137036267528033831)
  ·
    refine ⟨81093640705554401292050747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54062427137036267528033831 81093640705554401292050747)
    ·
      refine ⟨121640461058331601938076121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81093640705554401292050747 121640461058331601938076121)
      ·
        refine ⟨91230345793748701453557091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121640461058331601938076121 91230345793748701453557091)
        ·
          refine ⟨136845518690623052180335637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91230345793748701453557091 136845518690623052180335637)
          ·
            refine ⟨6414633688622955570953233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 136845518690623052180335637 6414633688622955570953233)
            ·
              refine ⟨4810975266467216678214925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6414633688622955570953233 4810975266467216678214925)
              ·
                refine ⟨1804115724925206254330597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4810975266467216678214925 1804115724925206254330597)
                ·
                  refine ⟨338271698423476172686987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1804115724925206254330597 338271698423476172686987)
                  ·
                    rfl

theorem cell21_1482259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 3, 4].length) (baseStart_1482259 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1482259 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1482259 prefixEnd_1482259 := by exact prefixLift 1482259
  have htrace : WordTrace (prefixWord ++ tailWord_1482259) baseStart_1482259 baseEnd_1482259 := by
    simpa [prefixWord, tailWord_1482259, baseEnd_1482259] using wordTrace_append hprefix tailTrace_1482259
  have hstable : (prefixWord ++ tailWord_1482259).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482259).length < 2 ^ (prefixWord ++ tailWord_1482259).sum := by decide
  have hdescent : baseEnd_1482259 < baseStart_1482259 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482369 : List Nat := [1, 2, 4, 2, 1, 4, 2, 1, 4]
def baseStart_1482369 : Nat := 118140960795 + 1482369 * 2 ^ 59
def prefixEnd_1482369 : Nat := 4983230072969 + 3 ^ 40 * 1482369 * 2
def baseEnd_1482369 : Nat := 338296801922140425853429

theorem tailTrace_1482369 : CollatzResearch.WordTrace tailWord_1482369 prefixEnd_1482369 338296801922140425853429 := by
  unfold tailWord_1482369
  simp only [CollatzResearch.WordTrace]
  refine ⟨54066439166637756314538161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36044292777758504209692107 54066439166637756314538161)
  ·
    refine ⟨40549829374978317235903621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54066439166637756314538161 40549829374978317235903621)
    ·
      refine ⟨7603093007808434481731929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40549829374978317235903621 7603093007808434481731929)
      ·
        refine ⟨5702319755856325861298947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7603093007808434481731929 5702319755856325861298947)
        ·
          refine ⟨8553479633784488791948421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5702319755856325861298947 8553479633784488791948421)
          ·
            refine ⟨1603777431334591648490329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8553479633784488791948421 1603777431334591648490329)
            ·
              refine ⟨1202833073500943736367747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1603777431334591648490329 1202833073500943736367747)
              ·
                refine ⟨1804249610251415604551621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1202833073500943736367747 1804249610251415604551621)
                ·
                  refine ⟨338296801922140425853429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1804249610251415604551621 338296801922140425853429)
                  ·
                    rfl

theorem cell21_1482369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 2, 1, 4].length) (baseStart_1482369 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1482369 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1482369 prefixEnd_1482369 := by exact prefixLift 1482369
  have htrace : WordTrace (prefixWord ++ tailWord_1482369) baseStart_1482369 baseEnd_1482369 := by
    simpa [prefixWord, tailWord_1482369, baseEnd_1482369] using wordTrace_append hprefix tailTrace_1482369
  have hstable : (prefixWord ++ tailWord_1482369).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482369).length < 2 ^ (prefixWord ++ tailWord_1482369).sum := by decide
  have hdescent : baseEnd_1482369 < baseStart_1482369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482397 : List Nat := [1, 4, 2, 1, 1, 1, 1, 7, 3]
def baseStart_1482397 : Nat := 118140960795 + 1482397 * 2 ^ 59
def prefixEnd_1482397 : Nat := 4983230072969 + 3 ^ 40 * 1482397 * 2
def baseEnd_1482397 : Nat := 338303191903618599386705

theorem tailTrace_1482397 : CollatzResearch.WordTrace tailWord_1482397 prefixEnd_1482397 338303191903618599386705 := by
  unfold tailWord_1482397
  simp only [CollatzResearch.WordTrace]
  refine ⟨54067460410536317096557445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36044973607024211397704963 54067460410536317096557445)
  ·
    refine ⟨10137648826975559455604521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54067460410536317096557445 10137648826975559455604521)
    ·
      refine ⟨7603236620231669591703391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10137648826975559455604521 7603236620231669591703391)
      ·
        refine ⟨11404854930347504387555087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7603236620231669591703391 11404854930347504387555087)
        ·
          refine ⟨17107282395521256581332631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11404854930347504387555087 17107282395521256581332631)
          ·
            refine ⟨25660923593281884871998947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17107282395521256581332631 25660923593281884871998947)
            ·
              refine ⟨38491385389922827307998421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25660923593281884871998947 38491385389922827307998421)
              ·
                refine ⟨902141845076316265031213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 38491385389922827307998421 902141845076316265031213)
                ·
                  refine ⟨338303191903618599386705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 902141845076316265031213 338303191903618599386705)
                  ·
                    rfl

theorem cell21_1482397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 7, 3].length) (baseStart_1482397 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1482397 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1482397 prefixEnd_1482397 := by exact prefixLift 1482397
  have htrace : WordTrace (prefixWord ++ tailWord_1482397) baseStart_1482397 baseEnd_1482397 := by
    simpa [prefixWord, tailWord_1482397, baseEnd_1482397] using wordTrace_append hprefix tailTrace_1482397
  have hstable : (prefixWord ++ tailWord_1482397).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482397).length < 2 ^ (prefixWord ++ tailWord_1482397).sum := by decide
  have hdescent : baseEnd_1482397 < baseStart_1482397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482425 : List Nat := [1, 2, 1, 4, 1, 1, 5, 6]
def baseStart_1482425 : Nat := 118140960795 + 1482425 * 2 ^ 59
def prefixEnd_1482425 : Nat := 4983230072969 + 3 ^ 40 * 1482425 * 2
def baseEnd_1482425 : Nat := 112769860628365590973327

theorem tailTrace_1482425 : CollatzResearch.WordTrace tailWord_1482425 prefixEnd_1482425 112769860628365590973327 := by
  unfold tailWord_1482425
  simp only [CollatzResearch.WordTrace]
  refine ⟨54068481654434877878576729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36045654436289918585717819 54068481654434877878576729)
  ·
    refine ⟨40551361240826158408932547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54068481654434877878576729 40551361240826158408932547)
    ·
      refine ⟨60827041861239237613398821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40551361240826158408932547 60827041861239237613398821)
      ·
        refine ⟨11405070348982357052512279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60827041861239237613398821 11405070348982357052512279)
        ·
          refine ⟨17107605523473535578768419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11405070348982357052512279 17107605523473535578768419)
          ·
            refine ⟨25661408285210303368152629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17107605523473535578768419 25661408285210303368152629)
            ·
              refine ⟨2405757026738465940764309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25661408285210303368152629 2405757026738465940764309)
              ·
                refine ⟨112769860628365590973327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2405757026738465940764309 112769860628365590973327)
                ·
                  rfl

theorem cell21_1482425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5, 6].length) (baseStart_1482425 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1482425 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1482425 prefixEnd_1482425 := by exact prefixLift 1482425
  have htrace : WordTrace (prefixWord ++ tailWord_1482425) baseStart_1482425 baseEnd_1482425 := by
    simpa [prefixWord, tailWord_1482425, baseEnd_1482425] using wordTrace_append hprefix tailTrace_1482425
  have hstable : (prefixWord ++ tailWord_1482425).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482425).length < 2 ^ (prefixWord ++ tailWord_1482425).sum := by decide
  have hdescent : baseEnd_1482425 < baseStart_1482425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482580 : List Nat := [2, 4, 1, 1, 3, 2, 2, 2, 4]
def baseStart_1482580 : Nat := 118140960795 + 1482580 * 2 ^ 59
def prefixEnd_1482580 : Nat := 4983230072969 + 3 ^ 40 * 1482580 * 2
def baseEnd_1482580 : Nat := 338344954996850947836331

theorem tailTrace_1482580 : CollatzResearch.WordTrace tailWord_1482580 prefixEnd_1482580 338344954996850947836331 := by
  unfold tailWord_1482580
  simp only [CollatzResearch.WordTrace]
  refine ⟨27037067484436669675234597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36049423312582226233646129 27037067484436669675234597)
  ·
    refine ⟨5069450153331875564106487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27037067484436669675234597 5069450153331875564106487)
    ·
      refine ⟨7604175229997813346159731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5069450153331875564106487 7604175229997813346159731)
      ·
        refine ⟨11406262844996720019239597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7604175229997813346159731 11406262844996720019239597)
        ·
          refine ⟨4277348566873770007214849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11406262844996720019239597 4277348566873770007214849)
          ·
            refine ⟨3208011425155327505411137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4277348566873770007214849 3208011425155327505411137)
            ·
              refine ⟨2406008568866495629058353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3208011425155327505411137 2406008568866495629058353)
              ·
                refine ⟨1804506426649871721793765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2406008568866495629058353 1804506426649871721793765)
                ·
                  refine ⟨338344954996850947836331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1804506426649871721793765 338344954996850947836331)
                  ·
                    rfl

theorem cell21_1482580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2, 2, 4].length) (baseStart_1482580 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1482580 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1482580 prefixEnd_1482580 := by exact prefixLift 1482580
  have htrace : WordTrace (prefixWord ++ tailWord_1482580) baseStart_1482580 baseEnd_1482580 := by
    simpa [prefixWord, tailWord_1482580, baseEnd_1482580] using wordTrace_append hprefix tailTrace_1482580
  have hstable : (prefixWord ++ tailWord_1482580).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482580).length < 2 ^ (prefixWord ++ tailWord_1482580).sum := by decide
  have hdescent : baseEnd_1482580 < baseStart_1482580 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482583 : List Nat := [1, 1, 3, 2, 5, 2, 2, 2, 3]
def baseStart_1482583 : Nat := 118140960795 + 1482583 * 2 ^ 59
def prefixEnd_1482583 : Nat := 4983230072969 + 3 ^ 40 * 1482583 * 2
def baseEnd_1482583 : Nat := 338345639637723609286325

theorem tailTrace_1482583 : CollatzResearch.WordTrace tailWord_1482583 prefixEnd_1482583 338345639637723609286325 := by
  unfold tailWord_1482583
  simp only [CollatzResearch.WordTrace]
  refine ⟨54074244387862470862828403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36049496258574980575218935 54074244387862470862828403)
  ·
    refine ⟨81111366581793706294242605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54074244387862470862828403 81111366581793706294242605)
    ·
      refine ⟨30416762468172639860340977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81111366581793706294242605 30416762468172639860340977)
      ·
        refine ⟨22812571851129479895255733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30416762468172639860340977 22812571851129479895255733)
        ·
          refine ⟨2138678611043388740180225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22812571851129479895255733 2138678611043388740180225)
          ·
            refine ⟨1604008958282541555135169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2138678611043388740180225 1604008958282541555135169)
            ·
              refine ⟨1203006718711906166351377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1604008958282541555135169 1203006718711906166351377)
              ·
                refine ⟨902255039033929624763533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1203006718711906166351377 902255039033929624763533)
                ·
                  refine ⟨338345639637723609286325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 902255039033929624763533 338345639637723609286325)
                  ·
                    rfl

theorem cell21_1482583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 2, 2, 3].length) (baseStart_1482583 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1482583 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1482583 prefixEnd_1482583 := by exact prefixLift 1482583
  have htrace : WordTrace (prefixWord ++ tailWord_1482583) baseStart_1482583 baseEnd_1482583 := by
    simpa [prefixWord, tailWord_1482583, baseEnd_1482583] using wordTrace_append hprefix tailTrace_1482583
  have hstable : (prefixWord ++ tailWord_1482583).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482583).length < 2 ^ (prefixWord ++ tailWord_1482583).sum := by decide
  have hdescent : baseEnd_1482583 < baseStart_1482583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482594 : List Nat := [3, 3, 2, 1, 2, 1, 3, 6]
def baseStart_1482594 : Nat := 118140960795 + 1482594 * 2 ^ 59
def prefixEnd_1482594 : Nat := 4983230072969 + 3 ^ 40 * 1482594 * 2
def baseEnd_1482594 : Nat := 112782716662530011534323

theorem tailTrace_1482594 : CollatzResearch.WordTrace tailWord_1482594 prefixEnd_1482594 112782716662530011534323 := by
  unfold tailWord_1482594
  simp only [CollatzResearch.WordTrace]
  refine ⟨13518661397705654935369709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36049763727215079827652557 13518661397705654935369709)
  ·
    refine ⟨5069498024139620600763641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13518661397705654935369709 5069498024139620600763641)
    ·
      refine ⟨3802123518104715450572731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5069498024139620600763641 3802123518104715450572731)
      ·
        refine ⟨5703185277157073175859097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3802123518104715450572731 5703185277157073175859097)
        ·
          refine ⟨4277388957867804881894323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5703185277157073175859097 4277388957867804881894323)
          ·
            refine ⟨6416083436801707322841485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4277388957867804881894323 6416083436801707322841485)
            ·
              refine ⟨2406031288800640246065557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6416083436801707322841485 2406031288800640246065557)
              ·
                refine ⟨112782716662530011534323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2406031288800640246065557 112782716662530011534323)
                ·
                  rfl

theorem cell21_1482594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3, 6].length) (baseStart_1482594 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1482594 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1482594 prefixEnd_1482594 := by exact prefixLift 1482594
  have htrace : WordTrace (prefixWord ++ tailWord_1482594) baseStart_1482594 baseEnd_1482594 := by
    simpa [prefixWord, tailWord_1482594, baseEnd_1482594] using wordTrace_append hprefix tailTrace_1482594
  have hstable : (prefixWord ++ tailWord_1482594).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482594).length < 2 ^ (prefixWord ++ tailWord_1482594).sum := by decide
  have hdescent : baseEnd_1482594 < baseStart_1482594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482642 : List Nat := [3, 2, 3, 2, 1, 1, 2, 4, 3]
def baseStart_1482642 : Nat := 118140960795 + 1482642 * 2 ^ 59
def prefixEnd_1482642 : Nat := 4983230072969 + 3 ^ 40 * 1482642 * 2
def baseEnd_1482642 : Nat := 338359104241552617802871

theorem tailTrace_1482642 : CollatzResearch.WordTrace tailWord_1482642 prefixEnd_1482642 338359104241552617802871 := by
  unfold tailWord_1482642
  simp only [CollatzResearch.WordTrace]
  refine ⟨13519099073662180984806545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36050930863099149292817453 13519099073662180984806545)
  ·
    refine ⟨10139324305246635738604909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13519099073662180984806545 10139324305246635738604909)
    ·
      refine ⟨3802246614467488401976841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10139324305246635738604909 3802246614467488401976841)
      ·
        refine ⟨2851684960850616301482631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3802246614467488401976841 2851684960850616301482631)
        ·
          refine ⟨4277527441275924452223947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2851684960850616301482631 4277527441275924452223947)
          ·
            refine ⟨6416291161913886678335921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4277527441275924452223947 6416291161913886678335921)
            ·
              refine ⟨4812218371435415008751941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6416291161913886678335921 4812218371435415008751941)
              ·
                refine ⟨902290944644140314140989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4812218371435415008751941 902290944644140314140989)
                ·
                  refine ⟨338359104241552617802871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 902290944644140314140989 338359104241552617802871)
                  ·
                    rfl

theorem cell21_1482642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 4, 3].length) (baseStart_1482642 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1482642 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1482642 prefixEnd_1482642 := by exact prefixLift 1482642
  have htrace : WordTrace (prefixWord ++ tailWord_1482642) baseStart_1482642 baseEnd_1482642 := by
    simpa [prefixWord, tailWord_1482642, baseEnd_1482642] using wordTrace_append hprefix tailTrace_1482642
  have hstable : (prefixWord ++ tailWord_1482642).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482642).length < 2 ^ (prefixWord ++ tailWord_1482642).sum := by decide
  have hdescent : baseEnd_1482642 < baseStart_1482642 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482676 : List Nat := [2, 5, 2, 1, 2, 2, 1, 3, 3]
def baseStart_1482676 : Nat := 118140960795 + 1482676 * 2 ^ 59
def prefixEnd_1482676 : Nat := 4983230072969 + 3 ^ 40 * 1482676 * 2
def baseEnd_1482676 : Nat := 338366863504776114236135

theorem tailTrace_1482676 : CollatzResearch.WordTrace tailWord_1482676 prefixEnd_1482676 338366863504776114236135 := by
  unfold tailWord_1482676
  simp only [CollatzResearch.WordTrace]
  refine ⟨27038818188262773872981941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36051757584350365163975921 27038818188262773872981941)
  ·
    refine ⟨2534889205149635050592057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27038818188262773872981941 2534889205149635050592057)
    ·
      refine ⟨1901166903862226287944043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2534889205149635050592057 1901166903862226287944043)
      ·
        refine ⟨2851750355793339431916065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1901166903862226287944043 2851750355793339431916065)
        ·
          refine ⟨2138812766845004573937049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2851750355793339431916065 2138812766845004573937049)
          ·
            refine ⟨1604109575133753430452787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2138812766845004573937049 1604109575133753430452787)
            ·
              refine ⟨2406164362700630145679181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1604109575133753430452787 2406164362700630145679181)
              ·
                refine ⟨902311636012736304629693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2406164362700630145679181 902311636012736304629693)
                ·
                  refine ⟨338366863504776114236135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 902311636012736304629693 338366863504776114236135)
                  ·
                    rfl

theorem cell21_1482676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 1, 3, 3].length) (baseStart_1482676 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1482676 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1482676 prefixEnd_1482676 := by exact prefixLift 1482676
  have htrace : WordTrace (prefixWord ++ tailWord_1482676) baseStart_1482676 baseEnd_1482676 := by
    simpa [prefixWord, tailWord_1482676, baseEnd_1482676] using wordTrace_append hprefix tailTrace_1482676
  have hstable : (prefixWord ++ tailWord_1482676).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482676).length < 2 ^ (prefixWord ++ tailWord_1482676).sum := by decide
  have hdescent : baseEnd_1482676 < baseStart_1482676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482698 : List Nat := [3, 1, 2, 1, 2, 1, 4, 1, 6]
def baseStart_1482698 : Nat := 118140960795 + 1482698 * 2 ^ 59
def prefixEnd_1482698 : Nat := 4983230072969 + 3 ^ 40 * 1482698 * 2
def baseEnd_1482698 : Nat := 338371884204508964869423

theorem tailTrace_1482698 : CollatzResearch.WordTrace tailWord_1482698 prefixEnd_1482698 338371884204508964869423 := by
  unfold tailWord_1482698
  simp only [CollatzResearch.WordTrace]
  refine ⟨13519609695611461375816187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36052292521630563668843165 13519609695611461375816187)
  ·
    refine ⟨20279414543417192063724281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13519609695611461375816187 20279414543417192063724281)
    ·
      refine ⟨15209560907562894047793211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20279414543417192063724281 15209560907562894047793211)
      ·
        refine ⟨22814341361344341071689817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15209560907562894047793211 22814341361344341071689817)
        ·
          refine ⟨17110756021008255803767363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22814341361344341071689817 17110756021008255803767363)
          ·
            refine ⟨25666134031512383705651045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17110756021008255803767363 25666134031512383705651045)
            ·
              refine ⟨4812400130908571944809571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25666134031512383705651045 4812400130908571944809571)
              ·
                refine ⟨7218600196362857917214357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4812400130908571944809571 7218600196362857917214357)
                ·
                  refine ⟨338371884204508964869423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7218600196362857917214357 338371884204508964869423)
                  ·
                    rfl

theorem cell21_1482698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 1, 6].length) (baseStart_1482698 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1482698 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1482698 prefixEnd_1482698 := by exact prefixLift 1482698
  have htrace : WordTrace (prefixWord ++ tailWord_1482698) baseStart_1482698 baseEnd_1482698 := by
    simpa [prefixWord, tailWord_1482698, baseEnd_1482698] using wordTrace_append hprefix tailTrace_1482698
  have hstable : (prefixWord ++ tailWord_1482698).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482698).length < 2 ^ (prefixWord ++ tailWord_1482698).sum := by decide
  have hdescent : baseEnd_1482698 < baseStart_1482698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482794 : List Nat := [3, 1, 4, 1, 2, 2, 2, 3, 3]
def baseStart_1482794 : Nat := 118140960795 + 1482794 * 2 ^ 59
def prefixEnd_1482794 : Nat := 4983230072969 + 3 ^ 40 * 1482794 * 2
def baseEnd_1482794 : Nat := 338393792712434131269227

theorem tailTrace_1482794 : CollatzResearch.WordTrace tailWord_1482794 prefixEnd_1482794 338393792712434131269227 := by
  unfold tailWord_1482794
  simp only [CollatzResearch.WordTrace]
  refine ⟨13520485047524513474689859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36054626793398702599172957 13520485047524513474689859)
  ·
    refine ⟨20280727571286770212034789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13520485047524513474689859 20280727571286770212034789)
    ·
      refine ⟨3802636419616269414756523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20280727571286770212034789 3802636419616269414756523)
      ·
        refine ⟨5703954629424404122134785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3802636419616269414756523 5703954629424404122134785)
        ·
          refine ⟨4277965972068303091601089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5703954629424404122134785 4277965972068303091601089)
          ·
            refine ⟨3208474479051227318700817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4277965972068303091601089 3208474479051227318700817)
            ·
              refine ⟨2406355859288420489025613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3208474479051227318700817 2406355859288420489025613)
              ·
                refine ⟨902383447233157683384605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2406355859288420489025613 902383447233157683384605)
                ·
                  refine ⟨338393792712434131269227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 902383447233157683384605 338393792712434131269227)
                  ·
                    rfl

theorem cell21_1482794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2, 3, 3].length) (baseStart_1482794 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1482794 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1482794 prefixEnd_1482794 := by exact prefixLift 1482794
  have htrace : WordTrace (prefixWord ++ tailWord_1482794) baseStart_1482794 baseEnd_1482794 := by
    simpa [prefixWord, tailWord_1482794, baseEnd_1482794] using wordTrace_append hprefix tailTrace_1482794
  have hstable : (prefixWord ++ tailWord_1482794).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482794).length < 2 ^ (prefixWord ++ tailWord_1482794).sum := by decide
  have hdescent : baseEnd_1482794 < baseStart_1482794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482808 : List Nat := [2, 1, 2, 1, 6, 2, 1, 2, 4]
def baseStart_1482808 : Nat := 118140960795 + 1482808 * 2 ^ 59
def prefixEnd_1482808 : Nat := 4983230072969 + 3 ^ 40 * 1482808 * 2
def baseEnd_1482808 : Nat := 338396987703173218035865

theorem tailTrace_1482808 : CollatzResearch.WordTrace tailWord_1482808 prefixEnd_1482808 338396987703173218035865 := by
  unfold tailWord_1482808
  simp only [CollatzResearch.WordTrace]
  refine ⟨27041225406023667144884539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36054967208031556193179385 27041225406023667144884539)
  ·
    refine ⟨40561838109035500717326809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27041225406023667144884539 40561838109035500717326809)
    ·
      refine ⟨30421378581776625537995107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40561838109035500717326809 30421378581776625537995107)
      ·
        refine ⟨45632067872664938306992661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30421378581776625537995107 45632067872664938306992661)
        ·
          refine ⟨2139003181531168983140281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 45632067872664938306992661 2139003181531168983140281)
          ·
            refine ⟨1604252386148376737355211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2139003181531168983140281 1604252386148376737355211)
            ·
              refine ⟨2406378579222565106032817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1604252386148376737355211 2406378579222565106032817)
              ·
                refine ⟨1804783934416923829524613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2406378579222565106032817 1804783934416923829524613)
                ·
                  refine ⟨338396987703173218035865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1804783934416923829524613 338396987703173218035865)
                  ·
                    rfl

theorem cell21_1482808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 1, 2, 4].length) (baseStart_1482808 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1482808 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1482808 prefixEnd_1482808 := by exact prefixLift 1482808
  have htrace : WordTrace (prefixWord ++ tailWord_1482808) baseStart_1482808 baseEnd_1482808 := by
    simpa [prefixWord, tailWord_1482808, baseEnd_1482808] using wordTrace_append hprefix tailTrace_1482808
  have hstable : (prefixWord ++ tailWord_1482808).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482808).length < 2 ^ (prefixWord ++ tailWord_1482808).sum := by decide
  have hdescent : baseEnd_1482808 < baseStart_1482808 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482822 : List Nat := [6, 1, 1, 1, 1, 1, 2, 8]
def baseStart_1482822 : Nat := 118140960795 + 1482822 * 2 ^ 59
def prefixEnd_1482822 : Nat := 4983230072969 + 3 ^ 40 * 1482822 * 2
def baseEnd_1482822 : Nat := 112800060897970768267501

theorem tailTrace_1482822 : CollatzResearch.WordTrace tailWord_1482822 prefixEnd_1482822 112800060897970768267501 := by
  unfold tailWord_1482822
  simp only [CollatzResearch.WordTrace]
  refine ⟨1690092544812394208774335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 36055307622664409787185813 1690092544812394208774335)
  ·
    refine ⟨2535138817218591313161503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1690092544812394208774335 2535138817218591313161503)
    ·
      refine ⟨3802708225827886969742255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2535138817218591313161503 3802708225827886969742255)
      ·
        refine ⟨5704062338741830454613383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3802708225827886969742255 5704062338741830454613383)
        ·
          refine ⟨8556093508112745681920075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5704062338741830454613383 8556093508112745681920075)
          ·
            refine ⟨12834140262169118522880113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8556093508112745681920075 12834140262169118522880113)
            ·
              refine ⟨9625605196626838892160085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12834140262169118522880113 9625605196626838892160085)
              ·
                refine ⟨112800060897970768267501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9625605196626838892160085 112800060897970768267501)
                ·
                  rfl

theorem cell21_1482822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_1482822 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1482822 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1482822 prefixEnd_1482822 := by exact prefixLift 1482822
  have htrace : WordTrace (prefixWord ++ tailWord_1482822) baseStart_1482822 baseEnd_1482822 := by
    simpa [prefixWord, tailWord_1482822, baseEnd_1482822] using wordTrace_append hprefix tailTrace_1482822
  have hstable : (prefixWord ++ tailWord_1482822).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482822).length < 2 ^ (prefixWord ++ tailWord_1482822).sum := by decide
  have hdescent : baseEnd_1482822 < baseStart_1482822 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482853 : List Nat := [1, 3, 1, 3, 2, 2, 3, 3, 3]
def baseStart_1482853 : Nat := 118140960795 + 1482853 * 2 ^ 59
def prefixEnd_1482853 : Nat := 4983230072969 + 3 ^ 40 * 1482853 * 2
def baseEnd_1482853 : Nat := 338407257316263139785773

theorem tailTrace_1482853 : CollatzResearch.WordTrace tailWord_1482853 prefixEnd_1482853 338407257316263139785773 := by
  unfold tailWord_1482853
  simp only [CollatzResearch.WordTrace]
  refine ⟨54084092096884306975157213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36056061397922871316771475 54084092096884306975157213)
  ·
    refine ⟨20281534536331615115683955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54084092096884306975157213 20281534536331615115683955)
    ·
      refine ⟨30422301804497422673525933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20281534536331615115683955 30422301804497422673525933)
      ·
        refine ⟨11408363176686533502572225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30422301804497422673525933 11408363176686533502572225)
        ·
          refine ⟨8556272382514900126929169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11408363176686533502572225 8556272382514900126929169)
          ·
            refine ⟨6417204286886175095196877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8556272382514900126929169 6417204286886175095196877)
            ·
              refine ⟨2406451607582315660698829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6417204286886175095196877 2406451607582315660698829)
              ·
                refine ⟨902419352843368372762061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2406451607582315660698829 902419352843368372762061)
                ·
                  refine ⟨338407257316263139785773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 902419352843368372762061 338407257316263139785773)
                  ·
                    rfl

theorem cell21_1482853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3, 3, 3].length) (baseStart_1482853 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1482853 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1482853 prefixEnd_1482853 := by exact prefixLift 1482853
  have htrace : WordTrace (prefixWord ++ tailWord_1482853) baseStart_1482853 baseEnd_1482853 := by
    simpa [prefixWord, tailWord_1482853, baseEnd_1482853] using wordTrace_append hprefix tailTrace_1482853
  have hstable : (prefixWord ++ tailWord_1482853).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482853).length < 2 ^ (prefixWord ++ tailWord_1482853).sum := by decide
  have hdescent : baseEnd_1482853 < baseStart_1482853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482864 : List Nat := [2, 1, 1, 1, 5, 2, 9]
def baseStart_1482864 : Nat := 118140960795 + 1482864 * 2 ^ 59
def prefixEnd_1482864 : Nat := 4983230072969 + 3 ^ 40 * 1482864 * 2
def baseEnd_1482864 : Nat := 37601085296236618344713

theorem tailTrace_1482864 : CollatzResearch.WordTrace tailWord_1482864 prefixEnd_1482864 37601085296236618344713 := by
  unfold tailWord_1482864
  simp only [CollatzResearch.WordTrace]
  refine ⟨27042246649922227926903823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36056328866562970569205097 27042246649922227926903823)
  ·
    refine ⟨40563369974883341890355735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27042246649922227926903823 40563369974883341890355735)
    ·
      refine ⟨60845054962325012835533603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40563369974883341890355735 60845054962325012835533603)
      ·
        refine ⟨91267582443487519253300405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60845054962325012835533603 91267582443487519253300405)
        ·
          refine ⟨8556335854076954929996913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 91267582443487519253300405 8556335854076954929996913)
          ·
            refine ⟨6417251890557716197497685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8556335854076954929996913 6417251890557716197497685)
            ·
              refine ⟨37601085296236618344713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6417251890557716197497685 37601085296236618344713)
              ·
                rfl

theorem cell21_1482864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 9].length) (baseStart_1482864 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1482864 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1482864 prefixEnd_1482864 := by exact prefixLift 1482864
  have htrace : WordTrace (prefixWord ++ tailWord_1482864) baseStart_1482864 baseEnd_1482864 := by
    simpa [prefixWord, tailWord_1482864, baseEnd_1482864] using wordTrace_append hprefix tailTrace_1482864
  have hstable : (prefixWord ++ tailWord_1482864).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482864).length < 2 ^ (prefixWord ++ tailWord_1482864).sum := by decide
  have hdescent : baseEnd_1482864 < baseStart_1482864 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482946 : List Nat := [3, 5, 1, 1, 1, 2, 1, 2, 5]
def baseStart_1482946 : Nat := 118140960795 + 1482946 * 2 ^ 59
def prefixEnd_1482946 : Nat := 4983230072969 + 3 ^ 40 * 1482946 * 2
def baseEnd_1482946 : Nat := 338428481183315644735583

theorem tailTrace_1482946 : CollatzResearch.WordTrace tailWord_1482946 prefixEnd_1482946 338428481183315644735583 := by
  unfold tailWord_1482946
  simp only [CollatzResearch.WordTrace]
  refine ⟨13521871021386845964573173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36058322723698255905528461 13521871021386845964573173)
  ·
    refine ⟨1267675408255016809178735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13521871021386845964573173 1267675408255016809178735)
    ·
      refine ⟨1901513112382525213768103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1267675408255016809178735 1901513112382525213768103)
      ·
        refine ⟨2852269668573787820652155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1901513112382525213768103 2852269668573787820652155)
        ·
          refine ⟨4278404502860681730978233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2852269668573787820652155 4278404502860681730978233)
          ·
            refine ⟨3208803377145511298233675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4278404502860681730978233 3208803377145511298233675)
            ·
              refine ⟨4813205065718266947350513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3208803377145511298233675 4813205065718266947350513)
              ·
                refine ⟨3609903799288700210512885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4813205065718266947350513 3609903799288700210512885)
                ·
                  refine ⟨338428481183315644735583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3609903799288700210512885 338428481183315644735583)
                  ·
                    rfl

theorem cell21_1482946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_1482946 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1482946 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1482946 prefixEnd_1482946 := by exact prefixLift 1482946
  have htrace : WordTrace (prefixWord ++ tailWord_1482946) baseStart_1482946 baseEnd_1482946 := by
    simpa [prefixWord, tailWord_1482946, baseEnd_1482946] using wordTrace_append hprefix tailTrace_1482946
  have hstable : (prefixWord ++ tailWord_1482946).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482946).length < 2 ^ (prefixWord ++ tailWord_1482946).sum := by decide
  have hdescent : baseEnd_1482946 < baseStart_1482946 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482985 : List Nat := [1, 2, 1, 1, 1, 2, 2, 5, 6]
def baseStart_1482985 : Nat := 118140960795 + 1482985 * 2 ^ 59
def prefixEnd_1482985 : Nat := 4983230072969 + 3 ^ 40 * 1482985 * 2
def baseEnd_1482985 : Nat := 338437381514660243585503

theorem tailTrace_1482985 : CollatzResearch.WordTrace tailWord_1482985 prefixEnd_1482985 338437381514660243585503 := by
  unfold tailWord_1482985
  simp only [CollatzResearch.WordTrace]
  refine ⟨54088906532406093518962409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36059271021604062345974939 54088906532406093518962409)
  ·
    refine ⟨40566679899304570139221807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54088906532406093518962409 40566679899304570139221807)
    ·
      refine ⟨60850019848956855208832711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40566679899304570139221807 60850019848956855208832711)
      ·
        refine ⟨91275029773435282813249067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60850019848956855208832711 91275029773435282813249067)
        ·
          refine ⟨136912544660152924219873601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91275029773435282813249067 136912544660152924219873601)
          ·
            refine ⟨102684408495114693164905201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136912544660152924219873601 102684408495114693164905201)
            ·
              refine ⟨77013306371336019873678901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102684408495114693164905201 77013306371336019873678901)
              ·
                refine ⟨7219997472312751863157397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 77013306371336019873678901 7219997472312751863157397)
                ·
                  refine ⟨338437381514660243585503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7219997472312751863157397 338437381514660243585503)
                  ·
                    rfl

theorem cell21_1482985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 5, 6].length) (baseStart_1482985 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1482985 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1482985 prefixEnd_1482985 := by exact prefixLift 1482985
  have htrace : WordTrace (prefixWord ++ tailWord_1482985) baseStart_1482985 baseEnd_1482985 := by
    simpa [prefixWord, tailWord_1482985, baseEnd_1482985] using wordTrace_append hprefix tailTrace_1482985
  have hstable : (prefixWord ++ tailWord_1482985).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482985).length < 2 ^ (prefixWord ++ tailWord_1482985).sum := by decide
  have hdescent : baseEnd_1482985 < baseStart_1482985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482988 : List Nat := [2, 2, 1, 1, 2, 3, 1, 6, 3]
def baseStart_1482988 : Nat := 118140960795 + 1482988 * 2 ^ 59
def prefixEnd_1482988 : Nat := 4983230072969 + 3 ^ 40 * 1482988 * 2
def baseEnd_1482988 : Nat := 338438066155532905035497

theorem tailTrace_1482988 : CollatzResearch.WordTrace tailWord_1482988 prefixEnd_1482988 338438066155532905035497 := by
  unfold tailWord_1482988
  simp only [CollatzResearch.WordTrace]
  refine ⟨27044507975697612515660809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36059343967596816687547745 27044507975697612515660809)
  ·
    refine ⟨20283380981773209386745607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27044507975697612515660809 20283380981773209386745607)
    ·
      refine ⟨30425071472659814080118411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20283380981773209386745607 30425071472659814080118411)
      ·
        refine ⟨45637607208989721120177617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30425071472659814080118411 45637607208989721120177617)
        ·
          refine ⟨34228205406742290840133213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45637607208989721120177617 34228205406742290840133213)
          ·
            refine ⟨12835577027528359065049955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34228205406742290840133213 12835577027528359065049955)
            ·
              refine ⟨19253365541292538597574933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12835577027528359065049955 19253365541292538597574933)
              ·
                refine ⟨902501509748087746761325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 19253365541292538597574933 902501509748087746761325)
                ·
                  refine ⟨338438066155532905035497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 902501509748087746761325 338438066155532905035497)
                  ·
                    rfl

theorem cell21_1482988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 6, 3].length) (baseStart_1482988 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1482988 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1482988 prefixEnd_1482988 := by exact prefixLift 1482988
  have htrace : WordTrace (prefixWord ++ tailWord_1482988) baseStart_1482988 baseEnd_1482988 := by
    simpa [prefixWord, tailWord_1482988, baseEnd_1482988] using wordTrace_append hprefix tailTrace_1482988
  have hstable : (prefixWord ++ tailWord_1482988).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482988).length < 2 ^ (prefixWord ++ tailWord_1482988).sum := by decide
  have hdescent : baseEnd_1482988 < baseStart_1482988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483050 : List Nat := [3, 1, 4, 2, 2, 1, 2, 6]
def baseStart_1483050 : Nat := 118140960795 + 1483050 * 2 ^ 59
def prefixEnd_1483050 : Nat := 4983230072969 + 3 ^ 40 * 1483050 * 2
def baseEnd_1483050 : Nat := 112817405133411525000679

theorem tailTrace_1483050 : CollatzResearch.WordTrace tailWord_1483050 prefixEnd_1483050 112817405133411525000679 := by
  unfold tailWord_1483050
  simp only [CollatzResearch.WordTrace]
  refine ⟨13522819319292652405019651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36060851518113739746719069 13522819319292652405019651)
  ·
    refine ⟨20284228978938978607529477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13522819319292652405019651 20284228978938978607529477)
    ·
      refine ⟨3803292933551058488911777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20284228978938978607529477 3803292933551058488911777)
      ·
        refine ⟨2852469700163293866683833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3803292933551058488911777 2852469700163293866683833)
        ·
          refine ⟨2139352275122470400012875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2852469700163293866683833 2139352275122470400012875)
          ·
            refine ⟨3209028412683705600019313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2139352275122470400012875 3209028412683705600019313)
            ·
              refine ⟨2406771309512779200014485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3209028412683705600019313 2406771309512779200014485)
              ·
                refine ⟨112817405133411525000679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2406771309512779200014485 112817405133411525000679)
                ·
                  rfl

theorem cell21_1483050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 2, 6].length) (baseStart_1483050 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1483050 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1483050 prefixEnd_1483050 := by exact prefixLift 1483050
  have htrace : WordTrace (prefixWord ++ tailWord_1483050) baseStart_1483050 baseEnd_1483050 := by
    simpa [prefixWord, tailWord_1483050, baseEnd_1483050] using wordTrace_append hprefix tailTrace_1483050
  have hstable : (prefixWord ++ tailWord_1483050).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483050).length < 2 ^ (prefixWord ++ tailWord_1483050).sum := by decide
  have hdescent : baseEnd_1483050 < baseStart_1483050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483092 : List Nat := [2, 4, 1, 1, 2, 11]
def baseStart_1483092 : Nat := 118140960795 + 1483092 * 2 ^ 59
def prefixEnd_1483092 : Nat := 4983230072969 + 3 ^ 40 * 1483092 * 2
def baseEnd_1483092 : Nat := 12535622236016734640813

theorem tailTrace_1483092 : CollatzResearch.WordTrace tailWord_1483092 prefixEnd_1483092 12535622236016734640813 := by
  unfold tailWord_1483092
  simp only [CollatzResearch.WordTrace]
  refine ⟨27046404571509225396553765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36061872762012300528738353 27046404571509225396553765)
  ·
    refine ⟨5071200857157979761853831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27046404571509225396553765 5071200857157979761853831)
    ·
      refine ⟨7606801285736969642780747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5071200857157979761853831 7606801285736969642780747)
      ·
        refine ⟨11410201928605454464171121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7606801285736969642780747 11410201928605454464171121)
        ·
          refine ⟨8557651446454090848128341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11410201928605454464171121 8557651446454090848128341)
          ·
            refine ⟨12535622236016734640813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 8557651446454090848128341 12535622236016734640813)
            ·
              rfl

theorem cell21_1483092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 11].length) (baseStart_1483092 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1483092 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1483092 prefixEnd_1483092 := by exact prefixLift 1483092
  have htrace : WordTrace (prefixWord ++ tailWord_1483092) baseStart_1483092 baseEnd_1483092 := by
    simpa [prefixWord, tailWord_1483092, baseEnd_1483092] using wordTrace_append hprefix tailTrace_1483092
  have hstable : (prefixWord ++ tailWord_1483092).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483092).length < 2 ^ (prefixWord ++ tailWord_1483092).sum := by decide
  have hdescent : baseEnd_1483092 < baseStart_1483092 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483109 : List Nat := [1, 3, 1, 3, 1, 5, 1, 6]
def baseStart_1483109 : Nat := 118140960795 + 1483109 * 2 ^ 59
def prefixEnd_1483109 : Nat := 4983230072969 + 3 ^ 40 * 1483109 * 2
def baseEnd_1483109 : Nat := 112821893334687861172861

theorem tailTrace_1483109 : CollatzResearch.WordTrace tailWord_1483109 prefixEnd_1483109 112821893334687861172861 := by
  unfold tailWord_1483109
  simp only [CollatzResearch.WordTrace]
  refine ⟨54093429183956862696476381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36062286122637908464317587 54093429183956862696476381)
  ·
    refine ⟨20285035943983823511178643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54093429183956862696476381 20285035943983823511178643)
    ·
      refine ⟨30427553915975735266767965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20285035943983823511178643 30427553915975735266767965)
      ·
        refine ⟨11410332718490900725037987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30427553915975735266767965 11410332718490900725037987)
        ·
          refine ⟨17115499077736351087556981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11410332718490900725037987 17115499077736351087556981)
          ·
            refine ⟨1604578038537782914458467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17115499077736351087556981 1604578038537782914458467)
            ·
              refine ⟨2406867057806674371687701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1604578038537782914458467 2406867057806674371687701)
              ·
                refine ⟨112821893334687861172861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2406867057806674371687701 112821893334687861172861)
                ·
                  rfl

theorem cell21_1483109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 1, 6].length) (baseStart_1483109 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1483109 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1483109 prefixEnd_1483109 := by exact prefixLift 1483109
  have htrace : WordTrace (prefixWord ++ tailWord_1483109) baseStart_1483109 baseEnd_1483109 := by
    simpa [prefixWord, tailWord_1483109, baseEnd_1483109] using wordTrace_append hprefix tailTrace_1483109
  have hstable : (prefixWord ++ tailWord_1483109).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483109).length < 2 ^ (prefixWord ++ tailWord_1483109).sum := by decide
  have hdescent : baseEnd_1483109 < baseStart_1483109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483171 : List Nat := [1, 1, 1, 4, 1, 5, 3, 1, 4]
def baseStart_1483171 : Nat := 118140960795 + 1483171 * 2 ^ 59
def prefixEnd_1483171 : Nat := 4983230072969 + 3 ^ 40 * 1483171 * 2
def baseEnd_1483171 : Nat := 338479829248765253485123

theorem tailTrace_1483171 : CollatzResearch.WordTrace tailWord_1483171 prefixEnd_1483171 338479829248765253485123 := by
  unfold tailWord_1483171
  simp only [CollatzResearch.WordTrace]
  refine ⟨54095690509732247285233367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36063793673154831523488911 54095690509732247285233367)
  ·
    refine ⟨81143535764598370927850051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54095690509732247285233367 81143535764598370927850051)
    ·
      refine ⟨121715303646897556391775077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81143535764598370927850051 121715303646897556391775077)
      ·
        refine ⟨22821619433793291823457827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 121715303646897556391775077 22821619433793291823457827)
        ·
          refine ⟨34232429150689937735186741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22821619433793291823457827 34232429150689937735186741)
          ·
            refine ⟨3209290232877181662673757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34232429150689937735186741 3209290232877181662673757)
            ·
              refine ⟨1203483837328943123502659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3209290232877181662673757 1203483837328943123502659)
              ·
                refine ⟨1805225755993414685253989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1203483837328943123502659 1805225755993414685253989)
                ·
                  refine ⟨338479829248765253485123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1805225755993414685253989 338479829248765253485123)
                  ·
                    rfl

theorem cell21_1483171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 3, 1, 4].length) (baseStart_1483171 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1483171 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1483171 prefixEnd_1483171 := by exact prefixLift 1483171
  have htrace : WordTrace (prefixWord ++ tailWord_1483171) baseStart_1483171 baseEnd_1483171 := by
    simpa [prefixWord, tailWord_1483171, baseEnd_1483171] using wordTrace_append hprefix tailTrace_1483171
  have hstable : (prefixWord ++ tailWord_1483171).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483171).length < 2 ^ (prefixWord ++ tailWord_1483171).sum := by decide
  have hdescent : baseEnd_1483171 < baseStart_1483171 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483185 : List Nat := [1, 2, 2, 4, 1, 2, 4, 5]
def baseStart_1483185 : Nat := 118140960795 + 1483185 * 2 ^ 59
def prefixEnd_1483185 : Nat := 4983230072969 + 3 ^ 40 * 1483185 * 2
def baseEnd_1483185 : Nat := 112827674746501446750587

theorem tailTrace_1483185 : CollatzResearch.WordTrace tailWord_1483185 prefixEnd_1483185 112827674746501446750587 := by
  unfold tailWord_1483185
  simp only [CollatzResearch.WordTrace]
  refine ⟨54096201131681527676243009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36064134087787685117495339 54096201131681527676243009)
  ·
    refine ⟨40572150848761145757182257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54096201131681527676243009 40572150848761145757182257)
    ·
      refine ⟨30429113136570859317886693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40572150848761145757182257 30429113136570859317886693)
      ·
        refine ⟨5705458713107036122103755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30429113136570859317886693 5705458713107036122103755)
        ·
          refine ⟨8558188069660554183155633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5705458713107036122103755 8558188069660554183155633)
          ·
            refine ⟨6418641052245415637366725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8558188069660554183155633 6418641052245415637366725)
            ·
              refine ⟨1203495197296015432006261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6418641052245415637366725 1203495197296015432006261)
              ·
                refine ⟨112827674746501446750587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1203495197296015432006261 112827674746501446750587)
                ·
                  rfl

theorem cell21_1483185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 4, 5].length) (baseStart_1483185 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1483185 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1483185 prefixEnd_1483185 := by exact prefixLift 1483185
  have htrace : WordTrace (prefixWord ++ tailWord_1483185) baseStart_1483185 baseEnd_1483185 := by
    simpa [prefixWord, tailWord_1483185, baseEnd_1483185] using wordTrace_append hprefix tailTrace_1483185
  have hstable : (prefixWord ++ tailWord_1483185).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483185).length < 2 ^ (prefixWord ++ tailWord_1483185).sum := by decide
  have hdescent : baseEnd_1483185 < baseStart_1483185 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483258 : List Nat := [3, 1, 1, 1, 1, 2, 2, 1, 9]
def baseStart_1483258 : Nat := 118140960795 + 1483258 * 2 ^ 59
def prefixEnd_1483258 : Nat := 4983230072969 + 3 ^ 40 * 1483258 * 2
def baseEnd_1483258 : Nat := 338499683834072435534945

theorem tailTrace_1483258 : CollatzResearch.WordTrace tailWord_1483258 prefixEnd_1483258 338499683834072435534945 := by
  unfold tailWord_1483258
  simp only [CollatzResearch.WordTrace]
  refine ⟨13524715915104265285912607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36065909106944707429100285 13524715915104265285912607)
  ·
    refine ⟨20287073872656397928868911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13524715915104265285912607 20287073872656397928868911)
    ·
      refine ⟨30430610808984596893303367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20287073872656397928868911 30430610808984596893303367)
      ·
        refine ⟨45645916213476895339955051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30430610808984596893303367 45645916213476895339955051)
        ·
          refine ⟨68468874320215343009932577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45645916213476895339955051 68468874320215343009932577)
          ·
            refine ⟨51351655740161507257449433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68468874320215343009932577 51351655740161507257449433)
            ·
              refine ⟨38513741805121130443087075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51351655740161507257449433 38513741805121130443087075)
              ·
                refine ⟨57770612707681695664630613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38513741805121130443087075 57770612707681695664630613)
                ·
                  refine ⟨338499683834072435534945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 57770612707681695664630613 338499683834072435534945)
                  ·
                    rfl

theorem cell21_1483258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 9].length) (baseStart_1483258 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1483258 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1483258 prefixEnd_1483258 := by exact prefixLift 1483258
  have htrace : WordTrace (prefixWord ++ tailWord_1483258) baseStart_1483258 baseEnd_1483258 := by
    simpa [prefixWord, tailWord_1483258, baseEnd_1483258] using wordTrace_append hprefix tailTrace_1483258
  have hstable : (prefixWord ++ tailWord_1483258).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483258).length < 2 ^ (prefixWord ++ tailWord_1483258).sum := by decide
  have hdescent : baseEnd_1483258 < baseStart_1483258 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483385 : List Nat := [1, 2, 1, 3, 3, 3, 3, 2, 3]
def baseStart_1483385 : Nat := 118140960795 + 1483385 * 2 ^ 59
def prefixEnd_1483385 : Nat := 4983230072969 + 3 ^ 40 * 1483385 * 2
def baseEnd_1483385 : Nat := 338528666964348436918019

theorem tailTrace_1483385 : CollatzResearch.WordTrace tailWord_1483385 prefixEnd_1483385 338528666964348436918019 := by
  unfold tailWord_1483385
  simp only [CollatzResearch.WordTrace]
  refine ⟨54103495730956961833523609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36068997153971307889015739 54103495730956961833523609)
  ·
    refine ⟨40577621798217721375142707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54103495730956961833523609 40577621798217721375142707)
    ·
      refine ⟨60866432697326582062714061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40577621798217721375142707 60866432697326582062714061)
      ·
        refine ⟨22824912261497468273517773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60866432697326582062714061 22824912261497468273517773)
        ·
          refine ⟨8559342098061550602569165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22824912261497468273517773 8559342098061550602569165)
          ·
            refine ⟨3209753286773081475963437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8559342098061550602569165 3209753286773081475963437)
            ·
              refine ⟨1203657482539905553486289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3209753286773081475963437 1203657482539905553486289)
              ·
                refine ⟨902743111904929165114717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1203657482539905553486289 902743111904929165114717)
                ·
                  refine ⟨338528666964348436918019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 902743111904929165114717 338528666964348436918019)
                  ·
                    rfl

theorem cell21_1483385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 3, 2, 3].length) (baseStart_1483385 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1483385 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1483385 prefixEnd_1483385 := by exact prefixLift 1483385
  have htrace : WordTrace (prefixWord ++ tailWord_1483385) baseStart_1483385 baseEnd_1483385 := by
    simpa [prefixWord, tailWord_1483385, baseEnd_1483385] using wordTrace_append hprefix tailTrace_1483385
  have hstable : (prefixWord ++ tailWord_1483385).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483385).length < 2 ^ (prefixWord ++ tailWord_1483385).sum := by decide
  have hdescent : baseEnd_1483385 < baseStart_1483385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483396 : List Nat := [2, 3, 2, 1, 3, 1, 1, 8]
def baseStart_1483396 : Nat := 118140960795 + 1483396 * 2 ^ 59
def prefixEnd_1483396 : Nat := 4983230072969 + 3 ^ 40 * 1483396 * 2
def baseEnd_1483396 : Nat := 112843725771404954078221

theorem tailTrace_1483396 : CollatzResearch.WordTrace tailWord_1483396 prefixEnd_1483396 112843725771404954078221 := by
  unfold tailWord_1483396
  simp only [CollatzResearch.WordTrace]
  refine ⟨27051948466958555356087021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36069264622611407141449361 27051948466958555356087021)
  ·
    refine ⟨10144480675109458258532633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27051948466958555356087021 10144480675109458258532633)
    ·
      refine ⟨7608360506332093693899475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10144480675109458258532633 7608360506332093693899475)
      ·
        refine ⟨11412540759498140540849213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7608360506332093693899475 11412540759498140540849213)
        ·
          refine ⟨4279702784811802702818455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11412540759498140540849213 4279702784811802702818455)
          ·
            refine ⟨6419554177217704054227683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4279702784811802702818455 6419554177217704054227683)
            ·
              refine ⟨9629331265826556081341525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6419554177217704054227683 9629331265826556081341525)
              ·
                refine ⟨112843725771404954078221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9629331265826556081341525 112843725771404954078221)
                ·
                  rfl

theorem cell21_1483396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 8].length) (baseStart_1483396 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1483396 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1483396 prefixEnd_1483396 := by exact prefixLift 1483396
  have htrace : WordTrace (prefixWord ++ tailWord_1483396) baseStart_1483396 baseEnd_1483396 := by
    simpa [prefixWord, tailWord_1483396, baseEnd_1483396] using wordTrace_append hprefix tailTrace_1483396
  have hstable : (prefixWord ++ tailWord_1483396).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483396).length < 2 ^ (prefixWord ++ tailWord_1483396).sum := by decide
  have hdescent : baseEnd_1483396 < baseStart_1483396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483503 : List Nat := [1, 1, 2, 1, 5, 3, 2, 1, 5]
def baseStart_1483503 : Nat := 118140960795 + 1483503 * 2 ^ 59
def prefixEnd_1483503 : Nat := 4983230072969 + 3 ^ 40 * 1483503 * 2
def baseEnd_1483503 : Nat := 338555596172006453951111

theorem tailTrace_1483503 : CollatzResearch.WordTrace tailWord_1483503 prefixEnd_1483503 338555596172006453951111 := by
  unfold tailWord_1483503
  simp only [CollatzResearch.WordTrace]
  refine ⟨54107799544529467986319163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36071866363019645324212775 54107799544529467986319163)
  ·
    refine ⟨81161699316794201979478745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54107799544529467986319163 81161699316794201979478745)
    ·
      refine ⟨60871274487595651484609059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81161699316794201979478745 60871274487595651484609059)
      ·
        refine ⟨91306911731393477226913589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60871274487595651484609059 91306911731393477226913589)
        ·
          refine ⟨8560022974818138490023149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 91306911731393477226913589 8560022974818138490023149)
          ·
            refine ⟨3210008615556801933758681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8560022974818138490023149 3210008615556801933758681)
            ·
              refine ⟨2407506461667601450319011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3210008615556801933758681 2407506461667601450319011)
              ·
                refine ⟨3611259692501402175478517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2407506461667601450319011 3611259692501402175478517)
                ·
                  refine ⟨338555596172006453951111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3611259692501402175478517 338555596172006453951111)
                  ·
                    rfl

theorem cell21_1483503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2, 1, 5].length) (baseStart_1483503 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1483503 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1483503 prefixEnd_1483503 := by exact prefixLift 1483503
  have htrace : WordTrace (prefixWord ++ tailWord_1483503) baseStart_1483503 baseEnd_1483503 := by
    simpa [prefixWord, tailWord_1483503, baseEnd_1483503] using wordTrace_append hprefix tailTrace_1483503
  have hstable : (prefixWord ++ tailWord_1483503).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483503).length < 2 ^ (prefixWord ++ tailWord_1483503).sum := by decide
  have hdescent : baseEnd_1483503 < baseStart_1483503 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483548 : List Nat := [2, 2, 3, 1, 1, 5, 7]
def baseStart_1483548 : Nat := 118140960795 + 1483548 * 2 ^ 59
def prefixEnd_1483548 : Nat := 4983230072969 + 3 ^ 40 * 1483548 * 2
def baseEnd_1483548 : Nat := 37618429531677375077891

theorem tailTrace_1483548 : CollatzResearch.WordTrace tailWord_1483548 prefixEnd_1483548 37618429531677375077891 := by
  unfold tailWord_1483548
  simp only [CollatzResearch.WordTrace]
  refine ⟨27054720414683220335853649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36072960552910960447804865 27054720414683220335853649)
  ·
    refine ⟨20291040311012415251890237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27054720414683220335853649 20291040311012415251890237)
    ·
      refine ⟨7609140116629655719458839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20291040311012415251890237 7609140116629655719458839)
      ·
        refine ⟨11413710174944483579188259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7609140116629655719458839 11413710174944483579188259)
        ·
          refine ⟨17120565262416725368782389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11413710174944483579188259 17120565262416725368782389)
          ·
            refine ⟨1605052993351568003323349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17120565262416725368782389 1605052993351568003323349)
            ·
              refine ⟨37618429531677375077891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1605052993351568003323349 37618429531677375077891)
              ·
                rfl

theorem cell21_1483548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 7].length) (baseStart_1483548 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1483548 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1483548 prefixEnd_1483548 := by exact prefixLift 1483548
  have htrace : WordTrace (prefixWord ++ tailWord_1483548) baseStart_1483548 baseEnd_1483548 := by
    simpa [prefixWord, tailWord_1483548, baseEnd_1483548] using wordTrace_append hprefix tailTrace_1483548
  have hstable : (prefixWord ++ tailWord_1483548).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483548).length < 2 ^ (prefixWord ++ tailWord_1483548).sum := by decide
  have hdescent : baseEnd_1483548 < baseStart_1483548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483607 : List Nat := [1, 1, 3, 2, 4, 10]
def baseStart_1483607 : Nat := 118140960795 + 1483607 * 2 ^ 59
def prefixEnd_1483607 : Nat := 4983230072969 + 3 ^ 40 * 1483607 * 2
def baseEnd_1483607 : Nat := 12539975199589829045095

theorem tailTrace_1483607 : CollatzResearch.WordTrace tailWord_1483607 prefixEnd_1483607 12539975199589829045095 := by
  unfold tailWord_1483607
  simp only [CollatzResearch.WordTrace]
  refine ⟨54111592736152693748105075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36074395157435129165403383 54111592736152693748105075)
  ·
    refine ⟨81167389104229040622157613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54111592736152693748105075 81167389104229040622157613)
    ·
      refine ⟨30437770914085890233309105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81167389104229040622157613 30437770914085890233309105)
      ·
        refine ⟨22828328185564417674981829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30437770914085890233309105 22828328185564417674981829)
        ·
          refine ⟨4280311534793328314059093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22828328185564417674981829 4280311534793328314059093)
          ·
            refine ⟨12539975199589829045095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4280311534793328314059093 12539975199589829045095)
            ·
              rfl

theorem cell21_1483607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 10].length) (baseStart_1483607 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1483607 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1483607 prefixEnd_1483607 := by exact prefixLift 1483607
  have htrace : WordTrace (prefixWord ++ tailWord_1483607) baseStart_1483607 baseEnd_1483607 := by
    simpa [prefixWord, tailWord_1483607, baseEnd_1483607] using wordTrace_append hprefix tailTrace_1483607
  have hstable : (prefixWord ++ tailWord_1483607).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483607).length < 2 ^ (prefixWord ++ tailWord_1483607).sum := by decide
  have hdescent : baseEnd_1483607 < baseStart_1483607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483610 : List Nat := [3, 1, 1, 2, 1, 5, 2, 2, 4]
def baseStart_1483610 : Nat := 118140960795 + 1483610 * 2 ^ 59
def prefixEnd_1483610 : Nat := 4983230072969 + 3 ^ 40 * 1483610 * 2
def baseEnd_1483610 : Nat := 338580015029798045667559

theorem tailTrace_1483610 : CollatzResearch.WordTrace tailWord_1483610 prefixEnd_1483610 338580015029798045667559 := by
  unfold tailWord_1483610
  simp only [CollatzResearch.WordTrace]
  refine ⟨13527925538785456315116071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36074468103427883506976189 13527925538785456315116071)
  ·
    refine ⟨20291888308178184472674107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13527925538785456315116071 20291888308178184472674107)
    ·
      refine ⟨30437832462267276709011161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20291888308178184472674107 30437832462267276709011161)
      ·
        refine ⟨22828374346700457531758371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30437832462267276709011161 22828374346700457531758371)
        ·
          refine ⟨34242561520050686297637557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22828374346700457531758371 34242561520050686297637557)
          ·
            refine ⟨3210240142504751840403521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34242561520050686297637557 3210240142504751840403521)
            ·
              refine ⟨2407680106878563880302641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3210240142504751840403521 2407680106878563880302641)
              ·
                refine ⟨1805760080158922910226981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2407680106878563880302641 1805760080158922910226981)
                ·
                  refine ⟨338580015029798045667559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1805760080158922910226981 338580015029798045667559)
                  ·
                    rfl

theorem cell21_1483610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2, 2, 4].length) (baseStart_1483610 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1483610 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1483610 prefixEnd_1483610 := by exact prefixLift 1483610
  have htrace : WordTrace (prefixWord ++ tailWord_1483610) baseStart_1483610 baseEnd_1483610 := by
    simpa [prefixWord, tailWord_1483610, baseEnd_1483610] using wordTrace_append hprefix tailTrace_1483610
  have hstable : (prefixWord ++ tailWord_1483610).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483610).length < 2 ^ (prefixWord ++ tailWord_1483610).sum := by decide
  have hdescent : baseEnd_1483610 < baseStart_1483610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483624 : List Nat := [2, 1, 4, 2, 1, 2, 3, 6]
def baseStart_1483624 : Nat := 118140960795 + 1483624 * 2 ^ 59
def prefixEnd_1483624 : Nat := 4983230072969 + 3 ^ 40 * 1483624 * 2
def baseEnd_1483624 : Nat := 112861070006845710811399

theorem tailTrace_1483624 : CollatzResearch.WordTrace tailWord_1483624 prefixEnd_1483624 112861070006845710811399 := by
  unfold tailWord_1483624
  simp only [CollatzResearch.WordTrace]
  refine ⟨27056106388545552825736963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36074808518060737100982617 27056106388545552825736963)
  ·
    refine ⟨40584159582818329238605445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27056106388545552825736963 40584159582818329238605445)
    ·
      refine ⟨7609529921778436732238521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40584159582818329238605445 7609529921778436732238521)
      ·
        refine ⟨5707147441333827549178891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7609529921778436732238521 5707147441333827549178891)
        ·
          refine ⟨8560721162000741323768337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5707147441333827549178891 8560721162000741323768337)
          ·
            refine ⟨6420540871500555992826253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8560721162000741323768337 6420540871500555992826253)
            ·
              refine ⟨2407702826812708497309845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6420540871500555992826253 2407702826812708497309845)
              ·
                refine ⟨112861070006845710811399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2407702826812708497309845 112861070006845710811399)
                ·
                  rfl

theorem cell21_1483624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3, 6].length) (baseStart_1483624 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1483624 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1483624 prefixEnd_1483624 := by exact prefixLift 1483624
  have htrace : WordTrace (prefixWord ++ tailWord_1483624) baseStart_1483624 baseEnd_1483624 := by
    simpa [prefixWord, tailWord_1483624, baseEnd_1483624] using wordTrace_append hprefix tailTrace_1483624
  have hstable : (prefixWord ++ tailWord_1483624).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483624).length < 2 ^ (prefixWord ++ tailWord_1483624).sum := by decide
  have hdescent : baseEnd_1483624 < baseStart_1483624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483669 : List Nat := [1, 3, 2, 1, 1, 5, 1, 1, 6]
def baseStart_1483669 : Nat := 118140960795 + 1483669 * 2 ^ 59
def prefixEnd_1483669 : Nat := 4983230072969 + 3 ^ 40 * 1483669 * 2
def baseEnd_1483669 : Nat := 338593479633627054184105

theorem tailTrace_1483669 : CollatzResearch.WordTrace tailWord_1483669 prefixEnd_1483669 338593479633627054184105 := by
  unfold tailWord_1483669
  simp only [CollatzResearch.WordTrace]
  refine ⟨54113854061928078336862061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36075902707952052224574707 54113854061928078336862061)
  ·
    refine ⟨20292695273223029376323273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54113854061928078336862061 20292695273223029376323273)
    ·
      refine ⟨15219521454917272032242455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20292695273223029376323273 15219521454917272032242455)
      ·
        refine ⟨22829282182375908048363683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15219521454917272032242455 22829282182375908048363683)
        ·
          refine ⟨34243923273563862072545525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22829282182375908048363683 34243923273563862072545525)
          ·
            refine ⟨3210367806896612069301143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34243923273563862072545525 3210367806896612069301143)
            ·
              refine ⟨4815551710344918103951715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3210367806896612069301143 4815551710344918103951715)
              ·
                refine ⟨7223327565517377155927573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4815551710344918103951715 7223327565517377155927573)
                ·
                  refine ⟨338593479633627054184105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7223327565517377155927573 338593479633627054184105)
                  ·
                    rfl

theorem cell21_1483669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 1, 6].length) (baseStart_1483669 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1483669 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1483669 prefixEnd_1483669 := by exact prefixLift 1483669
  have htrace : WordTrace (prefixWord ++ tailWord_1483669) baseStart_1483669 baseEnd_1483669 := by
    simpa [prefixWord, tailWord_1483669, baseEnd_1483669] using wordTrace_append hprefix tailTrace_1483669
  have hstable : (prefixWord ++ tailWord_1483669).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483669).length < 2 ^ (prefixWord ++ tailWord_1483669).sum := by decide
  have hdescent : baseEnd_1483669 < baseStart_1483669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483759 : List Nat := [1, 1, 2, 1, 4, 3, 2, 7]
def baseStart_1483759 : Nat := 118140960795 + 1483759 * 2 ^ 59
def prefixEnd_1483759 : Nat := 4983230072969 + 3 ^ 40 * 1483759 * 2
def baseEnd_1483759 : Nat := 112871339619935632561307

theorem tailTrace_1483759 : CollatzResearch.WordTrace tailWord_1483759 prefixEnd_1483759 112871339619935632561307 := by
  unfold tailWord_1483759
  simp only [CollatzResearch.WordTrace]
  refine ⟨54117136631602023707638331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36078091087734682471758887 54117136631602023707638331)
  ·
    refine ⟨81175704947403035561457497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54117136631602023707638331 81175704947403035561457497)
    ·
      refine ⟨60881778710552276671093123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81175704947403035561457497 60881778710552276671093123)
      ·
        refine ⟨91322668065828415006639685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60881778710552276671093123 91322668065828415006639685)
        ·
          refine ⟨17123000262342827813744941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 91322668065828415006639685 17123000262342827813744941)
          ·
            refine ⟨6421125098378560430154353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17123000262342827813744941 6421125098378560430154353)
            ·
              refine ⟨4815843823783920322615765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6421125098378560430154353 4815843823783920322615765)
              ·
                refine ⟨112871339619935632561307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4815843823783920322615765 112871339619935632561307)
                ·
                  rfl

theorem cell21_1483759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 7].length) (baseStart_1483759 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1483759 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1483759 prefixEnd_1483759 := by exact prefixLift 1483759
  have htrace : WordTrace (prefixWord ++ tailWord_1483759) baseStart_1483759 baseEnd_1483759 := by
    simpa [prefixWord, tailWord_1483759, baseEnd_1483759] using wordTrace_append hprefix tailTrace_1483759
  have hstable : (prefixWord ++ tailWord_1483759).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483759).length < 2 ^ (prefixWord ++ tailWord_1483759).sum := by decide
  have hdescent : baseEnd_1483759 < baseStart_1483759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483838 : List Nat := [4, 2, 1, 3, 1, 2, 1, 1, 6]
def baseStart_1483838 : Nat := 118140960795 + 1483838 * 2 ^ 59
def prefixEnd_1483838 : Nat := 4983230072969 + 3 ^ 40 * 1483838 * 2
def baseEnd_1483838 : Nat := 338632047736120315867093

theorem tailTrace_1483838 : CollatzResearch.WordTrace tailWord_1483838 prefixEnd_1483838 338632047736120315867093 := by
  unfold tailWord_1483838
  simp only [CollatzResearch.WordTrace]
  refine ⟨6765002249789477524970521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36080011998877213466509445 6765002249789477524970521)
  ·
    refine ⟨5073751687342108143727891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6765002249789477524970521 5073751687342108143727891)
    ·
      refine ⟨7610627531013162215591837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5073751687342108143727891 7610627531013162215591837)
      ·
        refine ⟨2853985324129935830846939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7610627531013162215591837 2853985324129935830846939)
        ·
          refine ⟨4280977986194903746270409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2853985324129935830846939 4280977986194903746270409)
          ·
            refine ⟨3210733489646177809702807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4280977986194903746270409 3210733489646177809702807)
            ·
              refine ⟨4816100234469266714554211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3210733489646177809702807 4816100234469266714554211)
              ·
                refine ⟨7224150351703900071831317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4816100234469266714554211 7224150351703900071831317)
                ·
                  refine ⟨338632047736120315867093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7224150351703900071831317 338632047736120315867093)
                  ·
                    rfl

theorem cell21_1483838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 1, 6].length) (baseStart_1483838 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1483838 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1483838 prefixEnd_1483838 := by exact prefixLift 1483838
  have htrace : WordTrace (prefixWord ++ tailWord_1483838) baseStart_1483838 baseEnd_1483838 := by
    simpa [prefixWord, tailWord_1483838, baseEnd_1483838] using wordTrace_append hprefix tailTrace_1483838
  have hstable : (prefixWord ++ tailWord_1483838).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483838).length < 2 ^ (prefixWord ++ tailWord_1483838).sum := by decide
  have hdescent : baseEnd_1483838 < baseStart_1483838 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483869 : List Nat := [1, 4, 4, 1, 2, 1, 1, 7]
def baseStart_1483869 : Nat := 118140960795 + 1483869 * 2 ^ 59
def prefixEnd_1483869 : Nat := 4983230072969 + 3 ^ 40 * 1483869 * 2
def baseEnd_1483869 : Nat := 112879707452823716950121

theorem tailTrace_1483869 : CollatzResearch.WordTrace tailWord_1483869 prefixEnd_1483869 112879707452823716950121 := by
  unfold tailWord_1483869
  simp only [CollatzResearch.WordTrace]
  refine ⟨54121148661203512494142661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36080765774135674996095107 54121148661203512494142661)
  ·
    refine ⟨10147715373975658592651749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54121148661203512494142661 10147715373975658592651749)
    ·
      refine ⟨1902696632620435986122203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10147715373975658592651749 1902696632620435986122203)
      ·
        refine ⟨2854044948930653979183305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1902696632620435986122203 2854044948930653979183305)
        ·
          refine ⟨2140533711697990484387479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2854044948930653979183305 2140533711697990484387479)
          ·
            refine ⟨3210800567546985726581219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2140533711697990484387479 3210800567546985726581219)
            ·
              refine ⟨4816200851320478589871829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3210800567546985726581219 4816200851320478589871829)
              ·
                refine ⟨112879707452823716950121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4816200851320478589871829 112879707452823716950121)
                ·
                  rfl

theorem cell21_1483869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 7].length) (baseStart_1483869 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1483869 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1483869 prefixEnd_1483869 := by exact prefixLift 1483869
  have htrace : WordTrace (prefixWord ++ tailWord_1483869) baseStart_1483869 baseEnd_1483869 := by
    simpa [prefixWord, tailWord_1483869, baseEnd_1483869] using wordTrace_append hprefix tailTrace_1483869
  have hstable : (prefixWord ++ tailWord_1483869).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483869).length < 2 ^ (prefixWord ++ tailWord_1483869).sum := by decide
  have hdescent : baseEnd_1483869 < baseStart_1483869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483900 : List Nat := [2, 2, 2, 1, 1, 3, 5, 2, 3]
def baseStart_1483900 : Nat := 118140960795 + 1483900 * 2 ^ 59
def prefixEnd_1483900 : Nat := 4983230072969 + 3 ^ 40 * 1483900 * 2
def baseEnd_1483900 : Nat := 338646196980821985833633

theorem tailTrace_1483900 : CollatzResearch.WordTrace tailWord_1483900 prefixEnd_1483900 338646196980821985833633 := by
  unfold tailWord_1483900
  simp only [CollatzResearch.WordTrace]
  refine ⟨27061139662045602394260577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36081519549394136525680769 27061139662045602394260577)
  ·
    refine ⟨20295854746534201795695433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27061139662045602394260577 20295854746534201795695433)
    ·
      refine ⟨15221891059900651346771575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20295854746534201795695433 15221891059900651346771575)
      ·
        refine ⟨22832836589850977020157363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15221891059900651346771575 22832836589850977020157363)
        ·
          refine ⟨34249254884776465530236045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22832836589850977020157363 34249254884776465530236045)
          ·
            refine ⟨12843470581791174573838517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34249254884776465530236045 12843470581791174573838517)
            ·
              refine ⟨1204075367042922616297361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12843470581791174573838517 1204075367042922616297361)
              ·
                refine ⟨903056525282191962223021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1204075367042922616297361 903056525282191962223021)
                ·
                  refine ⟨338646196980821985833633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 903056525282191962223021 338646196980821985833633)
                  ·
                    rfl

theorem cell21_1483900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 5, 2, 3].length) (baseStart_1483900 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1483900 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1483900 prefixEnd_1483900 := by exact prefixLift 1483900
  have htrace : WordTrace (prefixWord ++ tailWord_1483900) baseStart_1483900 baseEnd_1483900 := by
    simpa [prefixWord, tailWord_1483900, baseEnd_1483900] using wordTrace_append hprefix tailTrace_1483900
  have hstable : (prefixWord ++ tailWord_1483900).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483900).length < 2 ^ (prefixWord ++ tailWord_1483900).sum := by decide
  have hdescent : baseEnd_1483900 < baseStart_1483900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483959 : List Nat := [1, 1, 3, 1, 4, 1, 3, 4, 3]
def baseStart_1483959 : Nat := 118140960795 + 1483959 * 2 ^ 59
def prefixEnd_1483959 : Nat := 4983230072969 + 3 ^ 40 * 1483959 * 2
def baseEnd_1483959 : Nat := 338659661584650994350179

theorem tailTrace_1483959 : CollatzResearch.WordTrace tailWord_1483959 prefixEnd_1483959 338659661584650994350179 := by
  unfold tailWord_1483959
  simp only [CollatzResearch.WordTrace]
  refine ⟨54124431230877457864918931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36082954153918305243279287 54124431230877457864918931)
  ·
    refine ⟨81186646846316186797378397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54124431230877457864918931 81186646846316186797378397)
    ·
      refine ⟨30444992567368570049016899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81186646846316186797378397 30444992567368570049016899)
      ·
        refine ⟨45667488851052855073525349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30444992567368570049016899 45667488851052855073525349)
        ·
          refine ⟨8562654159572410326286003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45667488851052855073525349 8562654159572410326286003)
          ·
            refine ⟨12843981239358615489429005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8562654159572410326286003 12843981239358615489429005)
            ·
              refine ⟨4816492964759480808535877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12843981239358615489429005 4816492964759480808535877)
              ·
                refine ⟨903092430892402651600477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4816492964759480808535877 903092430892402651600477)
                ·
                  refine ⟨338659661584650994350179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 903092430892402651600477 338659661584650994350179)
                  ·
                    rfl

theorem cell21_1483959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 4, 3].length) (baseStart_1483959 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1483959 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1483959 prefixEnd_1483959 := by exact prefixLift 1483959
  have htrace : WordTrace (prefixWord ++ tailWord_1483959) baseStart_1483959 baseEnd_1483959 := by
    simpa [prefixWord, tailWord_1483959, baseEnd_1483959] using wordTrace_append hprefix tailTrace_1483959
  have hstable : (prefixWord ++ tailWord_1483959).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483959).length < 2 ^ (prefixWord ++ tailWord_1483959).sum := by decide
  have hdescent : baseEnd_1483959 < baseStart_1483959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484007 : List Nat := [1, 1, 5, 3, 2, 2, 1, 2, 4]
def baseStart_1484007 : Nat := 118140960795 + 1484007 * 2 ^ 59
def prefixEnd_1484007 : Nat := 4983230072969 + 3 ^ 40 * 1484007 * 2
def baseEnd_1484007 : Nat := 338670615838613577550081

theorem tailTrace_1484007 : CollatzResearch.WordTrace tailWord_1484007 prefixEnd_1484007 338670615838613577550081 := by
  unfold tailWord_1484007
  simp only [CollatzResearch.WordTrace]
  refine ⟨54126181934703562062666275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36084121289802374708444183 54126181934703562062666275)
  ·
    refine ⟨81189272902055343093999413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54126181934703562062666275 81189272902055343093999413)
    ·
      refine ⟨7611494334567688415062445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 81189272902055343093999413 7611494334567688415062445)
      ·
        refine ⟨2854310375462883155648417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7611494334567688415062445 2854310375462883155648417)
        ·
          refine ⟨2140732781597162366736313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2854310375462883155648417 2140732781597162366736313)
          ·
            refine ⟨1605549586197871775052235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2140732781597162366736313 1605549586197871775052235)
            ·
              refine ⟨2408324379296807662578353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1605549586197871775052235 2408324379296807662578353)
              ·
                refine ⟨1806243284472605746933765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2408324379296807662578353 1806243284472605746933765)
                ·
                  refine ⟨338670615838613577550081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1806243284472605746933765 338670615838613577550081)
                  ·
                    rfl

theorem cell21_1484007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 1, 2, 4].length) (baseStart_1484007 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1484007 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1484007 prefixEnd_1484007 := by exact prefixLift 1484007
  have htrace : WordTrace (prefixWord ++ tailWord_1484007) baseStart_1484007 baseEnd_1484007 := by
    simpa [prefixWord, tailWord_1484007, baseEnd_1484007] using wordTrace_append hprefix tailTrace_1484007
  have hstable : (prefixWord ++ tailWord_1484007).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484007).length < 2 ^ (prefixWord ++ tailWord_1484007).sum := by decide
  have hdescent : baseEnd_1484007 < baseStart_1484007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484094 : List Nat := [4, 2, 1, 2, 1, 1, 2, 1, 7]
def baseStart_1484094 : Nat := 118140960795 + 1484094 * 2 ^ 59
def prefixEnd_1484094 : Nat := 4983230072969 + 3 ^ 40 * 1484094 * 2
def baseEnd_1484094 : Nat := 338690470423920759599903

theorem tailTrace_1484094 : CollatzResearch.WordTrace tailWord_1484094 prefixEnd_1484094 338690470423920759599903 := by
  unfold tailWord_1484094
  simp only [CollatzResearch.WordTrace]
  refine ⟨6766169385673546990135417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36086236723592250614055557 6766169385673546990135417)
  ·
    refine ⟨5074627039255160242601563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6766169385673546990135417 5074627039255160242601563)
    ·
      refine ⟨7611940558882740363902345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5074627039255160242601563 7611940558882740363902345)
      ·
        refine ⟨5708955419162055272926759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7611940558882740363902345 5708955419162055272926759)
        ·
          refine ⟨8563433128743082909390139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5708955419162055272926759 8563433128743082909390139)
          ·
            refine ⟨12845149693114624364085209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8563433128743082909390139 12845149693114624364085209)
            ·
              refine ⟨9633862269835968273063907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12845149693114624364085209 9633862269835968273063907)
              ·
                refine ⟨14450793404753952409595861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9633862269835968273063907 14450793404753952409595861)
                ·
                  refine ⟨338690470423920759599903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14450793404753952409595861 338690470423920759599903)
                  ·
                    rfl

theorem cell21_1484094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_1484094 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1484094 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1484094 prefixEnd_1484094 := by exact prefixLift 1484094
  have htrace : WordTrace (prefixWord ++ tailWord_1484094) baseStart_1484094 baseEnd_1484094 := by
    simpa [prefixWord, tailWord_1484094, baseEnd_1484094] using wordTrace_append hprefix tailTrace_1484094
  have hstable : (prefixWord ++ tailWord_1484094).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484094).length < 2 ^ (prefixWord ++ tailWord_1484094).sum := by decide
  have hdescent : baseEnd_1484094 < baseStart_1484094 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484128 : List Nat := [2, 1, 1, 3, 4, 1, 4, 2, 3]
def baseStart_1484128 : Nat := 118140960795 + 1484128 * 2 ^ 59
def prefixEnd_1484128 : Nat := 4983230072969 + 3 ^ 40 * 1484128 * 2
def baseEnd_1484128 : Nat := 338698229687144256033167

theorem tailTrace_1484128 : CollatzResearch.WordTrace tailWord_1484128 prefixEnd_1484128 338698229687144256033167 := by
  unfold tailWord_1484128
  simp only [CollatzResearch.WordTrace]
  refine ⟨27065297583632599863910519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36087063444843466485214025 27065297583632599863910519)
  ·
    refine ⟨40597946375448899795865779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27065297583632599863910519 40597946375448899795865779)
    ·
      refine ⟨60896919563173349693798669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40597946375448899795865779 60896919563173349693798669)
      ·
        refine ⟨22836344836190006135174501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60896919563173349693798669 22836344836190006135174501)
        ·
          refine ⟨4281814656785626150345219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22836344836190006135174501 4281814656785626150345219)
          ·
            refine ⟨6422721985178439225517829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4281814656785626150345219 6422721985178439225517829)
            ·
              refine ⟨1204260372220957354784593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6422721985178439225517829 1204260372220957354784593)
              ·
                refine ⟨903195279165718016088445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1204260372220957354784593 903195279165718016088445)
                ·
                  refine ⟨338698229687144256033167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 903195279165718016088445 338698229687144256033167)
                  ·
                    rfl

theorem cell21_1484128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 4, 2, 3].length) (baseStart_1484128 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1484128 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1484128 prefixEnd_1484128 := by exact prefixLift 1484128
  have htrace : WordTrace (prefixWord ++ tailWord_1484128) baseStart_1484128 baseEnd_1484128 := by
    simpa [prefixWord, tailWord_1484128, baseEnd_1484128] using wordTrace_append hprefix tailTrace_1484128
  have hstable : (prefixWord ++ tailWord_1484128).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484128).length < 2 ^ (prefixWord ++ tailWord_1484128).sum := by decide
  have hdescent : baseEnd_1484128 < baseStart_1484128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484153 : List Nat := [1, 2, 1, 3, 2, 1, 3, 1, 7]
def baseStart_1484153 : Nat := 118140960795 + 1484153 * 2 ^ 59
def prefixEnd_1484153 : Nat := 4983230072969 + 3 ^ 40 * 1484153 * 2
def baseEnd_1484153 : Nat := 338703935027749768116449

theorem tailTrace_1484153 : CollatzResearch.WordTrace tailWord_1484153 prefixEnd_1484153 338703935027749768116449 := by
  unfold tailWord_1484153
  simp only [CollatzResearch.WordTrace]
  refine ⟨54131506992174628997481113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36087671328116419331654075 54131506992174628997481113)
  ·
    refine ⟨40598630244130971748110835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54131506992174628997481113 40598630244130971748110835)
    ·
      refine ⟨60897945366196457622166253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40598630244130971748110835 60897945366196457622166253)
      ·
        refine ⟨22836729512323671608312345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60897945366196457622166253 22836729512323671608312345)
        ·
          refine ⟨17127547134242753706234259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22836729512323671608312345 17127547134242753706234259)
          ·
            refine ⟨25691320701364130559351389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17127547134242753706234259 25691320701364130559351389)
            ·
              refine ⟨9634245263011548959756771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25691320701364130559351389 9634245263011548959756771)
              ·
                refine ⟨14451367894517323439635157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9634245263011548959756771 14451367894517323439635157)
                ·
                  refine ⟨338703935027749768116449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14451367894517323439635157 338703935027749768116449)
                  ·
                    rfl

theorem cell21_1484153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 1, 7].length) (baseStart_1484153 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1484153 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1484153 prefixEnd_1484153 := by exact prefixLift 1484153
  have htrace : WordTrace (prefixWord ++ tailWord_1484153) baseStart_1484153 baseEnd_1484153 := by
    simpa [prefixWord, tailWord_1484153, baseEnd_1484153] using wordTrace_append hprefix tailTrace_1484153
  have hstable : (prefixWord ++ tailWord_1484153).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484153).length < 2 ^ (prefixWord ++ tailWord_1484153).sum := by decide
  have hdescent : baseEnd_1484153 < baseStart_1484153 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484305 : List Nat := [1, 2, 2, 1, 1, 2, 4, 3, 5]
def baseStart_1484305 : Nat := 118140960795 + 1484305 * 2 ^ 59
def prefixEnd_1484305 : Nat := 4983230072969 + 3 ^ 40 * 1484305 * 2
def baseEnd_1484305 : Nat := 338738623498631281582805

theorem tailTrace_1484305 : CollatzResearch.WordTrace tailWord_1484305 prefixEnd_1484305 338738623498631281582805 := by
  unfold tailWord_1484305
  simp only [CollatzResearch.WordTrace]
  refine ⟨54137050887623958957014369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36091367258415972638009579 54137050887623958957014369)
  ·
    refine ⟨40602788165717969217760777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54137050887623958957014369 40602788165717969217760777)
    ·
      refine ⟨30452091124288476913320583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40602788165717969217760777 30452091124288476913320583)
      ·
        refine ⟨45678136686432715369980875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30452091124288476913320583 45678136686432715369980875)
        ·
          refine ⟨68517205029649073054971313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45678136686432715369980875 68517205029649073054971313)
          ·
            refine ⟨51387903772236804791228485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68517205029649073054971313 51387903772236804791228485)
            ·
              refine ⟨9635231957294400898355341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51387903772236804791228485 9635231957294400898355341)
              ·
                refine ⟨3613211983985400336883253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9635231957294400898355341 3613211983985400336883253)
                ·
                  refine ⟨338738623498631281582805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3613211983985400336883253 338738623498631281582805)
                  ·
                    rfl

theorem cell21_1484305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 3, 5].length) (baseStart_1484305 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1484305 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1484305 prefixEnd_1484305 := by exact prefixLift 1484305
  have htrace : WordTrace (prefixWord ++ tailWord_1484305) baseStart_1484305 baseEnd_1484305 := by
    simpa [prefixWord, tailWord_1484305, baseEnd_1484305] using wordTrace_append hprefix tailTrace_1484305
  have hstable : (prefixWord ++ tailWord_1484305).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484305).length < 2 ^ (prefixWord ++ tailWord_1484305).sum := by decide
  have hdescent : baseEnd_1484305 < baseStart_1484305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484339 : List Nat := [1, 1, 1, 2, 4, 4, 2, 3, 3]
def baseStart_1484339 : Nat := 118140960795 + 1484339 * 2 ^ 59
def prefixEnd_1484339 : Nat := 4983230072969 + 3 ^ 40 * 1484339 * 2
def baseEnd_1484339 : Nat := 338746382761854778016069

theorem tailTrace_1484339 : CollatzResearch.WordTrace tailWord_1484339 prefixEnd_1484339 338746382761854778016069 := by
  unfold tailWord_1484339
  simp only [CollatzResearch.WordTrace]
  refine ⟨54138290969500782763752071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36092193979667188509168047 54138290969500782763752071)
  ·
    refine ⟨81207436454251174145628107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54138290969500782763752071 81207436454251174145628107)
    ·
      refine ⟨121811154681376761218442161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81207436454251174145628107 121811154681376761218442161)
      ·
        refine ⟨91358366011032570913831621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121811154681376761218442161 91358366011032570913831621)
        ·
          refine ⟨17129693627068607046343429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 91358366011032570913831621 17129693627068607046343429)
          ·
            refine ⟨3211817555075363821189393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17129693627068607046343429 3211817555075363821189393)
            ·
              refine ⟨2408863166306522865892045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3211817555075363821189393 2408863166306522865892045)
              ·
                refine ⟨903323687364946074709517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2408863166306522865892045 903323687364946074709517)
                ·
                  refine ⟨338746382761854778016069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 903323687364946074709517 338746382761854778016069)
                  ·
                    rfl

theorem cell21_1484339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2, 3, 3].length) (baseStart_1484339 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1484339 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1484339 prefixEnd_1484339 := by exact prefixLift 1484339
  have htrace : WordTrace (prefixWord ++ tailWord_1484339) baseStart_1484339 baseEnd_1484339 := by
    simpa [prefixWord, tailWord_1484339, baseEnd_1484339] using wordTrace_append hprefix tailTrace_1484339
  have hstable : (prefixWord ++ tailWord_1484339).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484339).length < 2 ^ (prefixWord ++ tailWord_1484339).sum := by decide
  have hdescent : baseEnd_1484339 < baseStart_1484339 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484370 : List Nat := [3, 2, 2, 1, 2, 3, 3, 1, 4]
def baseStart_1484370 : Nat := 118140960795 + 1484370 * 2 ^ 59
def prefixEnd_1484370 : Nat := 4983230072969 + 3 ^ 40 * 1484370 * 2
def baseEnd_1484370 : Nat := 338753457384205612999339

theorem tailTrace_1484370 : CollatzResearch.WordTrace tailWord_1484370 prefixEnd_1484370 338753457384205612999339 := by
  unfold tailWord_1484370
  simp only [CollatzResearch.WordTrace]
  refine ⟨13534855408097118764532641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36092947754925650038753709 13534855408097118764532641)
  ·
    refine ⟨10151141556072839073399481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13534855408097118764532641 10151141556072839073399481)
    ·
      refine ⟨7613356167054629305049611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10151141556072839073399481 7613356167054629305049611)
      ·
        refine ⟨11420034250581943957574417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7613356167054629305049611 11420034250581943957574417)
        ·
          refine ⟨8565025687936457968180813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11420034250581943957574417 8565025687936457968180813)
          ·
            refine ⟨3211884632976171738067805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8565025687936457968180813 3211884632976171738067805)
            ·
              refine ⟨1204456737366064401775427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3211884632976171738067805 1204456737366064401775427)
              ·
                refine ⟨1806685106049096602663141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1204456737366064401775427 1806685106049096602663141)
                ·
                  refine ⟨338753457384205612999339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1806685106049096602663141 338753457384205612999339)
                  ·
                    rfl

theorem cell21_1484370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 3, 1, 4].length) (baseStart_1484370 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1484370 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1484370 prefixEnd_1484370 := by exact prefixLift 1484370
  have htrace : WordTrace (prefixWord ++ tailWord_1484370) baseStart_1484370 baseEnd_1484370 := by
    simpa [prefixWord, tailWord_1484370, baseEnd_1484370] using wordTrace_append hprefix tailTrace_1484370
  have hstable : (prefixWord ++ tailWord_1484370).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484370).length < 2 ^ (prefixWord ++ tailWord_1484370).sum := by decide
  have hdescent : baseEnd_1484370 < baseStart_1484370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484412 : List Nat := [2, 2, 2, 1, 1, 2, 1, 6, 4]
def baseStart_1484412 : Nat := 118140960795 + 1484412 * 2 ^ 59
def prefixEnd_1484412 : Nat := 4983230072969 + 3 ^ 40 * 1484412 * 2
def baseEnd_1484412 : Nat := 338763042356422873299253

theorem tailTrace_1484412 : CollatzResearch.WordTrace tailWord_1484412 prefixEnd_1484412 338763042356422873299253 := by
  unfold tailWord_1484412
  simp only [CollatzResearch.WordTrace]
  refine ⟨27070476749118158115579745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36093968998824210820772993 27070476749118158115579745)
  ·
    refine ⟨20302857561838618586684809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27070476749118158115579745 20302857561838618586684809)
    ·
      refine ⟨15227143171378963940013607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20302857561838618586684809 15227143171378963940013607)
      ·
        refine ⟨22840714757068445910020411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15227143171378963940013607 22840714757068445910020411)
        ·
          refine ⟨34261072135602668865030617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22840714757068445910020411 34261072135602668865030617)
          ·
            refine ⟨25695804101702001648772963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34261072135602668865030617 25695804101702001648772963)
            ·
              refine ⟨38543706152553002473159445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25695804101702001648772963 38543706152553002473159445)
              ·
                refine ⟨1806736225900921990929349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 38543706152553002473159445 1806736225900921990929349)
                ·
                  refine ⟨338763042356422873299253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1806736225900921990929349 338763042356422873299253)
                  ·
                    rfl

theorem cell21_1484412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 6, 4].length) (baseStart_1484412 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1484412 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1484412 prefixEnd_1484412 := by exact prefixLift 1484412
  have htrace : WordTrace (prefixWord ++ tailWord_1484412) baseStart_1484412 baseEnd_1484412 := by
    simpa [prefixWord, tailWord_1484412, baseEnd_1484412] using wordTrace_append hprefix tailTrace_1484412
  have hstable : (prefixWord ++ tailWord_1484412).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484412).length < 2 ^ (prefixWord ++ tailWord_1484412).sum := by decide
  have hdescent : baseEnd_1484412 < baseStart_1484412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484488 : List Nat := [2, 1, 3, 1, 2, 2, 1, 5, 4]
def baseStart_1484488 : Nat := 118140960795 + 1484488 * 2 ^ 59
def prefixEnd_1484488 : Nat := 4983230072969 + 3 ^ 40 * 1484488 * 2
def baseEnd_1484488 : Nat := 338780386591863630032431

theorem tailTrace_1484488 : CollatzResearch.WordTrace tailWord_1484488 prefixEnd_1484488 338780386591863630032431 := by
  unfold tailWord_1484488
  simp only [CollatzResearch.WordTrace]
  refine ⟨27071862722980490605463059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36095816963973987473950745 27071862722980490605463059)
  ·
    refine ⟨40607794084470735908194589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27071862722980490605463059 40607794084470735908194589)
    ·
      refine ⟨15227922781676525965572971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40607794084470735908194589 15227922781676525965572971)
      ·
        refine ⟨22841884172514788948359457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15227922781676525965572971 22841884172514788948359457)
        ·
          refine ⟨17131413129386091711269593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22841884172514788948359457 17131413129386091711269593)
          ·
            refine ⟨12848559847039568783452195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17131413129386091711269593 12848559847039568783452195)
            ·
              refine ⟨19272839770559353175178293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12848559847039568783452195 19272839770559353175178293)
              ·
                refine ⟨1806828728489939360172965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19272839770559353175178293 1806828728489939360172965)
                ·
                  refine ⟨338780386591863630032431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1806828728489939360172965 338780386591863630032431)
                  ·
                    rfl

theorem cell21_1484488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 5, 4].length) (baseStart_1484488 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1484488 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1484488 prefixEnd_1484488 := by exact prefixLift 1484488
  have htrace : WordTrace (prefixWord ++ tailWord_1484488) baseStart_1484488 baseEnd_1484488 := by
    simpa [prefixWord, tailWord_1484488, baseEnd_1484488] using wordTrace_append hprefix tailTrace_1484488
  have hstable : (prefixWord ++ tailWord_1484488).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484488).length < 2 ^ (prefixWord ++ tailWord_1484488).sum := by decide
  have hdescent : baseEnd_1484488 < baseStart_1484488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484567 : List Nat := [1, 1, 3, 4, 2, 1, 3, 3, 3]
def baseStart_1484567 : Nat := 118140960795 + 1484567 * 2 ^ 59
def prefixEnd_1484567 : Nat := 4983230072969 + 3 ^ 40 * 1484567 * 2
def baseEnd_1484567 : Nat := 338798415468177048215603

theorem tailTrace_1484567 : CollatzResearch.WordTrace tailWord_1484567 prefixEnd_1484567 338798415468177048215603 := by
  unfold tailWord_1484567
  simp only [CollatzResearch.WordTrace]
  refine ⟨54146606812674777703051955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36097737875116518468701303 54146606812674777703051955)
  ·
    refine ⟨81219910219012166554577933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54146606812674777703051955 81219910219012166554577933)
    ·
      refine ⟨30457466332129562457966725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81219910219012166554577933 30457466332129562457966725)
      ·
        refine ⟨5710774937274292960868761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30457466332129562457966725 5710774937274292960868761)
        ·
          refine ⟨4283081202955719720651571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5710774937274292960868761 4283081202955719720651571)
          ·
            refine ⟨6424621804433579580977357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4283081202955719720651571 6424621804433579580977357)
            ·
              refine ⟨2409233176662592342866509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6424621804433579580977357 2409233176662592342866509)
              ·
                refine ⟨903462441248472128574941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2409233176662592342866509 903462441248472128574941)
                ·
                  refine ⟨338798415468177048215603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 903462441248472128574941 338798415468177048215603)
                  ·
                    rfl

theorem cell21_1484567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3, 3, 3].length) (baseStart_1484567 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1484567 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1484567 prefixEnd_1484567 := by exact prefixLift 1484567
  have htrace : WordTrace (prefixWord ++ tailWord_1484567) baseStart_1484567 baseEnd_1484567 := by
    simpa [prefixWord, tailWord_1484567, baseEnd_1484567] using wordTrace_append hprefix tailTrace_1484567
  have hstable : (prefixWord ++ tailWord_1484567).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484567).length < 2 ^ (prefixWord ++ tailWord_1484567).sum := by decide
  have hdescent : baseEnd_1484567 < baseStart_1484567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484584 : List Nat := [2, 1, 5, 1, 1, 3, 3, 2, 3]
def baseStart_1484584 : Nat := 118140960795 + 1484584 * 2 ^ 59
def prefixEnd_1484584 : Nat := 4983230072969 + 3 ^ 40 * 1484584 * 2
def baseEnd_1484584 : Nat := 338802295099788796432235

theorem tailTrace_1484584 : CollatzResearch.WordTrace tailWord_1484584 prefixEnd_1484584 338802295099788796432235 := by
  unfold tailWord_1484584
  simp only [CollatzResearch.WordTrace]
  refine ⟨27073613426806594803210403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36098151235742126404280537 27073613426806594803210403)
  ·
    refine ⟨40610420140209892204815605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27073613426806594803210403 40610420140209892204815605)
    ·
      refine ⟨3807226888144677394201463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40610420140209892204815605 3807226888144677394201463)
      ·
        refine ⟨5710840332217016091302195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3807226888144677394201463 5710840332217016091302195)
        ·
          refine ⟨8566260498325524136953293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5710840332217016091302195 8566260498325524136953293)
          ·
            refine ⟨3212347686872071551357485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8566260498325524136953293 3212347686872071551357485)
            ·
              refine ⟨1204630382577026831759057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3212347686872071551357485 1204630382577026831759057)
              ·
                refine ⟨903472786932770123819293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1204630382577026831759057 903472786932770123819293)
                ·
                  refine ⟨338802295099788796432235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 903472786932770123819293 338802295099788796432235)
                  ·
                    rfl

theorem cell21_1484584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 3, 2, 3].length) (baseStart_1484584 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1484584 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1484584 prefixEnd_1484584 := by exact prefixLift 1484584
  have htrace : WordTrace (prefixWord ++ tailWord_1484584) baseStart_1484584 baseEnd_1484584 := by
    simpa [prefixWord, tailWord_1484584, baseEnd_1484584] using wordTrace_append hprefix tailTrace_1484584
  have hstable : (prefixWord ++ tailWord_1484584).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484584).length < 2 ^ (prefixWord ++ tailWord_1484584).sum := by decide
  have hdescent : baseEnd_1484584 < baseStart_1484584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484595 : List Nat := [1, 1, 1, 2, 7, 1, 2, 6]
def baseStart_1484595 : Nat := 118140960795 + 1484595 * 2 ^ 59
def prefixEnd_1484595 : Nat := 4983230072969 + 3 ^ 40 * 1484595 * 2
def baseEnd_1484595 : Nat := 112934935149885073916293

theorem tailTrace_1484595 : CollatzResearch.WordTrace tailWord_1484595 prefixEnd_1484595 112934935149885073916293 := by
  unfold tailWord_1484595
  simp only [CollatzResearch.WordTrace]
  refine ⟨54147628056573338485071239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36098418704382225656714159 54147628056573338485071239)
  ·
    refine ⟨81221442084860007727606859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54147628056573338485071239 81221442084860007727606859)
    ·
      refine ⟨121832163127290011591410289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81221442084860007727606859 121832163127290011591410289)
      ·
        refine ⟨91374122345467508693557717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121832163127290011591410289 91374122345467508693557717)
        ·
          refine ⟨2141580992471894735005259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 91374122345467508693557717 2141580992471894735005259)
          ·
            refine ⟨3212371488707842102507889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2141580992471894735005259 3212371488707842102507889)
            ·
              refine ⟨2409278616530881576880917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3212371488707842102507889 2409278616530881576880917)
              ·
                refine ⟨112934935149885073916293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2409278616530881576880917 112934935149885073916293)
                ·
                  rfl

theorem cell21_1484595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 2, 6].length) (baseStart_1484595 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1484595 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1484595 prefixEnd_1484595 := by exact prefixLift 1484595
  have htrace : WordTrace (prefixWord ++ tailWord_1484595) baseStart_1484595 baseEnd_1484595 := by
    simpa [prefixWord, tailWord_1484595, baseEnd_1484595] using wordTrace_append hprefix tailTrace_1484595
  have hstable : (prefixWord ++ tailWord_1484595).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484595).length < 2 ^ (prefixWord ++ tailWord_1484595).sum := by decide
  have hdescent : baseEnd_1484595 < baseStart_1484595 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484598 : List Nat := [5, 1, 2, 2, 1, 2, 1, 3, 4]
def baseStart_1484598 : Nat := 118140960795 + 1484598 * 2 ^ 59
def prefixEnd_1484598 : Nat := 4983230072969 + 3 ^ 40 * 1484598 * 2
def baseEnd_1484598 : Nat := 338805490090527883198873

theorem tailTrace_1484598 : CollatzResearch.WordTrace tailWord_1484598 prefixEnd_1484598 338805490090527883198873 := by
  unfold tailWord_1484598
  simp only [CollatzResearch.WordTrace]
  refine ⟨3384233592222654374839403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36098491650374979998286965 3384233592222654374839403)
  ·
    refine ⟨5076350388333981562259105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3384233592222654374839403 5076350388333981562259105)
    ·
      refine ⟨3807262791250486171694329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5076350388333981562259105 3807262791250486171694329)
      ·
        refine ⟨2855447093437864628770747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3807262791250486171694329 2855447093437864628770747)
        ·
          refine ⟨4283170640156796943156121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2855447093437864628770747 4283170640156796943156121)
          ·
            refine ⟨3212377980117597707367091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4283170640156796943156121 3212377980117597707367091)
            ·
              refine ⟨4818566970176396561050637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3212377980117597707367091 4818566970176396561050637)
              ·
                refine ⟨1806962613816148710393989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4818566970176396561050637 1806962613816148710393989)
                ·
                  refine ⟨338805490090527883198873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1806962613816148710393989 338805490090527883198873)
                  ·
                    rfl

theorem cell21_1484598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 3, 4].length) (baseStart_1484598 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1484598 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1484598 prefixEnd_1484598 := by exact prefixLift 1484598
  have htrace : WordTrace (prefixWord ++ tailWord_1484598) baseStart_1484598 baseEnd_1484598 := by
    simpa [prefixWord, tailWord_1484598, baseEnd_1484598] using wordTrace_append hprefix tailTrace_1484598
  have hstable : (prefixWord ++ tailWord_1484598).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484598).length < 2 ^ (prefixWord ++ tailWord_1484598).sum := by decide
  have hdescent : baseEnd_1484598 < baseStart_1484598 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484640 : List Nat := [2, 1, 1, 3, 3, 2, 1, 4, 4]
def baseStart_1484640 : Nat := 118140960795 + 1484640 * 2 ^ 59
def prefixEnd_1484640 : Nat := 4983230072969 + 3 ^ 40 * 1484640 * 2
def baseEnd_1484640 : Nat := 338815075062745143498787

theorem tailTrace_1484640 : CollatzResearch.WordTrace tailWord_1484640 prefixEnd_1484640 338815075062745143498787 := by
  unfold tailWord_1484640
  simp only [CollatzResearch.WordTrace]
  refine ⟨27074634670705155585229687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36099512894273540780306249 27074634670705155585229687)
  ·
    refine ⟨40611952006057733377844531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27074634670705155585229687 40611952006057733377844531)
    ·
      refine ⟨60917928009086600066766797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40611952006057733377844531 60917928009086600066766797)
      ·
        refine ⟨22844223003407475025037549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60917928009086600066766797 22844223003407475025037549)
        ·
          refine ⟨8566583626277803134389081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22844223003407475025037549 8566583626277803134389081)
          ·
            refine ⟨6424937719708352350791811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8566583626277803134389081 6424937719708352350791811)
            ·
              refine ⟨9637406579562528526187717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6424937719708352350791811 9637406579562528526187717)
              ·
                refine ⟨1807013733667974098660197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9637406579562528526187717 1807013733667974098660197)
                ·
                  refine ⟨338815075062745143498787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1807013733667974098660197 338815075062745143498787)
                  ·
                    rfl

theorem cell21_1484640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 4, 4].length) (baseStart_1484640 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1484640 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1484640 prefixEnd_1484640 := by exact prefixLift 1484640
  have htrace : WordTrace (prefixWord ++ tailWord_1484640) baseStart_1484640 baseEnd_1484640 := by
    simpa [prefixWord, tailWord_1484640, baseEnd_1484640] using wordTrace_append hprefix tailTrace_1484640
  have hstable : (prefixWord ++ tailWord_1484640).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484640).length < 2 ^ (prefixWord ++ tailWord_1484640).sum := by decide
  have hdescent : baseEnd_1484640 < baseStart_1484640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484643 : List Nat := [1, 1, 1, 5, 4, 1, 1, 4, 3]
def baseStart_1484643 : Nat := 118140960795 + 1484643 * 2 ^ 59
def prefixEnd_1484643 : Nat := 4983230072969 + 3 ^ 40 * 1484643 * 2
def baseEnd_1484643 : Nat := 338815759703617804948781

theorem tailTrace_1484643 : CollatzResearch.WordTrace tailWord_1484643 prefixEnd_1484643 338815759703617804948781 := by
  unfold tailWord_1484643
  simp only [CollatzResearch.WordTrace]
  refine ⟨54149378760399442682818583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36099585840266295121879055 54149378760399442682818583)
  ·
    refine ⟨81224068140599164024227875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54149378760399442682818583 81224068140599164024227875)
    ·
      refine ⟨121836102210898746036341813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81224068140599164024227875 121836102210898746036341813)
      ·
        refine ⟨11422134582271757440907045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 121836102210898746036341813 11422134582271757440907045)
        ·
          refine ⟨2141650234175954520170071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11422134582271757440907045 2141650234175954520170071)
          ·
            refine ⟨3212475351263931780255107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2141650234175954520170071 3212475351263931780255107)
            ·
              refine ⟨4818713026895897670382661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3212475351263931780255107 4818713026895897670382661)
              ·
                refine ⟨903508692542980813196749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4818713026895897670382661 903508692542980813196749)
                ·
                  refine ⟨338815759703617804948781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 903508692542980813196749 338815759703617804948781)
                  ·
                    rfl

theorem cell21_1484643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 4, 3].length) (baseStart_1484643 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1484643 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1484643 prefixEnd_1484643 := by exact prefixLift 1484643
  have htrace : WordTrace (prefixWord ++ tailWord_1484643) baseStart_1484643 baseEnd_1484643 := by
    simpa [prefixWord, tailWord_1484643, baseEnd_1484643] using wordTrace_append hprefix tailTrace_1484643
  have hstable : (prefixWord ++ tailWord_1484643).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484643).length < 2 ^ (prefixWord ++ tailWord_1484643).sum := by decide
  have hdescent : baseEnd_1484643 < baseStart_1484643 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484837 : List Nat := [1, 3, 1, 2, 2, 4, 1, 2, 5]
def baseStart_1484837 : Nat := 118140960795 + 1484837 * 2 ^ 59
def prefixEnd_1484837 : Nat := 4983230072969 + 3 ^ 40 * 1484837 * 2
def baseEnd_1484837 : Nat := 338860033146716578715051

theorem tailTrace_1484837 : CollatzResearch.WordTrace tailWord_1484837 prefixEnd_1484837 338860033146716578715051 := by
  unfold tailWord_1484837
  simp only [CollatzResearch.WordTrace]
  refine ⟨54156454521696613815380765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36104303014464409210253843 54156454521696613815380765)
  ·
    refine ⟨20308670445636230180767787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54156454521696613815380765 20308670445636230180767787)
    ·
      refine ⟨30463005668454345271151681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20308670445636230180767787 30463005668454345271151681)
      ·
        refine ⟨22847254251340758953363761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30463005668454345271151681 22847254251340758953363761)
        ·
          refine ⟨17135440688505569215022821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22847254251340758953363761 17135440688505569215022821)
          ·
            refine ⟨3212895129094794227816779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17135440688505569215022821 3212895129094794227816779)
            ·
              refine ⟨4819342693642191341725169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3212895129094794227816779 4819342693642191341725169)
              ·
                refine ⟨3614507020231643506293877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4819342693642191341725169 3614507020231643506293877)
                ·
                  refine ⟨338860033146716578715051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3614507020231643506293877 338860033146716578715051)
                  ·
                    rfl

theorem cell21_1484837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 2, 5].length) (baseStart_1484837 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1484837 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1484837 prefixEnd_1484837 := by exact prefixLift 1484837
  have htrace : WordTrace (prefixWord ++ tailWord_1484837) baseStart_1484837 baseEnd_1484837 := by
    simpa [prefixWord, tailWord_1484837, baseEnd_1484837] using wordTrace_append hprefix tailTrace_1484837
  have hstable : (prefixWord ++ tailWord_1484837).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484837).length < 2 ^ (prefixWord ++ tailWord_1484837).sum := by decide
  have hdescent : baseEnd_1484837 < baseStart_1484837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484885 : List Nat := [1, 3, 2, 2, 1, 4, 3, 1, 4]
def baseStart_1484885 : Nat := 118140960795 + 1484885 * 2 ^ 59
def prefixEnd_1484885 : Nat := 4983230072969 + 3 ^ 40 * 1484885 * 2
def baseEnd_1484885 : Nat := 338870987400679161914953

theorem tailTrace_1484885 : CollatzResearch.WordTrace tailWord_1484885 prefixEnd_1484885 338870987400679161914953 := by
  unfold tailWord_1484885
  simp only [CollatzResearch.WordTrace]
  refine ⟨54158205225522718013128109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36105470150348478675418739 54158205225522718013128109)
  ·
    refine ⟨20309326959571019254923041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54158205225522718013128109 20309326959571019254923041)
    ·
      refine ⟨15231995219678264441192281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20309326959571019254923041 15231995219678264441192281)
      ·
        refine ⟨11423996414758698330894211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15231995219678264441192281 11423996414758698330894211)
        ·
          refine ⟨17135994622138047496341317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11423996414758698330894211 17135994622138047496341317)
          ·
            refine ⟨3212998991650883905563997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17135994622138047496341317 3212998991650883905563997)
            ·
              refine ⟨1204874621869081464586499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3212998991650883905563997 1204874621869081464586499)
              ·
                refine ⟨1807311932803622196879749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1204874621869081464586499 1807311932803622196879749)
                ·
                  refine ⟨338870987400679161914953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1807311932803622196879749 338870987400679161914953)
                  ·
                    rfl

theorem cell21_1484885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 3, 1, 4].length) (baseStart_1484885 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1484885 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1484885 prefixEnd_1484885 := by exact prefixLift 1484885
  have htrace : WordTrace (prefixWord ++ tailWord_1484885) baseStart_1484885 baseEnd_1484885 := by
    simpa [prefixWord, tailWord_1484885, baseEnd_1484885] using wordTrace_append hprefix tailTrace_1484885
  have hstable : (prefixWord ++ tailWord_1484885).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484885).length < 2 ^ (prefixWord ++ tailWord_1484885).sum := by decide
  have hdescent : baseEnd_1484885 < baseStart_1484885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484981 : List Nat := [1, 3, 3, 4, 1, 2, 2, 2, 3]
def baseStart_1484981 : Nat := 118140960795 + 1484981 * 2 ^ 59
def prefixEnd_1484981 : Nat := 4983230072969 + 3 ^ 40 * 1484981 * 2
def baseEnd_1484981 : Nat := 338892895908604328314757

theorem tailTrace_1484981 : CollatzResearch.WordTrace tailWord_1484981 prefixEnd_1484981 338892895908604328314757 := by
  unfold tailWord_1484981
  simp only [CollatzResearch.WordTrace]
  refine ⟨54161706633174926408622797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36107804422116617605748531 54161706633174926408622797)
  ·
    refine ⟨20310639987440597403233549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54161706633174926408622797 20310639987440597403233549)
    ·
      refine ⟨7616489995290224026212581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20310639987440597403233549 7616489995290224026212581)
      ·
        refine ⟨1428091874116917004914859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7616489995290224026212581 1428091874116917004914859)
        ·
          refine ⟨2142137811175375507372289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1428091874116917004914859 2142137811175375507372289)
          ·
            refine ⟨1606603358381531630529217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2142137811175375507372289 1606603358381531630529217)
            ·
              refine ⟨1204952518786148722896913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1606603358381531630529217 1204952518786148722896913)
              ·
                refine ⟨903714389089611542172685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1204952518786148722896913 903714389089611542172685)
                ·
                  refine ⟨338892895908604328314757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 903714389089611542172685 338892895908604328314757)
                  ·
                    rfl

theorem cell21_1484981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 2, 2, 3].length) (baseStart_1484981 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1484981 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1484981 prefixEnd_1484981 := by exact prefixLift 1484981
  have htrace : WordTrace (prefixWord ++ tailWord_1484981) baseStart_1484981 baseEnd_1484981 := by
    simpa [prefixWord, tailWord_1484981, baseEnd_1484981] using wordTrace_append hprefix tailTrace_1484981
  have hstable : (prefixWord ++ tailWord_1484981).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484981).length < 2 ^ (prefixWord ++ tailWord_1484981).sum := by decide
  have hdescent : baseEnd_1484981 < baseStart_1484981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485003 : List Nat := [1, 1, 1, 1, 3, 2, 3, 5, 4]
def baseStart_1485003 : Nat := 118140960795 + 1485003 * 2 ^ 59
def prefixEnd_1485003 : Nat := 4983230072969 + 3 ^ 40 * 1485003 * 2
def baseEnd_1485003 : Nat := 338897916608337178948045

theorem tailTrace_1485003 : CollatzResearch.WordTrace tailWord_1485003 prefixEnd_1485003 338897916608337178948045 := by
  unfold tailWord_1485003
  simp only [CollatzResearch.WordTrace]
  refine ⟨54162509039095224165923663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36108339359396816110615775 54162509039095224165923663)
  ·
    refine ⟨81243763558642836248885495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54162509039095224165923663 81243763558642836248885495)
    ·
      refine ⟨121865645337964254373328243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81243763558642836248885495 121865645337964254373328243)
      ·
        refine ⟨182798468006946381559992365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121865645337964254373328243 182798468006946381559992365)
        ·
          refine ⟨68549425502604893084997137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 182798468006946381559992365 68549425502604893084997137)
          ·
            refine ⟨51412069126953669813747853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68549425502604893084997137 51412069126953669813747853)
            ·
              refine ⟨19279525922607626180155445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51412069126953669813747853 19279525922607626180155445)
              ·
                refine ⟨1807455555244464954389573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19279525922607626180155445 1807455555244464954389573)
                ·
                  refine ⟨338897916608337178948045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1807455555244464954389573 338897916608337178948045)
                  ·
                    rfl

theorem cell21_1485003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 5, 4].length) (baseStart_1485003 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1485003 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1485003 prefixEnd_1485003 := by exact prefixLift 1485003
  have htrace : WordTrace (prefixWord ++ tailWord_1485003) baseStart_1485003 baseEnd_1485003 := by
    simpa [prefixWord, tailWord_1485003, baseEnd_1485003] using wordTrace_append hprefix tailTrace_1485003
  have hstable : (prefixWord ++ tailWord_1485003).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485003).length < 2 ^ (prefixWord ++ tailWord_1485003).sum := by decide
  have hdescent : baseEnd_1485003 < baseStart_1485003 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485017 : List Nat := [1, 2, 1, 2, 3, 1, 2, 9]
def baseStart_1485017 : Nat := 118140960795 + 1485017 * 2 ^ 59
def prefixEnd_1485017 : Nat := 4983230072969 + 3 ^ 40 * 1485017 * 2
def baseEnd_1485017 : Nat := 112967037199692088571561

theorem tailTrace_1485017 : CollatzResearch.WordTrace tailWord_1485017 prefixEnd_1485017 112967037199692088571561 := by
  unfold tailWord_1485017
  simp only [CollatzResearch.WordTrace]
  refine ⟨54163019661044504556933305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36108679774029669704622203 54163019661044504556933305)
  ·
    refine ⟨40622264745783378417699979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54163019661044504556933305 40622264745783378417699979)
    ·
      refine ⟨60933397118675067626549969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40622264745783378417699979 60933397118675067626549969)
      ·
        refine ⟨45700047839006300719912477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60933397118675067626549969 45700047839006300719912477)
        ·
          refine ⟨17137517939627362769967179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45700047839006300719912477 17137517939627362769967179)
          ·
            refine ⟨25706276909441044154950769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17137517939627362769967179 25706276909441044154950769)
            ·
              refine ⟨19279707682080783116213077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25706276909441044154950769 19279707682080783116213077)
              ·
                refine ⟨112967037199692088571561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19279707682080783116213077 112967037199692088571561)
                ·
                  rfl

theorem cell21_1485017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 9].length) (baseStart_1485017 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1485017 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1485017 prefixEnd_1485017 := by exact prefixLift 1485017
  have htrace : WordTrace (prefixWord ++ tailWord_1485017) baseStart_1485017 baseEnd_1485017 := by
    simpa [prefixWord, tailWord_1485017, baseEnd_1485017] using wordTrace_append hprefix tailTrace_1485017
  have hstable : (prefixWord ++ tailWord_1485017).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485017).length < 2 ^ (prefixWord ++ tailWord_1485017).sum := by decide
  have hdescent : baseEnd_1485017 < baseStart_1485017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485079 : List Nat := [1, 1, 3, 4, 1, 2, 1, 2, 6]
def baseStart_1485079 : Nat := 118140960795 + 1485079 * 2 ^ 59
def prefixEnd_1485079 : Nat := 4983230072969 + 3 ^ 40 * 1485079 * 2
def baseEnd_1485079 : Nat := 338915260843777935681223

theorem tailTrace_1485079 : CollatzResearch.WordTrace tailWord_1485079 prefixEnd_1485079 338915260843777935681223 := by
  unfold tailWord_1485079
  simp only [CollatzResearch.WordTrace]
  refine ⟨54165280986819889145690291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36110187324546592763793527 54165280986819889145690291)
  ·
    refine ⟨81247921480229833718535437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54165280986819889145690291 81247921480229833718535437)
    ·
      refine ⟨30467970555086187644450789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81247921480229833718535437 30467970555086187644450789)
      ·
        refine ⟨5712744479078660183334523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30467970555086187644450789 5712744479078660183334523)
        ·
          refine ⟨8569116718617990275001785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5712744479078660183334523 8569116718617990275001785)
          ·
            refine ⟨6426837538963492706251339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8569116718617990275001785 6426837538963492706251339)
            ·
              refine ⟨9640256308445239059377009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6426837538963492706251339 9640256308445239059377009)
              ·
                refine ⟨7230192231333929294532757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9640256308445239059377009 7230192231333929294532757)
                ·
                  refine ⟨338915260843777935681223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7230192231333929294532757 338915260843777935681223)
                  ·
                    rfl

theorem cell21_1485079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 2, 6].length) (baseStart_1485079 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1485079 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1485079 prefixEnd_1485079 := by exact prefixLift 1485079
  have htrace : WordTrace (prefixWord ++ tailWord_1485079) baseStart_1485079 baseEnd_1485079 := by
    simpa [prefixWord, tailWord_1485079, baseEnd_1485079] using wordTrace_append hprefix tailTrace_1485079
  have hstable : (prefixWord ++ tailWord_1485079).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485079).length < 2 ^ (prefixWord ++ tailWord_1485079).sum := by decide
  have hdescent : baseEnd_1485079 < baseStart_1485079 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485113 : List Nat := [1, 2, 1, 6, 1, 1, 4, 1, 4]
def baseStart_1485113 : Nat := 118140960795 + 1485113 * 2 ^ 59
def prefixEnd_1485113 : Nat := 4983230072969 + 3 ^ 40 * 1485113 * 2
def baseEnd_1485113 : Nat := 338923020107001432114487

theorem tailTrace_1485113 : CollatzResearch.WordTrace tailWord_1485113 prefixEnd_1485113 338923020107001432114487 := by
  unfold tailWord_1485113
  simp only [CollatzResearch.WordTrace]
  refine ⟨54166521068696712952427993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36111014045797808634951995 54166521068696712952427993)
  ·
    refine ⟨40624890801522534714320995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54166521068696712952427993 40624890801522534714320995)
    ·
      refine ⟨60937336202283802071481493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40624890801522534714320995 60937336202283802071481493)
      ·
        refine ⟨2856437634482053222100695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 60937336202283802071481493 2856437634482053222100695)
        ·
          refine ⟨4284656451723079833151043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2856437634482053222100695 4284656451723079833151043)
          ·
            refine ⟨6426984677584619749726565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4284656451723079833151043 6426984677584619749726565)
            ·
              refine ⟨1205059627047116203073731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6426984677584619749726565 1205059627047116203073731)
              ·
                refine ⟨1807589440570674304610597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1205059627047116203073731 1807589440570674304610597)
                ·
                  refine ⟨338923020107001432114487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1807589440570674304610597 338923020107001432114487)
                  ·
                    rfl

theorem cell21_1485113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 4, 1, 4].length) (baseStart_1485113 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1485113 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1485113 prefixEnd_1485113 := by exact prefixLift 1485113
  have htrace : WordTrace (prefixWord ++ tailWord_1485113) baseStart_1485113 baseEnd_1485113 := by
    simpa [prefixWord, tailWord_1485113, baseEnd_1485113] using wordTrace_append hprefix tailTrace_1485113
  have hstable : (prefixWord ++ tailWord_1485113).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485113).length < 2 ^ (prefixWord ++ tailWord_1485113).sum := by decide
  have hdescent : baseEnd_1485113 < baseStart_1485113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485150 : List Nat := [4, 4, 2, 1, 1, 1, 1, 4, 3]
def baseStart_1485150 : Nat := 118140960795 + 1485150 * 2 ^ 59
def prefixEnd_1485150 : Nat := 4983230072969 + 3 ^ 40 * 1485150 * 2
def baseEnd_1485150 : Nat := 338931464011097589997745

theorem tailTrace_1485150 : CollatzResearch.WordTrace tailWord_1485150 prefixEnd_1485150 338931464011097589997745 := by
  unfold tailWord_1485150
  simp only [CollatzResearch.WordTrace]
  refine ⟨6770983821195333533940613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36111913713041778847683269 6770983821195333533940613)
  ·
    refine ⟨1269559466474125037613865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6770983821195333533940613 1269559466474125037613865)
    ·
      refine ⟨952169599855593778210399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1269559466474125037613865 952169599855593778210399)
      ·
        refine ⟨1428254399783390667315599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 952169599855593778210399 1428254399783390667315599)
        ·
          refine ⟨2142381599675086000973399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1428254399783390667315599 2142381599675086000973399)
          ·
            refine ⟨3213572399512629001460099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2142381599675086000973399 3213572399512629001460099)
            ·
              refine ⟨4820358599268943502190149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3213572399512629001460099 4820358599268943502190149)
              ·
                refine ⟨903817237362926906660653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4820358599268943502190149 903817237362926906660653)
                ·
                  refine ⟨338931464011097589997745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 903817237362926906660653 338931464011097589997745)
                  ·
                    rfl

theorem cell21_1485150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_1485150 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1485150 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1485150 prefixEnd_1485150 := by exact prefixLift 1485150
  have htrace : WordTrace (prefixWord ++ tailWord_1485150) baseStart_1485150 baseEnd_1485150 := by
    simpa [prefixWord, tailWord_1485150, baseEnd_1485150] using wordTrace_append hprefix tailTrace_1485150
  have hstable : (prefixWord ++ tailWord_1485150).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485150).length < 2 ^ (prefixWord ++ tailWord_1485150).sum := by decide
  have hdescent : baseEnd_1485150 < baseStart_1485150 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485282 : List Nat := [3, 3, 3, 2, 1, 1, 1, 3, 4]
def baseStart_1485282 : Nat := 118140960795 + 1485282 * 2 ^ 59
def prefixEnd_1485282 : Nat := 4983230072969 + 3 ^ 40 * 1485282 * 2
def baseEnd_1485282 : Nat := 338961588209494693797475

theorem tailTrace_1485282 : CollatzResearch.WordTrace tailWord_1485282 prefixEnd_1485282 338961588209494693797475 := by
  unfold tailWord_1485282
  simp only [CollatzResearch.WordTrace]
  refine ⟨13543171251271113703832525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36115123336722969876886733 13543171251271113703832525)
  ·
    refine ⟨5078689219226667638937197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13543171251271113703832525 5078689219226667638937197)
    ·
      refine ⟨1904508457210000364601449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5078689219226667638937197 1904508457210000364601449)
      ·
        refine ⟨1428381342907500273451087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1904508457210000364601449 1428381342907500273451087)
        ·
          refine ⟨2142572014361250410176631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1428381342907500273451087 2142572014361250410176631)
          ·
            refine ⟨3213858021541875615264947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2142572014361250410176631 3213858021541875615264947)
            ·
              refine ⟨4820787032312813422897421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3213858021541875615264947 4820787032312813422897421)
              ·
                refine ⟨1807795137117305033586533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4820787032312813422897421 1807795137117305033586533)
                ·
                  refine ⟨338961588209494693797475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1807795137117305033586533 338961588209494693797475)
                  ·
                    rfl

theorem cell21_1485282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 3, 4].length) (baseStart_1485282 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1485282 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1485282 prefixEnd_1485282 := by exact prefixLift 1485282
  have htrace : WordTrace (prefixWord ++ tailWord_1485282) baseStart_1485282 baseEnd_1485282 := by
    simpa [prefixWord, tailWord_1485282, baseEnd_1485282] using wordTrace_append hprefix tailTrace_1485282
  have hstable : (prefixWord ++ tailWord_1485282).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485282).length < 2 ^ (prefixWord ++ tailWord_1485282).sum := by decide
  have hdescent : baseEnd_1485282 < baseStart_1485282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485324 : List Nat := [2, 2, 1, 2, 4, 2, 2, 2, 4]
def baseStart_1485324 : Nat := 118140960795 + 1485324 * 2 ^ 59
def prefixEnd_1485324 : Nat := 4983230072969 + 3 ^ 40 * 1485324 * 2
def baseEnd_1485324 : Nat := 338971173181711954097389

theorem tailTrace_1485324 : CollatzResearch.WordTrace tailWord_1485324 prefixEnd_1485324 338971173181711954097389 := by
  unfold tailWord_1485324
  simp only [CollatzResearch.WordTrace]
  refine ⟨27087108435466147994179513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36116144580621530658906017 27087108435466147994179513)
  ·
    refine ⟨20315331326599610995634635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27087108435466147994179513 20315331326599610995634635)
    ·
      refine ⟨30472996989899416493451953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20315331326599610995634635 30472996989899416493451953)
      ·
        refine ⟨22854747742424562370088965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30472996989899416493451953 22854747742424562370088965)
        ·
          refine ⟨4285265201704605444391681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22854747742424562370088965 4285265201704605444391681)
          ·
            refine ⟨3213948901278454083293761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4285265201704605444391681 3213948901278454083293761)
            ·
              refine ⟨2410461675958840562470321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3213948901278454083293761 2410461675958840562470321)
              ·
                refine ⟨1807846256969130421852741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2410461675958840562470321 1807846256969130421852741)
                ·
                  refine ⟨338971173181711954097389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1807846256969130421852741 338971173181711954097389)
                  ·
                    rfl

theorem cell21_1485324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2, 2, 4].length) (baseStart_1485324 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1485324 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1485324 prefixEnd_1485324 := by exact prefixLift 1485324
  have htrace : WordTrace (prefixWord ++ tailWord_1485324) baseStart_1485324 baseEnd_1485324 := by
    simpa [prefixWord, tailWord_1485324, baseEnd_1485324] using wordTrace_append hprefix tailTrace_1485324
  have hstable : (prefixWord ++ tailWord_1485324).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485324).length < 2 ^ (prefixWord ++ tailWord_1485324).sum := by decide
  have hdescent : baseEnd_1485324 < baseStart_1485324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485383 : List Nat := [1, 1, 4, 1, 4, 2, 1, 1, 6]
def baseStart_1485383 : Nat := 118140960795 + 1485383 * 2 ^ 59
def prefixEnd_1485383 : Nat := 4983230072969 + 3 ^ 40 * 1485383 * 2
def baseEnd_1485383 : Nat := 338984637785540962613935

theorem tailTrace_1485383 : CollatzResearch.WordTrace tailWord_1485383 prefixEnd_1485383 338984637785540962613935 := by
  unfold tailWord_1485383
  simp only [CollatzResearch.WordTrace]
  refine ⟨54176368777718549064756803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36117579185145699376504535 54176368777718549064756803)
  ·
    refine ⟨81264553166577823597135205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54176368777718549064756803 81264553166577823597135205)
    ·
      refine ⟨15237103718733341924462851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81264553166577823597135205 15237103718733341924462851)
      ·
        refine ⟨22855655578100012886694277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15237103718733341924462851 22855655578100012886694277)
        ·
          refine ⟨4285435420893752416255177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22855655578100012886694277 4285435420893752416255177)
          ·
            refine ⟨3214076565670314312191383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4285435420893752416255177 3214076565670314312191383)
            ·
              refine ⟨4821114848505471468287075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3214076565670314312191383 4821114848505471468287075)
              ·
                refine ⟨7231672272758207202430613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4821114848505471468287075 7231672272758207202430613)
                ·
                  refine ⟨338984637785540962613935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7231672272758207202430613 338984637785540962613935)
                  ·
                    rfl

theorem cell21_1485383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 1, 6].length) (baseStart_1485383 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1485383 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1485383 prefixEnd_1485383 := by exact prefixLift 1485383
  have htrace : WordTrace (prefixWord ++ tailWord_1485383) baseStart_1485383 baseEnd_1485383 := by
    simpa [prefixWord, tailWord_1485383, baseEnd_1485383] using wordTrace_append hprefix tailTrace_1485383
  have hstable : (prefixWord ++ tailWord_1485383).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485383).length < 2 ^ (prefixWord ++ tailWord_1485383).sum := by decide
  have hdescent : baseEnd_1485383 < baseStart_1485383 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485406 : List Nat := [4, 4, 1, 2, 1, 2, 2, 5]
def baseStart_1485406 : Nat := 118140960795 + 1485406 * 2 ^ 59
def prefixEnd_1485406 : Nat := 4983230072969 + 3 ^ 40 * 1485406 * 2
def baseEnd_1485406 : Nat := 112996628899632677910185

theorem tailTrace_1485406 : CollatzResearch.WordTrace tailWord_1485406 prefixEnd_1485406 112996628899632677910185 := by
  unfold tailWord_1485406
  simp only [CollatzResearch.WordTrace]
  refine ⟨6772150957079402999105509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36118138437756815995229381 6772150957079402999105509)
  ·
    refine ⟨1269778304452388062332283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6772150957079402999105509 1269778304452388062332283)
    ·
      refine ⟨1904667456678582093498425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1269778304452388062332283 1904667456678582093498425)
      ·
        refine ⟨1428500592508936570123819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1904667456678582093498425 1428500592508936570123819)
        ·
          refine ⟨2142750888763404855185729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1428500592508936570123819 2142750888763404855185729)
          ·
            refine ⟨1607063166572553641389297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2142750888763404855185729 1607063166572553641389297)
            ·
              refine ⟨1205297374929415231041973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1607063166572553641389297 1205297374929415231041973)
              ·
                refine ⟨112996628899632677910185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1205297374929415231041973 112996628899632677910185)
                ·
                  rfl

theorem cell21_1485406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 2, 5].length) (baseStart_1485406 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1485406 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1485406 prefixEnd_1485406 := by exact prefixLift 1485406
  have htrace : WordTrace (prefixWord ++ tailWord_1485406) baseStart_1485406 baseEnd_1485406 := by
    simpa [prefixWord, tailWord_1485406, baseEnd_1485406] using wordTrace_append hprefix tailTrace_1485406
  have hstable : (prefixWord ++ tailWord_1485406).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485406).length < 2 ^ (prefixWord ++ tailWord_1485406).sum := by decide
  have hdescent : baseEnd_1485406 < baseStart_1485406 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485445 : List Nat := [1, 3, 1, 1, 4, 4, 1, 1, 5]
def baseStart_1485445 : Nat := 118140960795 + 1485445 * 2 ^ 59
def prefixEnd_1485445 : Nat := 4983230072969 + 3 ^ 40 * 1485445 * 2
def baseEnd_1485445 : Nat := 338998787030242632580475

theorem tailTrace_1485445 : CollatzResearch.WordTrace tailWord_1485445 prefixEnd_1485445 338998787030242632580475 := by
  unfold tailWord_1485445
  simp only [CollatzResearch.WordTrace]
  refine ⟨54178630103493933653513789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36119086735662622435675859 54178630103493933653513789)
  ·
    refine ⟨20316986288810225120067671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54178630103493933653513789 20316986288810225120067671)
    ·
      refine ⟨30475479433215337680101507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20316986288810225120067671 30475479433215337680101507)
      ·
        refine ⟨45713219149823006520152261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30475479433215337680101507 45713219149823006520152261)
        ·
          refine ⟨8571228590591813722528549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45713219149823006520152261 8571228590591813722528549)
          ·
            refine ⟨1607105360735965072974103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8571228590591813722528549 1607105360735965072974103)
            ·
              refine ⟨2410658041103947609461155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1607105360735965072974103 2410658041103947609461155)
              ·
                refine ⟨3615987061655921414191733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2410658041103947609461155 3615987061655921414191733)
                ·
                  refine ⟨338998787030242632580475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3615987061655921414191733 338998787030242632580475)
                  ·
                    rfl

theorem cell21_1485445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 1, 1, 5].length) (baseStart_1485445 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1485445 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1485445 prefixEnd_1485445 := by exact prefixLift 1485445
  have htrace : WordTrace (prefixWord ++ tailWord_1485445) baseStart_1485445 baseEnd_1485445 := by
    simpa [prefixWord, tailWord_1485445, baseEnd_1485445] using wordTrace_append hprefix tailTrace_1485445
  have hstable : (prefixWord ++ tailWord_1485445).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485445).length < 2 ^ (prefixWord ++ tailWord_1485445).sum := by decide
  have hdescent : baseEnd_1485445 < baseStart_1485445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485549 : List Nat := [1, 5, 1, 2, 1, 1, 10]
def baseStart_1485549 : Nat := 118140960795 + 1485549 * 2 ^ 59
def prefixEnd_1485549 : Nat := 4983230072969 + 3 ^ 40 * 1485549 * 2
def baseEnd_1485549 : Nat := 37669169027462395871881

theorem tailTrace_1485549 : CollatzResearch.WordTrace tailWord_1485549 prefixEnd_1485549 37669169027462395871881 := by
  unfold tailWord_1485549
  simp only [CollatzResearch.WordTrace]
  refine ⟨54182423295117159415299701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36121615530078106276866467 54182423295117159415299701)
  ·
    refine ⟨5079602183917233695184347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 54182423295117159415299701 5079602183917233695184347)
    ·
      refine ⟨7619403275875850542776521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5079602183917233695184347 7619403275875850542776521)
      ·
        refine ⟨5714552456906887907082391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7619403275875850542776521 5714552456906887907082391)
        ·
          refine ⟨8571828685360331860623587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5714552456906887907082391 8571828685360331860623587)
          ·
            refine ⟨12857743028040497790935381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8571828685360331860623587 12857743028040497790935381)
            ·
              refine ⟨37669169027462395871881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 12857743028040497790935381 37669169027462395871881)
              ·
                rfl

theorem cell21_1485549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 10].length) (baseStart_1485549 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1485549 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1485549 prefixEnd_1485549 := by exact prefixLift 1485549
  have htrace : WordTrace (prefixWord ++ tailWord_1485549) baseStart_1485549 baseEnd_1485549 := by
    simpa [prefixWord, tailWord_1485549, baseEnd_1485549] using wordTrace_append hprefix tailTrace_1485549
  have hstable : (prefixWord ++ tailWord_1485549).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485549).length < 2 ^ (prefixWord ++ tailWord_1485549).sum := by decide
  have hdescent : baseEnd_1485549 < baseStart_1485549 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485594 : List Nat := [3, 1, 1, 3, 2, 1, 1, 1, 8]
def baseStart_1485594 : Nat := 118140960795 + 1485594 * 2 ^ 59
def prefixEnd_1485594 : Nat := 4983230072969 + 3 ^ 40 * 1485594 * 2
def baseEnd_1485594 : Nat := 339032790860251484596837

theorem tailTrace_1485594 : CollatzResearch.WordTrace tailWord_1485594 prefixEnd_1485594 339032790860251484596837 := by
  unfold tailWord_1485594
  simp only [CollatzResearch.WordTrace]
  refine ⟨13546016144988533025171959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36122709719969421400458557 13546016144988533025171959)
  ·
    refine ⟨20319024217482799537757939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13546016144988533025171959 20319024217482799537757939)
    ·
      refine ⟨30478536326224199306636909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20319024217482799537757939 30478536326224199306636909)
      ·
        refine ⟨11429451122334074739988841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30478536326224199306636909 11429451122334074739988841)
        ·
          refine ⟨8572088341750556054991631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11429451122334074739988841 8572088341750556054991631)
          ·
            refine ⟨12858132512625834082487447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8572088341750556054991631 12858132512625834082487447)
            ·
              refine ⟨19287198768938751123731171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12858132512625834082487447 19287198768938751123731171)
              ·
                refine ⟨28930798153408126685596757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19287198768938751123731171 28930798153408126685596757)
                ·
                  refine ⟨339032790860251484596837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28930798153408126685596757 339032790860251484596837)
                  ·
                    rfl

theorem cell21_1485594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 8].length) (baseStart_1485594 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1485594 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1485594 prefixEnd_1485594 := by exact prefixLift 1485594
  have htrace : WordTrace (prefixWord ++ tailWord_1485594) baseStart_1485594 baseEnd_1485594 := by
    simpa [prefixWord, tailWord_1485594, baseEnd_1485594] using wordTrace_append hprefix tailTrace_1485594
  have hstable : (prefixWord ++ tailWord_1485594).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485594).length < 2 ^ (prefixWord ++ tailWord_1485594).sum := by decide
  have hdescent : baseEnd_1485594 < baseStart_1485594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485614 : List Nat := [4, 1, 3, 2, 1, 3, 1, 1, 5]
def baseStart_1485614 : Nat := 118140960795 + 1485614 * 2 ^ 59
def prefixEnd_1485614 : Nat := 4983230072969 + 3 ^ 40 * 1485614 * 2
def baseEnd_1485614 : Nat := 339037355132735894263463

theorem tailTrace_1485614 : CollatzResearch.WordTrace tailWord_1485614 prefixEnd_1485614 339037355132735894263463 := by
  unfold tailWord_1485614
  simp only [CollatzResearch.WordTrace]
  refine ⟨6773099254985209439551987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36123196026587783677610597 6773099254985209439551987)
  ·
    refine ⟨10159648882477814159327981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6773099254985209439551987 10159648882477814159327981)
    ·
      refine ⟨3809868330929180309747993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10159648882477814159327981 3809868330929180309747993)
      ·
        refine ⟨2857401248196885232310995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3809868330929180309747993 2857401248196885232310995)
        ·
          refine ⟨4286101872295327848466493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2857401248196885232310995 4286101872295327848466493)
          ·
            refine ⟨1607288202110747943174935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4286101872295327848466493 1607288202110747943174935)
            ·
              refine ⟨2410932303166121914762403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1607288202110747943174935 2410932303166121914762403)
              ·
                refine ⟨3616398454749182872143605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2410932303166121914762403 3616398454749182872143605)
                ·
                  refine ⟨339037355132735894263463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3616398454749182872143605 339037355132735894263463)
                  ·
                    rfl

theorem cell21_1485614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 1, 1, 5].length) (baseStart_1485614 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1485614 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1485614 prefixEnd_1485614 := by exact prefixLift 1485614
  have htrace : WordTrace (prefixWord ++ tailWord_1485614) baseStart_1485614 baseEnd_1485614 := by
    simpa [prefixWord, tailWord_1485614, baseEnd_1485614] using wordTrace_append hprefix tailTrace_1485614
  have hstable : (prefixWord ++ tailWord_1485614).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485614).length < 2 ^ (prefixWord ++ tailWord_1485614).sum := by decide
  have hdescent : baseEnd_1485614 < baseStart_1485614 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485639 : List Nat := [1, 1, 4, 1, 2, 1, 1, 3, 7]
def baseStart_1485639 : Nat := 118140960795 + 1485639 * 2 ^ 59
def prefixEnd_1485639 : Nat := 4983230072969 + 3 ^ 40 * 1485639 * 2
def baseEnd_1485639 : Nat := 339043060473341406346745

theorem tailTrace_1485639 : CollatzResearch.WordTrace tailWord_1485639 prefixEnd_1485639 339043060473341406346745 := by
  unfold tailWord_1485639
  simp only [CollatzResearch.WordTrace]
  refine ⟨54185705864791104786075971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36123803909860736524050647 54185705864791104786075971)
  ·
    refine ⟨81278558797186657179113957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54185705864791104786075971 81278558797186657179113957)
    ·
      refine ⟨15239729774472498221083867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81278558797186657179113957 15239729774472498221083867)
      ·
        refine ⟨22859594661708747331625801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15239729774472498221083867 22859594661708747331625801)
        ·
          refine ⟨17144695996281560498719351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22859594661708747331625801 17144695996281560498719351)
          ·
            refine ⟨25717043994422340748079027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17144695996281560498719351 25717043994422340748079027)
            ·
              refine ⟨38575565991633511122118541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25717043994422340748079027 38575565991633511122118541)
              ·
                refine ⟨14465837246862566670794453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38575565991633511122118541 14465837246862566670794453)
                ·
                  refine ⟨339043060473341406346745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14465837246862566670794453 339043060473341406346745)
                  ·
                    rfl

theorem cell21_1485639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 3, 7].length) (baseStart_1485639 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1485639 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1485639 prefixEnd_1485639 := by exact prefixLift 1485639
  have htrace : WordTrace (prefixWord ++ tailWord_1485639) baseStart_1485639 baseEnd_1485639 := by
    simpa [prefixWord, tailWord_1485639, baseEnd_1485639] using wordTrace_append hprefix tailTrace_1485639
  have hstable : (prefixWord ++ tailWord_1485639).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485639).length < 2 ^ (prefixWord ++ tailWord_1485639).sum := by decide
  have hdescent : baseEnd_1485639 < baseStart_1485639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485732 : List Nat := [2, 3, 1, 2, 1, 2, 4, 1, 5]
def baseStart_1485732 : Nat := 118140960795 + 1485732 * 2 ^ 59
def prefixEnd_1485732 : Nat := 4983230072969 + 3 ^ 40 * 1485732 * 2
def baseEnd_1485732 : Nat := 339064284340393911296555

theorem tailTrace_1485732 : CollatzResearch.WordTrace tailWord_1485732 prefixEnd_1485732 339064284340393911296555 := by
  unfold tailWord_1485732
  simp only [CollatzResearch.WordTrace]
  refine ⟨27094548926727090834605725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36126065235636121112807633 27094548926727090834605725)
  ·
    refine ⟨10160455847522659062977147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27094548926727090834605725 10160455847522659062977147)
    ·
      refine ⟨15240683771283988594465721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10160455847522659062977147 15240683771283988594465721)
      ·
        refine ⟨11430512828462991445849291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15240683771283988594465721 11430512828462991445849291)
        ·
          refine ⟨17145769242694487168773937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11430512828462991445849291 17145769242694487168773937)
          ·
            refine ⟨12859326932020865376580453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17145769242694487168773937 12859326932020865376580453)
            ·
              refine ⟨2411123799753912258108835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12859326932020865376580453 2411123799753912258108835)
              ·
                refine ⟨3616685699630868387163253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2411123799753912258108835 3616685699630868387163253)
                ·
                  refine ⟨339064284340393911296555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3616685699630868387163253 339064284340393911296555)
                  ·
                    rfl

theorem cell21_1485732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4, 1, 5].length) (baseStart_1485732 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1485732 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1485732 prefixEnd_1485732 := by exact prefixLift 1485732
  have htrace : WordTrace (prefixWord ++ tailWord_1485732) baseStart_1485732 baseEnd_1485732 := by
    simpa [prefixWord, tailWord_1485732, baseEnd_1485732] using wordTrace_append hprefix tailTrace_1485732
  have hstable : (prefixWord ++ tailWord_1485732).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485732).length < 2 ^ (prefixWord ++ tailWord_1485732).sum := by decide
  have hdescent : baseEnd_1485732 < baseStart_1485732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485794 : List Nat := [3, 3, 3, 1, 1, 1, 1, 8]
def baseStart_1485794 : Nat := 118140960795 + 1485794 * 2 ^ 59
def prefixEnd_1485794 : Nat := 4983230072969 + 3 ^ 40 * 1485794 * 2
def baseEnd_1485794 : Nat := 113026144528365193754365

theorem tailTrace_1485794 : CollatzResearch.WordTrace tailWord_1485794 prefixEnd_1485794 113026144528365193754365 := by
  unfold tailWord_1485794
  simp only [CollatzResearch.WordTrace]
  refine ⟨13547839794807391564492109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36127572786153044171978957 13547839794807391564492109)
  ·
    refine ⟨5080439923052771836684541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13547839794807391564492109 5080439923052771836684541)
    ·
      refine ⟨1905164971144789438756703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5080439923052771836684541 1905164971144789438756703)
      ·
        refine ⟨2857747456717184158135055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1905164971144789438756703 2857747456717184158135055)
        ·
          refine ⟨4286621185075776237202583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2857747456717184158135055 4286621185075776237202583)
          ·
            refine ⟨6429931777613664355803875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4286621185075776237202583 6429931777613664355803875)
            ·
              refine ⟨9644897666420496533705813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6429931777613664355803875 9644897666420496533705813)
              ·
                refine ⟨113026144528365193754365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9644897666420496533705813 113026144528365193754365)
                ·
                  rfl

theorem cell21_1485794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 8].length) (baseStart_1485794 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1485794 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1485794 prefixEnd_1485794 := by exact prefixLift 1485794
  have htrace : WordTrace (prefixWord ++ tailWord_1485794) baseStart_1485794 baseEnd_1485794 := by
    simpa [prefixWord, tailWord_1485794, baseEnd_1485794] using wordTrace_append hprefix tailTrace_1485794
  have hstable : (prefixWord ++ tailWord_1485794).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485794).length < 2 ^ (prefixWord ++ tailWord_1485794).sum := by decide
  have hdescent : baseEnd_1485794 < baseStart_1485794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485836 : List Nat := [2, 2, 1, 2, 3, 11]
def baseStart_1485836 : Nat := 118140960795 + 1485836 * 2 ^ 59
def prefixEnd_1485836 : Nat := 4983230072969 + 3 ^ 40 * 1485836 * 2
def baseEnd_1485836 : Nat := 12558815502122697835667

theorem tailTrace_1485836 : CollatzResearch.WordTrace tailWord_1485836 prefixEnd_1485836 12558815502122697835667 := by
  unfold tailWord_1485836
  simp only [CollatzResearch.WordTrace]
  refine ⟨27096445522538703715498681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36128594030051604953998241 27096445522538703715498681)
  ·
    refine ⟨20322334141904027786624011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27096445522538703715498681 20322334141904027786624011)
    ·
      refine ⟨30483501212856041679936017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20322334141904027786624011 30483501212856041679936017)
      ·
        refine ⟨22862625909642031259952013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30483501212856041679936017 22862625909642031259952013)
        ·
          refine ⟨8573484716115761722482005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22862625909642031259952013 8573484716115761722482005)
          ·
            refine ⟨12558815502122697835667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 8573484716115761722482005 12558815502122697835667)
            ·
              rfl

theorem cell21_1485836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 11].length) (baseStart_1485836 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1485836 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1485836 prefixEnd_1485836 := by exact prefixLift 1485836
  have htrace : WordTrace (prefixWord ++ tailWord_1485836) baseStart_1485836 baseEnd_1485836 := by
    simpa [prefixWord, tailWord_1485836, baseEnd_1485836] using wordTrace_append hprefix tailTrace_1485836
  have hstable : (prefixWord ++ tailWord_1485836).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485836).length < 2 ^ (prefixWord ++ tailWord_1485836).sum := by decide
  have hdescent : baseEnd_1485836 < baseStart_1485836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485867 : List Nat := [1, 1, 1, 1, 2, 1, 7, 2, 5]
def baseStart_1485867 : Nat := 118140960795 + 1485867 * 2 ^ 59
def prefixEnd_1485867 : Nat := 4983230072969 + 3 ^ 40 * 1485867 * 2
def baseEnd_1485867 : Nat := 339095093179663676546279

theorem tailTrace_1485867 : CollatzResearch.WordTrace tailWord_1485867 prefixEnd_1485867 339095093179663676546279 := by
  unfold tailWord_1485867
  simp only [CollatzResearch.WordTrace]
  refine ⟨54194021707965099725375855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36129347805310066483583903 54194021707965099725375855)
  ·
    refine ⟨81291032561947649588063783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54194021707965099725375855 81291032561947649588063783)
    ·
      refine ⟨121936548842921474382095675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81291032561947649588063783 121936548842921474382095675)
      ·
        refine ⟨182904823264382211573143513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121936548842921474382095675 182904823264382211573143513)
        ·
          refine ⟨137178617448286658679857635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182904823264382211573143513 137178617448286658679857635)
          ·
            refine ⟨205767926172429988019786453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137178617448286658679857635 205767926172429988019786453)
            ·
              refine ⟨4822685769666327844213745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 205767926172429988019786453 4822685769666327844213745)
              ·
                refine ⟨3617014327249745883160309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4822685769666327844213745 3617014327249745883160309)
                ·
                  refine ⟨339095093179663676546279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3617014327249745883160309 339095093179663676546279)
                  ·
                    rfl

theorem cell21_1485867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 2, 5].length) (baseStart_1485867 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1485867 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1485867 prefixEnd_1485867 := by exact prefixLift 1485867
  have htrace : WordTrace (prefixWord ++ tailWord_1485867) baseStart_1485867 baseEnd_1485867 := by
    simpa [prefixWord, tailWord_1485867, baseEnd_1485867] using wordTrace_append hprefix tailTrace_1485867
  have hstable : (prefixWord ++ tailWord_1485867).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485867).length < 2 ^ (prefixWord ++ tailWord_1485867).sum := by decide
  have hdescent : baseEnd_1485867 < baseStart_1485867 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
