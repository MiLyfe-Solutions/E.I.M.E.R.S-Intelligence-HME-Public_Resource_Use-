import V185TrunkScan23Chunk0608

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3601393 : List Nat := [1, 2, 2, 2, 4, 1, 3, 2, 6]
def baseStart_3601393 : Nat := 118140960795 + 3601393 * 2 ^ 59
def prefixEnd_3601393 : Nat := 4983230072969 + 3 ^ 40 * 3601393 * 2
def baseEnd_3601393 : Nat := 205471737193081474113889

theorem tailTrace_3601393 : CollatzResearch.WordTrace tailWord_3601393 prefixEnd_3601393 205471737193081474113889 := by
  unfold tailWord_3601393
  simp only [CollatzResearch.WordTrace]
  refine ⟨131353593841775704801368833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87569062561183803200912555 131353593841775704801368833)
  ·
    refine ⟨98515195381331778601026625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131353593841775704801368833 98515195381331778601026625)
    ·
      refine ⟨73886396535998833950769969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98515195381331778601026625 73886396535998833950769969)
      ·
        refine ⟨55414797401999125463077477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73886396535998833950769969 55414797401999125463077477)
        ·
          refine ⟨10390274512874836024327027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55414797401999125463077477 10390274512874836024327027)
          ·
            refine ⟨15585411769312254036490541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10390274512874836024327027 15585411769312254036490541)
            ·
              refine ⟨5844529413492095263683953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15585411769312254036490541 5844529413492095263683953)
              ·
                refine ⟨4383397060119071447762965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5844529413492095263683953 4383397060119071447762965)
                ·
                  refine ⟨205471737193081474113889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4383397060119071447762965 205471737193081474113889)
                  ·
                    rfl

theorem cell23_3601393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3, 2, 6].length) (baseStart_3601393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3601393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3601393 prefixEnd_3601393 := by exact prefixLift 3601393
  have htrace : WordTrace (prefixWord ++ tailWord_3601393) baseStart_3601393 baseEnd_3601393 := by
    simpa [prefixWord, tailWord_3601393, baseEnd_3601393] using wordTrace_append hprefix tailTrace_3601393
  have hstable : (prefixWord ++ tailWord_3601393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3601393).length < 2 ^ (prefixWord ++ tailWord_3601393).sum := by decide
  have hdescent : baseEnd_3601393 < baseStart_3601393 := by decide
  rcases family_descends (prefixWord ++ tailWord_3601393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3601413 : List Nat := [1, 3, 1, 1, 2, 3, 1, 1, 3, 5, 2]
def baseStart_3601413 : Nat := 118140960795 + 3601413 * 2 ^ 59
def prefixEnd_3601413 : Nat := 4983230072969 + 3 ^ 40 * 3601413 * 2
def baseEnd_3601413 : Nat := 1849255904350823188774909

theorem tailTrace_3601413 : CollatzResearch.WordTrace tailWord_3601413 prefixEnd_3601413 1849255904350823188774909 := by
  unfold tailWord_3601413
  simp only [CollatzResearch.WordTrace]
  refine ⟨131354323301703248217096893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87569548867802165478064595 131354323301703248217096893)
  ·
    refine ⟨49257871238138718081411335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131354323301703248217096893 49257871238138718081411335)
    ·
      refine ⟨73886806857208077122117003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49257871238138718081411335 73886806857208077122117003)
      ·
        refine ⟨110830210285812115683175505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73886806857208077122117003 110830210285812115683175505)
        ·
          refine ⟨83122657714359086762381629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110830210285812115683175505 83122657714359086762381629)
          ·
            refine ⟨31170996642884657535893111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83122657714359086762381629 31170996642884657535893111)
            ·
              refine ⟨46756494964326986303839667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31170996642884657535893111 46756494964326986303839667)
              ·
                refine ⟨70134742446490479455759501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46756494964326986303839667 70134742446490479455759501)
                ·
                  refine ⟨26300528417433929795909813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70134742446490479455759501 26300528417433929795909813)
                  ·
                    refine ⟨2465674539134430918366545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26300528417433929795909813 2465674539134430918366545)
                    ·
                      refine ⟨1849255904350823188774909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2465674539134430918366545 1849255904350823188774909)
                      ·
                        rfl

theorem cell23_3601413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 3, 5, 2].length) (baseStart_3601413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3601413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3601413 prefixEnd_3601413 := by exact prefixLift 3601413
  have htrace : WordTrace (prefixWord ++ tailWord_3601413) baseStart_3601413 baseEnd_3601413 := by
    simpa [prefixWord, tailWord_3601413, baseEnd_3601413] using wordTrace_append hprefix tailTrace_3601413
  have hstable : (prefixWord ++ tailWord_3601413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3601413).length < 2 ^ (prefixWord ++ tailWord_3601413).sum := by decide
  have hdescent : baseEnd_3601413 < baseStart_3601413 := by decide
  rcases family_descends (prefixWord ++ tailWord_3601413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3601420 : List Nat := [2, 2, 1, 2, 3, 2, 2, 2, 3, 1, 3]
def baseStart_3601420 : Nat := 118140960795 + 3601420 * 2 ^ 59
def prefixEnd_3601420 : Nat := 4983230072969 + 3 ^ 40 * 3601420 * 2
def baseEnd_3601420 : Nat := 1849259498715404661387377

theorem tailTrace_3601420 : CollatzResearch.WordTrace tailWord_3601420 prefixEnd_3601420 1849259498715404661387377 := by
  unfold tailWord_3601420
  simp only [CollatzResearch.WordTrace]
  refine ⟨65677289306338944206300857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87569719075118592275067809 65677289306338944206300857)
  ·
    refine ⟨49257966979754208154725643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65677289306338944206300857 49257966979754208154725643)
    ·
      refine ⟨73886950469631312232088465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49257966979754208154725643 73886950469631312232088465)
      ·
        refine ⟨55415212852223484174066349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73886950469631312232088465 55415212852223484174066349)
        ·
          refine ⟨20780704819583806565274881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55415212852223484174066349 20780704819583806565274881)
          ·
            refine ⟨15585528614687854923956161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20780704819583806565274881 15585528614687854923956161)
            ·
              refine ⟨11689146461015891192967121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15585528614687854923956161 11689146461015891192967121)
              ·
                refine ⟨8766859845761918394725341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11689146461015891192967121 8766859845761918394725341)
                ·
                  refine ⟨3287572442160719398022003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8766859845761918394725341 3287572442160719398022003)
                  ·
                    refine ⟨4931358663241079097033005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3287572442160719398022003 4931358663241079097033005)
                    ·
                      refine ⟨1849259498715404661387377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4931358663241079097033005 1849259498715404661387377)
                      ·
                        rfl

theorem cell23_3601420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 2, 3, 1, 3].length) (baseStart_3601420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3601420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3601420 prefixEnd_3601420 := by exact prefixLift 3601420
  have htrace : WordTrace (prefixWord ++ tailWord_3601420) baseStart_3601420 baseEnd_3601420 := by
    simpa [prefixWord, tailWord_3601420, baseEnd_3601420] using wordTrace_append hprefix tailTrace_3601420
  have hstable : (prefixWord ++ tailWord_3601420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3601420).length < 2 ^ (prefixWord ++ tailWord_3601420).sum := by decide
  have hdescent : baseEnd_3601420 < baseStart_3601420 := by decide
  rcases family_descends (prefixWord ++ tailWord_3601420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3601447 : List Nat := [1, 1, 7, 1, 1, 1, 1, 1, 4, 3, 2]
def baseStart_3601447 : Nat := 118140960795 + 3601447 * 2 ^ 59
def prefixEnd_3601447 : Nat := 4983230072969 + 3 ^ 40 * 3601447 * 2
def baseEnd_3601447 : Nat := 1849273362693076055749753

theorem tailTrace_3601447 : CollatzResearch.WordTrace tailWord_3601447 prefixEnd_3601447 1849273362693076055749753 := by
  unfold tailWord_3601447
  simp only [CollatzResearch.WordTrace]
  refine ⟨131355563383580072023834595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87570375589053381349223063 131355563383580072023834595)
  ·
    refine ⟨197033345075370108035751893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131355563383580072023834595 197033345075370108035751893)
    ·
      refine ⟨4617969025203986907087935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 197033345075370108035751893 4617969025203986907087935)
      ·
        refine ⟨6926953537805980360631903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4617969025203986907087935 6926953537805980360631903)
        ·
          refine ⟨10390430306708970540947855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6926953537805980360631903 10390430306708970540947855)
          ·
            refine ⟨15585645460063455811421783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10390430306708970540947855 15585645460063455811421783)
            ·
              refine ⟨23378468190095183717132675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15585645460063455811421783 23378468190095183717132675)
              ·
                refine ⟨35067702285142775575699013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23378468190095183717132675 35067702285142775575699013)
                ·
                  refine ⟨6575194178464270420443565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35067702285142775575699013 6575194178464270420443565)
                  ·
                    refine ⟨2465697816924101407666337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6575194178464270420443565 2465697816924101407666337)
                    ·
                      refine ⟨1849273362693076055749753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2465697816924101407666337 1849273362693076055749753)
                      ·
                        rfl

theorem cell23_3601447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 1, 4, 3, 2].length) (baseStart_3601447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3601447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3601447 prefixEnd_3601447 := by exact prefixLift 3601447
  have htrace : WordTrace (prefixWord ++ tailWord_3601447) baseStart_3601447 baseEnd_3601447 := by
    simpa [prefixWord, tailWord_3601447, baseEnd_3601447] using wordTrace_append hprefix tailTrace_3601447
  have hstable : (prefixWord ++ tailWord_3601447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3601447).length < 2 ^ (prefixWord ++ tailWord_3601447).sum := by decide
  have hdescent : baseEnd_3601447 < baseStart_3601447 := by decide
  rcases family_descends (prefixWord ++ tailWord_3601447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3601456 : List Nat := [2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 6]
def baseStart_3601456 : Nat := 118140960795 + 3601456 * 2 ^ 59
def prefixEnd_3601456 : Nat := 4983230072969 + 3 ^ 40 * 3601456 * 2
def baseEnd_3601456 : Nat := 1849277984018966520537211

theorem tailTrace_3601456 : CollatzResearch.WordTrace tailWord_3601456 prefixEnd_3601456 1849277984018966520537211 := by
  unfold tailWord_3601456
  simp only [CollatzResearch.WordTrace]
  refine ⟨65677945820273733280456111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87570594427031644373941481 65677945820273733280456111)
  ·
    refine ⟨98516918730410599920684167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65677945820273733280456111 98516918730410599920684167)
    ·
      refine ⟨147775378095615899881026251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98516918730410599920684167 147775378095615899881026251)
      ·
        refine ⟨221663067143423849821539377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147775378095615899881026251 221663067143423849821539377)
        ·
          refine ⟨166247300357567887366154533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 221663067143423849821539377 166247300357567887366154533)
          ·
            refine ⟨31171368817043978881153975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 166247300357567887366154533 31171368817043978881153975)
            ·
              refine ⟨46757053225565968321730963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31171368817043978881153975 46757053225565968321730963)
              ·
                refine ⟨70135579838348952482596445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46757053225565968321730963 70135579838348952482596445)
                ·
                  refine ⟨26300842439380857180973667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70135579838348952482596445 26300842439380857180973667)
                  ·
                    refine ⟨39451263659071285771460501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26300842439380857180973667 39451263659071285771460501)
                    ·
                      refine ⟨1849277984018966520537211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39451263659071285771460501 1849277984018966520537211)
                      ·
                        rfl

theorem cell23_3601456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 6].length) (baseStart_3601456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3601456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3601456 prefixEnd_3601456 := by exact prefixLift 3601456
  have htrace : WordTrace (prefixWord ++ tailWord_3601456) baseStart_3601456 baseEnd_3601456 := by
    simpa [prefixWord, tailWord_3601456, baseEnd_3601456] using wordTrace_append hprefix tailTrace_3601456
  have hstable : (prefixWord ++ tailWord_3601456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3601456).length < 2 ^ (prefixWord ++ tailWord_3601456).sum := by decide
  have hdescent : baseEnd_3601456 < baseStart_3601456 := by decide
  rcases family_descends (prefixWord ++ tailWord_3601456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3601463 : List Nat := [1, 1, 3, 1, 2, 2, 1, 4, 3, 2, 3]
def baseStart_3601463 : Nat := 118140960795 + 3601463 * 2 ^ 59
def prefixEnd_3601463 : Nat := 4983230072969 + 3 ^ 40 * 3601463 * 2
def baseEnd_3601463 : Nat := 1849281578383547993149679

theorem tailTrace_3601463 : CollatzResearch.WordTrace tailWord_3601463 prefixEnd_3601463 1849281578383547993149679 := by
  unfold tailWord_3601463
  simp only [CollatzResearch.WordTrace]
  refine ⟨131356146951522106756417043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87570764634348071170944695 131356146951522106756417043)
  ·
    refine ⟨197034220427283160134625565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131356146951522106756417043 197034220427283160134625565)
    ·
      refine ⟨73887832660231185050484587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197034220427283160134625565 73887832660231185050484587)
      ·
        refine ⟨110831748990346777575726881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73887832660231185050484587 110831748990346777575726881)
        ·
          refine ⟨83123811742760083181795161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110831748990346777575726881 83123811742760083181795161)
          ·
            refine ⟨62342858807070062386346371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83123811742760083181795161 62342858807070062386346371)
            ·
              refine ⟨93514288210605093579519557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62342858807070062386346371 93514288210605093579519557)
              ·
                refine ⟨17533929039488455046159917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93514288210605093579519557 17533929039488455046159917)
                ·
                  refine ⟨6575223389808170642309969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17533929039488455046159917 6575223389808170642309969)
                  ·
                    refine ⟨4931417542356127981732477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6575223389808170642309969 4931417542356127981732477)
                    ·
                      refine ⟨1849281578383547993149679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4931417542356127981732477 1849281578383547993149679)
                      ·
                        rfl

theorem cell23_3601463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 4, 3, 2, 3].length) (baseStart_3601463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3601463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3601463 prefixEnd_3601463 := by exact prefixLift 3601463
  have htrace : WordTrace (prefixWord ++ tailWord_3601463) baseStart_3601463 baseEnd_3601463 := by
    simpa [prefixWord, tailWord_3601463, baseEnd_3601463] using wordTrace_append hprefix tailTrace_3601463
  have hstable : (prefixWord ++ tailWord_3601463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3601463).length < 2 ^ (prefixWord ++ tailWord_3601463).sum := by decide
  have hdescent : baseEnd_3601463 < baseStart_3601463 := by decide
  rcases family_descends (prefixWord ++ tailWord_3601463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3601466 : List Nat := [3, 1, 1, 1, 3, 1, 3, 10]
def baseStart_3601466 : Nat := 118140960795 + 3601466 * 2 ^ 59
def prefixEnd_3601466 : Nat := 4983230072969 + 3 ^ 40 * 3601466 * 2
def baseEnd_3601466 : Nat := 68491967363907832644895

theorem tailTrace_3601466 : CollatzResearch.WordTrace tailWord_3601466 prefixEnd_3601466 68491967363907832644895 := by
  unfold tailWord_3601466
  simp only [CollatzResearch.WordTrace]
  refine ⟨32839064092627809567194063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87570837580340825512517501 32839064092627809567194063)
  ·
    refine ⟨49258596138941714350791095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32839064092627809567194063 49258596138941714350791095)
    ·
      refine ⟨73887894208412571526186643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49258596138941714350791095 73887894208412571526186643)
      ·
        refine ⟨110831841312618857289279965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73887894208412571526186643 110831841312618857289279965)
        ·
          refine ⟨41561940492232071483479987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110831841312618857289279965 41561940492232071483479987)
          ·
            refine ⟨62342910738348107225219981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41561940492232071483479987 62342910738348107225219981)
            ·
              refine ⟨23378591526880540209457493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62342910738348107225219981 23378591526880540209457493)
              ·
                refine ⟨68491967363907832644895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 23378591526880540209457493 68491967363907832644895)
                ·
                  rfl

theorem cell23_3601466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 10].length) (baseStart_3601466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3601466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3601466 prefixEnd_3601466 := by exact prefixLift 3601466
  have htrace : WordTrace (prefixWord ++ tailWord_3601466) baseStart_3601466 baseEnd_3601466 := by
    simpa [prefixWord, tailWord_3601466, baseEnd_3601466] using wordTrace_append hprefix tailTrace_3601466
  have hstable : (prefixWord ++ tailWord_3601466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3601466).length < 2 ^ (prefixWord ++ tailWord_3601466).sum := by decide
  have hdescent : baseEnd_3601466 < baseStart_3601466 := by decide
  rcases family_descends (prefixWord ++ tailWord_3601466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3601490 : List Nat := [3, 2, 2, 1, 3, 2, 1, 2, 1, 2, 4]
def baseStart_3601490 : Nat := 118140960795 + 3601490 * 2 ^ 59
def prefixEnd_3601490 : Nat := 4983230072969 + 3 ^ 40 * 3601490 * 2
def baseEnd_3601490 : Nat := 1849295442361219387512055

theorem tailTrace_3601490 : CollatzResearch.WordTrace tailWord_3601490 prefixEnd_3601490 1849295442361219387512055 := by
  unfold tailWord_3601490
  simp only [CollatzResearch.WordTrace]
  refine ⟨32839282930606072591912481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87571421148282860245099949 32839282930606072591912481)
  ·
    refine ⟨24629462197954554443934361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32839282930606072591912481 24629462197954554443934361)
    ·
      refine ⟨18472096648465915832950771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24629462197954554443934361 18472096648465915832950771)
      ·
        refine ⟨27708144972698873749426157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18472096648465915832950771 27708144972698873749426157)
        ·
          refine ⟨10390554364762077656034809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27708144972698873749426157 10390554364762077656034809)
          ·
            refine ⟨7792915773571558242026107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10390554364762077656034809 7792915773571558242026107)
            ·
              refine ⟨11689373660357337363039161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7792915773571558242026107 11689373660357337363039161)
              ·
                refine ⟨8767030245268003022279371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11689373660357337363039161 8767030245268003022279371)
                ·
                  refine ⟨13150545367902004533419057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8767030245268003022279371 13150545367902004533419057)
                  ·
                    refine ⟨9862909025926503400064293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13150545367902004533419057 9862909025926503400064293)
                    ·
                      refine ⟨1849295442361219387512055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9862909025926503400064293 1849295442361219387512055)
                      ·
                        rfl

theorem cell23_3601490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 2, 1, 2, 4].length) (baseStart_3601490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3601490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3601490 prefixEnd_3601490 := by exact prefixLift 3601490
  have htrace : WordTrace (prefixWord ++ tailWord_3601490) baseStart_3601490 baseEnd_3601490 := by
    simpa [prefixWord, tailWord_3601490, baseEnd_3601490] using wordTrace_append hprefix tailTrace_3601490
  have hstable : (prefixWord ++ tailWord_3601490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3601490).length < 2 ^ (prefixWord ++ tailWord_3601490).sum := by decide
  have hdescent : baseEnd_3601490 < baseStart_3601490 := by decide
  rcases family_descends (prefixWord ++ tailWord_3601490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3601511 : List Nat := [1, 1, 5, 1, 1, 3, 4, 2, 1, 2, 2]
def baseStart_3601511 : Nat := 118140960795 + 3601511 * 2 ^ 59
def prefixEnd_3601511 : Nat := 4983230072969 + 3 ^ 40 * 3601511 * 2
def baseEnd_3601511 : Nat := 1849306225454963805349459

theorem tailTrace_3601511 : CollatzResearch.WordTrace tailWord_3601511 prefixEnd_3601511 1849306225454963805349459 := by
  unfold tailWord_3601511
  simp only [CollatzResearch.WordTrace]
  refine ⟨131357897655348210954164387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87571931770232140636109591 131357897655348210954164387)
  ·
    refine ⟨197036846483022316431246581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131357897655348210954164387 197036846483022316431246581)
    ·
      refine ⟨18472204357783342165429367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 197036846483022316431246581 18472204357783342165429367)
      ·
        refine ⟨27708306536675013248144051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18472204357783342165429367 27708306536675013248144051)
        ·
          refine ⟨41562459805012519872216077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27708306536675013248144051 41562459805012519872216077)
          ·
            refine ⟨15585922426879694952081029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41562459805012519872216077 15585922426879694952081029)
            ·
              refine ⟨2922360455039942803515193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15585922426879694952081029 2922360455039942803515193)
              ·
                refine ⟨2191770341279957102636395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2922360455039942803515193 2191770341279957102636395)
                ·
                  refine ⟨3287655511919935653954593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2191770341279957102636395 3287655511919935653954593)
                  ·
                    refine ⟨2465741633939951740465945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3287655511919935653954593 2465741633939951740465945)
                    ·
                      refine ⟨1849306225454963805349459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2465741633939951740465945 1849306225454963805349459)
                      ·
                        rfl

theorem cell23_3601511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 4, 2, 1, 2, 2].length) (baseStart_3601511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3601511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3601511 prefixEnd_3601511 := by exact prefixLift 3601511
  have htrace : WordTrace (prefixWord ++ tailWord_3601511) baseStart_3601511 baseEnd_3601511 := by
    simpa [prefixWord, tailWord_3601511, baseEnd_3601511] using wordTrace_append hprefix tailTrace_3601511
  have hstable : (prefixWord ++ tailWord_3601511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3601511).length < 2 ^ (prefixWord ++ tailWord_3601511).sum := by decide
  have hdescent : baseEnd_3601511 < baseStart_3601511 := by decide
  rcases family_descends (prefixWord ++ tailWord_3601511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3601520 : List Nat := [2, 1, 1, 1, 5, 1, 1, 1, 5, 3, 2]
def baseStart_3601520 : Nat := 118140960795 + 3601520 * 2 ^ 59
def prefixEnd_3601520 : Nat := 4983230072969 + 3 ^ 40 * 3601520 * 2
def baseEnd_3601520 : Nat := 1849310846780854270136917

theorem tailTrace_3601520 : CollatzResearch.WordTrace tailWord_3601520 prefixEnd_3601520 1849310846780854270136917 := by
  unfold tailWord_3601520
  simp only [CollatzResearch.WordTrace]
  refine ⟨65679112956157802745621007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87572150608210403660828009 65679112956157802745621007)
  ·
    refine ⟨98518669434236704118431511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65679112956157802745621007 98518669434236704118431511)
    ·
      refine ⟨147778004151355056177647267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98518669434236704118431511 147778004151355056177647267)
      ·
        refine ⟨221667006227032584266470901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147778004151355056177647267 221667006227032584266470901)
        ·
          refine ⟨20781281833784304774981647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 221667006227032584266470901 20781281833784304774981647)
          ·
            refine ⟨31171922750676457162472471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20781281833784304774981647 31171922750676457162472471)
            ·
              refine ⟨46757884126014685743708707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31171922750676457162472471 46757884126014685743708707)
              ·
                refine ⟨70136826189022028615563061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46757884126014685743708707 70136826189022028615563061)
                ·
                  refine ⟨6575327455220815182709037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70136826189022028615563061 6575327455220815182709037)
                  ·
                    refine ⟨2465747795707805693515889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6575327455220815182709037 2465747795707805693515889)
                    ·
                      refine ⟨1849310846780854270136917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2465747795707805693515889 1849310846780854270136917)
                      ·
                        rfl

theorem cell23_3601520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 5, 3, 2].length) (baseStart_3601520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3601520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3601520 prefixEnd_3601520 := by exact prefixLift 3601520
  have htrace : WordTrace (prefixWord ++ tailWord_3601520) baseStart_3601520 baseEnd_3601520 := by
    simpa [prefixWord, tailWord_3601520, baseEnd_3601520] using wordTrace_append hprefix tailTrace_3601520
  have hstable : (prefixWord ++ tailWord_3601520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3601520).length < 2 ^ (prefixWord ++ tailWord_3601520).sum := by decide
  have hdescent : baseEnd_3601520 < baseStart_3601520 := by decide
  rcases family_descends (prefixWord ++ tailWord_3601520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3601533 : List Nat := [1, 4, 1, 1, 3, 1, 1, 2, 2, 3, 4]
def baseStart_3601533 : Nat := 118140960795 + 3601533 * 2 ^ 59
def prefixEnd_3601533 : Nat := 4983230072969 + 3 ^ 40 * 3601533 * 2
def baseEnd_3601533 : Nat := 1849317522029362719274357

theorem tailTrace_3601533 : CollatzResearch.WordTrace tailWord_3601533 prefixEnd_3601533 1849317522029362719274357 := by
  unfold tailWord_3601533
  simp only [CollatzResearch.WordTrace]
  refine ⟨131358700061268508711465253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87572466707512339140976835 131358700061268508711465253)
  ·
    refine ⟨24629756261487845383399735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131358700061268508711465253 24629756261487845383399735)
    ·
      refine ⟨36944634392231768075099603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24629756261487845383399735 36944634392231768075099603)
      ·
        refine ⟨55416951588347652112649405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36944634392231768075099603 55416951588347652112649405)
        ·
          refine ⟨20781356845630369542243527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55416951588347652112649405 20781356845630369542243527)
          ·
            refine ⟨31172035268445554313365291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20781356845630369542243527 31172035268445554313365291)
            ·
              refine ⟨46758052902668331470047937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31172035268445554313365291 46758052902668331470047937)
              ·
                refine ⟨35068539677001248602535953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46758052902668331470047937 35068539677001248602535953)
                ·
                  refine ⟨26301404757750936451901965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35068539677001248602535953 26301404757750936451901965)
                  ·
                    refine ⟨9863026784156601169463237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26301404757750936451901965 9863026784156601169463237)
                    ·
                      refine ⟨1849317522029362719274357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9863026784156601169463237 1849317522029362719274357)
                      ·
                        rfl

theorem cell23_3601533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 2, 2, 3, 4].length) (baseStart_3601533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3601533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3601533 prefixEnd_3601533 := by exact prefixLift 3601533
  have htrace : WordTrace (prefixWord ++ tailWord_3601533) baseStart_3601533 baseEnd_3601533 := by
    simpa [prefixWord, tailWord_3601533, baseEnd_3601533] using wordTrace_append hprefix tailTrace_3601533
  have hstable : (prefixWord ++ tailWord_3601533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3601533).length < 2 ^ (prefixWord ++ tailWord_3601533).sum := by decide
  have hdescent : baseEnd_3601533 < baseStart_3601533 := by decide
  rcases family_descends (prefixWord ++ tailWord_3601533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3601537 : List Nat := [1, 2, 4, 2, 2, 1, 2, 1, 3, 3, 2]
def baseStart_3601537 : Nat := 118140960795 + 3601537 * 2 ^ 59
def prefixEnd_3601537 : Nat := 4983230072969 + 3 ^ 40 * 3601537 * 2
def baseEnd_3601537 : Nat := 1849319575951980703624339

theorem tailTrace_3601537 : CollatzResearch.WordTrace tailWord_3601537 prefixEnd_3601537 1849319575951980703624339 := by
  unfold tailWord_3601537
  simp only [CollatzResearch.WordTrace]
  refine ⟨131358845953254017394610865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87572563968836011596407243 131358845953254017394610865)
  ·
    refine ⟨98519134464940513045958149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131358845953254017394610865 98519134464940513045958149)
    ·
      refine ⟨18472337712176346196117153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98519134464940513045958149 18472337712176346196117153)
      ·
        refine ⟨13854253284132259647087865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18472337712176346196117153 13854253284132259647087865)
        ·
          refine ⟨10390689963099194735315899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13854253284132259647087865 10390689963099194735315899)
          ·
            refine ⟨15586034944648792102973849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10390689963099194735315899 15586034944648792102973849)
            ·
              refine ⟨11689526208486594077230387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15586034944648792102973849 11689526208486594077230387)
              ·
                refine ⟨17534289312729891115845581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11689526208486594077230387 17534289312729891115845581)
                ·
                  refine ⟨6575358492273709168442093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17534289312729891115845581 6575358492273709168442093)
                  ·
                    refine ⟨2465759434602640938165785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6575358492273709168442093 2465759434602640938165785)
                    ·
                      refine ⟨1849319575951980703624339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2465759434602640938165785 1849319575951980703624339)
                      ·
                        rfl

theorem cell23_3601537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 1, 3, 3, 2].length) (baseStart_3601537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3601537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3601537 prefixEnd_3601537 := by exact prefixLift 3601537
  have htrace : WordTrace (prefixWord ++ tailWord_3601537) baseStart_3601537 baseEnd_3601537 := by
    simpa [prefixWord, tailWord_3601537, baseEnd_3601537] using wordTrace_append hprefix tailTrace_3601537
  have hstable : (prefixWord ++ tailWord_3601537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3601537).length < 2 ^ (prefixWord ++ tailWord_3601537).sum := by decide
  have hdescent : baseEnd_3601537 < baseStart_3601537 := by decide
  rcases family_descends (prefixWord ++ tailWord_3601537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3601554 : List Nat := [3, 2, 3, 1, 1, 3, 1, 3, 1, 3, 2]
def baseStart_3601554 : Nat := 118140960795 + 3601554 * 2 ^ 59
def prefixEnd_3601554 : Nat := 4983230072969 + 3 ^ 40 * 3601554 * 2
def baseEnd_3601554 : Nat := 1849328305123107137111761

theorem tailTrace_3601554 : CollatzResearch.WordTrace tailWord_3601554 prefixEnd_3601554 1849328305123107137111761 := by
  unfold tailWord_3601554
  simp only [CollatzResearch.WordTrace]
  refine ⟨32839866498548107324494929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87572977329461619531986477 32839866498548107324494929)
  ·
    refine ⟨24629899873911080493371197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32839866498548107324494929 24629899873911080493371197)
    ·
      refine ⟨9236212452716655185014199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24629899873911080493371197 9236212452716655185014199)
      ·
        refine ⟨13854318679074982777521299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9236212452716655185014199 13854318679074982777521299)
        ·
          refine ⟨20781478018612474166281949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13854318679074982777521299 20781478018612474166281949)
          ·
            refine ⟨7793054256979677812355731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20781478018612474166281949 7793054256979677812355731)
            ·
              refine ⟨11689581385469516718533597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7793054256979677812355731 11689581385469516718533597)
              ·
                refine ⟨4383593019551068769450099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11689581385469516718533597 4383593019551068769450099)
                ·
                  refine ⟨6575389529326603154175149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4383593019551068769450099 6575389529326603154175149)
                  ·
                    refine ⟨2465771073497476182815681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6575389529326603154175149 2465771073497476182815681)
                    ·
                      refine ⟨1849328305123107137111761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2465771073497476182815681 1849328305123107137111761)
                      ·
                        rfl

theorem cell23_3601554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 3, 1, 3, 2].length) (baseStart_3601554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3601554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3601554 prefixEnd_3601554 := by exact prefixLift 3601554
  have htrace : WordTrace (prefixWord ++ tailWord_3601554) baseStart_3601554 baseEnd_3601554 := by
    simpa [prefixWord, tailWord_3601554, baseEnd_3601554] using wordTrace_append hprefix tailTrace_3601554
  have hstable : (prefixWord ++ tailWord_3601554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3601554).length < 2 ^ (prefixWord ++ tailWord_3601554).sum := by decide
  have hdescent : baseEnd_3601554 < baseStart_3601554 := by decide
  rcases family_descends (prefixWord ++ tailWord_3601554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3601573 : List Nat := [1, 3, 1, 2, 1, 4, 1, 3, 7]
def baseStart_3601573 : Nat := 118140960795 + 3601573 * 2 ^ 59
def prefixEnd_3601573 : Nat := 4983230072969 + 3 ^ 40 * 3601573 * 2
def baseEnd_3601573 : Nat := 205482006806171395863797

theorem tailTrace_3601573 : CollatzResearch.WordTrace tailWord_3601573 prefixEnd_3601573 205482006806171395863797 := by
  unfold tailWord_3601573
  simp only [CollatzResearch.WordTrace]
  refine ⟨131360158981123595542921373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87573439320749063695280915 131360158981123595542921373)
  ·
    refine ⟨49260059617921348328595515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131360158981123595542921373 49260059617921348328595515)
    ·
      refine ⟨73890089426882022492893273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49260059617921348328595515 73890089426882022492893273)
      ·
        refine ⟨55417567070161516869669955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73890089426882022492893273 55417567070161516869669955)
        ·
          refine ⟨83126350605242275304504933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55417567070161516869669955 83126350605242275304504933)
          ·
            refine ⟨15586190738482926619594675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83126350605242275304504933 15586190738482926619594675)
            ·
              refine ⟨23379286107724389929392013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15586190738482926619594675 23379286107724389929392013)
              ·
                refine ⟨8767232290396646223522005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23379286107724389929392013 8767232290396646223522005)
                ·
                  refine ⟨205482006806171395863797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8767232290396646223522005 205482006806171395863797)
                  ·
                    rfl

theorem cell23_3601573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 3, 7].length) (baseStart_3601573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3601573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3601573 prefixEnd_3601573 := by exact prefixLift 3601573
  have htrace : WordTrace (prefixWord ++ tailWord_3601573) baseStart_3601573 baseEnd_3601573 := by
    simpa [prefixWord, tailWord_3601573, baseEnd_3601573] using wordTrace_append hprefix tailTrace_3601573
  have hstable : (prefixWord ++ tailWord_3601573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3601573).length < 2 ^ (prefixWord ++ tailWord_3601573).sum := by decide
  have hdescent : baseEnd_3601573 < baseStart_3601573 := by decide
  rcases family_descends (prefixWord ++ tailWord_3601573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3601624 : List Nat := [2, 1, 2, 2, 5, 1, 3, 2, 5]
def baseStart_3601624 : Nat := 118140960795 + 3601624 * 2 ^ 59
def prefixEnd_3601624 : Nat := 4983230072969 + 3 ^ 40 * 3601624 * 2
def baseEnd_3601624 : Nat := 205484916529880207026271

theorem tailTrace_3601624 : CollatzResearch.WordTrace tailWord_3601624 prefixEnd_3601624 205484916529880207026271 := by
  unfold tailWord_3601624
  simp only [CollatzResearch.WordTrace]
  refine ⟨65681009551969415626513963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87574679402625887502018617 65681009551969415626513963)
  ·
    refine ⟨98521514327954123439770945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65681009551969415626513963 98521514327954123439770945)
    ·
      refine ⟨73891135745965592579828209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98521514327954123439770945 73891135745965592579828209)
      ·
        refine ⟨55418351809474194434871157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73891135745965592579828209 55418351809474194434871157)
        ·
          refine ⟨5195470482138205728269171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 55418351809474194434871157 5195470482138205728269171)
          ·
            refine ⟨7793205723207308592403757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5195470482138205728269171 7793205723207308592403757)
            ·
              refine ⟨2922452146202740722151409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7793205723207308592403757 2922452146202740722151409)
              ·
                refine ⟨2191839109652055541613557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2922452146202740722151409 2191839109652055541613557)
                ·
                  refine ⟨205484916529880207026271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2191839109652055541613557 205484916529880207026271)
                  ·
                    rfl

theorem cell23_3601624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 3, 2, 5].length) (baseStart_3601624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3601624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3601624 prefixEnd_3601624 := by exact prefixLift 3601624
  have htrace : WordTrace (prefixWord ++ tailWord_3601624) baseStart_3601624 baseEnd_3601624 := by
    simpa [prefixWord, tailWord_3601624, baseEnd_3601624] using wordTrace_append hprefix tailTrace_3601624
  have hstable : (prefixWord ++ tailWord_3601624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3601624).length < 2 ^ (prefixWord ++ tailWord_3601624).sum := by decide
  have hdescent : baseEnd_3601624 < baseStart_3601624 := by decide
  rcases family_descends (prefixWord ++ tailWord_3601624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3601640 : List Nat := [2, 1, 4, 1, 2, 1, 1, 2, 4, 1, 4]
def baseStart_3601640 : Nat := 118140960795 + 3601640 * 2 ^ 59
def prefixEnd_3601640 : Nat := 4983230072969 + 3 ^ 40 * 3601640 * 2
def baseEnd_3601640 : Nat := 1849372464459393800636365

theorem tailTrace_3601640 : CollatzResearch.WordTrace tailWord_3601640 prefixEnd_3601640 1849372464459393800636365 := by
  unfold tailWord_3601640
  simp only [CollatzResearch.WordTrace]
  refine ⟨65681301335940432992805187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87575068447920577323740249 65681301335940432992805187)
  ·
    refine ⟨98521952003910649489207781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65681301335940432992805187 98521952003910649489207781)
    ·
      refine ⟨18472866000733246779226459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98521952003910649489207781 18472866000733246779226459)
      ·
        refine ⟨27709299001099870168839689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18472866000733246779226459 27709299001099870168839689)
        ·
          refine ⟨20781974250824902626629767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27709299001099870168839689 20781974250824902626629767)
          ·
            refine ⟨31172961376237353939944651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20781974250824902626629767 31172961376237353939944651)
            ·
              refine ⟨46759442064356030909916977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31172961376237353939944651 46759442064356030909916977)
              ·
                refine ⟨35069581548267023182437733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46759442064356030909916977 35069581548267023182437733)
                ·
                  refine ⟨6575546540300066846707075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35069581548267023182437733 6575546540300066846707075)
                  ·
                    refine ⟨9863319810450100270060613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6575546540300066846707075 9863319810450100270060613)
                    ·
                      refine ⟨1849372464459393800636365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9863319810450100270060613 1849372464459393800636365)
                      ·
                        rfl

theorem cell23_3601640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 2, 4, 1, 4].length) (baseStart_3601640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3601640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3601640 prefixEnd_3601640 := by exact prefixLift 3601640
  have htrace : WordTrace (prefixWord ++ tailWord_3601640) baseStart_3601640 baseEnd_3601640 := by
    simpa [prefixWord, tailWord_3601640, baseEnd_3601640] using wordTrace_append hprefix tailTrace_3601640
  have hstable : (prefixWord ++ tailWord_3601640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3601640).length < 2 ^ (prefixWord ++ tailWord_3601640).sum := by decide
  have hdescent : baseEnd_3601640 < baseStart_3601640 := by decide
  rcases family_descends (prefixWord ++ tailWord_3601640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3601723 : List Nat := [1, 1, 1, 1, 1, 2, 1, 1, 4, 10]
def baseStart_3601723 : Nat := 118140960795 + 3601723 * 2 ^ 59
def prefixEnd_3601723 : Nat := 4983230072969 + 3 ^ 40 * 3601723 * 2
def baseEnd_3601723 : Nat := 616471694451238991966161

theorem tailTrace_3601723 : CollatzResearch.WordTrace tailWord_3601723 prefixEnd_3601723 616471694451238991966161 := by
  unfold tailWord_3601723
  simp only [CollatzResearch.WordTrace]
  refine ⟨131365629930580171160881823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87577086620386780773921215 131365629930580171160881823)
  ·
    refine ⟨197048444895870256741322735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131365629930580171160881823 197048444895870256741322735)
    ·
      refine ⟨295572667343805385111984103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197048444895870256741322735 295572667343805385111984103)
      ·
        refine ⟨443359001015708077667976155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295572667343805385111984103 443359001015708077667976155)
        ·
          refine ⟨665038501523562116501964233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 443359001015708077667976155 665038501523562116501964233)
          ·
            refine ⟨498778876142671587376473175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 665038501523562116501964233 498778876142671587376473175)
            ·
              refine ⟨748168314214007381064709763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 498778876142671587376473175 748168314214007381064709763)
              ·
                refine ⟨1122252471321011071597064645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 748168314214007381064709763 1122252471321011071597064645)
                ·
                  refine ⟨210422338372689575924449621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1122252471321011071597064645 210422338372689575924449621)
                  ·
                    refine ⟨616471694451238991966161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 210422338372689575924449621 616471694451238991966161)
                    ·
                      rfl

theorem cell23_3601723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 10].length) (baseStart_3601723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3601723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3601723 prefixEnd_3601723 := by exact prefixLift 3601723
  have htrace : WordTrace (prefixWord ++ tailWord_3601723) baseStart_3601723 baseEnd_3601723 := by
    simpa [prefixWord, tailWord_3601723, baseEnd_3601723] using wordTrace_append hprefix tailTrace_3601723
  have hstable : (prefixWord ++ tailWord_3601723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3601723).length < 2 ^ (prefixWord ++ tailWord_3601723).sum := by decide
  have hdescent : baseEnd_3601723 < baseStart_3601723 := by decide
  rcases family_descends (prefixWord ++ tailWord_3601723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3601727 : List Nat := [1, 1, 2, 2, 4, 3, 1, 3, 1, 5]
def baseStart_3601727 : Nat := 118140960795 + 3601727 * 2 ^ 59
def prefixEnd_3601727 : Nat := 4983230072969 + 3 ^ 40 * 3601727 * 2
def baseEnd_3601727 : Nat := 616472379092111653416155

theorem tailTrace_3601727 : CollatzResearch.WordTrace tailWord_3601727 prefixEnd_3601727 616472379092111653416155 := by
  unfold tailWord_3601727
  simp only [CollatzResearch.WordTrace]
  refine ⟨131365775822565679844027435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87577183881710453229351623 131365775822565679844027435)
  ·
    refine ⟨197048663733848519766041153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131365775822565679844027435 197048663733848519766041153)
    ·
      refine ⟨147786497800386389824530865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197048663733848519766041153 147786497800386389824530865)
      ·
        refine ⟨110839873350289792368398149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147786497800386389824530865 110839873350289792368398149)
        ·
          refine ⟨20782476253179336069074653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110839873350289792368398149 20782476253179336069074653)
          ·
            refine ⟨7793428594942251025902995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20782476253179336069074653 7793428594942251025902995)
            ·
              refine ⟨11690142892413376538854493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7793428594942251025902995 11690142892413376538854493)
              ·
                refine ⟨4383803584655016202070435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11690142892413376538854493 4383803584655016202070435)
                ·
                  refine ⟨6575705376982524303105653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4383803584655016202070435 6575705376982524303105653)
                  ·
                    refine ⟨616472379092111653416155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6575705376982524303105653 616472379092111653416155)
                    ·
                      rfl

theorem cell23_3601727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 3, 1, 5].length) (baseStart_3601727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3601727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3601727 prefixEnd_3601727 := by exact prefixLift 3601727
  have htrace : WordTrace (prefixWord ++ tailWord_3601727) baseStart_3601727 baseEnd_3601727 := by
    simpa [prefixWord, tailWord_3601727, baseEnd_3601727] using wordTrace_append hprefix tailTrace_3601727
  have hstable : (prefixWord ++ tailWord_3601727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3601727).length < 2 ^ (prefixWord ++ tailWord_3601727).sum := by decide
  have hdescent : baseEnd_3601727 < baseStart_3601727 := by decide
  rcases family_descends (prefixWord ++ tailWord_3601727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3601764 : List Nat := [2, 3, 1, 1, 3, 3, 2, 2, 1, 1, 4]
def baseStart_3601764 : Nat := 118140960795 + 3601764 * 2 ^ 59
def prefixEnd_3601764 : Nat := 4983230072969 + 3 ^ 40 * 3601764 * 2
def baseEnd_3601764 : Nat := 1849436136060551315485795

theorem tailTrace_3601764 : CollatzResearch.WordTrace tailWord_3601764 prefixEnd_3601764 1849436136060551315485795 := by
  unfold tailWord_3601764
  simp only [CollatzResearch.WordTrace]
  refine ⟨65683562661715817581562173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87578083548954423442082897 65683562661715817581562173)
  ·
    refine ⟨24631335998143431593085815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65683562661715817581562173 24631335998143431593085815)
    ·
      refine ⟨36947003997215147389628723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24631335998143431593085815 36947003997215147389628723)
      ·
        refine ⟨55420505995822721084443085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36947003997215147389628723 55420505995822721084443085)
        ·
          refine ⟨20782689748433520406666157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55420505995822721084443085 20782689748433520406666157)
          ·
            refine ⟨7793508655662570152499809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20782689748433520406666157 7793508655662570152499809)
            ·
              refine ⟨5845131491746927614374857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7793508655662570152499809 5845131491746927614374857)
              ·
                refine ⟨4383848618810195710781143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5845131491746927614374857 4383848618810195710781143)
                ·
                  refine ⟨6575772928215293566171715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4383848618810195710781143 6575772928215293566171715)
                  ·
                    refine ⟨9863659392322940349257573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6575772928215293566171715 9863659392322940349257573)
                    ·
                      refine ⟨1849436136060551315485795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9863659392322940349257573 1849436136060551315485795)
                      ·
                        rfl

theorem cell23_3601764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2, 2, 1, 1, 4].length) (baseStart_3601764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3601764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3601764 prefixEnd_3601764 := by exact prefixLift 3601764
  have htrace : WordTrace (prefixWord ++ tailWord_3601764) baseStart_3601764 baseEnd_3601764 := by
    simpa [prefixWord, tailWord_3601764, baseEnd_3601764] using wordTrace_append hprefix tailTrace_3601764
  have hstable : (prefixWord ++ tailWord_3601764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3601764).length < 2 ^ (prefixWord ++ tailWord_3601764).sum := by decide
  have hdescent : baseEnd_3601764 < baseStart_3601764 := by decide
  rcases family_descends (prefixWord ++ tailWord_3601764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3601794 : List Nat := [3, 4, 2, 1, 1, 1, 1, 2, 1, 1, 6]
def baseStart_3601794 : Nat := 118140960795 + 3601794 * 2 ^ 59
def prefixEnd_3601794 : Nat := 4983230072969 + 3 ^ 40 * 3601794 * 2
def baseEnd_3601794 : Nat := 1849451540480186198110657

theorem tailTrace_3601794 : CollatzResearch.WordTrace tailWord_3601794 prefixEnd_3601794 1849451540480186198110657 := by
  unfold tailWord_3601794
  simp only [CollatzResearch.WordTrace]
  refine ⟨32842054878330737571679109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87578813008881966857810957 32842054878330737571679109)
  ·
    refine ⟨6157885289687013294689833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32842054878330737571679109 6157885289687013294689833)
    ·
      refine ⟨4618413967265259971017375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6157885289687013294689833 4618413967265259971017375)
      ·
        refine ⟨6927620950897889956526063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4618413967265259971017375 6927620950897889956526063)
        ·
          refine ⟨10391431426346834934789095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6927620950897889956526063 10391431426346834934789095)
          ·
            refine ⟨15587147139520252402183643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10391431426346834934789095 15587147139520252402183643)
            ·
              refine ⟨23380720709280378603275465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15587147139520252402183643 23380720709280378603275465)
              ·
                refine ⟨17535540531960283952456599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23380720709280378603275465 17535540531960283952456599)
                ·
                  refine ⟨26303310797940425928684899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17535540531960283952456599 26303310797940425928684899)
                  ·
                    refine ⟨39454966196910638893027349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26303310797940425928684899 39454966196910638893027349)
                    ·
                      refine ⟨1849451540480186198110657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39454966196910638893027349 1849451540480186198110657)
                      ·
                        rfl

theorem cell23_3601794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_3601794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3601794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3601794 prefixEnd_3601794 := by exact prefixLift 3601794
  have htrace : WordTrace (prefixWord ++ tailWord_3601794) baseStart_3601794 baseEnd_3601794 := by
    simpa [prefixWord, tailWord_3601794, baseEnd_3601794] using wordTrace_append hprefix tailTrace_3601794
  have hstable : (prefixWord ++ tailWord_3601794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3601794).length < 2 ^ (prefixWord ++ tailWord_3601794).sum := by decide
  have hdescent : baseEnd_3601794 < baseStart_3601794 := by decide
  rcases family_descends (prefixWord ++ tailWord_3601794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3601824 : List Nat := [2, 1, 1, 4, 1, 2, 3, 1, 3, 3, 2]
def baseStart_3601824 : Nat := 118140960795 + 3601824 * 2 ^ 59
def prefixEnd_3601824 : Nat := 4983230072969 + 3 ^ 40 * 3601824 * 2
def baseEnd_3601824 : Nat := 1849466944899821080735519

theorem tailTrace_3601824 : CollatzResearch.WordTrace tailWord_3601824 prefixEnd_3601824 1849466944899821080735519 := by
  unfold tailWord_3601824
  simp only [CollatzResearch.WordTrace]
  refine ⟨65684656851607132705154263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87579542468809510273539017 65684656851607132705154263)
  ·
    refine ⟨98526985277410699057731395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65684656851607132705154263 98526985277410699057731395)
    ·
      refine ⟨147790477916116048586597093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98526985277410699057731395 147790477916116048586597093)
      ·
        refine ⟨27710714609271759109986955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 147790477916116048586597093 27710714609271759109986955)
        ·
          refine ⟨41566071913907638664980433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27710714609271759109986955 41566071913907638664980433)
          ·
            refine ⟨31174553935430728998735325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41566071913907638664980433 31174553935430728998735325)
            ·
              refine ⟨11690457725786523374525747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31174553935430728998735325 11690457725786523374525747)
              ·
                refine ⟨17535686588679785061788621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11690457725786523374525747 17535686588679785061788621)
                ·
                  refine ⟨6575882470754919398170733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17535686588679785061788621 6575882470754919398170733)
                  ·
                    refine ⟨2465955926533094774314025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6575882470754919398170733 2465955926533094774314025)
                    ·
                      refine ⟨1849466944899821080735519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2465955926533094774314025 1849466944899821080735519)
                      ·
                        rfl

theorem cell23_3601824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 1, 3, 3, 2].length) (baseStart_3601824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3601824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3601824 prefixEnd_3601824 := by exact prefixLift 3601824
  have htrace : WordTrace (prefixWord ++ tailWord_3601824) baseStart_3601824 baseEnd_3601824 := by
    simpa [prefixWord, tailWord_3601824, baseEnd_3601824] using wordTrace_append hprefix tailTrace_3601824
  have hstable : (prefixWord ++ tailWord_3601824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3601824).length < 2 ^ (prefixWord ++ tailWord_3601824).sum := by decide
  have hdescent : baseEnd_3601824 < baseStart_3601824 := by decide
  rcases family_descends (prefixWord ++ tailWord_3601824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3601840 : List Nat := [2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 5]
def baseStart_3601840 : Nat := 118140960795 + 3601840 * 2 ^ 59
def prefixEnd_3601840 : Nat := 4983230072969 + 3 ^ 40 * 3601840 * 2
def baseEnd_3601840 : Nat := 1849475160590293018135445

theorem tailTrace_3601840 : CollatzResearch.WordTrace tailWord_3601840 prefixEnd_3601840 1849475160590293018135445 := by
  unfold tailWord_3601840
  simp only [CollatzResearch.WordTrace]
  refine ⟨65684948635578150071445487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87579931514104200095260649 65684948635578150071445487)
  ·
    refine ⟨98527422953367225107168231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65684948635578150071445487 98527422953367225107168231)
    ·
      refine ⟨147791134430050837660752347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98527422953367225107168231 147791134430050837660752347)
      ·
        refine ⟨221686701645076256491128521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147791134430050837660752347 221686701645076256491128521)
        ·
          refine ⟨166265026233807192368346391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 221686701645076256491128521 166265026233807192368346391)
          ·
            refine ⟨249397539350710788552519587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166265026233807192368346391 249397539350710788552519587)
            ·
              refine ⟨374096309026066182828779381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249397539350710788552519587 374096309026066182828779381)
              ·
                refine ⟨35071528971193704640198067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 374096309026066182828779381 35071528971193704640198067)
                ·
                  refine ⟨52607293456790556960297101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35071528971193704640198067 52607293456790556960297101)
                  ·
                    refine ⟨19727735046296458860111413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52607293456790556960297101 19727735046296458860111413)
                    ·
                      refine ⟨1849475160590293018135445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19727735046296458860111413 1849475160590293018135445)
                      ·
                        rfl

theorem cell23_3601840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 5].length) (baseStart_3601840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3601840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3601840 prefixEnd_3601840 := by exact prefixLift 3601840
  have htrace : WordTrace (prefixWord ++ tailWord_3601840) baseStart_3601840 baseEnd_3601840 := by
    simpa [prefixWord, tailWord_3601840, baseEnd_3601840] using wordTrace_append hprefix tailTrace_3601840
  have hstable : (prefixWord ++ tailWord_3601840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3601840).length < 2 ^ (prefixWord ++ tailWord_3601840).sum := by decide
  have hdescent : baseEnd_3601840 < baseStart_3601840 := by decide
  rcases family_descends (prefixWord ++ tailWord_3601840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3601850 : List Nat := [3, 1, 1, 1, 2, 1, 1, 1, 1, 5, 6]
def baseStart_3601850 : Nat := 118140960795 + 3601850 * 2 ^ 59
def prefixEnd_3601850 : Nat := 4983230072969 + 3 ^ 40 * 3601850 * 2
def baseEnd_3601850 : Nat := 1849480295396837979010399

theorem tailTrace_3601850 : CollatzResearch.WordTrace tailWord_3601850 prefixEnd_3601850 1849480295396837979010399 := by
  unfold tailWord_3601850
  simp only [CollatzResearch.WordTrace]
  refine ⟨32842565500280017962688751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87580174667413381233836669 32842565500280017962688751)
  ·
    refine ⟨49263848250420026944033127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32842565500280017962688751 49263848250420026944033127)
    ·
      refine ⟨73895772375630040416049691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49263848250420026944033127 73895772375630040416049691)
      ·
        refine ⟨110843658563445060624074537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73895772375630040416049691 110843658563445060624074537)
        ·
          refine ⟨83132743922583795468055903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110843658563445060624074537 83132743922583795468055903)
          ·
            refine ⟨124699115883875693202083855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83132743922583795468055903 124699115883875693202083855)
            ·
              refine ⟨187048673825813539803125783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124699115883875693202083855 187048673825813539803125783)
              ·
                refine ⟨280573010738720309704688675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 187048673825813539803125783 280573010738720309704688675)
                ·
                  refine ⟨420859516108080464557033013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 280573010738720309704688675 420859516108080464557033013)
                  ·
                    refine ⟨39455579635132543552221845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 420859516108080464557033013 39455579635132543552221845)
                    ·
                      refine ⟨1849480295396837979010399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39455579635132543552221845 1849480295396837979010399)
                      ·
                        rfl

theorem cell23_3601850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 1, 5, 6].length) (baseStart_3601850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3601850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3601850 prefixEnd_3601850 := by exact prefixLift 3601850
  have htrace : WordTrace (prefixWord ++ tailWord_3601850) baseStart_3601850 baseEnd_3601850 := by
    simpa [prefixWord, tailWord_3601850, baseEnd_3601850] using wordTrace_append hprefix tailTrace_3601850
  have hstable : (prefixWord ++ tailWord_3601850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3601850).length < 2 ^ (prefixWord ++ tailWord_3601850).sum := by decide
  have hdescent : baseEnd_3601850 < baseStart_3601850 := by decide
  rcases family_descends (prefixWord ++ tailWord_3601850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3601854 : List Nat := [4, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2]
def baseStart_3601854 : Nat := 118140960795 + 3601854 * 2 ^ 59
def prefixEnd_3601854 : Nat := 4983230072969 + 3 ^ 40 * 3601854 * 2
def baseEnd_3601854 : Nat := 1849482349319455963360381

theorem tailTrace_3601854 : CollatzResearch.WordTrace tailWord_3601854 prefixEnd_3601854 1849482349319455963360381 := by
  unfold tailWord_3601854
  simp only [CollatzResearch.WordTrace]
  refine ⟨16421300986638197566737577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87580271928737053689267077 16421300986638197566737577)
  ·
    refine ⟨12315975739978648175053183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16421300986638197566737577 12315975739978648175053183)
    ·
      refine ⟨18473963609967972262579775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12315975739978648175053183 18473963609967972262579775)
      ·
        refine ⟨27710945414951958393869663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18473963609967972262579775 27710945414951958393869663)
        ·
          refine ⟨41566418122427937590804495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27710945414951958393869663 41566418122427937590804495)
          ·
            refine ⟨62349627183641906386206743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41566418122427937590804495 62349627183641906386206743)
            ·
              refine ⟨93524440775462859579310115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62349627183641906386206743 93524440775462859579310115)
              ·
                refine ⟨140286661163194289368965173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93524440775462859579310115 140286661163194289368965173)
                ·
                  refine ⟨13151874484049464628340485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 140286661163194289368965173 13151874484049464628340485)
                  ·
                    refine ⟨2465976465759274617813841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13151874484049464628340485 2465976465759274617813841)
                    ·
                      refine ⟨1849482349319455963360381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2465976465759274617813841 1849482349319455963360381)
                      ·
                        rfl

theorem cell23_3601854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2].length) (baseStart_3601854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3601854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3601854 prefixEnd_3601854 := by exact prefixLift 3601854
  have htrace : WordTrace (prefixWord ++ tailWord_3601854) baseStart_3601854 baseEnd_3601854 := by
    simpa [prefixWord, tailWord_3601854, baseEnd_3601854] using wordTrace_append hprefix tailTrace_3601854
  have hstable : (prefixWord ++ tailWord_3601854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3601854).length < 2 ^ (prefixWord ++ tailWord_3601854).sum := by decide
  have hdescent : baseEnd_3601854 < baseStart_3601854 := by decide
  rcases family_descends (prefixWord ++ tailWord_3601854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3601871 : List Nat := [1, 1, 2, 1, 1, 4, 4, 3, 2, 2, 2]
def baseStart_3601871 : Nat := 118140960795 + 3601871 * 2 ^ 59
def prefixEnd_3601871 : Nat := 4983230072969 + 3 ^ 40 * 3601871 * 2
def baseEnd_3601871 : Nat := 1849491078490582396847803

theorem tailTrace_3601871 : CollatzResearch.WordTrace tailWord_3601871 prefixEnd_3601871 1849491078490582396847803 := by
  unfold tailWord_3601871
  simp only [CollatzResearch.WordTrace]
  refine ⟨131371027934043992437269467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87580685289362661624846311 131371027934043992437269467)
  ·
    refine ⟨197056541901065988655904201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131371027934043992437269467 197056541901065988655904201)
    ·
      refine ⟨147792406425799491491928151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197056541901065988655904201 147792406425799491491928151)
      ·
        refine ⟨221688609638699237237892227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147792406425799491491928151 221688609638699237237892227)
        ·
          refine ⟨332532914458048855856838341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221688609638699237237892227 332532914458048855856838341)
          ·
            refine ⟨62349921460884160473157189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 332532914458048855856838341 62349921460884160473157189)
            ·
              refine ⟨11690610273915780088716973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62349921460884160473157189 11690610273915780088716973)
              ·
                refine ⟨4383978852718417533268865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11690610273915780088716973 4383978852718417533268865)
                ·
                  refine ⟨3287984139538813149951649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4383978852718417533268865 3287984139538813149951649)
                  ·
                    refine ⟨2465988104654109862463737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3287984139538813149951649 2465988104654109862463737)
                    ·
                      refine ⟨1849491078490582396847803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2465988104654109862463737 1849491078490582396847803)
                      ·
                        rfl

theorem cell23_3601871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 3, 2, 2, 2].length) (baseStart_3601871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3601871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3601871 prefixEnd_3601871 := by exact prefixLift 3601871
  have htrace : WordTrace (prefixWord ++ tailWord_3601871) baseStart_3601871 baseEnd_3601871 := by
    simpa [prefixWord, tailWord_3601871, baseEnd_3601871] using wordTrace_append hprefix tailTrace_3601871
  have hstable : (prefixWord ++ tailWord_3601871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3601871).length < 2 ^ (prefixWord ++ tailWord_3601871).sum := by decide
  have hdescent : baseEnd_3601871 < baseStart_3601871 := by decide
  rcases family_descends (prefixWord ++ tailWord_3601871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3601877 : List Nat := [1, 3, 2, 3, 1, 1, 3, 2, 7]
def baseStart_3601877 : Nat := 118140960795 + 3601877 * 2 ^ 59
def prefixEnd_3601877 : Nat := 4983230072969 + 3 ^ 40 * 3601877 * 2
def baseEnd_3601877 : Nat := 205499351041612152596975

theorem tailTrace_3601877 : CollatzResearch.WordTrace tailWord_3601877 prefixEnd_3601877 205499351041612152596975 := by
  unfold tailWord_3601877
  simp only [CollatzResearch.WordTrace]
  refine ⟨131371246772022255461987885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87580831181348170307991923 131371246772022255461987885)
  ·
    refine ⟨49264217539508345798245457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131371246772022255461987885 49264217539508345798245457)
    ·
      refine ⟨36948163154631259348684093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49264217539508345798245457 36948163154631259348684093)
      ·
        refine ⟨13855561182986722255756535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36948163154631259348684093 13855561182986722255756535)
        ·
          refine ⟨20783341774480083383634803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13855561182986722255756535 20783341774480083383634803)
          ·
            refine ⟨31175012661720125075452205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20783341774480083383634803 31175012661720125075452205)
            ·
              refine ⟨11690629748145046903294577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31175012661720125075452205 11690629748145046903294577)
              ·
                refine ⟨8767972311108785177470933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11690629748145046903294577 8767972311108785177470933)
                ·
                  refine ⟨205499351041612152596975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8767972311108785177470933 205499351041612152596975)
                  ·
                    rfl

theorem cell23_3601877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 2, 7].length) (baseStart_3601877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3601877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3601877 prefixEnd_3601877 := by exact prefixLift 3601877
  have htrace : WordTrace (prefixWord ++ tailWord_3601877) baseStart_3601877 baseEnd_3601877 := by
    simpa [prefixWord, tailWord_3601877, baseEnd_3601877] using wordTrace_append hprefix tailTrace_3601877
  have hstable : (prefixWord ++ tailWord_3601877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3601877).length < 2 ^ (prefixWord ++ tailWord_3601877).sum := by decide
  have hdescent : baseEnd_3601877 < baseStart_3601877 := by decide
  rcases family_descends (prefixWord ++ tailWord_3601877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3601887 : List Nat := [1, 1, 2, 3, 3, 1, 1, 2, 1, 5, 3]
def baseStart_3601887 : Nat := 118140960795 + 3601887 * 2 ^ 59
def prefixEnd_3601887 : Nat := 4983230072969 + 3 ^ 40 * 3601887 * 2
def baseEnd_3601887 : Nat := 1849499294181054334247729

theorem tailTrace_3601887 : CollatzResearch.WordTrace tailWord_3601887 prefixEnd_3601887 1849499294181054334247729 := by
  unfold tailWord_3601887
  simp only [CollatzResearch.WordTrace]
  refine ⟨131371611501986027169851915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87581074334657351446567943 131371611501986027169851915)
  ·
    refine ⟨197057417252979040754777873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131371611501986027169851915 197057417252979040754777873)
    ·
      refine ⟨147793062939734280566083405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197057417252979040754777873 147793062939734280566083405)
      ·
        refine ⟨55422398602400355212281277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147793062939734280566083405 55422398602400355212281277)
        ·
          refine ⟨20783399475900133204605479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55422398602400355212281277 20783399475900133204605479)
          ·
            refine ⟨31175099213850199806908219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20783399475900133204605479 31175099213850199806908219)
            ·
              refine ⟨46762648820775299710362329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31175099213850199806908219 46762648820775299710362329)
              ·
                refine ⟨35071986615581474782771747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46762648820775299710362329 35071986615581474782771747)
                ·
                  refine ⟨52607979923372212174157621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35071986615581474782771747 52607979923372212174157621)
                  ·
                    refine ⟨4931998117816144891327277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52607979923372212174157621 4931998117816144891327277)
                    ·
                      refine ⟨1849499294181054334247729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4931998117816144891327277 1849499294181054334247729)
                      ·
                        rfl

theorem cell23_3601887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 2, 1, 5, 3].length) (baseStart_3601887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3601887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3601887 prefixEnd_3601887 := by exact prefixLift 3601887
  have htrace : WordTrace (prefixWord ++ tailWord_3601887) baseStart_3601887 baseEnd_3601887 := by
    simpa [prefixWord, tailWord_3601887, baseEnd_3601887] using wordTrace_append hprefix tailTrace_3601887
  have hstable : (prefixWord ++ tailWord_3601887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3601887).length < 2 ^ (prefixWord ++ tailWord_3601887).sum := by decide
  have hdescent : baseEnd_3601887 < baseStart_3601887 := by decide
  rcases family_descends (prefixWord ++ tailWord_3601887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3601922 : List Nat := [3, 4, 1, 2, 1, 2, 3, 1, 2, 2, 2]
def baseStart_3601922 : Nat := 118140960795 + 3601922 * 2 ^ 59
def prefixEnd_3601922 : Nat := 4983230072969 + 3 ^ 40 * 3601922 * 2
def baseEnd_3601922 : Nat := 1849517266003961697310069

theorem tailTrace_3601922 : CollatzResearch.WordTrace tailWord_3601922 prefixEnd_3601922 1849517266003961697310069 := by
  unfold tailWord_3601922
  simp only [CollatzResearch.WordTrace]
  refine ⟨32843222014214807036844005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87581925371239485431584013 32843222014214807036844005)
  ·
    refine ⟨6158104127665276319408251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32843222014214807036844005 6158104127665276319408251)
    ·
      refine ⟨9237156191497914479112377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6158104127665276319408251 9237156191497914479112377)
      ·
        refine ⟨6927867143623435859334283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9237156191497914479112377 6927867143623435859334283)
        ·
          refine ⟨10391800715435153789001425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6927867143623435859334283 10391800715435153789001425)
          ·
            refine ⟨7793850536576365341751069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10391800715435153789001425 7793850536576365341751069)
            ·
              refine ⟨2922693951216137003156651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7793850536576365341751069 2922693951216137003156651)
              ·
                refine ⟨4384040926824205504734977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2922693951216137003156651 4384040926824205504734977)
                ·
                  refine ⟨3288030695118154128551233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4384040926824205504734977 3288030695118154128551233)
                  ·
                    refine ⟨2466023021338615596413425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3288030695118154128551233 2466023021338615596413425)
                    ·
                      refine ⟨1849517266003961697310069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2466023021338615596413425 1849517266003961697310069)
                      ·
                        rfl

theorem cell23_3601922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 3, 1, 2, 2, 2].length) (baseStart_3601922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3601922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3601922 prefixEnd_3601922 := by exact prefixLift 3601922
  have htrace : WordTrace (prefixWord ++ tailWord_3601922) baseStart_3601922 baseEnd_3601922 := by
    simpa [prefixWord, tailWord_3601922, baseEnd_3601922] using wordTrace_append hprefix tailTrace_3601922
  have hstable : (prefixWord ++ tailWord_3601922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3601922).length < 2 ^ (prefixWord ++ tailWord_3601922).sum := by decide
  have hdescent : baseEnd_3601922 < baseStart_3601922 := by decide
  rcases family_descends (prefixWord ++ tailWord_3601922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3601954 : List Nat := [3, 3, 1, 1, 1, 1, 2, 2, 5, 4]
def baseStart_3601954 : Nat := 118140960795 + 3601954 * 2 ^ 59
def prefixEnd_3601954 : Nat := 4983230072969 + 3 ^ 40 * 3601954 * 2
def baseEnd_3601954 : Nat := 616511232461635190703307

theorem tailTrace_3601954 : CollatzResearch.WordTrace tailWord_3601954 prefixEnd_3601954 616511232461635190703307 := by
  unfold tailWord_3601954
  simp only [CollatzResearch.WordTrace]
  refine ⟨32843513798185824403135229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87582703461828865075027277 32843513798185824403135229)
  ·
    refine ⟨12316317674319684151175711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32843513798185824403135229 12316317674319684151175711)
    ·
      refine ⟨18474476511479526226763567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12316317674319684151175711 18474476511479526226763567)
      ·
        refine ⟨27711714767219289340145351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18474476511479526226763567 27711714767219289340145351)
        ·
          refine ⟨41567572150828934010218027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27711714767219289340145351 41567572150828934010218027)
          ·
            refine ⟨62351358226243401015327041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41567572150828934010218027 62351358226243401015327041)
            ·
              refine ⟨46763518669682550761495281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62351358226243401015327041 46763518669682550761495281)
              ·
                refine ⟨35072639002261913071121461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46763518669682550761495281 35072639002261913071121461)
                ·
                  refine ⟨3288059906462054350417637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35072639002261913071121461 3288059906462054350417637)
                  ·
                    refine ⟨616511232461635190703307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3288059906462054350417637 616511232461635190703307)
                    ·
                      rfl

theorem cell23_3601954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 2, 5, 4].length) (baseStart_3601954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3601954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3601954 prefixEnd_3601954 := by exact prefixLift 3601954
  have htrace : WordTrace (prefixWord ++ tailWord_3601954) baseStart_3601954 baseEnd_3601954 := by
    simpa [prefixWord, tailWord_3601954, baseEnd_3601954] using wordTrace_append hprefix tailTrace_3601954
  have hstable : (prefixWord ++ tailWord_3601954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3601954).length < 2 ^ (prefixWord ++ tailWord_3601954).sum := by decide
  have hdescent : baseEnd_3601954 < baseStart_3601954 := by decide
  rcases family_descends (prefixWord ++ tailWord_3601954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3601971 : List Nat := [1, 1, 1, 2, 4, 5, 1, 1, 3, 4]
def baseStart_3601971 : Nat := 118140960795 + 3601971 * 2 ^ 59
def prefixEnd_3601971 : Nat := 4983230072969 + 3 ^ 40 * 3601971 * 2
def baseEnd_3601971 : Nat := 616514142185344001865781

theorem tailTrace_3601971 : CollatzResearch.WordTrace tailWord_3601971 prefixEnd_3601971 616514142185344001865781 := by
  unfold tailWord_3601971
  simp only [CollatzResearch.WordTrace]
  refine ⟨131374675233681709515909767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87583116822454473010606511 131374675233681709515909767)
  ·
    refine ⟨197062012850522564273864651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131374675233681709515909767 197062012850522564273864651)
    ·
      refine ⟨295593019275783846410796977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197062012850522564273864651 295593019275783846410796977)
      ·
        refine ⟨221694764456837884808097733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 295593019275783846410796977 221694764456837884808097733)
        ·
          refine ⟨41567768335657103401518325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 221694764456837884808097733 41567768335657103401518325)
          ·
            refine ⟨3896978281467853443892343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41567768335657103401518325 3896978281467853443892343)
            ·
              refine ⟨5845467422201780165838515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3896978281467853443892343 5845467422201780165838515)
              ·
                refine ⟨8768201133302670248757773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5845467422201780165838515 8768201133302670248757773)
                ·
                  refine ⟨3288075424988501343284165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8768201133302670248757773 3288075424988501343284165)
                  ·
                    refine ⟨616514142185344001865781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3288075424988501343284165 616514142185344001865781)
                    ·
                      rfl

theorem cell23_3601971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 1, 1, 3, 4].length) (baseStart_3601971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3601971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3601971 prefixEnd_3601971 := by exact prefixLift 3601971
  have htrace : WordTrace (prefixWord ++ tailWord_3601971) baseStart_3601971 baseEnd_3601971 := by
    simpa [prefixWord, tailWord_3601971, baseEnd_3601971] using wordTrace_append hprefix tailTrace_3601971
  have hstable : (prefixWord ++ tailWord_3601971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3601971).length < 2 ^ (prefixWord ++ tailWord_3601971).sum := by decide
  have hdescent : baseEnd_3601971 < baseStart_3601971 := by decide
  rcases family_descends (prefixWord ++ tailWord_3601971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3602044 : List Nat := [2, 2, 2, 1, 1, 2, 1, 2, 6, 4]
def baseStart_3602044 : Nat := 118140960795 + 3602044 * 2 ^ 59
def prefixEnd_3602044 : Nat := 4983230072969 + 3 ^ 40 * 3602044 * 2
def baseEnd_3602044 : Nat := 616526636881270073328169

theorem tailTrace_3602044 : CollatzResearch.WordTrace tailWord_3602044 prefixEnd_3602044 616526636881270073328169 := by
  unfold tailWord_3602044
  simp only [CollatzResearch.WordTrace]
  refine ⟨65688668881208621491658593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87584891841611495322211457 65688668881208621491658593)
  ·
    refine ⟨49266501660906466118743945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65688668881208621491658593 49266501660906466118743945)
    ·
      refine ⟨36949876245679849589057959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49266501660906466118743945 36949876245679849589057959)
      ·
        refine ⟨55424814368519774383586939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36949876245679849589057959 55424814368519774383586939)
        ·
          refine ⟨83137221552779661575380409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55424814368519774383586939 83137221552779661575380409)
          ·
            refine ⟨62352916164584746181535307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83137221552779661575380409 62352916164584746181535307)
            ·
              refine ⟨93529374246877119272302961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62352916164584746181535307 93529374246877119272302961)
              ·
                refine ⟨70147030685157839454227221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93529374246877119272302961 70147030685157839454227221)
                ·
                  refine ⟨3288142063366773724416901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 70147030685157839454227221 3288142063366773724416901)
                  ·
                    refine ⟨616526636881270073328169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3288142063366773724416901 616526636881270073328169)
                    ·
                      rfl

theorem cell23_3602044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 6, 4].length) (baseStart_3602044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3602044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3602044 prefixEnd_3602044 := by exact prefixLift 3602044
  have htrace : WordTrace (prefixWord ++ tailWord_3602044) baseStart_3602044 baseEnd_3602044 := by
    simpa [prefixWord, tailWord_3602044, baseEnd_3602044] using wordTrace_append hprefix tailTrace_3602044
  have hstable : (prefixWord ++ tailWord_3602044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3602044).length < 2 ^ (prefixWord ++ tailWord_3602044).sum := by decide
  have hdescent : baseEnd_3602044 < baseStart_3602044 := by decide
  rcases family_descends (prefixWord ++ tailWord_3602044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3602047 : List Nat := [1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 6]
def baseStart_3602047 : Nat := 118140960795 + 3602047 * 2 ^ 59
def prefixEnd_3602047 : Nat := 4983230072969 + 3 ^ 40 * 3602047 * 2
def baseEnd_3602047 : Nat := 1849581451085773708246993

theorem tailTrace_3602047 : CollatzResearch.WordTrace tailWord_3602047 prefixEnd_3602047 1849581451085773708246993 := by
  unfold tailWord_3602047
  simp only [CollatzResearch.WordTrace]
  refine ⟨131377447181406374495676395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87584964787604249663784263 131377447181406374495676395)
  ·
    refine ⟨197066170772109561743514593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131377447181406374495676395 197066170772109561743514593)
    ·
      refine ⟨147799628079082171307635945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197066170772109561743514593 147799628079082171307635945)
      ·
        refine ⟨110849721059311628480726959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147799628079082171307635945 110849721059311628480726959)
        ·
          refine ⟨166274581588967442721090439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110849721059311628480726959 166274581588967442721090439)
          ·
            refine ⟨249411872383451164081635659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166274581588967442721090439 249411872383451164081635659)
            ·
              refine ⟨374117808575176746122453489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249411872383451164081635659 374117808575176746122453489)
              ·
                refine ⟨280588356431382559591840117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 374117808575176746122453489 280588356431382559591840117)
                ·
                  refine ⟨26305158415442114961735011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 280588356431382559591840117 26305158415442114961735011)
                  ·
                    refine ⟨39457737623163172442602517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26305158415442114961735011 39457737623163172442602517)
                    ·
                      refine ⟨1849581451085773708246993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39457737623163172442602517 1849581451085773708246993)
                      ·
                        rfl

theorem cell23_3602047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 6].length) (baseStart_3602047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3602047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3602047 prefixEnd_3602047 := by exact prefixLift 3602047
  have htrace : WordTrace (prefixWord ++ tailWord_3602047) baseStart_3602047 baseEnd_3602047 := by
    simpa [prefixWord, tailWord_3602047, baseEnd_3602047] using wordTrace_append hprefix tailTrace_3602047
  have hstable : (prefixWord ++ tailWord_3602047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3602047).length < 2 ^ (prefixWord ++ tailWord_3602047).sum := by decide
  have hdescent : baseEnd_3602047 < baseStart_3602047 := by decide
  rcases family_descends (prefixWord ++ tailWord_3602047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3602057 : List Nat := [1, 2, 1, 1, 4, 1, 2, 11]
def baseStart_3602057 : Nat := 118140960795 + 3602057 * 2 ^ 59
def prefixEnd_3602057 : Nat := 4983230072969 + 3 ^ 40 * 3602057 * 2
def baseEnd_3602057 : Nat := 68503206884900691448961

theorem tailTrace_3602057 : CollatzResearch.WordTrace tailWord_3602057 prefixEnd_3602057 68503206884900691448961 := by
  unfold tailWord_3602057
  simp only [CollatzResearch.WordTrace]
  refine ⟨131377811911370146203540425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87585207940913430802360283 131377811911370146203540425)
  ·
    refine ⟨98533358933527609652655319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131377811911370146203540425 98533358933527609652655319)
    ·
      refine ⟨147800038400291414478982979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98533358933527609652655319 147800038400291414478982979)
      ·
        refine ⟨221700057600437121718474469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147800038400291414478982979 221700057600437121718474469)
        ·
          refine ⟨41568760800081960322213963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 221700057600437121718474469 41568760800081960322213963)
          ·
            refine ⟨62353141200122940483320945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41568760800081960322213963 62353141200122940483320945)
            ·
              refine ⟨46764855900092205362490709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62353141200122940483320945 46764855900092205362490709)
              ·
                refine ⟨68503206884900691448961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 46764855900092205362490709 68503206884900691448961)
                ·
                  rfl

theorem cell23_3602057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 11].length) (baseStart_3602057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3602057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3602057 prefixEnd_3602057 := by exact prefixLift 3602057
  have htrace : WordTrace (prefixWord ++ tailWord_3602057) baseStart_3602057 baseEnd_3602057 := by
    simpa [prefixWord, tailWord_3602057, baseEnd_3602057] using wordTrace_append hprefix tailTrace_3602057
  have hstable : (prefixWord ++ tailWord_3602057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3602057).length < 2 ^ (prefixWord ++ tailWord_3602057).sum := by decide
  have hdescent : baseEnd_3602057 < baseStart_3602057 := by decide
  rcases family_descends (prefixWord ++ tailWord_3602057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3602078 : List Nat := [4, 3, 1, 1, 1, 3, 1, 1, 4, 4]
def baseStart_3602078 : Nat := 118140960795 + 3602078 * 2 ^ 59
def prefixEnd_3602078 : Nat := 4983230072969 + 3 ^ 40 * 3602078 * 2
def baseEnd_3602078 : Nat := 616532456328687695653117

theorem tailTrace_3602078 : CollatzResearch.WordTrace tailWord_3602078 prefixEnd_3602078 616532456328687695653117 := by
  unfold tailWord_3602078
  simp only [CollatzResearch.WordTrace]
  refine ⟨16422322230536758348756861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87585718562862711193369925 16422322230536758348756861)
  ·
    refine ⟨6158370836451284380783823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16422322230536758348756861 6158370836451284380783823)
    ·
      refine ⟨9237556254676926571175735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6158370836451284380783823 9237556254676926571175735)
      ·
        refine ⟨13856334382015389856763603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9237556254676926571175735 13856334382015389856763603)
        ·
          refine ⟨20784501573023084785145405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13856334382015389856763603 20784501573023084785145405)
          ·
            refine ⟨7794188089883656794429527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20784501573023084785145405 7794188089883656794429527)
            ·
              refine ⟨11691282134825485191644291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7794188089883656794429527 11691282134825485191644291)
              ·
                refine ⟨17536923202238227787466437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11691282134825485191644291 17536923202238227787466437)
                ·
                  refine ⟨3288173100419667710149957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17536923202238227787466437 3288173100419667710149957)
                  ·
                    refine ⟨616532456328687695653117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3288173100419667710149957 616532456328687695653117)
                    ·
                      rfl

theorem cell23_3602078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 1, 4, 4].length) (baseStart_3602078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3602078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3602078 prefixEnd_3602078 := by exact prefixLift 3602078
  have htrace : WordTrace (prefixWord ++ tailWord_3602078) baseStart_3602078 baseEnd_3602078 := by
    simpa [prefixWord, tailWord_3602078, baseEnd_3602078] using wordTrace_append hprefix tailTrace_3602078
  have hstable : (prefixWord ++ tailWord_3602078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3602078).length < 2 ^ (prefixWord ++ tailWord_3602078).sum := by decide
  have hdescent : baseEnd_3602078 < baseStart_3602078 := by decide
  rcases family_descends (prefixWord ++ tailWord_3602078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3602085 : List Nat := [1, 3, 1, 2, 1, 2, 4, 4, 1, 2, 2]
def baseStart_3602085 : Nat := 118140960795 + 3602085 * 2 ^ 59
def prefixEnd_3602085 : Nat := 4983230072969 + 3 ^ 40 * 3602085 * 2
def baseEnd_3602085 : Nat := 1849600963350644559571819

theorem tailTrace_3602085 : CollatzResearch.WordTrace tailWord_3602085 prefixEnd_3602085 1849600963350644559571819 := by
  unfold tailWord_3602085
  simp only [CollatzResearch.WordTrace]
  refine ⟨131378833155268706985559709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87585888770179137990373139 131378833155268706985559709)
  ·
    refine ⟨49267062433225765119584891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131378833155268706985559709 49267062433225765119584891)
    ·
      refine ⟨73900593649838647679377337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49267062433225765119584891 73900593649838647679377337)
      ·
        refine ⟨55425445237378985759533003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73900593649838647679377337 55425445237378985759533003)
        ·
          refine ⟨83138167856068478639299505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55425445237378985759533003 83138167856068478639299505)
          ·
            refine ⟨62353625892051358979474629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83138167856068478639299505 62353625892051358979474629)
            ·
              refine ⟨11691304854759629808651493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62353625892051358979474629 11691304854759629808651493)
              ·
                refine ⟨2192119660267430589122155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11691304854759629808651493 2192119660267430589122155)
                ·
                  refine ⟨3288179490401145883683233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2192119660267430589122155 3288179490401145883683233)
                  ·
                    refine ⟨2466134617800859412762425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3288179490401145883683233 2466134617800859412762425)
                    ·
                      refine ⟨1849600963350644559571819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2466134617800859412762425 1849600963350644559571819)
                      ·
                        rfl

theorem cell23_3602085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 4, 1, 2, 2].length) (baseStart_3602085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3602085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3602085 prefixEnd_3602085 := by exact prefixLift 3602085
  have htrace : WordTrace (prefixWord ++ tailWord_3602085) baseStart_3602085 baseEnd_3602085 := by
    simpa [prefixWord, tailWord_3602085, baseEnd_3602085] using wordTrace_append hprefix tailTrace_3602085
  have hstable : (prefixWord ++ tailWord_3602085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3602085).length < 2 ^ (prefixWord ++ tailWord_3602085).sum := by decide
  have hdescent : baseEnd_3602085 < baseStart_3602085 := by decide
  rcases family_descends (prefixWord ++ tailWord_3602085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3602102 : List Nat := [5, 1, 3, 1, 1, 1, 2, 2, 3, 2, 2]
def baseStart_3602102 : Nat := 118140960795 + 3602102 * 2 ^ 59
def prefixEnd_3602102 : Nat := 4983230072969 + 3 ^ 40 * 3602102 * 2
def baseEnd_3602102 : Nat := 1849609692521770993059241

theorem tailTrace_3602102 : CollatzResearch.WordTrace tailWord_3602102 prefixEnd_3602102 1849609692521770993059241 := by
  unfold tailWord_3602102
  simp only [CollatzResearch.WordTrace]
  refine ⟨8211215824762944930558035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 87586302130804745925952373 8211215824762944930558035)
  ·
    refine ⟨12316823737144417395837053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8211215824762944930558035 12316823737144417395837053)
    ·
      refine ⟨4618808901429156523438895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12316823737144417395837053 4618808901429156523438895)
      ·
        refine ⟨6928213352143734785158343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4618808901429156523438895 6928213352143734785158343)
        ·
          refine ⟨10392320028215602177737515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6928213352143734785158343 10392320028215602177737515)
          ·
            refine ⟨15588480042323403266606273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10392320028215602177737515 15588480042323403266606273)
            ·
              refine ⟨11691360031742552449954705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15588480042323403266606273 11691360031742552449954705)
              ·
                refine ⟨8768520023806914337466029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11691360031742552449954705 8768520023806914337466029)
                ·
                  refine ⟨3288195008927592876549761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8768520023806914337466029 3288195008927592876549761)
                  ·
                    refine ⟨2466146256695694657412321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3288195008927592876549761 2466146256695694657412321)
                    ·
                      refine ⟨1849609692521770993059241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2466146256695694657412321 1849609692521770993059241)
                      ·
                        rfl

theorem cell23_3602102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 2, 3, 2, 2].length) (baseStart_3602102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3602102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3602102 prefixEnd_3602102 := by exact prefixLift 3602102
  have htrace : WordTrace (prefixWord ++ tailWord_3602102) baseStart_3602102 baseEnd_3602102 := by
    simpa [prefixWord, tailWord_3602102, baseEnd_3602102] using wordTrace_append hprefix tailTrace_3602102
  have hstable : (prefixWord ++ tailWord_3602102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3602102).length < 2 ^ (prefixWord ++ tailWord_3602102).sum := by decide
  have hdescent : baseEnd_3602102 < baseStart_3602102 := by decide
  rcases family_descends (prefixWord ++ tailWord_3602102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3602152 : List Nat := [2, 1, 4, 1, 3, 3, 2, 1, 2, 1, 3]
def baseStart_3602152 : Nat := 118140960795 + 3602152 * 2 ^ 59
def prefixEnd_3602152 : Nat := 4983230072969 + 3 ^ 40 * 3602152 * 2
def baseEnd_3602152 : Nat := 1849635366554495797434011

theorem tailTrace_3602152 : CollatzResearch.WordTrace tailWord_3602152 prefixEnd_3602152 1849635366554495797434011 := by
  unfold tailWord_3602152
  simp only [CollatzResearch.WordTrace]
  refine ⟨65690638423012988714124355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87587517897350651618832473 65690638423012988714124355)
  ·
    refine ⟨98535957634519483071186533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65690638423012988714124355 98535957634519483071186533)
    ·
      refine ⟨18475492056472403075847475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98535957634519483071186533 18475492056472403075847475)
      ·
        refine ⟨27713238084708604613771213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18475492056472403075847475 27713238084708604613771213)
        ·
          refine ⟨10392464281765726730164205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27713238084708604613771213 10392464281765726730164205)
          ·
            refine ⟨3897174105662147523811577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10392464281765726730164205 3897174105662147523811577)
            ·
              refine ⟨2922880579246610642858683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3897174105662147523811577 2922880579246610642858683)
              ·
                refine ⟨4384320868869915964288025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2922880579246610642858683 4384320868869915964288025)
                ·
                  refine ⟨3288240651652436973216019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4384320868869915964288025 3288240651652436973216019)
                  ·
                    refine ⟨4932360977478655459824029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3288240651652436973216019 4932360977478655459824029)
                    ·
                      refine ⟨1849635366554495797434011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4932360977478655459824029 1849635366554495797434011)
                      ·
                        rfl

theorem cell23_3602152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 2, 1, 2, 1, 3].length) (baseStart_3602152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3602152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3602152 prefixEnd_3602152 := by exact prefixLift 3602152
  have htrace : WordTrace (prefixWord ++ tailWord_3602152) baseStart_3602152 baseEnd_3602152 := by
    simpa [prefixWord, tailWord_3602152, baseEnd_3602152] using wordTrace_append hprefix tailTrace_3602152
  have hstable : (prefixWord ++ tailWord_3602152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3602152).length < 2 ^ (prefixWord ++ tailWord_3602152).sum := by decide
  have hdescent : baseEnd_3602152 < baseStart_3602152 := by decide
  rcases family_descends (prefixWord ++ tailWord_3602152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3602158 : List Nat := [4, 1, 2, 1, 1, 2, 2, 3, 1, 4, 2]
def baseStart_3602158 : Nat := 118140960795 + 3602158 * 2 ^ 59
def prefixEnd_3602158 : Nat := 4983230072969 + 3 ^ 40 * 3602158 * 2
def baseEnd_3602158 : Nat := 1849638447438422773958983

theorem tailTrace_3602158 : CollatzResearch.WordTrace tailWord_3602158 prefixEnd_3602158 1849638447438422773958983 := by
  unfold tailWord_3602158
  simp only [CollatzResearch.WordTrace]
  refine ⟨16422686960500530056620891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87587663789336160301978085 16422686960500530056620891)
  ·
    refine ⟨24634030440750795084931337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16422686960500530056620891 24634030440750795084931337)
    ·
      refine ⟨18475522830563096313698503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24634030440750795084931337 18475522830563096313698503)
      ·
        refine ⟨27713284245844644470547755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18475522830563096313698503 27713284245844644470547755)
        ·
          refine ⟨41569926368766966705821633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27713284245844644470547755 41569926368766966705821633)
          ·
            refine ⟨31177444776575225029366225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41569926368766966705821633 31177444776575225029366225)
            ·
              refine ⟨23383083582431418772024669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31177444776575225029366225 23383083582431418772024669)
              ·
                refine ⟨8768656343411782039509251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23383083582431418772024669 8768656343411782039509251)
                ·
                  refine ⟨13152984515117673059263877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8768656343411782039509251 13152984515117673059263877)
                  ·
                    refine ⟨2466184596584563698611977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13152984515117673059263877 2466184596584563698611977)
                    ·
                      refine ⟨1849638447438422773958983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2466184596584563698611977 1849638447438422773958983)
                      ·
                        rfl

theorem cell23_3602158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 3, 1, 4, 2].length) (baseStart_3602158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3602158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3602158 prefixEnd_3602158 := by exact prefixLift 3602158
  have htrace : WordTrace (prefixWord ++ tailWord_3602158) baseStart_3602158 baseEnd_3602158 := by
    simpa [prefixWord, tailWord_3602158, baseEnd_3602158] using wordTrace_append hprefix tailTrace_3602158
  have hstable : (prefixWord ++ tailWord_3602158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3602158).length < 2 ^ (prefixWord ++ tailWord_3602158).sum := by decide
  have hdescent : baseEnd_3602158 < baseStart_3602158 := by decide
  rcases family_descends (prefixWord ++ tailWord_3602158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3602228 : List Nat := [2, 5, 1, 1, 2, 2, 1, 1, 1, 7]
def baseStart_3602228 : Nat := 118140960795 + 3602228 * 2 ^ 59
def prefixEnd_3602228 : Nat := 4983230072969 + 3 ^ 40 * 3602228 * 2
def baseEnd_3602228 : Nat := 616558130361412500027887

theorem tailTrace_3602228 : CollatzResearch.WordTrace tailWord_3602228 prefixEnd_3602228 616558130361412500027887 := by
  unfold tailWord_3602228
  simp only [CollatzResearch.WordTrace]
  refine ⟨65692024396875321204007669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87589365862500428272010225 65692024396875321204007669)
  ·
    refine ⟨6158627287207061362875719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 65692024396875321204007669 6158627287207061362875719)
    ·
      refine ⟨9237940930810592044313579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6158627287207061362875719 9237940930810592044313579)
      ·
        refine ⟨13856911396215888066470369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9237940930810592044313579 13856911396215888066470369)
        ·
          refine ⟨10392683547161916049852777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13856911396215888066470369 10392683547161916049852777)
          ·
            refine ⟨7794512660371437037389583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10392683547161916049852777 7794512660371437037389583)
            ·
              refine ⟨11691768990557155556084375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7794512660371437037389583 11691768990557155556084375)
              ·
                refine ⟨17537653485835733334126563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11691768990557155556084375 17537653485835733334126563)
                ·
                  refine ⟨26306480228753600001189845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17537653485835733334126563 26306480228753600001189845)
                  ·
                    refine ⟨616558130361412500027887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26306480228753600001189845 616558130361412500027887)
                    ·
                      rfl

theorem cell23_3602228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_3602228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3602228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3602228 prefixEnd_3602228 := by exact prefixLift 3602228
  have htrace : WordTrace (prefixWord ++ tailWord_3602228) baseStart_3602228 baseEnd_3602228 := by
    simpa [prefixWord, tailWord_3602228, baseEnd_3602228] using wordTrace_append hprefix tailTrace_3602228
  have hstable : (prefixWord ++ tailWord_3602228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3602228).length < 2 ^ (prefixWord ++ tailWord_3602228).sum := by decide
  have hdescent : baseEnd_3602228 < baseStart_3602228 := by decide
  rcases family_descends (prefixWord ++ tailWord_3602228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3602231 : List Nat := [1, 1, 3, 1, 2, 1, 2, 5, 2, 1, 4]
def baseStart_3602231 : Nat := 118140960795 + 3602231 * 2 ^ 59
def prefixEnd_3602231 : Nat := 4983230072969 + 3 ^ 40 * 3602231 * 2
def baseEnd_3602231 : Nat := 1849675931526200988346147

theorem tailTrace_3602231 : CollatzResearch.WordTrace tailWord_3602231 prefixEnd_3602231 1849675931526200988346147 := by
  unfold tailWord_3602231
  simp only [CollatzResearch.WordTrace]
  refine ⟨131384158212739773920374547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87589438808493182613583031 131384158212739773920374547)
  ·
    refine ⟨197076237319109660880561821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131384158212739773920374547 197076237319109660880561821)
    ·
      refine ⟨73903588994666122830210683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197076237319109660880561821 73903588994666122830210683)
      ·
        refine ⟨110855383491999184245316025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73903588994666122830210683 110855383491999184245316025)
        ·
          refine ⟨83141537618999388183987019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110855383491999184245316025 83141537618999388183987019)
          ·
            refine ⟨124712306428499082275980529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83141537618999388183987019 124712306428499082275980529)
            ·
              refine ⟨93534229821374311706985397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124712306428499082275980529 93534229821374311706985397)
              ·
                refine ⟨8768834045753841722529881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 93534229821374311706985397 8768834045753841722529881)
                ·
                  refine ⟨6576625534315381291897411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8768834045753841722529881 6576625534315381291897411)
                  ·
                    refine ⟨9864938301473071937846117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6576625534315381291897411 9864938301473071937846117)
                    ·
                      refine ⟨1849675931526200988346147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9864938301473071937846117 1849675931526200988346147)
                      ·
                        rfl

theorem cell23_3602231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 5, 2, 1, 4].length) (baseStart_3602231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3602231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3602231 prefixEnd_3602231 := by exact prefixLift 3602231
  have htrace : WordTrace (prefixWord ++ tailWord_3602231) baseStart_3602231 baseEnd_3602231 := by
    simpa [prefixWord, tailWord_3602231, baseEnd_3602231] using wordTrace_append hprefix tailTrace_3602231
  have hstable : (prefixWord ++ tailWord_3602231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3602231).length < 2 ^ (prefixWord ++ tailWord_3602231).sum := by decide
  have hdescent : baseEnd_3602231 < baseStart_3602231 := by decide
  rcases family_descends (prefixWord ++ tailWord_3602231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3602248 : List Nat := [2, 1, 3, 1, 1, 4, 1, 2, 2, 4, 2]
def baseStart_3602248 : Nat := 118140960795 + 3602248 * 2 ^ 59
def prefixEnd_3602248 : Nat := 4983230072969 + 3 ^ 40 * 3602248 * 2
def baseEnd_3602248 : Nat := 1849684660697327421833569

theorem tailTrace_3602248 : CollatzResearch.WordTrace tailWord_3602248 prefixEnd_3602248 1849684660697327421833569 := by
  unfold tailWord_3602248
  simp only [CollatzResearch.WordTrace]
  refine ⟨65692389126839092911871699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87589852169118790549162265 65692389126839092911871699)
  ·
    refine ⟨98538583690258639367807549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65692389126839092911871699 98538583690258639367807549)
    ·
      refine ⟨36951968883846989762927831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98538583690258639367807549 36951968883846989762927831)
      ·
        refine ⟨55427953325770484644391747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36951968883846989762927831 55427953325770484644391747)
        ·
          refine ⟨83141929988655726966587621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55427953325770484644391747 83141929988655726966587621)
          ·
            refine ⟨15589111872872948806235179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83141929988655726966587621 15589111872872948806235179)
            ·
              refine ⟨23383667809309423209352769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15589111872872948806235179 23383667809309423209352769)
              ·
                refine ⟨17537750856982067407014577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23383667809309423209352769 17537750856982067407014577)
                ·
                  refine ⟨13153313142736550555260933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17537750856982067407014577 13153313142736550555260933)
                  ·
                    refine ⟨2466246214263103229111425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13153313142736550555260933 2466246214263103229111425)
                    ·
                      refine ⟨1849684660697327421833569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2466246214263103229111425 1849684660697327421833569)
                      ·
                        rfl

theorem cell23_3602248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 2, 2, 4, 2].length) (baseStart_3602248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3602248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3602248 prefixEnd_3602248 := by exact prefixLift 3602248
  have htrace : WordTrace (prefixWord ++ tailWord_3602248) baseStart_3602248 baseEnd_3602248 := by
    simpa [prefixWord, tailWord_3602248, baseEnd_3602248] using wordTrace_append hprefix tailTrace_3602248
  have hstable : (prefixWord ++ tailWord_3602248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3602248).length < 2 ^ (prefixWord ++ tailWord_3602248).sum := by decide
  have hdescent : baseEnd_3602248 < baseStart_3602248 := by decide
  rcases family_descends (prefixWord ++ tailWord_3602248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3602258 : List Nat := [3, 2, 2, 1, 1, 3, 1, 3, 3, 4]
def baseStart_3602258 : Nat := 118140960795 + 3602258 * 2 ^ 59
def prefixEnd_3602258 : Nat := 4983230072969 + 3 ^ 40 * 3602258 * 2
def baseEnd_3602258 : Nat := 616563265167957460902841

theorem tailTrace_3602258 : CollatzResearch.WordTrace tailWord_3602258 prefixEnd_3602258 616563265167957460902841 := by
  unfold tailWord_3602258
  simp only [CollatzResearch.WordTrace]
  refine ⟨32846285745910489382901857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87590095322427971687738285 32846285745910489382901857)
  ·
    refine ⟨24634714309432867037176393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32846285745910489382901857 24634714309432867037176393)
    ·
      refine ⟨18476035732074650277882295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24634714309432867037176393 18476035732074650277882295)
      ·
        refine ⟨27714053598111975416823443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18476035732074650277882295 27714053598111975416823443)
        ·
          refine ⟨41571080397167963125235165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27714053598111975416823443 41571080397167963125235165)
          ·
            refine ⟨15589155148937986171963187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41571080397167963125235165 15589155148937986171963187)
            ·
              refine ⟨23383732723406979257944781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15589155148937986171963187 23383732723406979257944781)
              ·
                refine ⟨8768899771277617221729293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23383732723406979257944781 8768899771277617221729293)
                ·
                  refine ⟨3288337414229106458148485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8768899771277617221729293 3288337414229106458148485)
                  ·
                    refine ⟨616563265167957460902841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3288337414229106458148485 616563265167957460902841)
                    ·
                      rfl

theorem cell23_3602258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 3, 3, 4].length) (baseStart_3602258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3602258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3602258 prefixEnd_3602258 := by exact prefixLift 3602258
  have htrace : WordTrace (prefixWord ++ tailWord_3602258) baseStart_3602258 baseEnd_3602258 := by
    simpa [prefixWord, tailWord_3602258, baseEnd_3602258] using wordTrace_append hprefix tailTrace_3602258
  have hstable : (prefixWord ++ tailWord_3602258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3602258).length < 2 ^ (prefixWord ++ tailWord_3602258).sum := by decide
  have hdescent : baseEnd_3602258 < baseStart_3602258 := by decide
  rcases family_descends (prefixWord ++ tailWord_3602258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3602298 : List Nat := [3, 1, 1, 1, 1, 1, 4, 2, 5, 1, 3]
def baseStart_3602298 : Nat := 118140960795 + 3602298 * 2 ^ 59
def prefixEnd_3602298 : Nat := 4983230072969 + 3 ^ 40 * 3602298 * 2
def baseEnd_3602298 : Nat := 1849710334730052226208339

theorem tailTrace_3602298 : CollatzResearch.WordTrace tailWord_3602298 prefixEnd_3602298 1849710334730052226208339 := by
  unfold tailWord_3602298
  simp only [CollatzResearch.WordTrace]
  refine ⟨32846650475874261090765887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87591067935664696242042365 32846650475874261090765887)
  ·
    refine ⟨49269975713811391636148831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32846650475874261090765887 49269975713811391636148831)
    ·
      refine ⟨73904963570717087454223247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49269975713811391636148831 73904963570717087454223247)
      ·
        refine ⟨110857445356075631181334871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73904963570717087454223247 110857445356075631181334871)
        ·
          refine ⟨166286168034113446772002307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110857445356075631181334871 166286168034113446772002307)
          ·
            refine ⟨249429252051170170158003461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166286168034113446772002307 249429252051170170158003461)
            ·
              refine ⟨46767984759594406904625649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 249429252051170170158003461 46767984759594406904625649)
              ·
                refine ⟨35075988569695805178469237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46767984759594406904625649 35075988569695805178469237)
                ·
                  refine ⟨3288373928408981735481491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35075988569695805178469237 3288373928408981735481491)
                  ·
                    refine ⟨4932560892613472603222237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3288373928408981735481491 4932560892613472603222237)
                    ·
                      refine ⟨1849710334730052226208339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4932560892613472603222237 1849710334730052226208339)
                      ·
                        rfl

theorem cell23_3602298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 2, 5, 1, 3].length) (baseStart_3602298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3602298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3602298 prefixEnd_3602298 := by exact prefixLift 3602298
  have htrace : WordTrace (prefixWord ++ tailWord_3602298) baseStart_3602298 baseEnd_3602298 := by
    simpa [prefixWord, tailWord_3602298, baseEnd_3602298] using wordTrace_append hprefix tailTrace_3602298
  have hstable : (prefixWord ++ tailWord_3602298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3602298).length < 2 ^ (prefixWord ++ tailWord_3602298).sum := by decide
  have hdescent : baseEnd_3602298 < baseStart_3602298 := by decide
  rcases family_descends (prefixWord ++ tailWord_3602298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3602301 : List Nat := [1, 4, 1, 1, 2, 1, 1, 2, 5, 5]
def baseStart_3602301 : Nat := 118140960795 + 3602301 * 2 ^ 59
def prefixEnd_3602301 : Nat := 4983230072969 + 3 ^ 40 * 3602301 * 2
def baseEnd_3602301 : Nat := 616570625057338571490275

theorem tailTrace_3602301 : CollatzResearch.WordTrace tailWord_3602301 prefixEnd_3602301 616570625057338571490275 := by
  unfold tailWord_3602301
  simp only [CollatzResearch.WordTrace]
  refine ⟨131386711322486175875422757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87591140881657450583615171 131386711322486175875422757)
  ·
    refine ⟨24635008372966157976641767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131386711322486175875422757 24635008372966157976641767)
    ·
      refine ⟨36952512559449236964962651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24635008372966157976641767 36952512559449236964962651)
      ·
        refine ⟨55428768839173855447443977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36952512559449236964962651 55428768839173855447443977)
        ·
          refine ⟨41571576629380391585582983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55428768839173855447443977 41571576629380391585582983)
          ·
            refine ⟨62357364944070587378374475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41571576629380391585582983 62357364944070587378374475)
            ·
              refine ⟨93536047416105881067561713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62357364944070587378374475 93536047416105881067561713)
              ·
                refine ⟨70152035562079410800671285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93536047416105881067561713 70152035562079410800671285)
                ·
                  refine ⟨6576753333944944762562933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70152035562079410800671285 6576753333944944762562933)
                  ·
                    refine ⟨616570625057338571490275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6576753333944944762562933 616570625057338571490275)
                    ·
                      rfl

theorem cell23_3602301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 5, 5].length) (baseStart_3602301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3602301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3602301 prefixEnd_3602301 := by exact prefixLift 3602301
  have htrace : WordTrace (prefixWord ++ tailWord_3602301) baseStart_3602301 baseEnd_3602301 := by
    simpa [prefixWord, tailWord_3602301, baseEnd_3602301] using wordTrace_append hprefix tailTrace_3602301
  have hstable : (prefixWord ++ tailWord_3602301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3602301).length < 2 ^ (prefixWord ++ tailWord_3602301).sum := by decide
  have hdescent : baseEnd_3602301 < baseStart_3602301 := by decide
  rcases family_descends (prefixWord ++ tailWord_3602301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3602302 : List Nat := [4, 2, 3, 1, 1, 2, 1, 2, 2, 2, 3]
def baseStart_3602302 : Nat := 118140960795 + 3602302 * 2 ^ 59
def prefixEnd_3602302 : Nat := 4983230072969 + 3 ^ 40 * 3602302 * 2
def baseEnd_3602302 : Nat := 1849712388652670210558321

theorem tailTrace_3602302 : CollatzResearch.WordTrace tailWord_3602302 prefixEnd_3602302 1849712388652670210558321 := by
  unfold tailWord_3602302
  simp only [CollatzResearch.WordTrace]
  refine ⟨16423343474435319130776145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87591165196988368697472773 16423343474435319130776145)
  ·
    refine ⟨12317507605826489348082109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16423343474435319130776145 12317507605826489348082109)
    ·
      refine ⟨4619065352184933505530791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12317507605826489348082109 4619065352184933505530791)
      ·
        refine ⟨6928598028277400258296187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4619065352184933505530791 6928598028277400258296187)
        ·
          refine ⟨10392897042416100387444281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6928598028277400258296187 10392897042416100387444281)
          ·
            refine ⟨7794672781812075290583211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10392897042416100387444281 7794672781812075290583211)
            ·
              refine ⟨11692009172718112935874817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7794672781812075290583211 11692009172718112935874817)
              ·
                refine ⟨8769006879538584701906113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11692009172718112935874817 8769006879538584701906113)
                ·
                  refine ⟨6576755159653938526429585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8769006879538584701906113 6576755159653938526429585)
                  ·
                    refine ⟨4932566369740453894822189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6576755159653938526429585 4932566369740453894822189)
                    ·
                      refine ⟨1849712388652670210558321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4932566369740453894822189 1849712388652670210558321)
                      ·
                        rfl

theorem cell23_3602302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_3602302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3602302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3602302 prefixEnd_3602302 := by exact prefixLift 3602302
  have htrace : WordTrace (prefixWord ++ tailWord_3602302) baseStart_3602302 baseEnd_3602302 := by
    simpa [prefixWord, tailWord_3602302, baseEnd_3602302] using wordTrace_append hprefix tailTrace_3602302
  have hstable : (prefixWord ++ tailWord_3602302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3602302).length < 2 ^ (prefixWord ++ tailWord_3602302).sum := by decide
  have hdescent : baseEnd_3602302 < baseStart_3602302 := by decide
  rcases family_descends (prefixWord ++ tailWord_3602302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3602322 : List Nat := [3, 2, 3, 2, 1, 3, 2, 1, 6]
def baseStart_3602322 : Nat := 118140960795 + 3602322 * 2 ^ 59
def prefixEnd_3602322 : Nat := 4983230072969 + 3 ^ 40 * 3602322 * 2
def baseEnd_3602322 : Nat := 205524739807306681367581

theorem tailTrace_3602322 : CollatzResearch.WordTrace tailWord_3602322 prefixEnd_3602322 205524739807306681367581 := by
  unfold tailWord_3602322
  simp only [CollatzResearch.WordTrace]
  refine ⟨32846869313852524115484305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87591651503606730974624813 32846869313852524115484305)
  ·
    refine ⟨24635151985389393086613229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32846869313852524115484305 24635151985389393086613229)
    ·
      refine ⟨9238181994521022407479961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24635151985389393086613229 9238181994521022407479961)
      ·
        refine ⟨6928636495890766805609971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9238181994521022407479961 6928636495890766805609971)
        ·
          refine ⟨10392954743836150208414957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6928636495890766805609971 10392954743836150208414957)
          ·
            refine ⟨3897358028938556328155609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10392954743836150208414957 3897358028938556328155609)
            ·
              refine ⟨2923018521703917246116707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3897358028938556328155609 2923018521703917246116707)
              ·
                refine ⟨4384527782555875869175061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2923018521703917246116707 4384527782555875869175061)
                ·
                  refine ⟨205524739807306681367581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4384527782555875869175061 205524739807306681367581)
                  ·
                    rfl

theorem cell23_3602322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 2, 1, 6].length) (baseStart_3602322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3602322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3602322 prefixEnd_3602322 := by exact prefixLift 3602322
  have htrace : WordTrace (prefixWord ++ tailWord_3602322) baseStart_3602322 baseEnd_3602322 := by
    simpa [prefixWord, tailWord_3602322, baseEnd_3602322] using wordTrace_append hprefix tailTrace_3602322
  have hstable : (prefixWord ++ tailWord_3602322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3602322).length < 2 ^ (prefixWord ++ tailWord_3602322).sum := by decide
  have hdescent : baseEnd_3602322 < baseStart_3602322 := by decide
  rcases family_descends (prefixWord ++ tailWord_3602322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3602341 : List Nat := [1, 3, 1, 2, 1, 1, 1, 4, 3, 1, 5]
def baseStart_3602341 : Nat := 118140960795 + 3602341 * 2 ^ 59
def prefixEnd_3602341 : Nat := 4983230072969 + 3 ^ 40 * 3602341 * 2
def baseEnd_3602341 : Nat := 1849732414398195557970641

theorem tailTrace_3602341 : CollatzResearch.WordTrace tailWord_3602341 prefixEnd_3602341 1849732414398195557970641 := by
  unfold tailWord_3602341
  simp only [CollatzResearch.WordTrace]
  refine ⟨131388170242341262706878877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87592113494894175137919251 131388170242341262706878877)
  ·
    refine ⟨49270563840877973515079579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131388170242341262706878877 49270563840877973515079579)
    ·
      refine ⟨73905845761316960272619369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49270563840877973515079579 73905845761316960272619369)
      ·
        refine ⟨55429384320987720204464527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73905845761316960272619369 55429384320987720204464527)
        ·
          refine ⟨83144076481481580306696791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55429384320987720204464527 83144076481481580306696791)
          ·
            refine ⟨124716114722222370460045187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83144076481481580306696791 124716114722222370460045187)
            ·
              refine ⟨187074172083333555690067781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124716114722222370460045187 187074172083333555690067781)
              ·
                refine ⟨35076407265625041691887709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 187074172083333555690067781 35076407265625041691887709)
                ·
                  refine ⟨13153652724609390634457891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35076407265625041691887709 13153652724609390634457891)
                  ·
                    refine ⟨19730479086914085951686837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13153652724609390634457891 19730479086914085951686837)
                    ·
                      refine ⟨1849732414398195557970641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19730479086914085951686837 1849732414398195557970641)
                      ·
                        rfl

theorem cell23_3602341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 4, 3, 1, 5].length) (baseStart_3602341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3602341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3602341 prefixEnd_3602341 := by exact prefixLift 3602341
  have htrace : WordTrace (prefixWord ++ tailWord_3602341) baseStart_3602341 baseEnd_3602341 := by
    simpa [prefixWord, tailWord_3602341, baseEnd_3602341] using wordTrace_append hprefix tailTrace_3602341
  have hstable : (prefixWord ++ tailWord_3602341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3602341).length < 2 ^ (prefixWord ++ tailWord_3602341).sum := by decide
  have hdescent : baseEnd_3602341 < baseStart_3602341 := by decide
  rcases family_descends (prefixWord ++ tailWord_3602341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3602355 : List Nat := [1, 1, 1, 2, 3, 1, 7, 1, 1, 1, 4]
def baseStart_3602355 : Nat := 118140960795 + 3602355 * 2 ^ 59
def prefixEnd_3602355 : Nat := 4983230072969 + 3 ^ 40 * 3602355 * 2
def baseEnd_3602355 : Nat := 1849739603127358503195577

theorem tailTrace_3602355 : CollatzResearch.WordTrace tailWord_3602355 prefixEnd_3602355 1849739603127358503195577 := by
  unfold tailWord_3602355
  simp only [CollatzResearch.WordTrace]
  refine ⟨131388680864290543097888519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87592453909527028731925679 131388680864290543097888519)
  ·
    refine ⟨197083021296435814646832779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131388680864290543097888519 197083021296435814646832779)
    ·
      refine ⟨295624531944653721970249169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197083021296435814646832779 295624531944653721970249169)
      ·
        refine ⟨221718398958490291477686877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 295624531944653721970249169 221718398958490291477686877)
        ·
          refine ⟨83144399609433859304132579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 221718398958490291477686877 83144399609433859304132579)
          ·
            refine ⟨124716599414150788956198869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83144399609433859304132579 124716599414150788956198869)
            ·
              refine ⟨2923045298769159116160911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 124716599414150788956198869 2923045298769159116160911)
              ·
                refine ⟨4384567948153738674241367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2923045298769159116160911 4384567948153738674241367)
                ·
                  refine ⟨6576851922230608011362051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4384567948153738674241367 6576851922230608011362051)
                  ·
                    refine ⟨9865277883345912017043077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6576851922230608011362051 9865277883345912017043077)
                    ·
                      refine ⟨1849739603127358503195577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9865277883345912017043077 1849739603127358503195577)
                      ·
                        rfl

theorem cell23_3602355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 7, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 7, 1, 1, 1, 4].length) (baseStart_3602355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3602355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3602355 prefixEnd_3602355 := by exact prefixLift 3602355
  have htrace : WordTrace (prefixWord ++ tailWord_3602355) baseStart_3602355 baseEnd_3602355 := by
    simpa [prefixWord, tailWord_3602355, baseEnd_3602355] using wordTrace_append hprefix tailTrace_3602355
  have hstable : (prefixWord ++ tailWord_3602355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3602355).length < 2 ^ (prefixWord ++ tailWord_3602355).sum := by decide
  have hdescent : baseEnd_3602355 < baseStart_3602355 := by decide
  rcases family_descends (prefixWord ++ tailWord_3602355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3602365 : List Nat := [1, 4, 1, 2, 3, 1, 1, 4, 2, 4]
def baseStart_3602365 : Nat := 118140960795 + 3602365 * 2 ^ 59
def prefixEnd_3602365 : Nat := 4983230072969 + 3 ^ 40 * 3602365 * 2
def baseEnd_3602365 : Nat := 616581579311301154690177

theorem tailTrace_3602365 : CollatzResearch.WordTrace tailWord_3602365 prefixEnd_3602365 616581579311301154690177 := by
  unfold tailWord_3602365
  simp only [CollatzResearch.WordTrace]
  refine ⟨131389045594254314805752549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87592697062836209870501699 131389045594254314805752549)
  ·
    refine ⟨24635446048922684026078603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131389045594254314805752549 24635446048922684026078603)
    ·
      refine ⟨36953169073384026039117905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24635446048922684026078603 36953169073384026039117905)
      ·
        refine ⟨27714876805038019529338429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36953169073384026039117905 27714876805038019529338429)
        ·
          refine ⟨10393078801889257323501911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27714876805038019529338429 10393078801889257323501911)
          ·
            refine ⟨15589618202833885985252867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10393078801889257323501911 15589618202833885985252867)
            ·
              refine ⟨23384427304250828977879301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15589618202833885985252867 23384427304250828977879301)
              ·
                refine ⟨4384580119547030433352369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23384427304250828977879301 4384580119547030433352369)
                ·
                  refine ⟨3288435089660272825014277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4384580119547030433352369 3288435089660272825014277)
                  ·
                    refine ⟨616581579311301154690177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3288435089660272825014277 616581579311301154690177)
                    ·
                      rfl

theorem cell23_3602365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 4, 2, 4].length) (baseStart_3602365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3602365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3602365 prefixEnd_3602365 := by exact prefixLift 3602365
  have htrace : WordTrace (prefixWord ++ tailWord_3602365) baseStart_3602365 baseEnd_3602365 := by
    simpa [prefixWord, tailWord_3602365, baseEnd_3602365] using wordTrace_append hprefix tailTrace_3602365
  have hstable : (prefixWord ++ tailWord_3602365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3602365).length < 2 ^ (prefixWord ++ tailWord_3602365).sum := by decide
  have hdescent : baseEnd_3602365 < baseStart_3602365 := by decide
  rcases family_descends (prefixWord ++ tailWord_3602365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3602366 : List Nat := [4, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3]
def baseStart_3602366 : Nat := 118140960795 + 3602366 * 2 ^ 59
def prefixEnd_3602366 : Nat := 4983230072969 + 3 ^ 40 * 3602366 * 2
def baseEnd_3602366 : Nat := 1849745251414557960158027

theorem tailTrace_3602366 : CollatzResearch.WordTrace tailWord_3602366 prefixEnd_3602366 1849745251414557960158027 := by
  unfold tailWord_3602366
  simp only [CollatzResearch.WordTrace]
  refine ⟨16423635258406336497067369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87592721378167127984359301 16423635258406336497067369)
  ·
    refine ⟨12317726443804752372800527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16423635258406336497067369 12317726443804752372800527)
    ·
      refine ⟨18476589665707128559200791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12317726443804752372800527 18476589665707128559200791)
      ·
        refine ⟨27714884498560692838801187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18476589665707128559200791 27714884498560692838801187)
        ·
          refine ⟨41572326747841039258201781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27714884498560692838801187 41572326747841039258201781)
          ·
            refine ⟨3897405632610097430456417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41572326747841039258201781 3897405632610097430456417)
            ·
              refine ⟨2923054224457573072842313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3897405632610097430456417 2923054224457573072842313)
              ·
                refine ⟨2192290668343179804631735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2923054224457573072842313 2192290668343179804631735)
                ·
                  refine ⟨3288436002514769706947603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2192290668343179804631735 3288436002514769706947603)
                  ·
                    refine ⟨4932654003772154560421405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3288436002514769706947603 4932654003772154560421405)
                    ·
                      refine ⟨1849745251414557960158027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4932654003772154560421405 1849745251414557960158027)
                      ·
                        rfl

theorem cell23_3602366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3].length) (baseStart_3602366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3602366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3602366 prefixEnd_3602366 := by exact prefixLift 3602366
  have htrace : WordTrace (prefixWord ++ tailWord_3602366) baseStart_3602366 baseEnd_3602366 := by
    simpa [prefixWord, tailWord_3602366, baseEnd_3602366] using wordTrace_append hprefix tailTrace_3602366
  have hstable : (prefixWord ++ tailWord_3602366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3602366).length < 2 ^ (prefixWord ++ tailWord_3602366).sum := by decide
  have hdescent : baseEnd_3602366 < baseStart_3602366 := by decide
  rcases family_descends (prefixWord ++ tailWord_3602366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3602391 : List Nat := [1, 1, 3, 2, 1, 1, 3, 2, 2, 7]
def baseStart_3602391 : Nat := 118140960795 + 3602391 * 2 ^ 59
def prefixEnd_3602391 : Nat := 4983230072969 + 3 ^ 40 * 3602391 * 2
def baseEnd_3602391 : Nat := 616586029476973454115137

theorem tailTrace_3602391 : CollatzResearch.WordTrace tailWord_3602391 prefixEnd_3602391 616586029476973454115137 := by
  unfold tailWord_3602391
  simp only [CollatzResearch.WordTrace]
  refine ⟨131389993892160121246199027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87593329261440080830799351 131389993892160121246199027)
  ·
    refine ⟨197084990838240181869298541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131389993892160121246199027 197084990838240181869298541)
    ·
      refine ⟨73906871564340068200986953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197084990838240181869298541 73906871564340068200986953)
      ·
        refine ⟨55430153673255051150740215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73906871564340068200986953 55430153673255051150740215)
        ·
          refine ⟨83145230509882576726110323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55430153673255051150740215 83145230509882576726110323)
          ·
            refine ⟨124717845764823865089165485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83145230509882576726110323 124717845764823865089165485)
            ·
              refine ⟨46769192161808949408437057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124717845764823865089165485 46769192161808949408437057)
              ·
                refine ⟨35076894121356712056327793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46769192161808949408437057 35076894121356712056327793)
                ·
                  refine ⟨26307670591017534042245845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35076894121356712056327793 26307670591017534042245845)
                  ·
                    refine ⟨616586029476973454115137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26307670591017534042245845 616586029476973454115137)
                    ·
                      rfl

theorem cell23_3602391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 2, 2, 7].length) (baseStart_3602391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3602391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3602391 prefixEnd_3602391 := by exact prefixLift 3602391
  have htrace : WordTrace (prefixWord ++ tailWord_3602391) baseStart_3602391 baseEnd_3602391 := by
    simpa [prefixWord, tailWord_3602391, baseEnd_3602391] using wordTrace_append hprefix tailTrace_3602391
  have hstable : (prefixWord ++ tailWord_3602391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3602391).length < 2 ^ (prefixWord ++ tailWord_3602391).sum := by decide
  have hdescent : baseEnd_3602391 < baseStart_3602391 := by decide
  rcases family_descends (prefixWord ++ tailWord_3602391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3602439 : List Nat := [1, 1, 4, 3, 1, 3, 3, 1, 2, 1, 3]
def baseStart_3602439 : Nat := 118140960795 + 3602439 * 2 ^ 59
def prefixEnd_3602439 : Nat := 4983230072969 + 3 ^ 40 * 3602439 * 2
def baseEnd_3602439 : Nat := 1849782735502336174545191

theorem tailTrace_3602439 : CollatzResearch.WordTrace tailWord_3602439 prefixEnd_3602439 1849782735502336174545191 := by
  unfold tailWord_3602439
  simp only [CollatzResearch.WordTrace]
  refine ⟨131391744595986225443946371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87594496397324150295964247 131391744595986225443946371)
  ·
    refine ⟨197087616893979338165919557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131391744595986225443946371 197087616893979338165919557)
    ·
      refine ⟨36953928167621125906109917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 197087616893979338165919557 36953928167621125906109917)
      ·
        refine ⟨13857723062857922214791219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36953928167621125906109917 13857723062857922214791219)
        ·
          refine ⟨20786584594286883322186829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13857723062857922214791219 20786584594286883322186829)
          ·
            refine ⟨7794969222857581245820061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20786584594286883322186829 7794969222857581245820061)
            ·
              refine ⟨2923113458571592967182523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7794969222857581245820061 2923113458571592967182523)
              ·
                refine ⟨4384670187857389450773785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2923113458571592967182523 4384670187857389450773785)
                ·
                  refine ⟨3288502640893042088080339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4384670187857389450773785 3288502640893042088080339)
                  ·
                    refine ⟨4932753961339563132120509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3288502640893042088080339 4932753961339563132120509)
                    ·
                      refine ⟨1849782735502336174545191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4932753961339563132120509 1849782735502336174545191)
                      ·
                        rfl

theorem cell23_3602439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 3, 1, 2, 1, 3].length) (baseStart_3602439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3602439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3602439 prefixEnd_3602439 := by exact prefixLift 3602439
  have htrace : WordTrace (prefixWord ++ tailWord_3602439) baseStart_3602439 baseEnd_3602439 := by
    simpa [prefixWord, tailWord_3602439, baseEnd_3602439] using wordTrace_append hprefix tailTrace_3602439
  have hstable : (prefixWord ++ tailWord_3602439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3602439).length < 2 ^ (prefixWord ++ tailWord_3602439).sum := by decide
  have hdescent : baseEnd_3602439 < baseStart_3602439 := by decide
  rcases family_descends (prefixWord ++ tailWord_3602439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3602465 : List Nat := [1, 2, 3, 2, 4, 1, 1, 1, 2, 1, 5]
def baseStart_3602465 : Nat := 118140960795 + 3602465 * 2 ^ 59
def prefixEnd_3602465 : Nat := 4983230072969 + 3 ^ 40 * 3602465 * 2
def baseEnd_3602465 : Nat := 1849796085999353072820071

theorem tailTrace_3602465 : CollatzResearch.WordTrace tailWord_3602465 prefixEnd_3602465 1849796085999353072820071 := by
  unfold tailWord_3602465
  simp only [CollatzResearch.WordTrace]
  refine ⟨131392692893892031884392849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87595128595928021256261899 131392692893892031884392849)
  ·
    refine ⟨98544519670419023913294637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131392692893892031884392849 98544519670419023913294637)
    ·
      refine ⟨36954194876407133967485489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98544519670419023913294637 36954194876407133967485489)
      ·
        refine ⟨27715646157305350475614117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36954194876407133967485489 27715646157305350475614117)
        ·
          refine ⟨5196683654494753214177647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27715646157305350475614117 5196683654494753214177647)
          ·
            refine ⟨7795025481742129821266471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5196683654494753214177647 7795025481742129821266471)
            ·
              refine ⟨11692538222613194731899707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7795025481742129821266471 11692538222613194731899707)
              ·
                refine ⟨17538807333919792097849561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11692538222613194731899707 17538807333919792097849561)
                ·
                  refine ⟨13154105500439844073387171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17538807333919792097849561 13154105500439844073387171)
                  ·
                    refine ⟨19731158250659766110080757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13154105500439844073387171 19731158250659766110080757)
                    ·
                      refine ⟨1849796085999353072820071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19731158250659766110080757 1849796085999353072820071)
                      ·
                        rfl

theorem cell23_3602465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 1, 2, 1, 5].length) (baseStart_3602465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3602465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3602465 prefixEnd_3602465 := by exact prefixLift 3602465
  have htrace : WordTrace (prefixWord ++ tailWord_3602465) baseStart_3602465 baseEnd_3602465 := by
    simpa [prefixWord, tailWord_3602465, baseEnd_3602465] using wordTrace_append hprefix tailTrace_3602465
  have hstable : (prefixWord ++ tailWord_3602465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3602465).length < 2 ^ (prefixWord ++ tailWord_3602465).sum := by decide
  have hdescent : baseEnd_3602465 < baseStart_3602465 := by decide
  rcases family_descends (prefixWord ++ tailWord_3602465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3602485 : List Nat := [1, 3, 3, 1, 1, 1, 2, 6, 5]
def baseStart_3602485 : Nat := 118140960795 + 3602485 * 2 ^ 59
def prefixEnd_3602485 : Nat := 4983230072969 + 3 ^ 40 * 3602485 * 2
def baseEnd_3602485 : Nat := 205534039512493666063331

theorem tailTrace_3602485 : CollatzResearch.WordTrace tailWord_3602485 prefixEnd_3602485 205534039512493666063331 := by
  unfold tailWord_3602485
  simp only [CollatzResearch.WordTrace]
  refine ⟨131393422353819575300120909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87595614902546383533413939 131393422353819575300120909)
  ·
    refine ⟨49272533382682340737545341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131393422353819575300120909 49272533382682340737545341)
    ·
      refine ⟨18477200018505877776579503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49272533382682340737545341 18477200018505877776579503)
      ·
        refine ⟨27715800027758816664869255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18477200018505877776579503 27715800027758816664869255)
        ·
          refine ⟨41573700041638224997303883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27715800027758816664869255 41573700041638224997303883)
          ·
            refine ⟨62360550062457337495955825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41573700041638224997303883 62360550062457337495955825)
            ·
              refine ⟨46770412546843003121966869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62360550062457337495955825 46770412546843003121966869)
              ·
                refine ⟨2192363088133265771342197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 46770412546843003121966869 2192363088133265771342197)
                ·
                  refine ⟨205534039512493666063331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2192363088133265771342197 205534039512493666063331)
                  ·
                    rfl

theorem cell23_3602485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 6, 5].length) (baseStart_3602485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3602485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3602485 prefixEnd_3602485 := by exact prefixLift 3602485
  have htrace : WordTrace (prefixWord ++ tailWord_3602485) baseStart_3602485 baseEnd_3602485 := by
    simpa [prefixWord, tailWord_3602485, baseEnd_3602485] using wordTrace_append hprefix tailTrace_3602485
  have hstable : (prefixWord ++ tailWord_3602485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3602485).length < 2 ^ (prefixWord ++ tailWord_3602485).sum := by decide
  have hdescent : baseEnd_3602485 < baseStart_3602485 := by decide
  rcases family_descends (prefixWord ++ tailWord_3602485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3602496 : List Nat := [2, 1, 1, 2, 2, 6, 2, 1, 2, 2, 2]
def baseStart_3602496 : Nat := 118140960795 + 3602496 * 2 ^ 59
def prefixEnd_3602496 : Nat := 4983230072969 + 3 ^ 40 * 3602496 * 2
def baseEnd_3602496 : Nat := 1849812003899642451532429

theorem tailTrace_3602496 : CollatzResearch.WordTrace tailWord_3602496 prefixEnd_3602496 1849812003899642451532429 := by
  unfold tailWord_3602496
  simp only [CollatzResearch.WordTrace]
  refine ⟨65696911778389862089385671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87595882371186482785847561 65696911778389862089385671)
  ·
    refine ⟨98545367667584793134078507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65696911778389862089385671 98545367667584793134078507)
    ·
      refine ⟨147818051501377189701117761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98545367667584793134078507 147818051501377189701117761)
      ·
        refine ⟨110863538626032892275838321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147818051501377189701117761 110863538626032892275838321)
        ·
          refine ⟨83147653969524669206878741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110863538626032892275838321 83147653969524669206878741)
          ·
            refine ⟨3897546279821468869072441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 83147653969524669206878741 3897546279821468869072441)
            ·
              refine ⟨2923159709866101651804331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3897546279821468869072441 2923159709866101651804331)
              ·
                refine ⟨4384739564799152477706497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2923159709866101651804331 4384739564799152477706497)
                ·
                  refine ⟨3288554673599364358279873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4384739564799152477706497 3288554673599364358279873)
                  ·
                    refine ⟨2466416005199523268709905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3288554673599364358279873 2466416005199523268709905)
                    ·
                      refine ⟨1849812003899642451532429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2466416005199523268709905 1849812003899642451532429)
                      ·
                        rfl

theorem cell23_3602496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 2, 1, 2, 2, 2].length) (baseStart_3602496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3602496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3602496 prefixEnd_3602496 := by exact prefixLift 3602496
  have htrace : WordTrace (prefixWord ++ tailWord_3602496) baseStart_3602496 baseEnd_3602496 := by
    simpa [prefixWord, tailWord_3602496, baseEnd_3602496] using wordTrace_append hprefix tailTrace_3602496
  have hstable : (prefixWord ++ tailWord_3602496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3602496).length < 2 ^ (prefixWord ++ tailWord_3602496).sum := by decide
  have hdescent : baseEnd_3602496 < baseStart_3602496 := by decide
  rcases family_descends (prefixWord ++ tailWord_3602496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3602535 : List Nat := [1, 1, 5, 1, 1, 2, 1, 4, 2, 1, 4]
def baseStart_3602535 : Nat := 118140960795 + 3602535 * 2 ^ 59
def prefixEnd_3602535 : Nat := 4983230072969 + 3 ^ 40 * 3602535 * 2
def baseEnd_3602535 : Nat := 1849832029645167798944749

theorem tailTrace_3602535 : CollatzResearch.WordTrace tailWord_3602535 prefixEnd_3602535 1849832029645167798944749 := by
  unfold tailWord_3602535
  simp only [CollatzResearch.WordTrace]
  refine ⟨131395246003638433839441059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87596830669092289226294039 131395246003638433839441059)
  ·
    refine ⟨197092869005457650759161589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131395246003638433839441059 197092869005457650759161589)
    ·
      refine ⟨18477456469261654758671399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 197092869005457650759161589 18477456469261654758671399)
      ·
        refine ⟨27716184703892482138007099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18477456469261654758671399 27716184703892482138007099)
        ·
          refine ⟨41574277055838723207010649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27716184703892482138007099 41574277055838723207010649)
          ·
            refine ⟨31180707791879042405257987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41574277055838723207010649 31180707791879042405257987)
            ·
              refine ⟨46771061687818563607886981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31180707791879042405257987 46771061687818563607886981)
              ·
                refine ⟨8769574066465980676478809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46771061687818563607886981 8769574066465980676478809)
                ·
                  refine ⟨6577180549849485507359107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8769574066465980676478809 6577180549849485507359107)
                  ·
                    refine ⟨9865770824774228261038661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6577180549849485507359107 9865770824774228261038661)
                    ·
                      refine ⟨1849832029645167798944749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9865770824774228261038661 1849832029645167798944749)
                      ·
                        rfl

theorem cell23_3602535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 4, 2, 1, 4].length) (baseStart_3602535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3602535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3602535 prefixEnd_3602535 := by exact prefixLift 3602535
  have htrace : WordTrace (prefixWord ++ tailWord_3602535) baseStart_3602535 baseEnd_3602535 := by
    simpa [prefixWord, tailWord_3602535, baseEnd_3602535] using wordTrace_append hprefix tailTrace_3602535
  have hstable : (prefixWord ++ tailWord_3602535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3602535).length < 2 ^ (prefixWord ++ tailWord_3602535).sum := by decide
  have hdescent : baseEnd_3602535 < baseStart_3602535 := by decide
  rcases family_descends (prefixWord ++ tailWord_3602535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3602545 : List Nat := [1, 2, 2, 2, 1, 1, 4, 3, 3, 4]
def baseStart_3602545 : Nat := 118140960795 + 3602545 * 2 ^ 59
def prefixEnd_3602545 : Nat := 4983230072969 + 3 ^ 40 * 3602545 * 2
def baseEnd_3602545 : Nat := 616612388150570919939901

theorem tailTrace_3602545 : CollatzResearch.WordTrace tailWord_3602545 prefixEnd_3602545 616612388150570919939901 := by
  unfold tailWord_3602545
  simp only [CollatzResearch.WordTrace]
  refine ⟨131395610733602205547305089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87597073822401470364870059 131395610733602205547305089)
  ·
    refine ⟨98546708050201654160478817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131395610733602205547305089 98546708050201654160478817)
    ·
      refine ⟨73910031037651240620359113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98546708050201654160478817 73910031037651240620359113)
      ·
        refine ⟨55432523278238430465269335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73910031037651240620359113 55432523278238430465269335)
        ·
          refine ⟨83148784917357645697904003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55432523278238430465269335 83148784917357645697904003)
          ·
            refine ⟨124723177376036468546856005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83148784917357645697904003 124723177376036468546856005)
            ·
              refine ⟨23385595758006837852535501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 124723177376036468546856005 23385595758006837852535501)
              ·
                refine ⟨8769598409252564194700813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23385595758006837852535501 8769598409252564194700813)
                ·
                  refine ⟨3288599403469711573012805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8769598409252564194700813 3288599403469711573012805)
                  ·
                    refine ⟨616612388150570919939901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3288599403469711573012805 616612388150570919939901)
                    ·
                      rfl

theorem cell23_3602545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 3, 3, 4].length) (baseStart_3602545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3602545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3602545 prefixEnd_3602545 := by exact prefixLift 3602545
  have htrace : WordTrace (prefixWord ++ tailWord_3602545) baseStart_3602545 baseEnd_3602545 := by
    simpa [prefixWord, tailWord_3602545, baseEnd_3602545] using wordTrace_append hprefix tailTrace_3602545
  have hstable : (prefixWord ++ tailWord_3602545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3602545).length < 2 ^ (prefixWord ++ tailWord_3602545).sum := by decide
  have hdescent : baseEnd_3602545 < baseStart_3602545 := by decide
  rcases family_descends (prefixWord ++ tailWord_3602545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3602592 : List Nat := [2, 1, 1, 4, 2, 4, 1, 2, 6]
def baseStart_3602592 : Nat := 118140960795 + 3602592 * 2 ^ 59
def prefixEnd_3602592 : Nat := 4983230072969 + 3 ^ 40 * 3602592 * 2
def baseEnd_3602592 : Nat := 205540144226941563992443

theorem tailTrace_3602592 : CollatzResearch.WordTrace tailWord_3602592 prefixEnd_3602592 205540144226941563992443 := by
  unfold tailWord_3602592
  simp only [CollatzResearch.WordTrace]
  refine ⟨65698662482215966287133015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87598216642954621716177353 65698662482215966287133015)
  ·
    refine ⟨98547993723323949430699523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65698662482215966287133015 98547993723323949430699523)
    ·
      refine ⟨147821990584985924146049285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98547993723323949430699523 147821990584985924146049285)
      ·
        refine ⟨27716623234684860777384241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 147821990584985924146049285 27716623234684860777384241)
        ·
          refine ⟨20787467426013645583038181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27716623234684860777384241 20787467426013645583038181)
          ·
            refine ⟨3897650142377558546819659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20787467426013645583038181 3897650142377558546819659)
            ·
              refine ⟨5846475213566337820229489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3897650142377558546819659 5846475213566337820229489)
              ·
                refine ⟨4384856410174753365172117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5846475213566337820229489 4384856410174753365172117)
                ·
                  refine ⟨205540144226941563992443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4384856410174753365172117 205540144226941563992443)
                  ·
                    rfl

theorem cell23_3602592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 1, 2, 6].length) (baseStart_3602592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3602592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3602592 prefixEnd_3602592 := by exact prefixLift 3602592
  have htrace : WordTrace (prefixWord ++ tailWord_3602592) baseStart_3602592 baseEnd_3602592 := by
    simpa [prefixWord, tailWord_3602592, baseEnd_3602592] using wordTrace_append hprefix tailTrace_3602592
  have hstable : (prefixWord ++ tailWord_3602592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3602592).length < 2 ^ (prefixWord ++ tailWord_3602592).sum := by decide
  have hdescent : baseEnd_3602592 < baseStart_3602592 := by decide
  rcases family_descends (prefixWord ++ tailWord_3602592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3602609 : List Nat := [1, 2, 2, 5, 2, 1, 3, 1, 6]
def baseStart_3602609 : Nat := 118140960795 + 3602609 * 2 ^ 59
def prefixEnd_3602609 : Nat := 4983230072969 + 3 ^ 40 * 3602609 * 2
def baseEnd_3602609 : Nat := 205541114134844501046601

theorem tailTrace_3602609 : CollatzResearch.WordTrace tailWord_3602609 prefixEnd_3602609 205541114134844501046601 := by
  unfold tailWord_3602609
  simp only [CollatzResearch.WordTrace]
  refine ⟨131397945005370344477634881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87598630003580229651756587 131397945005370344477634881)
  ·
    refine ⟨98548458754027758358226161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131397945005370344477634881 98548458754027758358226161)
    ·
      refine ⟨73911344065520818768669621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98548458754027758358226161 73911344065520818768669621)
      ·
        refine ⟨6929188506142576759562777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 73911344065520818768669621 6929188506142576759562777)
        ·
          refine ⟨5196891379606932569672083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6929188506142576759562777 5196891379606932569672083)
          ·
            refine ⟨7795337069410398854508125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5196891379606932569672083 7795337069410398854508125)
            ·
              refine ⟨2923251401028899570440547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7795337069410398854508125 2923251401028899570440547)
              ·
                refine ⟨4384877101543349355660821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2923251401028899570440547 4384877101543349355660821)
                ·
                  refine ⟨205541114134844501046601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4384877101543349355660821 205541114134844501046601)
                  ·
                    rfl

theorem cell23_3602609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 3, 1, 6].length) (baseStart_3602609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3602609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3602609 prefixEnd_3602609 := by exact prefixLift 3602609
  have htrace : WordTrace (prefixWord ++ tailWord_3602609) baseStart_3602609 baseEnd_3602609 := by
    simpa [prefixWord, tailWord_3602609, baseEnd_3602609] using wordTrace_append hprefix tailTrace_3602609
  have hstable : (prefixWord ++ tailWord_3602609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3602609).length < 2 ^ (prefixWord ++ tailWord_3602609).sum := by decide
  have hdescent : baseEnd_3602609 < baseStart_3602609 := by decide
  rcases family_descends (prefixWord ++ tailWord_3602609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3602635 : List Nat := [1, 1, 1, 1, 3, 2, 3, 1, 6, 4]
def baseStart_3602635 : Nat := 118140960795 + 3602635 * 2 ^ 59
def prefixEnd_3602635 : Nat := 4983230072969 + 3 ^ 40 * 3602635 * 2
def baseEnd_3602635 : Nat := 616627792570205802564763

theorem tailTrace_3602635 : CollatzResearch.WordTrace tailWord_3602635 prefixEnd_3602635 616627792570205802564763 := by
  unfold tailWord_3602635
  simp only [CollatzResearch.WordTrace]
  refine ⟨131398893303276150918081359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87599262202184100612054239 131398893303276150918081359)
  ·
    refine ⟨197098339954914226377122039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131398893303276150918081359 197098339954914226377122039)
    ·
      refine ⟨295647509932371339565683059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197098339954914226377122039 295647509932371339565683059)
      ·
        refine ⟨443471264898557009348524589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295647509932371339565683059 443471264898557009348524589)
        ·
          refine ⟨166301724336958878505696721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 443471264898557009348524589 166301724336958878505696721)
          ·
            refine ⟨124726293252719158879272541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166301724336958878505696721 124726293252719158879272541)
            ·
              refine ⟨46772359969769684579727203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124726293252719158879272541 46772359969769684579727203)
              ·
                refine ⟨70158539954654526869590805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46772359969769684579727203 70158539954654526869590805)
                ·
                  refine ⟨3288681560374430947012069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 70158539954654526869590805 3288681560374430947012069)
                  ·
                    refine ⟨616627792570205802564763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3288681560374430947012069 616627792570205802564763)
                    ·
                      rfl

theorem cell23_3602635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 6, 4].length) (baseStart_3602635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3602635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3602635 prefixEnd_3602635 := by exact prefixLift 3602635
  have htrace : WordTrace (prefixWord ++ tailWord_3602635) baseStart_3602635 baseEnd_3602635 := by
    simpa [prefixWord, tailWord_3602635, baseEnd_3602635] using wordTrace_append hprefix tailTrace_3602635
  have hstable : (prefixWord ++ tailWord_3602635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3602635).length < 2 ^ (prefixWord ++ tailWord_3602635).sum := by decide
  have hdescent : baseEnd_3602635 < baseStart_3602635 := by decide
  rcases family_descends (prefixWord ++ tailWord_3602635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3602646 : List Nat := [5, 2, 1, 2, 1, 1, 1, 1, 4, 3, 2]
def baseStart_3602646 : Nat := 118140960795 + 3602646 * 2 ^ 59
def prefixEnd_3602646 : Nat := 4983230072969 + 3 ^ 40 * 3602646 * 2
def baseEnd_3602646 : Nat := 1849889025997816864656739

theorem tailTrace_3602646 : CollatzResearch.WordTrace tailWord_3602646 prefixEnd_3602646 1849889025997816864656739 := by
  unfold tailWord_3602646
  simp only [CollatzResearch.WordTrace]
  refine ⟨8212455906639768737295737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 87599529670824199864487861 8212455906639768737295737)
  ·
    refine ⟨6159341929979826552971803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8212455906639768737295737 6159341929979826552971803)
    ·
      refine ⟨9239012894969739829457705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6159341929979826552971803 9239012894969739829457705)
      ·
        refine ⟨6929259671227304872093279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9239012894969739829457705 6929259671227304872093279)
        ·
          refine ⟨10393889506840957308139919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6929259671227304872093279 10393889506840957308139919)
          ·
            refine ⟨15590834260261435962209879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10393889506840957308139919 15590834260261435962209879)
            ·
              refine ⟨23386251390392153943314819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15590834260261435962209879 23386251390392153943314819)
              ·
                refine ⟨35079377085588230914972229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23386251390392153943314819 35079377085588230914972229)
                ·
                  refine ⟨6577383203547793296557293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35079377085588230914972229 6577383203547793296557293)
                  ·
                    refine ⟨2466518701330422486208985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6577383203547793296557293 2466518701330422486208985)
                    ·
                      refine ⟨1849889025997816864656739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2466518701330422486208985 1849889025997816864656739)
                      ·
                        rfl

theorem cell23_3602646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 1, 4, 3, 2].length) (baseStart_3602646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3602646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3602646 prefixEnd_3602646 := by exact prefixLift 3602646
  have htrace : WordTrace (prefixWord ++ tailWord_3602646) baseStart_3602646 baseEnd_3602646 := by
    simpa [prefixWord, tailWord_3602646, baseEnd_3602646] using wordTrace_append hprefix tailTrace_3602646
  have hstable : (prefixWord ++ tailWord_3602646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3602646).length < 2 ^ (prefixWord ++ tailWord_3602646).sum := by decide
  have hdescent : baseEnd_3602646 < baseStart_3602646 := by decide
  rcases family_descends (prefixWord ++ tailWord_3602646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3602696 : List Nat := [2, 1, 3, 2, 3, 2, 3, 1, 1, 2, 3]
def baseStart_3602696 : Nat := 118140960795 + 3602696 * 2 ^ 59
def prefixEnd_3602696 : Nat := 4983230072969 + 3 ^ 40 * 3602696 * 2
def baseEnd_3602696 : Nat := 1849914700030541669031509

theorem tailTrace_3602696 : CollatzResearch.WordTrace tailWord_3602696 prefixEnd_3602696 1849914700030541669031509 := by
  unfold tailWord_3602696
  simp only [CollatzResearch.WordTrace]
  refine ⟨65700559078027579168025971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87600745437370105557367961 65700559078027579168025971)
  ·
    refine ⟨98550838617041368752038957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65700559078027579168025971 98550838617041368752038957)
    ·
      refine ⟨36956564481390513282014609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98550838617041368752038957 36956564481390513282014609)
      ·
        refine ⟨27717423361042884961510957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36956564481390513282014609 27717423361042884961510957)
        ·
          refine ⟨10394033760391081860566609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27717423361042884961510957 10394033760391081860566609)
          ·
            refine ⟨7795525320293311395424957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10394033760391081860566609 7795525320293311395424957)
            ·
              refine ⟨2923321995109991773284359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7795525320293311395424957 2923321995109991773284359)
              ·
                refine ⟨4384982992664987659926539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2923321995109991773284359 4384982992664987659926539)
                ·
                  refine ⟨6577474488997481489889809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4384982992664987659926539 6577474488997481489889809)
                  ·
                    refine ⟨4933105866748111117417357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6577474488997481489889809 4933105866748111117417357)
                    ·
                      refine ⟨1849914700030541669031509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4933105866748111117417357 1849914700030541669031509)
                      ·
                        rfl

theorem cell23_3602696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 3, 1, 1, 2, 3].length) (baseStart_3602696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3602696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3602696 prefixEnd_3602696 := by exact prefixLift 3602696
  have htrace : WordTrace (prefixWord ++ tailWord_3602696) baseStart_3602696 baseEnd_3602696 := by
    simpa [prefixWord, tailWord_3602696, baseEnd_3602696] using wordTrace_append hprefix tailTrace_3602696
  have hstable : (prefixWord ++ tailWord_3602696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3602696).length < 2 ^ (prefixWord ++ tailWord_3602696).sum := by decide
  have hdescent : baseEnd_3602696 < baseStart_3602696 := by decide
  rcases family_descends (prefixWord ++ tailWord_3602696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3602709 : List Nat := [1, 3, 2, 1, 2, 1, 3, 4, 2, 1, 3]
def baseStart_3602709 : Nat := 118140960795 + 3602709 * 2 ^ 59
def prefixEnd_3602709 : Nat := 4983230072969 + 3 ^ 40 * 3602709 * 2
def baseEnd_3602709 : Nat := 1849921375279050118168949

theorem tailTrace_3602709 : CollatzResearch.WordTrace tailWord_3602709 prefixEnd_3602709 1849921375279050118168949 := by
  unfold tailWord_3602709
  simp only [CollatzResearch.WordTrace]
  refine ⟨131401592305008061556275181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87601061536672041037516787 131401592305008061556275181)
  ·
    refine ⟨49275597114378023083603193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131401592305008061556275181 49275597114378023083603193)
    ·
      refine ⟨36956697835783517312702395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49275597114378023083603193 36956697835783517312702395)
      ·
        refine ⟨55435046753675275969053593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36956697835783517312702395 55435046753675275969053593)
        ·
          refine ⟨41576285065256456976790195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55435046753675275969053593 41576285065256456976790195)
          ·
            refine ⟨62364427597884685465185293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41576285065256456976790195 62364427597884685465185293)
            ·
              refine ⟨23386660349206757049444485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62364427597884685465185293 23386660349206757049444485)
              ·
                refine ⟨4384998815476266946770841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23386660349206757049444485 4384998815476266946770841)
                ·
                  refine ⟨3288749111607200210078131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4384998815476266946770841 3288749111607200210078131)
                  ·
                    refine ⟨4933123667410800315117197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3288749111607200210078131 4933123667410800315117197)
                    ·
                      refine ⟨1849921375279050118168949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4933123667410800315117197 1849921375279050118168949)
                      ·
                        rfl

theorem cell23_3602709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 4, 2, 1, 3].length) (baseStart_3602709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3602709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3602709 prefixEnd_3602709 := by exact prefixLift 3602709
  have htrace : WordTrace (prefixWord ++ tailWord_3602709) baseStart_3602709 baseEnd_3602709 := by
    simpa [prefixWord, tailWord_3602709, baseEnd_3602709] using wordTrace_append hprefix tailTrace_3602709
  have hstable : (prefixWord ++ tailWord_3602709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3602709).length < 2 ^ (prefixWord ++ tailWord_3602709).sum := by decide
  have hdescent : baseEnd_3602709 < baseStart_3602709 := by decide
  rcases family_descends (prefixWord ++ tailWord_3602709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3602715 : List Nat := [1, 1, 1, 1, 1, 1, 7, 1, 2, 3, 4]
def baseStart_3602715 : Nat := 118140960795 + 3602715 * 2 ^ 59
def prefixEnd_3602715 : Nat := 4983230072969 + 3 ^ 40 * 3602715 * 2
def baseEnd_3602715 : Nat := 1849924456162977094693921

theorem tailTrace_3602715 : CollatzResearch.WordTrace tailWord_3602715 prefixEnd_3602715 1849924456162977094693921 := by
  unfold tailWord_3602715
  simp only [CollatzResearch.WordTrace]
  refine ⟨131401811142986324580993599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87601207428657549720662399 131401811142986324580993599)
  ·
    refine ⟨197102716714479486871490399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131401811142986324580993599 197102716714479486871490399)
    ·
      refine ⟨295654075071719230307235599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197102716714479486871490399 295654075071719230307235599)
      ·
        refine ⟨443481112607578845460853399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295654075071719230307235599 443481112607578845460853399)
        ·
          refine ⟨665221668911368268191280099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 443481112607578845460853399 665221668911368268191280099)
          ·
            refine ⟨997832503367052402286920149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 665221668911368268191280099 997832503367052402286920149)
            ·
              refine ⟨23386699297665290678599691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 997832503367052402286920149 23386699297665290678599691)
              ·
                refine ⟨35080048946497936017899537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23386699297665290678599691 35080048946497936017899537)
                ·
                  refine ⟨26310036709873452013424653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35080048946497936017899537 26310036709873452013424653)
                  ·
                    refine ⟨9866263766202544505034245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26310036709873452013424653 9866263766202544505034245)
                    ·
                      refine ⟨1849924456162977094693921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9866263766202544505034245 1849924456162977094693921)
                      ·
                        rfl

theorem cell23_3602715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 1, 2, 3, 4].length) (baseStart_3602715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3602715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3602715 prefixEnd_3602715 := by exact prefixLift 3602715
  have htrace : WordTrace (prefixWord ++ tailWord_3602715) baseStart_3602715 baseEnd_3602715 := by
    simpa [prefixWord, tailWord_3602715, baseEnd_3602715] using wordTrace_append hprefix tailTrace_3602715
  have hstable : (prefixWord ++ tailWord_3602715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3602715).length < 2 ^ (prefixWord ++ tailWord_3602715).sum := by decide
  have hdescent : baseEnd_3602715 < baseStart_3602715 := by decide
  rcases family_descends (prefixWord ++ tailWord_3602715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3602719 : List Nat := [1, 1, 2, 4, 3, 1, 1, 2, 3, 3, 2]
def baseStart_3602719 : Nat := 118140960795 + 3602719 * 2 ^ 59
def prefixEnd_3602719 : Nat := 4983230072969 + 3 ^ 40 * 3602719 * 2
def baseEnd_3602719 : Nat := 1849926510085595079043903

theorem tailTrace_3602719 : CollatzResearch.WordTrace tailWord_3602719 prefixEnd_3602719 1849926510085595079043903 := by
  unfold tailWord_3602719
  simp only [CollatzResearch.WordTrace]
  refine ⟨131401957034971833264139211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87601304689981222176092807 131401957034971833264139211)
  ·
    refine ⟨197102935552457749896208817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131401957034971833264139211 197102935552457749896208817)
    ·
      refine ⟨147827201664343312422156613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197102935552457749896208817 147827201664343312422156613)
      ·
        refine ⟨27717600312064371079154365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 147827201664343312422156613 27717600312064371079154365)
        ·
          refine ⟨10394100117024139154682887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27717600312064371079154365 10394100117024139154682887)
          ·
            refine ⟨15591150175536208732024331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10394100117024139154682887 15591150175536208732024331)
            ·
              refine ⟨23386725263304313098036497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15591150175536208732024331 23386725263304313098036497)
              ·
                refine ⟨17540043947478234823527373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23386725263304313098036497 17540043947478234823527373)
                ·
                  refine ⟨6577516480304338058822765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17540043947478234823527373 6577516480304338058822765)
                  ·
                    refine ⟨2466568680114126772058537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6577516480304338058822765 2466568680114126772058537)
                    ·
                      refine ⟨1849926510085595079043903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2466568680114126772058537 1849926510085595079043903)
                      ·
                        rfl

theorem cell23_3602719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 2, 3, 3, 2].length) (baseStart_3602719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3602719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3602719 prefixEnd_3602719 := by exact prefixLift 3602719
  have htrace : WordTrace (prefixWord ++ tailWord_3602719) baseStart_3602719 baseEnd_3602719 := by
    simpa [prefixWord, tailWord_3602719, baseEnd_3602719] using wordTrace_append hprefix tailTrace_3602719
  have hstable : (prefixWord ++ tailWord_3602719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3602719).length < 2 ^ (prefixWord ++ tailWord_3602719).sum := by decide
  have hdescent : baseEnd_3602719 < baseStart_3602719 := by decide
  rcases family_descends (prefixWord ++ tailWord_3602719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3602735 : List Nat := [1, 1, 2, 1, 2, 1, 4, 1, 4, 1, 5]
def baseStart_3602735 : Nat := 118140960795 + 3602735 * 2 ^ 59
def prefixEnd_3602735 : Nat := 4983230072969 + 3 ^ 40 * 3602735 * 2
def baseEnd_3602735 : Nat := 1849934725776067016443829

theorem tailTrace_3602735 : CollatzResearch.WordTrace tailWord_3602735 prefixEnd_3602735 1849934725776067016443829 := by
  unfold tailWord_3602735
  simp only [CollatzResearch.WordTrace]
  refine ⟨131402540602913867996721659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87601693735275911997814439 131402540602913867996721659)
  ·
    refine ⟨197103810904370801995082489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131402540602913867996721659 197103810904370801995082489)
    ·
      refine ⟨147827858178278101496311867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197103810904370801995082489 147827858178278101496311867)
      ·
        refine ⟨221741787267417152244467801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147827858178278101496311867 221741787267417152244467801)
        ·
          refine ⟨166306340450562864183350851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 221741787267417152244467801 166306340450562864183350851)
          ·
            refine ⟨249459510675844296275026277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166306340450562864183350851 249459510675844296275026277)
            ·
              refine ⟨46773658251720805551567427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 249459510675844296275026277 46773658251720805551567427)
              ·
                refine ⟨70160487377581208327351141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46773658251720805551567427 70160487377581208327351141)
                ·
                  refine ⟨13155091383296476561378339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70160487377581208327351141 13155091383296476561378339)
                  ·
                    refine ⟨19732637074944714842067509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13155091383296476561378339 19732637074944714842067509)
                    ·
                      refine ⟨1849934725776067016443829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19732637074944714842067509 1849934725776067016443829)
                      ·
                        rfl

theorem cell23_3602735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 4, 1, 5].length) (baseStart_3602735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3602735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3602735 prefixEnd_3602735 := by exact prefixLift 3602735
  have htrace : WordTrace (prefixWord ++ tailWord_3602735) baseStart_3602735 baseEnd_3602735 := by
    simpa [prefixWord, tailWord_3602735, baseEnd_3602735] using wordTrace_append hprefix tailTrace_3602735
  have hstable : (prefixWord ++ tailWord_3602735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3602735).length < 2 ^ (prefixWord ++ tailWord_3602735).sum := by decide
  have hdescent : baseEnd_3602735 < baseStart_3602735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3602735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3602753 : List Nat := [1, 2, 5, 2, 2, 1, 1, 3, 1, 3, 2]
def baseStart_3602753 : Nat := 118140960795 + 3602753 * 2 ^ 59
def prefixEnd_3602753 : Nat := 4983230072969 + 3 ^ 40 * 3602753 * 2
def baseEnd_3602753 : Nat := 1849943968427847946018747

theorem tailTrace_3602753 : CollatzResearch.WordTrace tailWord_3602753 prefixEnd_3602753 1849943968427847946018747 := by
  unfold tailWord_3602753
  simp only [CollatzResearch.WordTrace]
  refine ⟨131403197116848657070876913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87602131411232438047251275 131403197116848657070876913)
  ·
    refine ⟨98552397837636492803157685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131403197116848657070876913 98552397837636492803157685)
    ·
      refine ⟨9239287297278421200296033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 98552397837636492803157685 9239287297278421200296033)
      ·
        refine ⟨6929465472958815900222025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9239287297278421200296033 6929465472958815900222025)
        ·
          refine ⟨5197099104719111925166519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6929465472958815900222025 5197099104719111925166519)
          ·
            refine ⟨7795648657078667887749779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5197099104719111925166519 7795648657078667887749779)
            ·
              refine ⟨11693472985618001831624669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7795648657078667887749779 11693472985618001831624669)
              ·
                refine ⟨4385052369606750686859251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11693472985618001831624669 4385052369606750686859251)
                ·
                  refine ⟨6577578554410126030288877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4385052369606750686859251 6577578554410126030288877)
                  ·
                    refine ⟨2466591957903797261358329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6577578554410126030288877 2466591957903797261358329)
                    ·
                      refine ⟨1849943968427847946018747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2466591957903797261358329 1849943968427847946018747)
                      ·
                        rfl

theorem cell23_3602753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 3, 1, 3, 2].length) (baseStart_3602753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3602753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3602753 prefixEnd_3602753 := by exact prefixLift 3602753
  have htrace : WordTrace (prefixWord ++ tailWord_3602753) baseStart_3602753 baseEnd_3602753 := by
    simpa [prefixWord, tailWord_3602753, baseEnd_3602753] using wordTrace_append hprefix tailTrace_3602753
  have hstable : (prefixWord ++ tailWord_3602753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3602753).length < 2 ^ (prefixWord ++ tailWord_3602753).sum := by decide
  have hdescent : baseEnd_3602753 < baseStart_3602753 := by decide
  rcases family_descends (prefixWord ++ tailWord_3602753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3602766 : List Nat := [4, 1, 1, 1, 1, 1, 2, 6, 2, 2, 2]
def baseStart_3602766 : Nat := 118140960795 + 3602766 * 2 ^ 59
def prefixEnd_3602766 : Nat := 4983230072969 + 3 ^ 40 * 3602766 * 2
def baseEnd_3602766 : Nat := 1849950643676356395156187

theorem tailTrace_3602766 : CollatzResearch.WordTrace tailWord_3602766 prefixEnd_3602766 1849950643676356395156187 := by
  unfold tailWord_3602766
  simp only [CollatzResearch.WordTrace]
  refine ⟨16425458908225195036387519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87602447510534373527400101 16425458908225195036387519)
  ·
    refine ⟨24638188362337792554581279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16425458908225195036387519 24638188362337792554581279)
    ·
      refine ⟨36957282543506688831871919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24638188362337792554581279 36957282543506688831871919)
      ·
        refine ⟨55435923815260033247807879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36957282543506688831871919 55435923815260033247807879)
        ·
          refine ⟨83153885722890049871711819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55435923815260033247807879 83153885722890049871711819)
          ·
            refine ⟨124730828584335074807567729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83153885722890049871711819 124730828584335074807567729)
            ·
              refine ⟨93548121438251306105675797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124730828584335074807567729 93548121438251306105675797)
              ·
                refine ⟨4385068192418029973703553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 93548121438251306105675797 4385068192418029973703553)
                ·
                  refine ⟨3288801144313522480277665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4385068192418029973703553 3288801144313522480277665)
                  ·
                    refine ⟨2466600858235141860208249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3288801144313522480277665 2466600858235141860208249)
                    ·
                      refine ⟨1849950643676356395156187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2466600858235141860208249 1849950643676356395156187)
                      ·
                        rfl

theorem cell23_3602766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 6, 2, 2, 2].length) (baseStart_3602766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3602766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3602766 prefixEnd_3602766 := by exact prefixLift 3602766
  have htrace : WordTrace (prefixWord ++ tailWord_3602766) baseStart_3602766 baseEnd_3602766 := by
    simpa [prefixWord, tailWord_3602766, baseEnd_3602766] using wordTrace_append hprefix tailTrace_3602766
  have hstable : (prefixWord ++ tailWord_3602766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3602766).length < 2 ^ (prefixWord ++ tailWord_3602766).sum := by decide
  have hdescent : baseEnd_3602766 < baseStart_3602766 := by decide
  rcases family_descends (prefixWord ++ tailWord_3602766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3602772 : List Nat := [2, 4, 1, 1, 2, 2, 1, 3, 7]
def baseStart_3602772 : Nat := 118140960795 + 3602772 * 2 ^ 59
def prefixEnd_3602772 : Nat := 4983230072969 + 3 ^ 40 * 3602772 * 2
def baseEnd_3602772 : Nat := 205550413840031485742351

theorem tailTrace_3602772 : CollatzResearch.WordTrace tailWord_3602772 prefixEnd_3602772 205550413840031485742351 := by
  unfold tailWord_3602772
  simp only [CollatzResearch.WordTrace]
  refine ⟨65701945051889911657909285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87602593402519882210545713 65701945051889911657909285)
  ·
    refine ⟨12319114697229358435857991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65701945051889911657909285 12319114697229358435857991)
    ·
      refine ⟨18478672045844037653786987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12319114697229358435857991 18478672045844037653786987)
      ·
        refine ⟨27718008068766056480680481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18478672045844037653786987 27718008068766056480680481)
        ·
          refine ⟨20788506051574542360510361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27718008068766056480680481 20788506051574542360510361)
          ·
            refine ⟨15591379538680906770382771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20788506051574542360510361 15591379538680906770382771)
            ·
              refine ⟨23387069308021360155574157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15591379538680906770382771 23387069308021360155574157)
              ·
                refine ⟨8770150990508010058340309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23387069308021360155574157 8770150990508010058340309)
                ·
                  refine ⟨205550413840031485742351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8770150990508010058340309 205550413840031485742351)
                  ·
                    rfl

theorem cell23_3602772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 3, 7].length) (baseStart_3602772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3602772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3602772 prefixEnd_3602772 := by exact prefixLift 3602772
  have htrace : WordTrace (prefixWord ++ tailWord_3602772) baseStart_3602772 baseEnd_3602772 := by
    simpa [prefixWord, tailWord_3602772, baseEnd_3602772] using wordTrace_append hprefix tailTrace_3602772
  have hstable : (prefixWord ++ tailWord_3602772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3602772).length < 2 ^ (prefixWord ++ tailWord_3602772).sum := by decide
  have hdescent : baseEnd_3602772 < baseStart_3602772 := by decide
  rcases family_descends (prefixWord ++ tailWord_3602772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3602795 : List Nat := [1, 1, 1, 1, 2, 2, 2, 4, 1, 1, 7]
def baseStart_3602795 : Nat := 118140960795 + 3602795 * 2 ^ 59
def prefixEnd_3602795 : Nat := 4983230072969 + 3 ^ 40 * 3602795 * 2
def baseEnd_3602795 : Nat := 1849965534615336781693553

theorem tailTrace_3602795 : CollatzResearch.WordTrace tailWord_3602795 prefixEnd_3602795 1849965534615336781693553 := by
  unfold tailWord_3602795
  simp only [CollatzResearch.WordTrace]
  refine ⟨131404728982696498243905839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87603152655130998829270559 131404728982696498243905839)
  ·
    refine ⟨197107093474044747365858759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131404728982696498243905839 197107093474044747365858759)
    ·
      refine ⟨295660640211067121048788139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197107093474044747365858759 295660640211067121048788139)
      ·
        refine ⟨443490960316600681573182209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295660640211067121048788139 443490960316600681573182209)
        ·
          refine ⟨332618220237450511179886657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 443490960316600681573182209 332618220237450511179886657)
          ·
            refine ⟨249463665178087883384914993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 332618220237450511179886657 249463665178087883384914993)
            ·
              refine ⟨187097748883565912538686245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 249463665178087883384914993 187097748883565912538686245)
              ·
                refine ⟨35080827915668608601003671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 187097748883565912538686245 35080827915668608601003671)
                ·
                  refine ⟨52621241873502912901505507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35080827915668608601003671 52621241873502912901505507)
                  ·
                    refine ⟨78931862810254369352258261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52621241873502912901505507 78931862810254369352258261)
                    ·
                      refine ⟨1849965534615336781693553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 78931862810254369352258261 1849965534615336781693553)
                      ·
                        rfl

theorem cell23_3602795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 1, 1, 7].length) (baseStart_3602795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3602795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3602795 prefixEnd_3602795 := by exact prefixLift 3602795
  have htrace : WordTrace (prefixWord ++ tailWord_3602795) baseStart_3602795 baseEnd_3602795 := by
    simpa [prefixWord, tailWord_3602795, baseEnd_3602795] using wordTrace_append hprefix tailTrace_3602795
  have hstable : (prefixWord ++ tailWord_3602795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3602795).length < 2 ^ (prefixWord ++ tailWord_3602795).sum := by decide
  have hdescent : baseEnd_3602795 < baseStart_3602795 := by decide
  rcases family_descends (prefixWord ++ tailWord_3602795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3602802 : List Nat := [3, 2, 1, 2, 1, 3, 2, 1, 1, 7]
def baseStart_3602802 : Nat := 118140960795 + 3602802 * 2 ^ 59
def prefixEnd_3602802 : Nat := 4983230072969 + 3 ^ 40 * 3602802 * 2
def baseEnd_3602802 : Nat := 616656376326639418102007

theorem tailTrace_3602802 : CollatzResearch.WordTrace tailWord_3602802 prefixEnd_3602802 616656376326639418102007 := by
  unfold tailWord_3602802
  simp only [CollatzResearch.WordTrace]
  refine ⟨32851246073417784609852665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87603322862447425626273773 32851246073417784609852665)
  ·
    refine ⟨24638434555063338457389499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32851246073417784609852665 24638434555063338457389499)
    ·
      refine ⟨36957651832595007686084249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24638434555063338457389499 36957651832595007686084249)
      ·
        refine ⟨27718238874446255764563187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36957651832595007686084249 27718238874446255764563187)
        ·
          refine ⟨41577358311669383646844781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27718238874446255764563187 41577358311669383646844781)
          ·
            refine ⟨15591509366876018867566793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41577358311669383646844781 15591509366876018867566793)
            ·
              refine ⟨11693632025157014150675095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15591509366876018867566793 11693632025157014150675095)
              ·
                refine ⟨17540448037735521226012643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11693632025157014150675095 17540448037735521226012643)
                ·
                  refine ⟨26310672056603281839018965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17540448037735521226012643 26310672056603281839018965)
                  ·
                    refine ⟨616656376326639418102007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26310672056603281839018965 616656376326639418102007)
                    ·
                      rfl

theorem cell23_3602802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 1, 1, 7].length) (baseStart_3602802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3602802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3602802 prefixEnd_3602802 := by exact prefixLift 3602802
  have htrace : WordTrace (prefixWord ++ tailWord_3602802) baseStart_3602802 baseEnd_3602802 := by
    simpa [prefixWord, tailWord_3602802, baseEnd_3602802] using wordTrace_append hprefix tailTrace_3602802
  have hstable : (prefixWord ++ tailWord_3602802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3602802).length < 2 ^ (prefixWord ++ tailWord_3602802).sum := by decide
  have hdescent : baseEnd_3602802 < baseStart_3602802 := by decide
  rcases family_descends (prefixWord ++ tailWord_3602802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3602815 : List Nat := [1, 1, 2, 2, 1, 1, 2, 2, 1, 10]
def baseStart_3602815 : Nat := 118140960795 + 3602815 * 2 ^ 59
def prefixEnd_3602815 : Nat := 4983230072969 + 3 ^ 40 * 3602815 * 2
def baseEnd_3602815 : Nat := 616658601409475567814487

theorem tailTrace_3602815 : CollatzResearch.WordTrace tailWord_3602815 prefixEnd_3602815 616658601409475567814487 := by
  unfold tailWord_3602815
  simp only [CollatzResearch.WordTrace]
  refine ⟨131405458442624041659633899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87603638961749361106422599 131405458442624041659633899)
  ·
    refine ⟨197108187663936062489450849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131405458442624041659633899 197108187663936062489450849)
    ·
      refine ⟨147831140747952046867088137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197108187663936062489450849 147831140747952046867088137)
      ·
        refine ⟨110873355560964035150316103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147831140747952046867088137 110873355560964035150316103)
        ·
          refine ⟨166310033341446052725474155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110873355560964035150316103 166310033341446052725474155)
          ·
            refine ⟨249465050012169079088211233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166310033341446052725474155 249465050012169079088211233)
            ·
              refine ⟨187098787509126809316158425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 249465050012169079088211233 187098787509126809316158425)
              ·
                refine ⟨140324090631845106987118819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 187098787509126809316158425 140324090631845106987118819)
                ·
                  refine ⟨210486135947767660480678229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 140324090631845106987118819 210486135947767660480678229)
                  ·
                    refine ⟨616658601409475567814487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 210486135947767660480678229 616658601409475567814487)
                    ·
                      rfl

theorem cell23_3602815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 10].length) (baseStart_3602815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3602815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3602815 prefixEnd_3602815 := by exact prefixLift 3602815
  have htrace : WordTrace (prefixWord ++ tailWord_3602815) baseStart_3602815 baseEnd_3602815 := by
    simpa [prefixWord, tailWord_3602815, baseEnd_3602815] using wordTrace_append hprefix tailTrace_3602815
  have hstable : (prefixWord ++ tailWord_3602815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3602815).length < 2 ^ (prefixWord ++ tailWord_3602815).sum := by decide
  have hdescent : baseEnd_3602815 < baseStart_3602815 := by decide
  rcases family_descends (prefixWord ++ tailWord_3602815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3602819 : List Nat := [1, 1, 1, 3, 6, 1, 1, 2, 2, 5]
def baseStart_3602819 : Nat := 118140960795 + 3602819 * 2 ^ 59
def prefixEnd_3602819 : Nat := 4983230072969 + 3 ^ 40 * 3602819 * 2
def baseEnd_3602819 : Nat := 616659286050348229264481

theorem tailTrace_3602819 : CollatzResearch.WordTrace tailWord_3602819 prefixEnd_3602819 616659286050348229264481 := by
  unfold tailWord_3602819
  simp only [CollatzResearch.WordTrace]
  refine ⟨131405604334609550342779511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87603736223073033561853007 131405604334609550342779511)
  ·
    refine ⟨197108406501914325514169267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131405604334609550342779511 197108406501914325514169267)
    ·
      refine ⟨295662609752871488271253901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197108406501914325514169267 295662609752871488271253901)
      ·
        refine ⟨110873478657326808101720213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 295662609752871488271253901 110873478657326808101720213)
        ·
          refine ⟨5197194312062194129768135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 110873478657326808101720213 5197194312062194129768135)
          ·
            refine ⟨7795791468093291194652203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5197194312062194129768135 7795791468093291194652203)
            ·
              refine ⟨11693687202139936791978305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7795791468093291194652203 11693687202139936791978305)
              ·
                refine ⟨8770265401604952593983729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11693687202139936791978305 8770265401604952593983729)
                ·
                  refine ⟨6577699051203714445487797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8770265401604952593983729 6577699051203714445487797)
                  ·
                    refine ⟨616659286050348229264481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6577699051203714445487797 616659286050348229264481)
                    ·
                      rfl

theorem cell23_3602819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 2, 2, 5].length) (baseStart_3602819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3602819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3602819 prefixEnd_3602819 := by exact prefixLift 3602819
  have htrace : WordTrace (prefixWord ++ tailWord_3602819) baseStart_3602819 baseEnd_3602819 := by
    simpa [prefixWord, tailWord_3602819, baseEnd_3602819] using wordTrace_append hprefix tailTrace_3602819
  have hstable : (prefixWord ++ tailWord_3602819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3602819).length < 2 ^ (prefixWord ++ tailWord_3602819).sum := by decide
  have hdescent : baseEnd_3602819 < baseStart_3602819 := by decide
  rcases family_descends (prefixWord ++ tailWord_3602819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3602832 : List Nat := [2, 1, 1, 1, 1, 1, 2, 1, 9, 4]
def baseStart_3602832 : Nat := 118140960795 + 3602832 * 2 ^ 59
def prefixEnd_3602832 : Nat := 4983230072969 + 3 ^ 40 * 3602832 * 2
def baseEnd_3602832 : Nat := 616661511133184378976961

theorem tailTrace_3602832 : CollatzResearch.WordTrace tailWord_3602832 prefixEnd_3602832 616661511133184378976961 := by
  unfold tailWord_3602832
  simp only [CollatzResearch.WordTrace]
  refine ⟨65703039241781226781501375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87604052322374969042001833 65703039241781226781501375)
  ·
    refine ⟨98554558862671840172252063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65703039241781226781501375 98554558862671840172252063)
    ·
      refine ⟨147831838294007760258378095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98554558862671840172252063 147831838294007760258378095)
      ·
        refine ⟨221747757441011640387567143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147831838294007760258378095 221747757441011640387567143)
        ·
          refine ⟨332621636161517460581350715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221747757441011640387567143 332621636161517460581350715)
          ·
            refine ⟨498932454242276190872026073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 332621636161517460581350715 498932454242276190872026073)
            ·
              refine ⟨374199340681707143154019555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 498932454242276190872026073 374199340681707143154019555)
              ·
                refine ⟨561299011022560714731029333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 374199340681707143154019555 561299011022560714731029333)
                ·
                  refine ⟨3288861392710316687877125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 561299011022560714731029333 3288861392710316687877125)
                  ·
                    refine ⟨616661511133184378976961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3288861392710316687877125 616661511133184378976961)
                    ·
                      rfl

theorem cell23_3602832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 9, 4].length) (baseStart_3602832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3602832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3602832 prefixEnd_3602832 := by exact prefixLift 3602832
  have htrace : WordTrace (prefixWord ++ tailWord_3602832) baseStart_3602832 baseEnd_3602832 := by
    simpa [prefixWord, tailWord_3602832, baseEnd_3602832] using wordTrace_append hprefix tailTrace_3602832
  have hstable : (prefixWord ++ tailWord_3602832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3602832).length < 2 ^ (prefixWord ++ tailWord_3602832).sum := by decide
  have hdescent : baseEnd_3602832 < baseStart_3602832 := by decide
  rcases family_descends (prefixWord ++ tailWord_3602832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3602839 : List Nat := [1, 1, 3, 3, 1, 1, 2, 3, 2, 4, 2]
def baseStart_3602839 : Nat := 118140960795 + 3602839 * 2 ^ 59
def prefixEnd_3602839 : Nat := 4983230072969 + 3 ^ 40 * 3602839 * 2
def baseEnd_3602839 : Nat := 1849988127764134609543351

theorem tailTrace_3602839 : CollatzResearch.WordTrace tailWord_3602839 prefixEnd_3602839 1849988127764134609543351 := by
  unfold tailWord_3602839
  simp only [CollatzResearch.WordTrace]
  refine ⟨131406333794537093758507571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87604222529691395839005047 131406333794537093758507571)
  ·
    refine ⟨197109500691805640637761357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131406333794537093758507571 197109500691805640637761357)
    ·
      refine ⟨73916062759427115239160509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197109500691805640637761357 73916062759427115239160509)
      ·
        refine ⟨27718523534785168214685191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73916062759427115239160509 27718523534785168214685191)
        ·
          refine ⟨41577785302177752322027787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27718523534785168214685191 41577785302177752322027787)
          ·
            refine ⟨62366677953266628483041681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41577785302177752322027787 62366677953266628483041681)
            ·
              refine ⟨46775008464949971362281261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62366677953266628483041681 46775008464949971362281261)
              ·
                refine ⟨17540628174356239260855473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46775008464949971362281261 17540628174356239260855473)
                ·
                  refine ⟨13155471130767179445641605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17540628174356239260855473 13155471130767179445641605)
                  ·
                    refine ⟨2466650837018846146057801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13155471130767179445641605 2466650837018846146057801)
                    ·
                      refine ⟨1849988127764134609543351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2466650837018846146057801 1849988127764134609543351)
                      ·
                        rfl

theorem cell23_3602839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 3, 2, 4, 2].length) (baseStart_3602839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3602839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3602839 prefixEnd_3602839 := by exact prefixLift 3602839
  have htrace : WordTrace (prefixWord ++ tailWord_3602839) baseStart_3602839 baseEnd_3602839 := by
    simpa [prefixWord, tailWord_3602839, baseEnd_3602839] using wordTrace_append hprefix tailTrace_3602839
  have hstable : (prefixWord ++ tailWord_3602839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3602839).length < 2 ^ (prefixWord ++ tailWord_3602839).sum := by decide
  have hdescent : baseEnd_3602839 < baseStart_3602839 := by decide
  rcases family_descends (prefixWord ++ tailWord_3602839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3602852 : List Nat := [2, 3, 1, 2, 1, 1, 2, 1, 2, 4, 4]
def baseStart_3602852 : Nat := 118140960795 + 3602852 * 2 ^ 59
def prefixEnd_3602852 : Nat := 4983230072969 + 3 ^ 40 * 3602852 * 2
def baseEnd_3602852 : Nat := 1849994803012643058680791

theorem tailTrace_3602852 : CollatzResearch.WordTrace tailWord_3602852 prefixEnd_3602852 1849994803012643058680791 := by
  unfold tailWord_3602852
  simp only [CollatzResearch.WordTrace]
  refine ⟨65703403971744998489365405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87604538628993331319153873 65703403971744998489365405)
  ·
    refine ⟨24638776489404374433512027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65703403971744998489365405 24638776489404374433512027)
    ·
      refine ⟨36958164734106561650268041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24638776489404374433512027 36958164734106561650268041)
      ·
        refine ⟨27718623550579921237701031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36958164734106561650268041 27718623550579921237701031)
        ·
          refine ⟨41577935325869881856551547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27718623550579921237701031 41577935325869881856551547)
          ·
            refine ⟨62366902988804822784827321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41577935325869881856551547 62366902988804822784827321)
            ·
              refine ⟨46775177241603617088620491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62366902988804822784827321 46775177241603617088620491)
              ·
                refine ⟨70162765862405425632930737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46775177241603617088620491 70162765862405425632930737)
                ·
                  refine ⟨52622074396804069224698053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70162765862405425632930737 52622074396804069224698053)
                  ·
                    refine ⟨9866638949400762979630885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52622074396804069224698053 9866638949400762979630885)
                    ·
                      refine ⟨1849994803012643058680791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9866638949400762979630885 1849994803012643058680791)
                      ·
                        rfl

theorem cell23_3602852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 2, 4, 4].length) (baseStart_3602852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3602852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3602852 prefixEnd_3602852 := by exact prefixLift 3602852
  have htrace : WordTrace (prefixWord ++ tailWord_3602852) baseStart_3602852 baseEnd_3602852 := by
    simpa [prefixWord, tailWord_3602852, baseEnd_3602852] using wordTrace_append hprefix tailTrace_3602852
  have hstable : (prefixWord ++ tailWord_3602852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3602852).length < 2 ^ (prefixWord ++ tailWord_3602852).sum := by decide
  have hdescent : baseEnd_3602852 < baseStart_3602852 := by decide
  rcases family_descends (prefixWord ++ tailWord_3602852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3602856 : List Nat := [2, 1, 6, 1, 1, 1, 1, 3, 2, 1, 4]
def baseStart_3602856 : Nat := 118140960795 + 3602856 * 2 ^ 59
def prefixEnd_3602856 : Nat := 4983230072969 + 3 ^ 40 * 3602856 * 2
def baseEnd_3602856 : Nat := 1849996856935261043030773

theorem tailTrace_3602856 : CollatzResearch.WordTrace tailWord_3602856 prefixEnd_3602856 1849996856935261043030773 := by
  unfold tailWord_3602856
  simp only [CollatzResearch.WordTrace]
  refine ⟨65703476917737752830938211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87604635890317003774584281 65703476917737752830938211)
  ·
    refine ⟨98555215376606629246407317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65703476917737752830938211 98555215376606629246407317)
    ·
      refine ⟨4619775720778435745925343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 98555215376606629246407317 4619775720778435745925343)
      ·
        refine ⟨6929663581167653618888015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4619775720778435745925343 6929663581167653618888015)
        ·
          refine ⟨10394495371751480428332023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6929663581167653618888015 10394495371751480428332023)
          ·
            refine ⟨15591743057627220642498035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10394495371751480428332023 15591743057627220642498035)
            ·
              refine ⟨23387614586440830963747053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15591743057627220642498035 23387614586440830963747053)
              ·
                refine ⟨8770355469915311611405145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23387614586440830963747053 8770355469915311611405145)
                ·
                  refine ⟨6577766602436483708553859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8770355469915311611405145 6577766602436483708553859)
                  ·
                    refine ⟨9866649903654725562830789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6577766602436483708553859 9866649903654725562830789)
                    ·
                      refine ⟨1849996856935261043030773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9866649903654725562830789 1849996856935261043030773)
                      ·
                        rfl

theorem cell23_3602856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_3602856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3602856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3602856 prefixEnd_3602856 := by exact prefixLift 3602856
  have htrace : WordTrace (prefixWord ++ tailWord_3602856) baseStart_3602856 baseEnd_3602856 := by
    simpa [prefixWord, tailWord_3602856, baseEnd_3602856] using wordTrace_append hprefix tailTrace_3602856
  have hstable : (prefixWord ++ tailWord_3602856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3602856).length < 2 ^ (prefixWord ++ tailWord_3602856).sum := by decide
  have hdescent : baseEnd_3602856 < baseStart_3602856 := by decide
  rcases family_descends (prefixWord ++ tailWord_3602856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3602866 : List Nat := [3, 2, 1, 1, 1, 1, 4, 5, 1, 4]
def baseStart_3602866 : Nat := 118140960795 + 3602866 * 2 ^ 59
def prefixEnd_3602866 : Nat := 4983230072969 + 3 ^ 40 * 3602866 * 2
def baseEnd_3602866 : Nat := 616667330580602001301909

theorem tailTrace_3602866 : CollatzResearch.WordTrace tailWord_3602866 prefixEnd_3602866 616667330580602001301909 := by
  unfold tailWord_3602866
  simp only [CollatzResearch.WordTrace]
  refine ⟨32851829641359819342435113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87604879043626184913160301 32851829641359819342435113)
  ·
    refine ⟨24638872231019864506826335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32851829641359819342435113 24638872231019864506826335)
    ·
      refine ⟨36958308346529796760239503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24638872231019864506826335 36958308346529796760239503)
      ·
        refine ⟨55437462519794695140359255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36958308346529796760239503 55437462519794695140359255)
        ·
          refine ⟨83156193779692042710538883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55437462519794695140359255 83156193779692042710538883)
          ·
            refine ⟨124734290669538064065808325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83156193779692042710538883 124734290669538064065808325)
            ·
              refine ⟨23387679500538387012339061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 124734290669538064065808325 23387679500538387012339061)
              ·
                refine ⟨2192594953175473782406787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23387679500538387012339061 2192594953175473782406787)
                ·
                  refine ⟨3288892429763210673610181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2192594953175473782406787 3288892429763210673610181)
                  ·
                    refine ⟨616667330580602001301909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3288892429763210673610181 616667330580602001301909)
                    ·
                      rfl

theorem cell23_3602866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 5, 1, 4].length) (baseStart_3602866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3602866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3602866 prefixEnd_3602866 := by exact prefixLift 3602866
  have htrace : WordTrace (prefixWord ++ tailWord_3602866) baseStart_3602866 baseEnd_3602866 := by
    simpa [prefixWord, tailWord_3602866, baseEnd_3602866] using wordTrace_append hprefix tailTrace_3602866
  have hstable : (prefixWord ++ tailWord_3602866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3602866).length < 2 ^ (prefixWord ++ tailWord_3602866).sum := by decide
  have hdescent : baseEnd_3602866 < baseStart_3602866 := by decide
  rcases family_descends (prefixWord ++ tailWord_3602866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3602876 : List Nat := [2, 2, 2, 4, 1, 1, 2, 2, 2, 2, 3]
def baseStart_3602876 : Nat := 118140960795 + 3602876 * 2 ^ 59
def prefixEnd_3602876 : Nat := 4983230072969 + 3 ^ 40 * 3602876 * 2
def baseEnd_3602876 : Nat := 1850007126548350964780681

theorem tailTrace_3602876 : CollatzResearch.WordTrace tailWord_3602876 prefixEnd_3602876 1850007126548350964780681 := by
  unfold tailWord_3602876
  simp only [CollatzResearch.WordTrace]
  refine ⟨65703841647701524538802241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87605122196935366051736321 65703841647701524538802241)
  ·
    refine ⟨49277881235776143404101681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65703841647701524538802241 49277881235776143404101681)
    ·
      refine ⟨36958410926832107553076261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49277881235776143404101681 36958410926832107553076261)
      ·
        refine ⟨6929702048781020166201799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36958410926832107553076261 6929702048781020166201799)
        ·
          refine ⟨10394553073171530249302699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6929702048781020166201799 10394553073171530249302699)
          ·
            refine ⟨15591829609757295373954049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10394553073171530249302699 15591829609757295373954049)
            ·
              refine ⟨11693872207317971530465537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15591829609757295373954049 11693872207317971530465537)
              ·
                refine ⟨8770404155488478647849153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11693872207317971530465537 8770404155488478647849153)
                ·
                  refine ⟨6577803116616358985886865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8770404155488478647849153 6577803116616358985886865)
                  ·
                    refine ⟨4933352337462269239415149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6577803116616358985886865 4933352337462269239415149)
                    ·
                      refine ⟨1850007126548350964780681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4933352337462269239415149 1850007126548350964780681)
                      ·
                        rfl

theorem cell23_3602876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_3602876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3602876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3602876 prefixEnd_3602876 := by exact prefixLift 3602876
  have htrace : WordTrace (prefixWord ++ tailWord_3602876) baseStart_3602876 baseEnd_3602876 := by
    simpa [prefixWord, tailWord_3602876, baseEnd_3602876] using wordTrace_append hprefix tailTrace_3602876
  have hstable : (prefixWord ++ tailWord_3602876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3602876).length < 2 ^ (prefixWord ++ tailWord_3602876).sum := by decide
  have hdescent : baseEnd_3602876 < baseStart_3602876 := by decide
  rcases family_descends (prefixWord ++ tailWord_3602876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3602906 : List Nat := [3, 1, 1, 2, 3, 1, 3, 2, 3, 1, 3]
def baseStart_3602906 : Nat := 118140960795 + 3602906 * 2 ^ 59
def prefixEnd_3602906 : Nat := 4983230072969 + 3 ^ 40 * 3602906 * 2
def baseEnd_3602906 : Nat := 1850022530967985847405543

theorem tailTrace_3602906 : CollatzResearch.WordTrace tailWord_3602906 prefixEnd_3602906 1850022530967985847405543 := by
  unfold tailWord_3602906
  simp only [CollatzResearch.WordTrace]
  refine ⟨32852194371323591050299143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87605851656862909467464381 32852194371323591050299143)
  ·
    refine ⟨49278291556985386575448715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32852194371323591050299143 49278291556985386575448715)
    ·
      refine ⟨73917437335478079863173073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49278291556985386575448715 73917437335478079863173073)
      ·
        refine ⟨55438078001608559897379805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73917437335478079863173073 55438078001608559897379805)
        ·
          refine ⟨20789279250603209961517427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55438078001608559897379805 20789279250603209961517427)
          ·
            refine ⟨31183918875904814942276141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20789279250603209961517427 31183918875904814942276141)
            ·
              refine ⟨11693969578464305603353553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31183918875904814942276141 11693969578464305603353553)
              ·
                refine ⟨8770477183848229202515165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11693969578464305603353553 8770477183848229202515165)
                ·
                  refine ⟨3288928943943085950943187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8770477183848229202515165 3288928943943085950943187)
                  ·
                    refine ⟨4933393415914628926414781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3288928943943085950943187 4933393415914628926414781)
                    ·
                      refine ⟨1850022530967985847405543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4933393415914628926414781 1850022530967985847405543)
                      ·
                        rfl

theorem cell23_3602906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 2, 3, 1, 3].length) (baseStart_3602906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3602906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3602906 prefixEnd_3602906 := by exact prefixLift 3602906
  have htrace : WordTrace (prefixWord ++ tailWord_3602906) baseStart_3602906 baseEnd_3602906 := by
    simpa [prefixWord, tailWord_3602906, baseEnd_3602906] using wordTrace_append hprefix tailTrace_3602906
  have hstable : (prefixWord ++ tailWord_3602906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3602906).length < 2 ^ (prefixWord ++ tailWord_3602906).sum := by decide
  have hdescent : baseEnd_3602906 < baseStart_3602906 := by decide
  rcases family_descends (prefixWord ++ tailWord_3602906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3602909 : List Nat := [1, 4, 3, 1, 1, 1, 1, 3, 3, 5]
def baseStart_3602909 : Nat := 118140960795 + 3602909 * 2 ^ 59
def prefixEnd_3602909 : Nat := 4983230072969 + 3 ^ 40 * 3602909 * 2
def baseEnd_3602909 : Nat := 616674690469983111889343

theorem tailTrace_3602909 : CollatzResearch.WordTrace tailWord_3602909 prefixEnd_3602909 616674690469983111889343 := by
  unfold tailWord_3602909
  simp only [CollatzResearch.WordTrace]
  refine ⟨131408886904283495713555781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87605924602855663809037187 131408886904283495713555781)
  ·
    refine ⟨24639166294553155446291709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131408886904283495713555781 24639166294553155446291709)
    ·
      refine ⟨9239687360457433292359391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24639166294553155446291709 9239687360457433292359391)
      ·
        refine ⟨13859531040686149938539087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9239687360457433292359391 13859531040686149938539087)
        ·
          refine ⟨20789296561029224907808631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13859531040686149938539087 20789296561029224907808631)
          ·
            refine ⟨31183944841543837361712947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20789296561029224907808631 31183944841543837361712947)
            ·
              refine ⟨46775917262315756042569421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31183944841543837361712947 46775917262315756042569421)
              ·
                refine ⟨17540968973368408515963533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46775917262315756042569421 17540968973368408515963533)
                ·
                  refine ⟨6577863365013153193486325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17540968973368408515963533 6577863365013153193486325)
                  ·
                    refine ⟨616674690469983111889343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6577863365013153193486325 616674690469983111889343)
                    ·
                      rfl

theorem cell23_3602909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_3602909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3602909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3602909 prefixEnd_3602909 := by exact prefixLift 3602909
  have htrace : WordTrace (prefixWord ++ tailWord_3602909) baseStart_3602909 baseEnd_3602909 := by
    simpa [prefixWord, tailWord_3602909, baseEnd_3602909] using wordTrace_append hprefix tailTrace_3602909
  have hstable : (prefixWord ++ tailWord_3602909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3602909).length < 2 ^ (prefixWord ++ tailWord_3602909).sum := by decide
  have hdescent : baseEnd_3602909 < baseStart_3602909 := by decide
  rcases family_descends (prefixWord ++ tailWord_3602909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3602923 : List Nat := [1, 1, 1, 1, 2, 3, 6, 3, 1, 1, 3]
def baseStart_3602923 : Nat := 118140960795 + 3602923 * 2 ^ 59
def prefixEnd_3602923 : Nat := 4983230072969 + 3 ^ 40 * 3602923 * 2
def baseEnd_3602923 : Nat := 1850031260139112280892965

theorem tailTrace_3602923 : CollatzResearch.WordTrace tailWord_3602923 prefixEnd_3602923 1850031260139112280892965 := by
  unfold tailWord_3602923
  simp only [CollatzResearch.WordTrace]
  refine ⟨131409397526232776104565423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87606265017488517403043615 131409397526232776104565423)
  ·
    refine ⟨197114096289349164156848135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131409397526232776104565423 197114096289349164156848135)
    ·
      refine ⟨295671144434023746235272203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197114096289349164156848135 295671144434023746235272203)
      ·
        refine ⟨443506716651035619352908305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295671144434023746235272203 443506716651035619352908305)
        ·
          refine ⟨332630037488276714514681229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 443506716651035619352908305 332630037488276714514681229)
          ·
            refine ⟨124736264058103767943005461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 332630037488276714514681229 124736264058103767943005461)
            ·
              refine ⟨5847012377723614122328381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 124736264058103767943005461 5847012377723614122328381)
              ·
                refine ⟨2192629641646355295873143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5847012377723614122328381 2192629641646355295873143)
                ·
                  refine ⟨3288944462469532943809715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2192629641646355295873143 3288944462469532943809715)
                  ·
                    refine ⟨4933416693704299415714573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3288944462469532943809715 4933416693704299415714573)
                    ·
                      refine ⟨1850031260139112280892965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4933416693704299415714573 1850031260139112280892965)
                      ·
                        rfl

theorem cell23_3602923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6, 3, 1, 1, 3].length) (baseStart_3602923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3602923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3602923 prefixEnd_3602923 := by exact prefixLift 3602923
  have htrace : WordTrace (prefixWord ++ tailWord_3602923) baseStart_3602923 baseEnd_3602923 := by
    simpa [prefixWord, tailWord_3602923, baseEnd_3602923] using wordTrace_append hprefix tailTrace_3602923
  have hstable : (prefixWord ++ tailWord_3602923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3602923).length < 2 ^ (prefixWord ++ tailWord_3602923).sum := by decide
  have hdescent : baseEnd_3602923 < baseStart_3602923 := by decide
  rcases family_descends (prefixWord ++ tailWord_3602923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3602926 : List Nat := [4, 1, 2, 1, 2, 3, 1, 3, 1, 5]
def baseStart_3602926 : Nat := 118140960795 + 3602926 * 2 ^ 59
def prefixEnd_3602926 : Nat := 4983230072969 + 3 ^ 40 * 3602926 * 2
def baseEnd_3602926 : Nat := 616677600193691923051817

theorem tailTrace_3602926 : CollatzResearch.WordTrace tailWord_3602926 prefixEnd_3602926 616677600193691923051817 := by
  unfold tailWord_3602926
  simp only [CollatzResearch.WordTrace]
  refine ⟨16426188368152738452115579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87606337963481271744616421 16426188368152738452115579)
  ·
    refine ⟨24639282552229107678173369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16426188368152738452115579 24639282552229107678173369)
    ·
      refine ⟨18479461914171830758630027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24639282552229107678173369 18479461914171830758630027)
      ·
        refine ⟨27719192871257746137945041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18479461914171830758630027 27719192871257746137945041)
        ·
          refine ⟨20789394653443309603458781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27719192871257746137945041 20789394653443309603458781)
          ·
            refine ⟨7796022995041241101297043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20789394653443309603458781 7796022995041241101297043)
            ·
              refine ⟨11694034492561861651945565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7796022995041241101297043 11694034492561861651945565)
              ·
                refine ⟨4385262934710698119479587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11694034492561861651945565 4385262934710698119479587)
                ·
                  refine ⟨6577894402066047179219381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4385262934710698119479587 6577894402066047179219381)
                  ·
                    refine ⟨616677600193691923051817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6577894402066047179219381 616677600193691923051817)
                    ·
                      rfl

theorem cell23_3602926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 3, 1, 5].length) (baseStart_3602926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3602926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3602926 prefixEnd_3602926 := by exact prefixLift 3602926
  have htrace : WordTrace (prefixWord ++ tailWord_3602926) baseStart_3602926 baseEnd_3602926 := by
    simpa [prefixWord, tailWord_3602926, baseEnd_3602926] using wordTrace_append hprefix tailTrace_3602926
  have hstable : (prefixWord ++ tailWord_3602926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3602926).length < 2 ^ (prefixWord ++ tailWord_3602926).sum := by decide
  have hdescent : baseEnd_3602926 < baseStart_3602926 := by decide
  rcases family_descends (prefixWord ++ tailWord_3602926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3602949 : List Nat := [1, 3, 1, 1, 2, 2, 2, 1, 5, 2, 3]
def baseStart_3602949 : Nat := 118140960795 + 3602949 * 2 ^ 59
def prefixEnd_3602949 : Nat := 4983230072969 + 3 ^ 40 * 3602949 * 2
def baseEnd_3602949 : Nat := 1850044610636129179167845

theorem tailTrace_3602949 : CollatzResearch.WordTrace tailWord_3602949 prefixEnd_3602949 1850044610636129179167845 := by
  unfold tailWord_3602949
  simp only [CollatzResearch.WordTrace]
  refine ⟨131410345824138582545011901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87606897216092388363341267 131410345824138582545011901)
  ·
    refine ⟨49278879684051968454379463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131410345824138582545011901 49278879684051968454379463)
    ·
      refine ⟨73918319526077952681569195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49278879684051968454379463 73918319526077952681569195)
      ·
        refine ⟨110877479289116929022353793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73918319526077952681569195 110877479289116929022353793)
        ·
          refine ⟨83158109466837696766765345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110877479289116929022353793 83158109466837696766765345)
          ·
            refine ⟨62368582100128272575074009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83158109466837696766765345 62368582100128272575074009)
            ·
              refine ⟨46776436575096204431305507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62368582100128272575074009 46776436575096204431305507)
              ·
                refine ⟨70164654862644306646958261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46776436575096204431305507 70164654862644306646958261)
                ·
                  refine ⟨6577936393372903748152337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70164654862644306646958261 6577936393372903748152337)
                  ·
                    refine ⟨4933452295029677811114253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6577936393372903748152337 4933452295029677811114253)
                    ·
                      refine ⟨1850044610636129179167845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4933452295029677811114253 1850044610636129179167845)
                      ·
                        rfl

theorem cell23_3602949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 5, 2, 3].length) (baseStart_3602949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3602949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3602949 prefixEnd_3602949 := by exact prefixLift 3602949
  have htrace : WordTrace (prefixWord ++ tailWord_3602949) baseStart_3602949 baseEnd_3602949 := by
    simpa [prefixWord, tailWord_3602949, baseEnd_3602949] using wordTrace_append hprefix tailTrace_3602949
  have hstable : (prefixWord ++ tailWord_3602949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3602949).length < 2 ^ (prefixWord ++ tailWord_3602949).sum := by decide
  have hdescent : baseEnd_3602949 < baseStart_3602949 := by decide
  rcases family_descends (prefixWord ++ tailWord_3602949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3602952 : List Nat := [2, 1, 3, 2, 1, 1, 1, 12]
def baseStart_3602952 : Nat := 118140960795 + 3602952 * 2 ^ 59
def prefixEnd_3602952 : Nat := 4983230072969 + 3 ^ 40 * 3602952 * 2
def baseEnd_3602952 : Nat := 68520227817707135830753

theorem tailTrace_3602952 : CollatzResearch.WordTrace tailWord_3602952 prefixEnd_3602952 68520227817707135830753 := by
  unfold tailWord_3602952
  simp only [CollatzResearch.WordTrace]
  refine ⟨65705227621563857028685555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87606970162085142704914073 65705227621563857028685555)
  ·
    refine ⟨98557841432345785543028333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65705227621563857028685555 98557841432345785543028333)
    ·
      refine ⟨36959190537129669578635625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98557841432345785543028333 36959190537129669578635625)
      ·
        refine ⟨27719392902847252183976719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36959190537129669578635625 27719392902847252183976719)
        ·
          refine ⟨41579089354270878275965079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27719392902847252183976719 41579089354270878275965079)
          ·
            refine ⟨62368634031406317413947619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41579089354270878275965079 62368634031406317413947619)
            ·
              refine ⟨93552951047109476120921429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62368634031406317413947619 93552951047109476120921429)
              ·
                refine ⟨68520227817707135830753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 93552951047109476120921429 68520227817707135830753)
                ·
                  rfl

theorem cell23_3602952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 12].length) (baseStart_3602952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3602952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3602952 prefixEnd_3602952 := by exact prefixLift 3602952
  have htrace : WordTrace (prefixWord ++ tailWord_3602952) baseStart_3602952 baseEnd_3602952 := by
    simpa [prefixWord, tailWord_3602952, baseEnd_3602952] using wordTrace_append hprefix tailTrace_3602952
  have hstable : (prefixWord ++ tailWord_3602952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3602952).length < 2 ^ (prefixWord ++ tailWord_3602952).sum := by decide
  have hdescent : baseEnd_3602952 < baseStart_3602952 := by decide
  rcases family_descends (prefixWord ++ tailWord_3602952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3602956 : List Nat := [2, 2, 1, 2, 4, 3, 1, 1, 1, 6]
def baseStart_3602956 : Nat := 118140960795 + 3602956 * 2 ^ 59
def prefixEnd_3602956 : Nat := 4983230072969 + 3 ^ 40 * 3602956 * 2
def baseEnd_3602956 : Nat := 616682735000236883926771

theorem tailTrace_3602956 : CollatzResearch.WordTrace tailWord_3602956 prefixEnd_3602956 616682735000236883926771 := by
  unfold tailWord_3602956
  simp only [CollatzResearch.WordTrace]
  refine ⟨65705300567556611370258361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87607067423408815160344481 65705300567556611370258361)
  ·
    refine ⟨49278975425667458527693771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65705300567556611370258361 49278975425667458527693771)
    ·
      refine ⟨73918463138501187791540657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49278975425667458527693771 73918463138501187791540657)
      ·
        refine ⟨55438847353875890843655493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73918463138501187791540657 55438847353875890843655493)
        ·
          refine ⟨10394783878851729533185405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55438847353875890843655493 10394783878851729533185405)
          ·
            refine ⟨3898043954569398574944527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10394783878851729533185405 3898043954569398574944527)
            ·
              refine ⟨5847065931854097862416791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3898043954569398574944527 5847065931854097862416791)
              ·
                refine ⟨8770598897781146793625187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5847065931854097862416791 8770598897781146793625187)
                ·
                  refine ⟨13155898346671720190437781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8770598897781146793625187 13155898346671720190437781)
                  ·
                    refine ⟨616682735000236883926771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13155898346671720190437781 616682735000236883926771)
                    ·
                      rfl

theorem cell23_3602956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 1, 1, 1, 6].length) (baseStart_3602956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3602956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3602956 prefixEnd_3602956 := by exact prefixLift 3602956
  have htrace : WordTrace (prefixWord ++ tailWord_3602956) baseStart_3602956 baseEnd_3602956 := by
    simpa [prefixWord, tailWord_3602956, baseEnd_3602956] using wordTrace_append hprefix tailTrace_3602956
  have hstable : (prefixWord ++ tailWord_3602956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3602956).length < 2 ^ (prefixWord ++ tailWord_3602956).sum := by decide
  have hdescent : baseEnd_3602956 < baseStart_3602956 := by decide
  rcases family_descends (prefixWord ++ tailWord_3602956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3602997 : List Nat := [1, 3, 3, 1, 1, 2, 5, 2, 1, 2, 2]
def baseStart_3602997 : Nat := 118140960795 + 3602997 * 2 ^ 59
def prefixEnd_3602997 : Nat := 4983230072969 + 3 ^ 40 * 3602997 * 2
def baseEnd_3602997 : Nat := 1850069257707544991367625

theorem tailTrace_3602997 : CollatzResearch.WordTrace tailWord_3602997 prefixEnd_3602997 1850069257707544991367625 := by
  unfold tailWord_3602997
  simp only [CollatzResearch.WordTrace]
  refine ⟨131412096527964686742759245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87608064351976457828506163 131412096527964686742759245)
  ·
    refine ⟨49279536197986757528534717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131412096527964686742759245 49279536197986757528534717)
    ·
      refine ⟨18479826074245034073200519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49279536197986757528534717 18479826074245034073200519)
      ·
        refine ⟨27719739111367551109800779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18479826074245034073200519 27719739111367551109800779)
        ·
          refine ⟨41579608667051326664701169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27719739111367551109800779 41579608667051326664701169)
          ·
            refine ⟨31184706500288494998525877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41579608667051326664701169 31184706500288494998525877)
            ·
              refine ⟨2923566234402046406111801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31184706500288494998525877 2923566234402046406111801)
              ·
                refine ⟨2192674675801534804583851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2923566234402046406111801 2192674675801534804583851)
                ·
                  refine ⟨3289012013702302206875777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2192674675801534804583851 3289012013702302206875777)
                  ·
                    refine ⟨2466759010276726655156833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3289012013702302206875777 2466759010276726655156833)
                    ·
                      refine ⟨1850069257707544991367625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2466759010276726655156833 1850069257707544991367625)
                      ·
                        rfl

theorem cell23_3602997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 5, 2, 1, 2, 2].length) (baseStart_3602997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3602997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3602997 prefixEnd_3602997 := by exact prefixLift 3602997
  have htrace : WordTrace (prefixWord ++ tailWord_3602997) baseStart_3602997 baseEnd_3602997 := by
    simpa [prefixWord, tailWord_3602997, baseEnd_3602997] using wordTrace_append hprefix tailTrace_3602997
  have hstable : (prefixWord ++ tailWord_3602997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3602997).length < 2 ^ (prefixWord ++ tailWord_3602997).sum := by decide
  have hdescent : baseEnd_3602997 < baseStart_3602997 := by decide
  rcases family_descends (prefixWord ++ tailWord_3602997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3603013 : List Nat := [1, 3, 1, 1, 1, 6, 1, 3, 2, 1, 3]
def baseStart_3603013 : Nat := 118140960795 + 3603013 * 2 ^ 59
def prefixEnd_3603013 : Nat := 4983230072969 + 3 ^ 40 * 3603013 * 2
def baseEnd_3603013 : Nat := 1850077473398016928767551

theorem tailTrace_3603013 : CollatzResearch.WordTrace tailWord_3603013 prefixEnd_3603013 1850077473398016928767551 := by
  unfold tailWord_3603013
  simp only [CollatzResearch.WordTrace]
  refine ⟨131412680095906721475341693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87608453397271147650227795 131412680095906721475341693)
  ·
    refine ⟨49279755035965020553253135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131412680095906721475341693 49279755035965020553253135)
    ·
      refine ⟨73919632553947530829879703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49279755035965020553253135 73919632553947530829879703)
      ·
        refine ⟨110879448830921296244819555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73919632553947530829879703 110879448830921296244819555)
        ·
          refine ⟨166319173246381944367229333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110879448830921296244819555 166319173246381944367229333)
          ·
            refine ⟨7796211245924153642213875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 166319173246381944367229333 7796211245924153642213875)
            ·
              refine ⟨11694316868886230463320813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7796211245924153642213875 11694316868886230463320813)
              ·
                refine ⟨4385368825832336423745305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11694316868886230463320813 4385368825832336423745305)
                ·
                  refine ⟨3289026619374252317808979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4385368825832336423745305 3289026619374252317808979)
                  ·
                    refine ⟨4933539929061378476713469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3289026619374252317808979 4933539929061378476713469)
                    ·
                      refine ⟨1850077473398016928767551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4933539929061378476713469 1850077473398016928767551)
                      ·
                        rfl

theorem cell23_3603013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 3, 2, 1, 3].length) (baseStart_3603013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3603013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3603013 prefixEnd_3603013 := by exact prefixLift 3603013
  have htrace : WordTrace (prefixWord ++ tailWord_3603013) baseStart_3603013 baseEnd_3603013 := by
    simpa [prefixWord, tailWord_3603013, baseEnd_3603013] using wordTrace_append hprefix tailTrace_3603013
  have hstable : (prefixWord ++ tailWord_3603013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3603013).length < 2 ^ (prefixWord ++ tailWord_3603013).sum := by decide
  have hdescent : baseEnd_3603013 < baseStart_3603013 := by decide
  rcases family_descends (prefixWord ++ tailWord_3603013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3603023 : List Nat := [1, 1, 2, 1, 1, 2, 7, 2, 1, 3, 2]
def baseStart_3603023 : Nat := 118140960795 + 3603023 * 2 ^ 59
def prefixEnd_3603023 : Nat := 4983230072969 + 3 ^ 40 * 3603023 * 2
def baseEnd_3603023 : Nat := 1850082608204561889642505

theorem tailTrace_3603023 : CollatzResearch.WordTrace tailWord_3603023 prefixEnd_3603023 1850082608204561889642505 := by
  unfold tailWord_3603023
  simp only [CollatzResearch.WordTrace]
  refine ⟨131413044825870493183205723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87608696550580328788803815 131413044825870493183205723)
  ·
    refine ⟨197119567238805739774808585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131413044825870493183205723 197119567238805739774808585)
    ·
      refine ⟨147839675429104304831106439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197119567238805739774808585 147839675429104304831106439)
      ·
        refine ⟨221759513143656457246659659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147839675429104304831106439 221759513143656457246659659)
        ·
          refine ⟨332639269715484685869989489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221759513143656457246659659 332639269715484685869989489)
          ·
            refine ⟨249479452286613514402492117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 332639269715484685869989489 249479452286613514402492117)
            ·
              refine ⟨5847174662967504243808409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 249479452286613514402492117 5847174662967504243808409)
              ·
                refine ⟨4385380997225628182856307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5847174662967504243808409 4385380997225628182856307)
                ·
                  refine ⟨6578071495838442274284461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4385380997225628182856307 6578071495838442274284461)
                  ·
                    refine ⟨2466776810939415852856673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6578071495838442274284461 2466776810939415852856673)
                    ·
                      refine ⟨1850082608204561889642505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2466776810939415852856673 1850082608204561889642505)
                      ·
                        rfl

theorem cell23_3603023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7, 2, 1, 3, 2].length) (baseStart_3603023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3603023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3603023 prefixEnd_3603023 := by exact prefixLift 3603023
  have htrace : WordTrace (prefixWord ++ tailWord_3603023) baseStart_3603023 baseEnd_3603023 := by
    simpa [prefixWord, tailWord_3603023, baseEnd_3603023] using wordTrace_append hprefix tailTrace_3603023
  have hstable : (prefixWord ++ tailWord_3603023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3603023).length < 2 ^ (prefixWord ++ tailWord_3603023).sum := by decide
  have hdescent : baseEnd_3603023 < baseStart_3603023 := by decide
  rcases family_descends (prefixWord ++ tailWord_3603023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3603039 : List Nat := [1, 1, 2, 3, 1, 1, 1, 2, 4, 4, 3]
def baseStart_3603039 : Nat := 118140960795 + 3603039 * 2 ^ 59
def prefixEnd_3603039 : Nat := 4983230072969 + 3 ^ 40 * 3603039 * 2
def baseEnd_3603039 : Nat := 1850090823895033827042431

theorem tailTrace_3603039 : CollatzResearch.WordTrace tailWord_3603039 prefixEnd_3603039 1850090823895033827042431 := by
  unfold tailWord_3603039
  simp only [CollatzResearch.WordTrace]
  refine ⟨131413628393812527915788171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87609085595875018610525447 131413628393812527915788171)
  ·
    refine ⟨197120442590718791873682257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131413628393812527915788171 197120442590718791873682257)
    ·
      refine ⟨147840331943039093905261693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197120442590718791873682257 147840331943039093905261693)
      ·
        refine ⟨55440124478639660214473135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147840331943039093905261693 55440124478639660214473135)
        ·
          refine ⟨83160186717959490321709703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55440124478639660214473135 83160186717959490321709703)
          ·
            refine ⟨124740280076939235482564555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83160186717959490321709703 124740280076939235482564555)
            ·
              refine ⟨187110420115408853223846833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124740280076939235482564555 187110420115408853223846833)
              ·
                refine ⟨140332815086556639917885125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 187110420115408853223846833 140332815086556639917885125)
                ·
                  refine ⟨26312402828729369984603461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 140332815086556639917885125 26312402828729369984603461)
                  ·
                    refine ⟨4933575530386756872113149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26312402828729369984603461 4933575530386756872113149)
                    ·
                      refine ⟨1850090823895033827042431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4933575530386756872113149 1850090823895033827042431)
                      ·
                        rfl

theorem cell23_3603039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 4, 4, 3].length) (baseStart_3603039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3603039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3603039 prefixEnd_3603039 := by exact prefixLift 3603039
  have htrace : WordTrace (prefixWord ++ tailWord_3603039) baseStart_3603039 baseEnd_3603039 := by
    simpa [prefixWord, tailWord_3603039, baseEnd_3603039] using wordTrace_append hprefix tailTrace_3603039
  have hstable : (prefixWord ++ tailWord_3603039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3603039).length < 2 ^ (prefixWord ++ tailWord_3603039).sum := by decide
  have hdescent : baseEnd_3603039 < baseStart_3603039 := by decide
  rcases family_descends (prefixWord ++ tailWord_3603039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3603049 : List Nat := [1, 2, 1, 1, 1, 4, 1, 4, 2, 2, 4]
def baseStart_3603049 : Nat := 118140960795 + 3603049 * 2 ^ 59
def prefixEnd_3603049 : Nat := 4983230072969 + 3 ^ 40 * 3603049 * 2
def baseEnd_3603049 : Nat := 1850095958701578787917385

theorem tailTrace_3603049 : CollatzResearch.WordTrace tailWord_3603049 prefixEnd_3603049 1850095958701578787917385 := by
  unfold tailWord_3603049
  simp only [CollatzResearch.WordTrace]
  refine ⟨131413993123776299623652201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87609328749184199749101467 131413993123776299623652201)
  ·
    refine ⟨98560494842832224717739151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131413993123776299623652201 98560494842832224717739151)
    ·
      refine ⟨147840742264248337076608727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98560494842832224717739151 147840742264248337076608727)
      ·
        refine ⟨221761113396372505614913091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147840742264248337076608727 221761113396372505614913091)
        ·
          refine ⟨332641670094558758422369637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221761113396372505614913091 332641670094558758422369637)
          ·
            refine ⟨62370313142729767204194307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 332641670094558758422369637 62370313142729767204194307)
            ·
              refine ⟨93555469714094650806291461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62370313142729767204194307 93555469714094650806291461)
              ·
                refine ⟨17541650571392747026179649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93555469714094650806291461 17541650571392747026179649)
                ·
                  refine ⟨13156237928544560269634737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17541650571392747026179649 13156237928544560269634737)
                  ·
                    refine ⟨9867178446408420202226053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13156237928544560269634737 9867178446408420202226053)
                    ·
                      refine ⟨1850095958701578787917385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9867178446408420202226053 1850095958701578787917385)
                      ·
                        rfl

theorem cell23_3603049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 4, 2, 2, 4].length) (baseStart_3603049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3603049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3603049 prefixEnd_3603049 := by exact prefixLift 3603049
  have htrace : WordTrace (prefixWord ++ tailWord_3603049) baseStart_3603049 baseEnd_3603049 := by
    simpa [prefixWord, tailWord_3603049, baseEnd_3603049] using wordTrace_append hprefix tailTrace_3603049
  have hstable : (prefixWord ++ tailWord_3603049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3603049).length < 2 ^ (prefixWord ++ tailWord_3603049).sum := by decide
  have hdescent : baseEnd_3603049 < baseStart_3603049 := by decide
  rcases family_descends (prefixWord ++ tailWord_3603049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3603076 : List Nat := [2, 3, 2, 1, 3, 2, 1, 2, 7]
def baseStart_3603076 : Nat := 118140960795 + 3603076 * 2 ^ 59
def prefixEnd_3603076 : Nat := 4983230072969 + 3 ^ 40 * 3603076 * 2
def baseEnd_3603076 : Nat := 205567758075472242475529

theorem tailTrace_3603076 : CollatzResearch.WordTrace tailWord_3603076 prefixEnd_3603076 205567758075472242475529 := by
  unfold tailWord_3603076
  simp only [CollatzResearch.WordTrace]
  refine ⟨65707488947339241617442541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87609985263118988823256721 65707488947339241617442541)
  ·
    refine ⟨24640308355252215606540953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65707488947339241617442541 24640308355252215606540953)
    ·
      refine ⟨18480231266439161704905715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24640308355252215606540953 18480231266439161704905715)
      ·
        refine ⟨27720346899658742557358573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18480231266439161704905715 27720346899658742557358573)
        ·
          refine ⟨10395130087372028459009465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27720346899658742557358573 10395130087372028459009465)
          ·
            refine ⟨7796347565529021344257099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10395130087372028459009465 7796347565529021344257099)
            ·
              refine ⟨11694521348293532016385649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7796347565529021344257099 11694521348293532016385649)
              ·
                refine ⟨8770891011220149012289237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11694521348293532016385649 8770891011220149012289237)
                ·
                  refine ⟨205567758075472242475529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8770891011220149012289237 205567758075472242475529)
                  ·
                    rfl

theorem cell23_3603076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 2, 7].length) (baseStart_3603076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3603076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3603076 prefixEnd_3603076 := by exact prefixLift 3603076
  have htrace : WordTrace (prefixWord ++ tailWord_3603076) baseStart_3603076 baseEnd_3603076 := by
    simpa [prefixWord, tailWord_3603076, baseEnd_3603076] using wordTrace_append hprefix tailTrace_3603076
  have hstable : (prefixWord ++ tailWord_3603076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3603076).length < 2 ^ (prefixWord ++ tailWord_3603076).sum := by decide
  have hdescent : baseEnd_3603076 < baseStart_3603076 := by decide
  rcases family_descends (prefixWord ++ tailWord_3603076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3603086 : List Nat := [4, 1, 1, 3, 1, 1, 1, 2, 1, 5, 3]
def baseStart_3603086 : Nat := 118140960795 + 3603086 * 2 ^ 59
def prefixEnd_3603086 : Nat := 4983230072969 + 3 ^ 40 * 3603086 * 2
def baseEnd_3603086 : Nat := 1850114957485795143154715

theorem tailTrace_3603086 : CollatzResearch.WordTrace tailWord_3603086 prefixEnd_3603086 1850114957485795143154715 := by
  unfold tailWord_3603086
  simp only [CollatzResearch.WordTrace]
  refine ⟨16426917828080281867843639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87610228416428169961832741 16426917828080281867843639)
  ·
    refine ⟨24640376742120422801765459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16426917828080281867843639 24640376742120422801765459)
    ·
      refine ⟨36960565113180634202648189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24640376742120422801765459 36960565113180634202648189)
      ·
        refine ⟨13860211917442737825993071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36960565113180634202648189 13860211917442737825993071)
        ·
          refine ⟨20790317876164106738989607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13860211917442737825993071 20790317876164106738989607)
          ·
            refine ⟨31185476814246160108484411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20790317876164106738989607 31185476814246160108484411)
            ·
              refine ⟨46778215221369240162726617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31185476814246160108484411 46778215221369240162726617)
              ·
                refine ⟨35083661416026930122044963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46778215221369240162726617 35083661416026930122044963)
                ·
                  refine ⟨52625492124040395183067445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35083661416026930122044963 52625492124040395183067445)
                  ·
                    refine ⟨4933639886628787048412573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52625492124040395183067445 4933639886628787048412573)
                    ·
                      refine ⟨1850114957485795143154715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4933639886628787048412573 1850114957485795143154715)
                      ·
                        rfl

theorem cell23_3603086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 2, 1, 5, 3].length) (baseStart_3603086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3603086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3603086 prefixEnd_3603086 := by exact prefixLift 3603086
  have htrace : WordTrace (prefixWord ++ tailWord_3603086) baseStart_3603086 baseEnd_3603086 := by
    simpa [prefixWord, tailWord_3603086, baseEnd_3603086] using wordTrace_append hprefix tailTrace_3603086
  have hstable : (prefixWord ++ tailWord_3603086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3603086).length < 2 ^ (prefixWord ++ tailWord_3603086).sum := by decide
  have hdescent : baseEnd_3603086 < baseStart_3603086 := by decide
  rcases family_descends (prefixWord ++ tailWord_3603086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3603104 : List Nat := [2, 1, 1, 4, 5, 1, 1, 2, 2, 2, 2]
def baseStart_3603104 : Nat := 118140960795 + 3603104 * 2 ^ 59
def prefixEnd_3603104 : Nat := 4983230072969 + 3 ^ 40 * 3603104 * 2
def baseEnd_3603104 : Nat := 1850124200137576072729633

theorem tailTrace_3603104 : CollatzResearch.WordTrace tailWord_3603104 prefixEnd_3603104 1850124200137576072729633 := by
  unfold tailWord_3603104
  simp only [CollatzResearch.WordTrace]
  refine ⟨65707999569288522008452183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87610666092384696011269577 65707999569288522008452183)
  ·
    refine ⟨98561999353932783012678275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65707999569288522008452183 98561999353932783012678275)
    ·
      refine ⟨147842999030899174519017413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98561999353932783012678275 147842999030899174519017413)
      ·
        refine ⟨27720562318293595222315765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 147842999030899174519017413 27720562318293595222315765)
        ·
          refine ⟨2598802717340024552092103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27720562318293595222315765 2598802717340024552092103)
          ·
            refine ⟨3898204076010036828138155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2598802717340024552092103 3898204076010036828138155)
            ·
              refine ⟨5847306114015055242207233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3898204076010036828138155 5847306114015055242207233)
              ·
                refine ⟨4385479585511291431655425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5847306114015055242207233 4385479585511291431655425)
                ·
                  refine ⟨3289109689133468573741569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4385479585511291431655425 3289109689133468573741569)
                  ·
                    refine ⟨2466832266850101430306177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3289109689133468573741569 2466832266850101430306177)
                    ·
                      refine ⟨1850124200137576072729633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2466832266850101430306177 1850124200137576072729633)
                      ·
                        rfl

theorem cell23_3603104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 1, 2, 2, 2, 2].length) (baseStart_3603104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3603104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3603104 prefixEnd_3603104 := by exact prefixLift 3603104
  have htrace : WordTrace (prefixWord ++ tailWord_3603104) baseStart_3603104 baseEnd_3603104 := by
    simpa [prefixWord, tailWord_3603104, baseEnd_3603104] using wordTrace_append hprefix tailTrace_3603104
  have hstable : (prefixWord ++ tailWord_3603104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3603104).length < 2 ^ (prefixWord ++ tailWord_3603104).sum := by decide
  have hdescent : baseEnd_3603104 < baseStart_3603104 := by decide
  rcases family_descends (prefixWord ++ tailWord_3603104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3603179 : List Nat := [1, 1, 1, 1, 2, 4, 1, 1, 2, 9]
def baseStart_3603179 : Nat := 118140960795 + 3603179 * 2 ^ 59
def prefixEnd_3603179 : Nat := 4983230072969 + 3 ^ 40 * 3603179 * 2
def baseEnd_3603179 : Nat := 616720903728887759763929

theorem tailTrace_3603179 : CollatzResearch.WordTrace tailWord_3603179 prefixEnd_3603179 616720903728887759763929 := by
  unfold tailWord_3603179
  simp only [CollatzResearch.WordTrace]
  refine ⟨131418734613305331825884591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87612489742203554550589727 131418734613305331825884591)
  ·
    refine ⟨197128101919957997738826887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131418734613305331825884591 197128101919957997738826887)
    ·
      refine ⟨295692152879936996608240331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197128101919957997738826887 295692152879936996608240331)
      ·
        refine ⟨443538229319905494912360497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295692152879936996608240331 443538229319905494912360497)
        ·
          refine ⟨332653671989929121184270373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 443538229319905494912360497 332653671989929121184270373)
          ·
            refine ⟨62372563498111710222050695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 332653671989929121184270373 62372563498111710222050695)
            ·
              refine ⟨93558845247167565333076043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62372563498111710222050695 93558845247167565333076043)
              ·
                refine ⟨140338267870751347999614065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93558845247167565333076043 140338267870751347999614065)
                ·
                  refine ⟨105253700903063510999710549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 140338267870751347999614065 105253700903063510999710549)
                  ·
                    refine ⟨616720903728887759763929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 105253700903063510999710549 616720903728887759763929)
                    ·
                      rfl

theorem cell23_3603179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 9].length) (baseStart_3603179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3603179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3603179 prefixEnd_3603179 := by exact prefixLift 3603179
  have htrace : WordTrace (prefixWord ++ tailWord_3603179) baseStart_3603179 baseEnd_3603179 := by
    simpa [prefixWord, tailWord_3603179, baseEnd_3603179] using wordTrace_append hprefix tailTrace_3603179
  have hstable : (prefixWord ++ tailWord_3603179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3603179).length < 2 ^ (prefixWord ++ tailWord_3603179).sum := by decide
  have hdescent : baseEnd_3603179 < baseStart_3603179 := by decide
  rcases family_descends (prefixWord ++ tailWord_3603179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3603183 : List Nat := [1, 1, 2, 1, 5, 2, 4, 1, 6]
def baseStart_3603183 : Nat := 118140960795 + 3603183 * 2 ^ 59
def prefixEnd_3603183 : Nat := 4983230072969 + 3 ^ 40 * 3603183 * 2
def baseEnd_3603183 : Nat := 205573862789920140404641

theorem tailTrace_3603183 : CollatzResearch.WordTrace tailWord_3603183 prefixEnd_3603183 205573862789920140404641 := by
  unfold tailWord_3603183
  simp only [CollatzResearch.WordTrace]
  refine ⟨131418880505290840509030203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87612587003527227006020135 131418880505290840509030203)
  ·
    refine ⟨197128320757936260763545305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131418880505290840509030203 197128320757936260763545305)
    ·
      refine ⟨147846240568452195572658979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197128320757936260763545305 147846240568452195572658979)
      ·
        refine ⟨221769360852678293358988469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147846240568452195572658979 221769360852678293358988469)
        ·
          refine ⟨20790877579938590002405169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 221769360852678293358988469 20790877579938590002405169)
          ·
            refine ⟨15593158184953942501803877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20790877579938590002405169 15593158184953942501803877)
            ·
              refine ⟨2923717159678864219088227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15593158184953942501803877 2923717159678864219088227)
              ·
                refine ⟨4385575739518296328632341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2923717159678864219088227 4385575739518296328632341)
                ·
                  refine ⟨205573862789920140404641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4385575739518296328632341 205573862789920140404641)
                  ·
                    rfl

theorem cell23_3603183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 4, 1, 6].length) (baseStart_3603183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3603183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3603183 prefixEnd_3603183 := by exact prefixLift 3603183
  have htrace : WordTrace (prefixWord ++ tailWord_3603183) baseStart_3603183 baseEnd_3603183 := by
    simpa [prefixWord, tailWord_3603183, baseEnd_3603183] using wordTrace_append hprefix tailTrace_3603183
  have hstable : (prefixWord ++ tailWord_3603183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3603183).length < 2 ^ (prefixWord ++ tailWord_3603183).sum := by decide
  have hdescent : baseEnd_3603183 < baseStart_3603183 := by decide
  rcases family_descends (prefixWord ++ tailWord_3603183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3603193 : List Nat := [1, 2, 1, 3, 1, 1, 1, 6, 3, 1, 3]
def baseStart_3603193 : Nat := 118140960795 + 3603193 * 2 ^ 59
def prefixEnd_3603193 : Nat := 4983230072969 + 3 ^ 40 * 3603193 * 2
def baseEnd_3603193 : Nat := 1850169899915826224516723

theorem tailTrace_3603193 : CollatzResearch.WordTrace tailWord_3603193 prefixEnd_3603193 1850169899915826224516723 := by
  unfold tailWord_3603193
  simp only [CollatzResearch.WordTrace]
  refine ⟨131419245235254612216894233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87612830156836408144596155 131419245235254612216894233)
  ·
    refine ⟨98564433926440959162670675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131419245235254612216894233 98564433926440959162670675)
    ·
      refine ⟨147846650889661438744006013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98564433926440959162670675 147846650889661438744006013)
      ·
        refine ⟨55442494083623039529002255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147846650889661438744006013 55442494083623039529002255)
        ·
          refine ⟨83163741125434559293503383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55442494083623039529002255 83163741125434559293503383)
          ·
            refine ⟨124745611688151838940255075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83163741125434559293503383 124745611688151838940255075)
            ·
              refine ⟨187118417532227758410382613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124745611688151838940255075 187118417532227758410382613)
              ·
                refine ⟨8771175821823176175486685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 187118417532227758410382613 8771175821823176175486685)
                ·
                  refine ⟨3289190933183691065807507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8771175821823176175486685 3289190933183691065807507)
                  ·
                    refine ⟨4933786399775536598711261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3289190933183691065807507 4933786399775536598711261)
                    ·
                      refine ⟨1850169899915826224516723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4933786399775536598711261 1850169899915826224516723)
                      ·
                        rfl

theorem cell23_3603193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 6, 3, 1, 3].length) (baseStart_3603193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3603193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3603193 prefixEnd_3603193 := by exact prefixLift 3603193
  have htrace : WordTrace (prefixWord ++ tailWord_3603193) baseStart_3603193 baseEnd_3603193 := by
    simpa [prefixWord, tailWord_3603193, baseEnd_3603193] using wordTrace_append hprefix tailTrace_3603193
  have hstable : (prefixWord ++ tailWord_3603193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3603193).length < 2 ^ (prefixWord ++ tailWord_3603193).sum := by decide
  have hdescent : baseEnd_3603193 < baseStart_3603193 := by decide
  rcases family_descends (prefixWord ++ tailWord_3603193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3603226 : List Nat := [3, 1, 1, 3, 2, 1, 1, 2, 3, 6]
def baseStart_3603226 : Nat := 118140960795 + 3603226 * 2 ^ 59
def prefixEnd_3603226 : Nat := 4983230072969 + 3 ^ 40 * 3603226 * 2
def baseEnd_3603226 : Nat := 616728948259141531801357

theorem tailTrace_3603226 : CollatzResearch.WordTrace tailWord_3603226 prefixEnd_3603226 616728948259141531801357 := by
  unfold tailWord_3603226
  simp only [CollatzResearch.WordTrace]
  refine ⟨32855112211033764713211383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87613632562756705901897021 32855112211033764713211383)
  ·
    refine ⟨49282668316550647069817075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32855112211033764713211383 49282668316550647069817075)
    ·
      refine ⟨73924002474825970604725613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49282668316550647069817075 73924002474825970604725613)
      ·
        refine ⟨27721500928059738976772105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73924002474825970604725613 27721500928059738976772105)
        ·
          refine ⟨20791125696044804232579079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27721500928059738976772105 20791125696044804232579079)
          ·
            refine ⟨31186688544067206348868619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20791125696044804232579079 31186688544067206348868619)
            ·
              refine ⟨46780032816100809523302929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31186688544067206348868619 46780032816100809523302929)
              ·
                refine ⟨35085024612075607142477197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46780032816100809523302929 35085024612075607142477197)
                ·
                  refine ⟨13156884229528352678428949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35085024612075607142477197 13156884229528352678428949)
                  ·
                    refine ⟨616728948259141531801357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13156884229528352678428949 616728948259141531801357)
                    ·
                      rfl

theorem cell23_3603226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 2, 3, 6].length) (baseStart_3603226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3603226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3603226 prefixEnd_3603226 := by exact prefixLift 3603226
  have htrace : WordTrace (prefixWord ++ tailWord_3603226) baseStart_3603226 baseEnd_3603226 := by
    simpa [prefixWord, tailWord_3603226, baseEnd_3603226] using wordTrace_append hprefix tailTrace_3603226
  have hstable : (prefixWord ++ tailWord_3603226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3603226).length < 2 ^ (prefixWord ++ tailWord_3603226).sum := by decide
  have hdescent : baseEnd_3603226 < baseStart_3603226 := by decide
  rcases family_descends (prefixWord ++ tailWord_3603226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3603263 : List Nat := [1, 1, 2, 2, 5, 1, 2, 2, 1, 2, 4]
def baseStart_3603263 : Nat := 118140960795 + 3603263 * 2 ^ 59
def prefixEnd_3603263 : Nat := 4983230072969 + 3 ^ 40 * 3603263 * 2
def baseEnd_3603263 : Nat := 1850205843561640950641401

theorem tailTrace_3603263 : CollatzResearch.WordTrace tailWord_3603263 prefixEnd_3603263 1850205843561640950641401 := by
  unfold tailWord_3603263
  simp only [CollatzResearch.WordTrace]
  refine ⟨131421798345001014171942443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87614532230000676114628295 131421798345001014171942443)
  ·
    refine ⟨197132697517501521257913665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131421798345001014171942443 197132697517501521257913665)
    ·
      refine ⟨147849523138126140943435249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197132697517501521257913665 147849523138126140943435249)
      ·
        refine ⟨110887142353594605707576437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147849523138126140943435249 110887142353594605707576437)
        ·
          refine ⟨10395669595649494285085291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 110887142353594605707576437 10395669595649494285085291)
          ·
            refine ⟨15593504393474241427627937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10395669595649494285085291 15593504393474241427627937)
            ·
              refine ⟨11695128295105681070720953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15593504393474241427627937 11695128295105681070720953)
              ·
                refine ⟨8771346221329260803040715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11695128295105681070720953 8771346221329260803040715)
                ·
                  refine ⟨13157019331993891204561073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8771346221329260803040715 13157019331993891204561073)
                  ·
                    refine ⟨9867764498995418403420805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13157019331993891204561073 9867764498995418403420805)
                    ·
                      refine ⟨1850205843561640950641401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9867764498995418403420805 1850205843561640950641401)
                      ·
                        rfl

theorem cell23_3603263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 2, 1, 2, 4].length) (baseStart_3603263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3603263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3603263 prefixEnd_3603263 := by exact prefixLift 3603263
  have htrace : WordTrace (prefixWord ++ tailWord_3603263) baseStart_3603263 baseEnd_3603263 := by
    simpa [prefixWord, tailWord_3603263, baseEnd_3603263] using wordTrace_append hprefix tailTrace_3603263
  have hstable : (prefixWord ++ tailWord_3603263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3603263).length < 2 ^ (prefixWord ++ tailWord_3603263).sum := by decide
  have hdescent : baseEnd_3603263 < baseStart_3603263 := by decide
  rcases family_descends (prefixWord ++ tailWord_3603263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3603277 : List Nat := [1, 6, 1, 2, 2, 1, 1, 1, 4, 4]
def baseStart_3603277 : Nat := 118140960795 + 3603277 * 2 ^ 59
def prefixEnd_3603277 : Nat := 4983230072969 + 3 ^ 40 * 3603277 * 2
def baseEnd_3603277 : Nat := 616737677430267965288779

theorem tailTrace_3603277 : CollatzResearch.WordTrace tailWord_3603277 prefixEnd_3603277 616737677430267965288779 := by
  unfold tailWord_3603277
  simp only [CollatzResearch.WordTrace]
  refine ⟨131422308966950294562952085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87614872644633529708634723 131422308966950294562952085)
  ·
    refine ⟨6160420732825795057638379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 131422308966950294562952085 6160420732825795057638379)
    ·
      refine ⟨9240631099238692586457569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6160420732825795057638379 9240631099238692586457569)
      ·
        refine ⟨6930473324429019439843177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9240631099238692586457569 6930473324429019439843177)
        ·
          refine ⟨5197854993321764579882383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6930473324429019439843177 5197854993321764579882383)
          ·
            refine ⟨7796782489982646869823575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5197854993321764579882383 7796782489982646869823575)
            ·
              refine ⟨11695173734973970304735363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7796782489982646869823575 11695173734973970304735363)
              ·
                refine ⟨17542760602460955457103045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11695173734973970304735363 17542760602460955457103045)
                ·
                  refine ⟨3289267612961429148206821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17542760602460955457103045 3289267612961429148206821)
                  ·
                    refine ⟨616737677430267965288779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3289267612961429148206821 616737677430267965288779)
                    ·
                      rfl

theorem cell23_3603277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 1, 4, 4].length) (baseStart_3603277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3603277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3603277 prefixEnd_3603277 := by exact prefixLift 3603277
  have htrace : WordTrace (prefixWord ++ tailWord_3603277) baseStart_3603277 baseEnd_3603277 := by
    simpa [prefixWord, tailWord_3603277, baseEnd_3603277] using wordTrace_append hprefix tailTrace_3603277
  have hstable : (prefixWord ++ tailWord_3603277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3603277).length < 2 ^ (prefixWord ++ tailWord_3603277).sum := by decide
  have hdescent : baseEnd_3603277 < baseStart_3603277 := by decide
  rcases family_descends (prefixWord ++ tailWord_3603277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3603284 : List Nat := [2, 4, 1, 1, 4, 1, 2, 1, 3, 2, 2]
def baseStart_3603284 : Nat := 118140960795 + 3603284 * 2 ^ 59
def prefixEnd_3603284 : Nat := 4983230072969 + 3 ^ 40 * 3603284 * 2
def baseEnd_3603284 : Nat := 1850216626655385368478805

theorem tailTrace_3603284 : CollatzResearch.WordTrace tailWord_3603284 prefixEnd_3603284 1850216626655385368478805 := by
  unfold tailWord_3603284
  simp only [CollatzResearch.WordTrace]
  refine ⟨65711282138962467379228453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87615042851949956505637937 65711282138962467379228453)
  ·
    refine ⟨12320865401055462633605335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65711282138962467379228453 12320865401055462633605335)
    ·
      refine ⟨18481298101583193950408003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12320865401055462633605335 18481298101583193950408003)
      ·
        refine ⟨27721947152374790925612005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18481298101583193950408003 27721947152374790925612005)
        ·
          refine ⟨5197865091070273298552251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27721947152374790925612005 5197865091070273298552251)
          ·
            refine ⟨7796797636605409947828377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5197865091070273298552251 7796797636605409947828377)
            ·
              refine ⟨5847598227454057460871283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7796797636605409947828377 5847598227454057460871283)
              ·
                refine ⟨8771397341181086191306925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5847598227454057460871283 8771397341181086191306925)
                ·
                  refine ⟨3289274002942907321740097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8771397341181086191306925 3289274002942907321740097)
                  ·
                    refine ⟨2466955502207180491305073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3289274002942907321740097 2466955502207180491305073)
                    ·
                      refine ⟨1850216626655385368478805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2466955502207180491305073 1850216626655385368478805)
                      ·
                        rfl

theorem cell23_3603284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 2, 1, 3, 2, 2].length) (baseStart_3603284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3603284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3603284 prefixEnd_3603284 := by exact prefixLift 3603284
  have htrace : WordTrace (prefixWord ++ tailWord_3603284) baseStart_3603284 baseEnd_3603284 := by
    simpa [prefixWord, tailWord_3603284, baseEnd_3603284] using wordTrace_append hprefix tailTrace_3603284
  have hstable : (prefixWord ++ tailWord_3603284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3603284).length < 2 ^ (prefixWord ++ tailWord_3603284).sum := by decide
  have hdescent : baseEnd_3603284 < baseStart_3603284 := by decide
  rcases family_descends (prefixWord ++ tailWord_3603284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3603300 : List Nat := [2, 3, 1, 1, 4, 1, 3, 1, 1, 3, 3]
def baseStart_3603300 : Nat := 118140960795 + 3603300 * 2 ^ 59
def prefixEnd_3603300 : Nat := 4983230072969 + 3 ^ 40 * 3603300 * 2
def baseEnd_3603300 : Nat := 1850224842345857305878731

theorem tailTrace_3603300 : CollatzResearch.WordTrace tailWord_3603300 prefixEnd_3603300 1850224842345857305878731 := by
  unfold tailWord_3603300
  simp only [CollatzResearch.WordTrace]
  refine ⟨65711573922933484745519677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87615431897244646327359569 65711573922933484745519677)
  ·
    refine ⟨24641840221100056779569879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65711573922933484745519677 24641840221100056779569879)
    ·
      refine ⟨36962760331650085169354819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24641840221100056779569879 36962760331650085169354819)
      ·
        refine ⟨55444140497475127754032229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36962760331650085169354819 55444140497475127754032229)
        ·
          refine ⟨10395776343276586453881043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55444140497475127754032229 10395776343276586453881043)
          ·
            refine ⟨15593664514914879680821565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10395776343276586453881043 15593664514914879680821565)
            ·
              refine ⟨5847624193093079880308087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15593664514914879680821565 5847624193093079880308087)
              ·
                refine ⟨8771436289639619820462131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5847624193093079880308087 8771436289639619820462131)
                ·
                  refine ⟨13157154434459429730693197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8771436289639619820462131 13157154434459429730693197)
                  ·
                    refine ⟨4933932912922286149009949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13157154434459429730693197 4933932912922286149009949)
                    ·
                      refine ⟨1850224842345857305878731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4933932912922286149009949 1850224842345857305878731)
                      ·
                        rfl

theorem cell23_3603300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3, 1, 1, 3, 3].length) (baseStart_3603300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3603300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3603300 prefixEnd_3603300 := by exact prefixLift 3603300
  have htrace : WordTrace (prefixWord ++ tailWord_3603300) baseStart_3603300 baseEnd_3603300 := by
    simpa [prefixWord, tailWord_3603300, baseEnd_3603300] using wordTrace_append hprefix tailTrace_3603300
  have hstable : (prefixWord ++ tailWord_3603300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3603300).length < 2 ^ (prefixWord ++ tailWord_3603300).sum := by decide
  have hdescent : baseEnd_3603300 < baseStart_3603300 := by decide
  rcases family_descends (prefixWord ++ tailWord_3603300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3603318 : List Nat := [5, 1, 1, 3, 1, 3, 1, 3, 1, 2, 2]
def baseStart_3603318 : Nat := 118140960795 + 3603318 * 2 ^ 59
def prefixEnd_3603318 : Nat := 4983230072969 + 3 ^ 40 * 3603318 * 2
def baseEnd_3603318 : Nat := 1850234084997638235453649

theorem tailTrace_3603318 : CollatzResearch.WordTrace tailWord_3603318 prefixEnd_3603318 1850234084997638235453649 := by
  unfold tailWord_3603318
  simp only [CollatzResearch.WordTrace]
  refine ⟨8213987772487609910324663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 87615869573201172376796405 8213987772487609910324663)
  ·
    refine ⟨12320981658731414865486995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8213987772487609910324663 12320981658731414865486995)
    ·
      refine ⟨18481472488097122298230493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12320981658731414865486995 18481472488097122298230493)
      ·
        refine ⟨6930552183036420861836435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18481472488097122298230493 6930552183036420861836435)
        ·
          refine ⟨10395828274554631292754653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6930552183036420861836435 10395828274554631292754653)
          ·
            refine ⟨3898435602957986734782995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10395828274554631292754653 3898435602957986734782995)
            ·
              refine ⟨5847653404436980102174493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3898435602957986734782995 5847653404436980102174493)
              ·
                refine ⟨2192870026663867538315435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5847653404436980102174493 2192870026663867538315435)
                ·
                  refine ⟨3289305039995801307473153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2192870026663867538315435 3289305039995801307473153)
                  ·
                    refine ⟨2466978779996850980604865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3289305039995801307473153 2466978779996850980604865)
                    ·
                      refine ⟨1850234084997638235453649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2466978779996850980604865 1850234084997638235453649)
                      ·
                        rfl

theorem cell23_3603318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 1, 3, 1, 2, 2].length) (baseStart_3603318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3603318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3603318 prefixEnd_3603318 := by exact prefixLift 3603318
  have htrace : WordTrace (prefixWord ++ tailWord_3603318) baseStart_3603318 baseEnd_3603318 := by
    simpa [prefixWord, tailWord_3603318, baseEnd_3603318] using wordTrace_append hprefix tailTrace_3603318
  have hstable : (prefixWord ++ tailWord_3603318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3603318).length < 2 ^ (prefixWord ++ tailWord_3603318).sum := by decide
  have hdescent : baseEnd_3603318 < baseStart_3603318 := by decide
  rcases family_descends (prefixWord ++ tailWord_3603318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3603390 : List Nat := [4, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3]
def baseStart_3603390 : Nat := 118140960795 + 3603390 * 2 ^ 59
def prefixEnd_3603390 : Nat := 4983230072969 + 3 ^ 40 * 3603390 * 2
def baseEnd_3603390 : Nat := 1850271055604761953753317

theorem tailTrace_3603390 : CollatzResearch.WordTrace tailWord_3603390 prefixEnd_3603390 1850271055604761953753317 := by
  unfold tailWord_3603390
  simp only [CollatzResearch.WordTrace]
  refine ⟨16428303801942614357726953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87617620277027276574543749 16428303801942614357726953)
  ·
    refine ⟨12321227851456960768295215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16428303801942614357726953 12321227851456960768295215)
    ·
      refine ⟨18481841777185441152442823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12321227851456960768295215 18481841777185441152442823)
      ·
        refine ⟨27722762665778161728664235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18481841777185441152442823 27722762665778161728664235)
        ·
          refine ⟨41584143998667242592996353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27722762665778161728664235 41584143998667242592996353)
          ·
            refine ⟨31188107999000431944747265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41584143998667242592996353 31188107999000431944747265)
            ·
              refine ⟨23391080999250323958560449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31188107999000431944747265 23391080999250323958560449)
              ·
                refine ⟨17543310749437742968920337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23391080999250323958560449 17543310749437742968920337)
                ·
                  refine ⟨13157483062078307226690253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17543310749437742968920337 13157483062078307226690253)
                  ·
                    refine ⟨4934056148279365210008845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13157483062078307226690253 4934056148279365210008845)
                    ·
                      refine ⟨1850271055604761953753317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4934056148279365210008845 1850271055604761953753317)
                      ·
                        rfl

theorem cell23_3603390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3].length) (baseStart_3603390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3603390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3603390 prefixEnd_3603390 := by exact prefixLift 3603390
  have htrace : WordTrace (prefixWord ++ tailWord_3603390) baseStart_3603390 baseEnd_3603390 := by
    simpa [prefixWord, tailWord_3603390, baseEnd_3603390] using wordTrace_append hprefix tailTrace_3603390
  have hstable : (prefixWord ++ tailWord_3603390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3603390).length < 2 ^ (prefixWord ++ tailWord_3603390).sum := by decide
  have hdescent : baseEnd_3603390 < baseStart_3603390 := by decide
  rcases family_descends (prefixWord ++ tailWord_3603390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3603403 : List Nat := [1, 1, 1, 1, 3, 5, 2, 1, 1, 2, 5]
def baseStart_3603403 : Nat := 118140960795 + 3603403 * 2 ^ 59
def prefixEnd_3603403 : Nat := 4983230072969 + 3 ^ 40 * 3603403 * 2
def baseEnd_3603403 : Nat := 1850277730853270402890757

theorem tailTrace_3603403 : CollatzResearch.WordTrace tailWord_3603403 prefixEnd_3603403 1850277730853270402890757 := by
  unfold tailWord_3603403
  simp only [CollatzResearch.WordTrace]
  refine ⟨131426904564493818082038863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87617936376329212054692575 131426904564493818082038863)
  ·
    refine ⟨197140356846740727123058295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131426904564493818082038863 197140356846740727123058295)
    ·
      refine ⟨295710535270111090684587443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197140356846740727123058295 295710535270111090684587443)
      ·
        refine ⟨443565802905166636026881165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295710535270111090684587443 443565802905166636026881165)
        ·
          refine ⟨166337176089437488510080437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 443565802905166636026881165 166337176089437488510080437)
          ·
            refine ⟨15594110258384764547820041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 166337176089437488510080437 15594110258384764547820041)
            ·
              refine ⟨11695582693788573410865031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15594110258384764547820041 11695582693788573410865031)
              ·
                refine ⟨17543374040682860116297547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11695582693788573410865031 17543374040682860116297547)
                ·
                  refine ⟨26315061061024290174446321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17543374040682860116297547 26315061061024290174446321)
                  ·
                    refine ⟨19736295795768217630834741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26315061061024290174446321 19736295795768217630834741)
                    ·
                      refine ⟨1850277730853270402890757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19736295795768217630834741 1850277730853270402890757)
                      ·
                        rfl

theorem cell23_3603403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 1, 1, 2, 5].length) (baseStart_3603403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3603403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3603403 prefixEnd_3603403 := by exact prefixLift 3603403
  have htrace : WordTrace (prefixWord ++ tailWord_3603403) baseStart_3603403 baseEnd_3603403 := by
    simpa [prefixWord, tailWord_3603403, baseEnd_3603403] using wordTrace_append hprefix tailTrace_3603403
  have hstable : (prefixWord ++ tailWord_3603403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3603403).length < 2 ^ (prefixWord ++ tailWord_3603403).sum := by decide
  have hdescent : baseEnd_3603403 < baseStart_3603403 := by decide
  rcases family_descends (prefixWord ++ tailWord_3603403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3603450 : List Nat := [3, 1, 1, 1, 1, 2, 1, 6, 2, 2, 3]
def baseStart_3603450 : Nat := 118140960795 + 3603450 * 2 ^ 59
def prefixEnd_3603450 : Nat := 4983230072969 + 3 ^ 40 * 3603450 * 2
def baseEnd_3603450 : Nat := 1850301864444031719003041

theorem tailTrace_3603450 : CollatzResearch.WordTrace tailWord_3603450 prefixEnd_3603450 1850301864444031719003041 := by
  unfold tailWord_3603450
  simp only [CollatzResearch.WordTrace]
  refine ⟨32857154698830886277249951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87619079196882363405999869 32857154698830886277249951)
  ·
    refine ⟨49285732048246329415874927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32857154698830886277249951 49285732048246329415874927)
    ·
      refine ⟨73928598072369494123812391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49285732048246329415874927 73928598072369494123812391)
      ·
        refine ⟨110892897108554241185718587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73928598072369494123812391 110892897108554241185718587)
        ·
          refine ⟨166339345662831361778577881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110892897108554241185718587 166339345662831361778577881)
          ·
            refine ⟨124754509247123521333933411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166339345662831361778577881 124754509247123521333933411)
            ·
              refine ⟨187131763870685282000900117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124754509247123521333933411 187131763870685282000900117)
              ·
                refine ⟨8771801431438372593792193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 187131763870685282000900117 8771801431438372593792193)
                ·
                  refine ⟨6578851073578779445344145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8771801431438372593792193 6578851073578779445344145)
                  ·
                    refine ⟨4934138305184084584008109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6578851073578779445344145 4934138305184084584008109)
                    ·
                      refine ⟨1850301864444031719003041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4934138305184084584008109 1850301864444031719003041)
                      ·
                        rfl

theorem cell23_3603450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 6, 2, 2, 3].length) (baseStart_3603450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3603450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3603450 prefixEnd_3603450 := by exact prefixLift 3603450
  have htrace : WordTrace (prefixWord ++ tailWord_3603450) baseStart_3603450 baseEnd_3603450 := by
    simpa [prefixWord, tailWord_3603450, baseEnd_3603450] using wordTrace_append hprefix tailTrace_3603450
  have hstable : (prefixWord ++ tailWord_3603450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3603450).length < 2 ^ (prefixWord ++ tailWord_3603450).sum := by decide
  have hdescent : baseEnd_3603450 < baseStart_3603450 := by decide
  rcases family_descends (prefixWord ++ tailWord_3603450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3603457 : List Nat := [1, 2, 4, 1, 2, 3, 2, 1, 3, 4]
def baseStart_3603457 : Nat := 118140960795 + 3603457 * 2 ^ 59
def prefixEnd_3603457 : Nat := 4983230072969 + 3 ^ 40 * 3603457 * 2
def baseEnd_3603457 : Nat := 616768486269537730538503

theorem tailTrace_3603457 : CollatzResearch.WordTrace tailWord_3603457 prefixEnd_3603457 616768486269537730538503 := by
  unfold tailWord_3603457
  simp only [CollatzResearch.WordTrace]
  refine ⟨131428874106298185304504625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87619249404198790203003083 131428874106298185304504625)
  ·
    refine ⟨98571655579723638978378469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131428874106298185304504625 98571655579723638978378469)
    ·
      refine ⟨18482185421198182308445963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98571655579723638978378469 18482185421198182308445963)
      ·
        refine ⟨27723278131797273462668945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18482185421198182308445963 27723278131797273462668945)
        ·
          refine ⟨20792458598847955097001709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27723278131797273462668945 20792458598847955097001709)
          ·
            refine ⟨7797171974567983161375641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20792458598847955097001709 7797171974567983161375641)
            ·
              refine ⟨5847878980925987371031731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7797171974567983161375641 5847878980925987371031731)
              ·
                refine ⟨8771818471388981056547597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5847878980925987371031731 8771818471388981056547597)
                ·
                  refine ⟨3289431926770867896205349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8771818471388981056547597 3289431926770867896205349)
                  ·
                    refine ⟨616768486269537730538503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3289431926770867896205349 616768486269537730538503)
                    ·
                      rfl

theorem cell23_3603457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2, 1, 3, 4].length) (baseStart_3603457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3603457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3603457 prefixEnd_3603457 := by exact prefixLift 3603457
  have htrace : WordTrace (prefixWord ++ tailWord_3603457) baseStart_3603457 baseEnd_3603457 := by
    simpa [prefixWord, tailWord_3603457, baseEnd_3603457] using wordTrace_append hprefix tailTrace_3603457
  have hstable : (prefixWord ++ tailWord_3603457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3603457).length < 2 ^ (prefixWord ++ tailWord_3603457).sum := by decide
  have hdescent : baseEnd_3603457 < baseStart_3603457 := by decide
  rcases family_descends (prefixWord ++ tailWord_3603457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3603483 : List Nat := [1, 1, 1, 1, 1, 1, 3, 2, 7, 5]
def baseStart_3603483 : Nat := 118140960795 + 3603483 * 2 ^ 59
def prefixEnd_3603483 : Nat := 4983230072969 + 3 ^ 40 * 3603483 * 2
def baseEnd_3603483 : Nat := 616772936435210029963463

theorem tailTrace_3603483 : CollatzResearch.WordTrace tailWord_3603483 prefixEnd_3603483 616772936435210029963463 := by
  unfold tailWord_3603483
  simp only [CollatzResearch.WordTrace]
  refine ⟨131429822404203991744951103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87619881602802661163300735 131429822404203991744951103)
  ·
    refine ⟨197144733606305987617426655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131429822404203991744951103 197144733606305987617426655)
    ·
      refine ⟨295717100409458981426139983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197144733606305987617426655 295717100409458981426139983)
      ·
        refine ⟨443575650614188472139209975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295717100409458981426139983 443575650614188472139209975)
        ·
          refine ⟨665363475921282708208814963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 443575650614188472139209975 665363475921282708208814963)
          ·
            refine ⟨998045213881924062313222445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 665363475921282708208814963 998045213881924062313222445)
            ·
              refine ⟨374266955205721523367458417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 998045213881924062313222445 374266955205721523367458417)
              ·
                refine ⟨280700216404291142525593813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 374266955205721523367458417 280700216404291142525593813)
                ·
                  refine ⟨6578911321975573652943605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 280700216404291142525593813 6578911321975573652943605)
                  ·
                    refine ⟨616772936435210029963463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6578911321975573652943605 616772936435210029963463)
                    ·
                      rfl

theorem cell23_3603483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 7, 5].length) (baseStart_3603483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3603483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3603483 prefixEnd_3603483 := by exact prefixLift 3603483
  have htrace : WordTrace (prefixWord ++ tailWord_3603483) baseStart_3603483 baseEnd_3603483 := by
    simpa [prefixWord, tailWord_3603483, baseEnd_3603483] using wordTrace_append hprefix tailTrace_3603483
  have hstable : (prefixWord ++ tailWord_3603483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3603483).length < 2 ^ (prefixWord ++ tailWord_3603483).sum := by decide
  have hdescent : baseEnd_3603483 < baseStart_3603483 := by decide
  rcases family_descends (prefixWord ++ tailWord_3603483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3603500 : List Nat := [2, 2, 1, 1, 1, 2, 3, 5, 1, 5]
def baseStart_3603500 : Nat := 118140960795 + 3603500 * 2 ^ 59
def prefixEnd_3603500 : Nat := 4983230072969 + 3 ^ 40 * 3603500 * 2
def baseEnd_3603500 : Nat := 616775846158918841125937

theorem tailTrace_3603500 : CollatzResearch.WordTrace tailWord_3603500 prefixEnd_3603500 616775846158918841125937 := by
  unfold tailWord_3603500
  simp only [CollatzResearch.WordTrace]
  refine ⟨65715221222571201824159977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87620294963428269098879969 65715221222571201824159977)
  ·
    refine ⟨49286415916928401368119983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65715221222571201824159977 49286415916928401368119983)
    ·
      refine ⟨73929623875392602052179975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49286415916928401368119983 73929623875392602052179975)
      ·
        refine ⟨110894435813088903078269963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73929623875392602052179975 110894435813088903078269963)
        ·
          refine ⟨166341653719633354617404945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110894435813088903078269963 166341653719633354617404945)
          ·
            refine ⟨124756240289725015963053709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166341653719633354617404945 124756240289725015963053709)
            ·
              refine ⟨46783590108646880986145141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124756240289725015963053709 46783590108646880986145141)
              ·
                refine ⟨4385961572685645092451107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46783590108646880986145141 4385961572685645092451107)
                ·
                  refine ⟨6578942359028467638676661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4385961572685645092451107 6578942359028467638676661)
                  ·
                    refine ⟨616775846158918841125937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6578942359028467638676661 616775846158918841125937)
                    ·
                      rfl

theorem cell23_3603500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 5].length) (baseStart_3603500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3603500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3603500 prefixEnd_3603500 := by exact prefixLift 3603500
  have htrace : WordTrace (prefixWord ++ tailWord_3603500) baseStart_3603500 baseEnd_3603500 := by
    simpa [prefixWord, tailWord_3603500, baseEnd_3603500] using wordTrace_append hprefix tailTrace_3603500
  have hstable : (prefixWord ++ tailWord_3603500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3603500).length < 2 ^ (prefixWord ++ tailWord_3603500).sum := by decide
  have hdescent : baseEnd_3603500 < baseStart_3603500 := by decide
  rcases family_descends (prefixWord ++ tailWord_3603500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3603503 : List Nat := [1, 1, 2, 1, 2, 1, 1, 2, 1, 7, 4]
def baseStart_3603503 : Nat := 118140960795 + 3603503 * 2 ^ 59
def prefixEnd_3603503 : Nat := 4983230072969 + 3 ^ 40 * 3603503 * 2
def baseEnd_3603503 : Nat := 1850329078918720011640297

theorem tailTrace_3603503 : CollatzResearch.WordTrace tailWord_3603503 prefixEnd_3603503 1850329078918720011640297 := by
  unfold tailWord_3603503
  simp only [CollatzResearch.WordTrace]
  refine ⟨131430551864131535160679163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87620367909421023440452775 131430551864131535160679163)
  ·
    refine ⟨197145827796197302741018745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131430551864131535160679163 197145827796197302741018745)
    ·
      refine ⟨147859370847147977055764059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197145827796197302741018745 147859370847147977055764059)
      ·
        refine ⟨221789056270721965583646089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147859370847147977055764059 221789056270721965583646089)
        ·
          refine ⟨166341792203041474187734567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 221789056270721965583646089 166341792203041474187734567)
          ·
            refine ⟨249512688304562211281601851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166341792203041474187734567 249512688304562211281601851)
            ·
              refine ⟨374269032456843316922402777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249512688304562211281601851 374269032456843316922402777)
              ·
                refine ⟨280701774342632487691802083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 374269032456843316922402777 280701774342632487691802083)
                ·
                  refine ⟨421052661513948731537703125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 280701774342632487691802083 421052661513948731537703125)
                  ·
                    refine ⟨9868421754233173395414917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 421052661513948731537703125 9868421754233173395414917)
                    ·
                      refine ⟨1850329078918720011640297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9868421754233173395414917 1850329078918720011640297)
                      ·
                        rfl

theorem cell23_3603503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 7, 4].length) (baseStart_3603503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3603503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3603503 prefixEnd_3603503 := by exact prefixLift 3603503
  have htrace : WordTrace (prefixWord ++ tailWord_3603503) baseStart_3603503 baseEnd_3603503 := by
    simpa [prefixWord, tailWord_3603503, baseEnd_3603503] using wordTrace_append hprefix tailTrace_3603503
  have hstable : (prefixWord ++ tailWord_3603503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3603503).length < 2 ^ (prefixWord ++ tailWord_3603503).sum := by decide
  have hdescent : baseEnd_3603503 < baseStart_3603503 := by decide
  rcases family_descends (prefixWord ++ tailWord_3603503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3603508 : List Nat := [2, 5, 1, 2, 1, 2, 3, 2, 1, 4]
def baseStart_3603508 : Nat := 118140960795 + 3603508 * 2 ^ 59
def prefixEnd_3603508 : Nat := 4983230072969 + 3 ^ 40 * 3603508 * 2
def baseEnd_3603508 : Nat := 616777215440664164025925

theorem tailTrace_3603508 : CollatzResearch.WordTrace tailWord_3603508 prefixEnd_3603508 616777215440664164025925 := by
  unfold tailWord_3603508
  simp only [CollatzResearch.WordTrace]
  refine ⟨65715367114556710507305589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87620489486075614009740785 65715367114556710507305589)
  ·
    refine ⟨6160815666989691610059899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 65715367114556710507305589 6160815666989691610059899)
    ·
      refine ⟨9241223500484537415089849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6160815666989691610059899 9241223500484537415089849)
      ·
        refine ⟨6930917625363403061317387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9241223500484537415089849 6930917625363403061317387)
        ·
          refine ⟨10396376438045104591976081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6930917625363403061317387 10396376438045104591976081)
          ·
            refine ⟨7797282328533828443982061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10396376438045104591976081 7797282328533828443982061)
            ·
              refine ⟨2923980873200185666493273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7797282328533828443982061 2923980873200185666493273)
              ·
                refine ⟨2192985654900139249869955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2923980873200185666493273 2192985654900139249869955)
                ·
                  refine ⟨3289478482350208874804933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2192985654900139249869955 3289478482350208874804933)
                  ·
                    refine ⟨616777215440664164025925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3289478482350208874804933 616777215440664164025925)
                    ·
                      rfl

theorem cell23_3603508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 3, 2, 1, 4].length) (baseStart_3603508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3603508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3603508 prefixEnd_3603508 := by exact prefixLift 3603508
  have htrace : WordTrace (prefixWord ++ tailWord_3603508) baseStart_3603508 baseEnd_3603508 := by
    simpa [prefixWord, tailWord_3603508, baseEnd_3603508] using wordTrace_append hprefix tailTrace_3603508
  have hstable : (prefixWord ++ tailWord_3603508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3603508).length < 2 ^ (prefixWord ++ tailWord_3603508).sum := by decide
  have hdescent : baseEnd_3603508 < baseStart_3603508 := by decide
  rcases family_descends (prefixWord ++ tailWord_3603508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3603514 : List Nat := [3, 1, 1, 1, 3, 1, 2, 6, 1, 1, 3]
def baseStart_3603514 : Nat := 118140960795 + 3603514 * 2 ^ 59
def prefixEnd_3603514 : Nat := 4983230072969 + 3 ^ 40 * 3603514 * 2
def baseEnd_3603514 : Nat := 1850334727205919468602747

theorem tailTrace_3603514 : CollatzResearch.WordTrace tailWord_3603514 prefixEnd_3603514 1850334727205919468602747 := by
  unfold tailWord_3603514
  simp only [CollatzResearch.WordTrace]
  refine ⟨32857738266772921009832399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87620635378061122692886397 32857738266772921009832399)
  ·
    refine ⟨49286607400159381514748599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32857738266772921009832399 49286607400159381514748599)
    ·
      refine ⟨73929911100239072272122899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49286607400159381514748599 73929911100239072272122899)
      ·
        refine ⟨110894866650358608408184349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73929911100239072272122899 110894866650358608408184349)
        ·
          refine ⟨41585574993884478153069131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110894866650358608408184349 41585574993884478153069131)
          ·
            refine ⟨62378362490826717229603697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41585574993884478153069131 62378362490826717229603697)
            ·
              refine ⟨46783771868120037922202773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62378362490826717229603697 46783771868120037922202773)
              ·
                refine ⟨2192989306318126777603255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 46783771868120037922202773 2192989306318126777603255)
                ·
                  refine ⟨3289483959477190166404883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2192989306318126777603255 3289483959477190166404883)
                  ·
                    refine ⟨4934225939215785249607325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3289483959477190166404883 4934225939215785249607325)
                    ·
                      refine ⟨1850334727205919468602747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4934225939215785249607325 1850334727205919468602747)
                      ·
                        rfl

theorem cell23_3603514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 6, 1, 1, 3].length) (baseStart_3603514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3603514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3603514 prefixEnd_3603514 := by exact prefixLift 3603514
  have htrace : WordTrace (prefixWord ++ tailWord_3603514) baseStart_3603514 baseEnd_3603514 := by
    simpa [prefixWord, tailWord_3603514, baseEnd_3603514] using wordTrace_append hprefix tailTrace_3603514
  have hstable : (prefixWord ++ tailWord_3603514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3603514).length < 2 ^ (prefixWord ++ tailWord_3603514).sum := by decide
  have hdescent : baseEnd_3603514 < baseStart_3603514 := by decide
  rcases family_descends (prefixWord ++ tailWord_3603514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3603520 : List Nat := [2, 1, 1, 2, 2, 3, 2, 2, 3, 1, 4]
def baseStart_3603520 : Nat := 118140960795 + 3603520 * 2 ^ 59
def prefixEnd_3603520 : Nat := 4983230072969 + 3 ^ 40 * 3603520 * 2
def baseEnd_3603520 : Nat := 1850337808089846445127719

theorem tailTrace_3603520 : CollatzResearch.WordTrace tailWord_3603520 prefixEnd_3603520 1850337808089846445127719 := by
  unfold tailWord_3603520
  simp only [CollatzResearch.WordTrace]
  refine ⟨65715585952534973532024007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87620781270046631376032009 65715585952534973532024007)
  ·
    refine ⟨98573378928802460298036011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65715585952534973532024007 98573378928802460298036011)
    ·
      refine ⟨147860068393203690447054017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98573378928802460298036011 147860068393203690447054017)
      ·
        refine ⟨110895051294902767835290513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147860068393203690447054017 110895051294902767835290513)
        ·
          refine ⟨83171288471177075876467885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110895051294902767835290513 83171288471177075876467885)
          ·
            refine ⟨31189233176691403453675457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83171288471177075876467885 31189233176691403453675457)
            ·
              refine ⟨23391924882518552590256593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31189233176691403453675457 23391924882518552590256593)
              ·
                refine ⟨17543943661888914442692445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23391924882518552590256593 17543943661888914442692445)
                ·
                  refine ⟨6578978873208342916009667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17543943661888914442692445 6578978873208342916009667)
                  ·
                    refine ⟨9868468309812514374014501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6578978873208342916009667 9868468309812514374014501)
                    ·
                      refine ⟨1850337808089846445127719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9868468309812514374014501 1850337808089846445127719)
                      ·
                        rfl

theorem cell23_3603520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 2, 3, 1, 4].length) (baseStart_3603520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3603520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3603520 prefixEnd_3603520 := by exact prefixLift 3603520
  have htrace : WordTrace (prefixWord ++ tailWord_3603520) baseStart_3603520 baseEnd_3603520 := by
    simpa [prefixWord, tailWord_3603520, baseEnd_3603520] using wordTrace_append hprefix tailTrace_3603520
  have hstable : (prefixWord ++ tailWord_3603520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3603520).length < 2 ^ (prefixWord ++ tailWord_3603520).sum := by decide
  have hdescent : baseEnd_3603520 < baseStart_3603520 := by decide
  rcases family_descends (prefixWord ++ tailWord_3603520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3603521 : List Nat := [1, 2, 5, 1, 4, 1, 2, 1, 6]
def baseStart_3603521 : Nat := 118140960795 + 3603521 * 2 ^ 59
def prefixEnd_3603521 : Nat := 4983230072969 + 3 ^ 40 * 3603521 * 2
def baseEnd_3603521 : Nat := 205593146841166771246135

theorem tailTrace_3603521 : CollatzResearch.WordTrace tailWord_3603521 prefixEnd_3603521 205593146841166771246135 := by
  unfold tailWord_3603521
  simp only [CollatzResearch.WordTrace]
  refine ⟨131431208378066324234834417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87620805585377549489889611 131431208378066324234834417)
  ·
    refine ⟨98573406283549743176125813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131431208378066324234834417 98573406283549743176125813)
    ·
      refine ⟨9241256839082788422761795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 98573406283549743176125813 9241256839082788422761795)
      ·
        refine ⟨13861885258624182634142693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9241256839082788422761795 13861885258624182634142693)
        ·
          refine ⟨2599103485992034243901755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13861885258624182634142693 2599103485992034243901755)
          ·
            refine ⟨3898655228988051365852633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2599103485992034243901755 3898655228988051365852633)
            ·
              refine ⟨2923991421741038524389475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3898655228988051365852633 2923991421741038524389475)
              ·
                refine ⟨4385987132611557786584213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2923991421741038524389475 4385987132611557786584213)
                ·
                  refine ⟨205593146841166771246135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4385987132611557786584213 205593146841166771246135)
                  ·
                    rfl

theorem cell23_3603521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 2, 1, 6].length) (baseStart_3603521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3603521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3603521 prefixEnd_3603521 := by exact prefixLift 3603521
  have htrace : WordTrace (prefixWord ++ tailWord_3603521) baseStart_3603521 baseEnd_3603521 := by
    simpa [prefixWord, tailWord_3603521, baseEnd_3603521] using wordTrace_append hprefix tailTrace_3603521
  have hstable : (prefixWord ++ tailWord_3603521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3603521).length < 2 ^ (prefixWord ++ tailWord_3603521).sum := by decide
  have hdescent : baseEnd_3603521 < baseStart_3603521 := by decide
  rcases family_descends (prefixWord ++ tailWord_3603521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3603537 : List Nat := [1, 2, 2, 1, 3, 1, 5, 2, 1, 1, 4]
def baseStart_3603537 : Nat := 118140960795 + 3603537 * 2 ^ 59
def prefixEnd_3603537 : Nat := 4983230072969 + 3 ^ 40 * 3603537 * 2
def baseEnd_3603537 : Nat := 1850346537260972878615141

theorem tailTrace_3603537 : CollatzResearch.WordTrace tailWord_3603537 prefixEnd_3603537 1850346537260972878615141 := by
  unfold tailWord_3603537
  simp only [CollatzResearch.WordTrace]
  refine ⟨131431791946008358967416865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87621194630672239311611243 131431791946008358967416865)
  ·
    refine ⟨98573843959506269225562649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131431791946008358967416865 98573843959506269225562649)
    ·
      refine ⟨73930382969629701919171987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98573843959506269225562649 73930382969629701919171987)
      ·
        refine ⟨110895574454444552878757981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73930382969629701919171987 110895574454444552878757981)
        ·
          refine ⟨41585840420416707329534243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110895574454444552878757981 41585840420416707329534243)
          ·
            refine ⟨62378760630625060994301365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41585840420416707329534243 62378760630625060994301365)
            ·
              refine ⟨5848008809121099468215753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62378760630625060994301365 5848008809121099468215753)
              ·
                refine ⟨4386006606840824601161815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5848008809121099468215753 4386006606840824601161815)
                ·
                  refine ⟨6579009910261236901742723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4386006606840824601161815 6579009910261236901742723)
                  ·
                    refine ⟨9868514865391855352614085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6579009910261236901742723 9868514865391855352614085)
                    ·
                      refine ⟨1850346537260972878615141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9868514865391855352614085 1850346537260972878615141)
                      ·
                        rfl

theorem cell23_3603537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5, 2, 1, 1, 4].length) (baseStart_3603537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3603537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3603537 prefixEnd_3603537 := by exact prefixLift 3603537
  have htrace : WordTrace (prefixWord ++ tailWord_3603537) baseStart_3603537 baseEnd_3603537 := by
    simpa [prefixWord, tailWord_3603537, baseEnd_3603537] using wordTrace_append hprefix tailTrace_3603537
  have hstable : (prefixWord ++ tailWord_3603537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3603537).length < 2 ^ (prefixWord ++ tailWord_3603537).sum := by decide
  have hdescent : baseEnd_3603537 < baseStart_3603537 := by decide
  rcases family_descends (prefixWord ++ tailWord_3603537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3603540 : List Nat := [2, 4, 1, 1, 1, 1, 2, 2, 3, 1, 5]
def baseStart_3603540 : Nat := 118140960795 + 3603540 * 2 ^ 59
def prefixEnd_3603540 : Nat := 4983230072969 + 3 ^ 40 * 3603540 * 2
def baseEnd_3603540 : Nat := 1850348077702936366877627

theorem tailTrace_3603540 : CollatzResearch.WordTrace tailWord_3603540 prefixEnd_3603540 1850348077702936366877627 := by
  unfold tailWord_3603540
  simp only [CollatzResearch.WordTrace]
  refine ⟨65715950682498745239888037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87621267576664993653184049 65715950682498745239888037)
  ·
    refine ⟨12321740752968514732479007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65715950682498745239888037 12321740752968514732479007)
    ·
      refine ⟨18482611129452772098718511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12321740752968514732479007 18482611129452772098718511)
      ·
        refine ⟨27723916694179158148077767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18482611129452772098718511 27723916694179158148077767)
        ·
          refine ⟨41585875041268737222116651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27723916694179158148077767 41585875041268737222116651)
          ·
            refine ⟨62378812561903105833174977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41585875041268737222116651 62378812561903105833174977)
            ·
              refine ⟨46784109421427329374881233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62378812561903105833174977 46784109421427329374881233)
              ·
                refine ⟨35088082066070497031160925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46784109421427329374881233 35088082066070497031160925)
                ·
                  refine ⟨13158030774776436386685347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35088082066070497031160925 13158030774776436386685347)
                  ·
                    refine ⟨19737046162164654580028021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13158030774776436386685347 19737046162164654580028021)
                    ·
                      refine ⟨1850348077702936366877627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19737046162164654580028021 1850348077702936366877627)
                      ·
                        rfl

theorem cell23_3603540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 2, 3, 1, 5].length) (baseStart_3603540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3603540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3603540 prefixEnd_3603540 := by exact prefixLift 3603540
  have htrace : WordTrace (prefixWord ++ tailWord_3603540) baseStart_3603540 baseEnd_3603540 := by
    simpa [prefixWord, tailWord_3603540, baseEnd_3603540] using wordTrace_append hprefix tailTrace_3603540
  have hstable : (prefixWord ++ tailWord_3603540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3603540).length < 2 ^ (prefixWord ++ tailWord_3603540).sum := by decide
  have hdescent : baseEnd_3603540 < baseStart_3603540 := by decide
  rcases family_descends (prefixWord ++ tailWord_3603540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3603560 : List Nat := [2, 1, 4, 4, 12]
def baseStart_3603560 : Nat := 118140960795 + 3603560 * 2 ^ 59
def prefixEnd_3603560 : Nat := 4983230072969 + 3 ^ 40 * 3603560 * 2
def baseEnd_3603560 : Nat := 2538214468197566925415

theorem tailTrace_3603560 : CollatzResearch.WordTrace tailWord_3603560 prefixEnd_3603560 2538214468197566925415 := by
  unfold tailWord_3603560
  simp only [CollatzResearch.WordTrace]
  refine ⟨65716315412462516947752067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87621753883283355930336089 65716315412462516947752067)
  ·
    refine ⟨98574473118693775421628101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65716315412462516947752067 98574473118693775421628101)
    ·
      refine ⟨18482713709755082891555269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98574473118693775421628101 18482713709755082891555269)
      ·
        refine ⟨3465508820579078042166613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18482713709755082891555269 3465508820579078042166613)
        ·
          refine ⟨2538214468197566925415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 3465508820579078042166613 2538214468197566925415)
          ·
            rfl

theorem cell23_3603560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 12].length) (baseStart_3603560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3603560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3603560 prefixEnd_3603560 := by exact prefixLift 3603560
  have htrace : WordTrace (prefixWord ++ tailWord_3603560) baseStart_3603560 baseEnd_3603560 := by
    simpa [prefixWord, tailWord_3603560, baseEnd_3603560] using wordTrace_append hprefix tailTrace_3603560
  have hstable : (prefixWord ++ tailWord_3603560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3603560).length < 2 ^ (prefixWord ++ tailWord_3603560).sum := by decide
  have hdescent : baseEnd_3603560 < baseStart_3603560 := by decide
  rcases family_descends (prefixWord ++ tailWord_3603560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3603563 : List Nat := [1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 8]
def baseStart_3603563 : Nat := 118140960795 + 3603563 * 2 ^ 59
def prefixEnd_3603563 : Nat := 4983230072969 + 3 ^ 40 * 3603563 * 2
def baseEnd_3603563 : Nat := 1850359887757989776890021

theorem tailTrace_3603563 : CollatzResearch.WordTrace tailWord_3603563 prefixEnd_3603563 1850359887757989776890021 := by
  unfold tailWord_3603563
  simp only [CollatzResearch.WordTrace]
  refine ⟨131432740243914165407863343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87621826829276110271908895 131432740243914165407863343)
  ·
    refine ⟨197149110365871248111795015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131432740243914165407863343 197149110365871248111795015)
    ·
      refine ⟨295723665548806872167692523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197149110365871248111795015 295723665548806872167692523)
      ·
        refine ⟨443585498323210308251538785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295723665548806872167692523 443585498323210308251538785)
        ·
          refine ⟨332689123742407731188654089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 443585498323210308251538785 332689123742407731188654089)
          ·
            refine ⟨249516842806805798391490567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 332689123742407731188654089 249516842806805798391490567)
            ·
              refine ⟨374275264210208697587235851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249516842806805798391490567 374275264210208697587235851)
              ·
                refine ⟨561412896315313046380853777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 374275264210208697587235851 561412896315313046380853777)
                ·
                  refine ⟨421059672236484784785640333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 561412896315313046380853777 421059672236484784785640333)
                  ·
                    refine ⟨157897377088681794294615125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 421059672236484784785640333 157897377088681794294615125)
                    ·
                      refine ⟨1850359887757989776890021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 157897377088681794294615125 1850359887757989776890021)
                      ·
                        rfl

theorem cell23_3603563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 8].length) (baseStart_3603563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3603563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3603563 prefixEnd_3603563 := by exact prefixLift 3603563
  have htrace : WordTrace (prefixWord ++ tailWord_3603563) baseStart_3603563 baseEnd_3603563 := by
    simpa [prefixWord, tailWord_3603563, baseEnd_3603563] using wordTrace_append hprefix tailTrace_3603563
  have hstable : (prefixWord ++ tailWord_3603563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3603563).length < 2 ^ (prefixWord ++ tailWord_3603563).sum := by decide
  have hdescent : baseEnd_3603563 < baseStart_3603563 := by decide
  rcases family_descends (prefixWord ++ tailWord_3603563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3603577 : List Nat := [1, 2, 1, 3, 5, 2, 1, 8]
def baseStart_3603577 : Nat := 118140960795 + 3603577 * 2 ^ 59
def prefixEnd_3603577 : Nat := 4983230072969 + 3 ^ 40 * 3603577 * 2
def baseEnd_3603577 : Nat := 68532113943968619337591

theorem tailTrace_3603577 : CollatzResearch.WordTrace tailWord_3603577 prefixEnd_3603577 68532113943968619337591 := by
  unfold tailWord_3603577
  simp only [CollatzResearch.WordTrace]
  refine ⟨131433250865863445798872985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87622167243908963865915323 131433250865863445798872985)
  ·
    refine ⟨98574938149397584349154739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131433250865863445798872985 98574938149397584349154739)
    ·
      refine ⟨147862407224096376523732109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98574938149397584349154739 147862407224096376523732109)
      ·
        refine ⟨55448402709036141196399541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147862407224096376523732109 55448402709036141196399541)
        ·
          refine ⟨5198287753972138237162457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 55448402709036141196399541 5198287753972138237162457)
          ·
            refine ⟨3898715815479103677871843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5198287753972138237162457 3898715815479103677871843)
            ·
              refine ⟨5848073723218655516807765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3898715815479103677871843 5848073723218655516807765)
              ·
                refine ⟨68532113943968619337591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5848073723218655516807765 68532113943968619337591)
                ·
                  rfl

theorem cell23_3603577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 1, 8].length) (baseStart_3603577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3603577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3603577 prefixEnd_3603577 := by exact prefixLift 3603577
  have htrace : WordTrace (prefixWord ++ tailWord_3603577) baseStart_3603577 baseEnd_3603577 := by
    simpa [prefixWord, tailWord_3603577, baseEnd_3603577] using wordTrace_append hprefix tailTrace_3603577
  have hstable : (prefixWord ++ tailWord_3603577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3603577).length < 2 ^ (prefixWord ++ tailWord_3603577).sum := by decide
  have hdescent : baseEnd_3603577 < baseStart_3603577 := by decide
  rcases family_descends (prefixWord ++ tailWord_3603577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3603587 : List Nat := [1, 1, 1, 3, 3, 2, 4, 1, 1, 3, 3]
def baseStart_3603587 : Nat := 118140960795 + 3603587 * 2 ^ 59
def prefixEnd_3603587 : Nat := 4983230072969 + 3 ^ 40 * 3603587 * 2
def baseEnd_3603587 : Nat := 1850372211293697682989911

theorem tailTrace_3603587 : CollatzResearch.WordTrace tailWord_3603587 prefixEnd_3603587 1850372211293697682989911 := by
  unfold tailWord_3603587
  simp only [CollatzResearch.WordTrace]
  refine ⟨131433615595827217506737015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87622410397218145004491343 131433615595827217506737015)
  ·
    refine ⟨197150423393740826260105523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131433615595827217506737015 197150423393740826260105523)
    ·
      refine ⟨295725635090611239390158285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197150423393740826260105523 295725635090611239390158285)
      ·
        refine ⟨110897113158979214771309357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 295725635090611239390158285 110897113158979214771309357)
        ·
          refine ⟨41586417434617205539241009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110897113158979214771309357 41586417434617205539241009)
          ·
            refine ⟨31189813075962904154430757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41586417434617205539241009 31189813075962904154430757)
            ·
              refine ⟨5848089951743044528955767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31189813075962904154430757 5848089951743044528955767)
              ·
                refine ⟨8772134927614566793433651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5848089951743044528955767 8772134927614566793433651)
                ·
                  refine ⟨13158202391421850190150477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8772134927614566793433651 13158202391421850190150477)
                  ·
                    refine ⟨4934325896783193821306429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13158202391421850190150477 4934325896783193821306429)
                    ·
                      refine ⟨1850372211293697682989911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4934325896783193821306429 1850372211293697682989911)
                      ·
                        rfl

theorem cell23_3603587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4, 1, 1, 3, 3].length) (baseStart_3603587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3603587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3603587 prefixEnd_3603587 := by exact prefixLift 3603587
  have htrace : WordTrace (prefixWord ++ tailWord_3603587) baseStart_3603587 baseEnd_3603587 := by
    simpa [prefixWord, tailWord_3603587, baseEnd_3603587] using wordTrace_append hprefix tailTrace_3603587
  have hstable : (prefixWord ++ tailWord_3603587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3603587).length < 2 ^ (prefixWord ++ tailWord_3603587).sum := by decide
  have hdescent : baseEnd_3603587 < baseStart_3603587 := by decide
  rcases family_descends (prefixWord ++ tailWord_3603587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3603621 : List Nat := [1, 3, 1, 2, 1, 6, 1, 2, 2, 1, 3]
def baseStart_3603621 : Nat := 118140960795 + 3603621 * 2 ^ 59
def prefixEnd_3603621 : Nat := 4983230072969 + 3 ^ 40 * 3603621 * 2
def baseEnd_3603621 : Nat := 1850389669635950549964755

theorem tailTrace_3603621 : CollatzResearch.WordTrace tailWord_3603621 prefixEnd_3603621 1850389669635950549964755 := by
  unfold tailWord_3603621
  simp only [CollatzResearch.WordTrace]
  refine ⟨131434855677704041313474717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87623237118469360875649811 131434855677704041313474717)
  ·
    refine ⟨49288070879139015492553019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131434855677704041313474717 49288070879139015492553019)
    ·
      refine ⟨73932106318708523238829529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49288070879139015492553019 73932106318708523238829529)
      ·
        refine ⟨55449079739031392429122147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73932106318708523238829529 55449079739031392429122147)
        ·
          refine ⟨83173619608547088643683221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55449079739031392429122147 83173619608547088643683221)
          ·
            refine ⟨3898763419150644780172651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 83173619608547088643683221 3898763419150644780172651)
            ·
              refine ⟨5848145128725967170258977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3898763419150644780172651 5848145128725967170258977)
              ·
                refine ⟨4386108846544475377694233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5848145128725967170258977 4386108846544475377694233)
                ·
                  refine ⟨3289581634908356533270675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4386108846544475377694233 3289581634908356533270675)
                  ·
                    refine ⟨4934372452362534799906013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3289581634908356533270675 4934372452362534799906013)
                    ·
                      refine ⟨1850389669635950549964755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4934372452362534799906013 1850389669635950549964755)
                      ·
                        rfl

theorem cell23_3603621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 1, 2, 2, 1, 3].length) (baseStart_3603621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3603621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3603621 prefixEnd_3603621 := by exact prefixLift 3603621
  have htrace : WordTrace (prefixWord ++ tailWord_3603621) baseStart_3603621 baseEnd_3603621 := by
    simpa [prefixWord, tailWord_3603621, baseEnd_3603621] using wordTrace_append hprefix tailTrace_3603621
  have hstable : (prefixWord ++ tailWord_3603621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3603621).length < 2 ^ (prefixWord ++ tailWord_3603621).sum := by decide
  have hdescent : baseEnd_3603621 < baseStart_3603621 := by decide
  rcases family_descends (prefixWord ++ tailWord_3603621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3603640 : List Nat := [2, 1, 2, 1, 2, 1, 2, 3, 1, 4, 4]
def baseStart_3603640 : Nat := 118140960795 + 3603640 * 2 ^ 59
def prefixEnd_3603640 : Nat := 4983230072969 + 3 ^ 40 * 3603640 * 2
def baseEnd_3603640 : Nat := 1850399425768385975627167

theorem tailTrace_3603640 : CollatzResearch.WordTrace tailWord_3603640 prefixEnd_3603640 1850399425768385975627167 := by
  unfold tailWord_3603640
  simp only [CollatzResearch.WordTrace]
  refine ⟨65717774332317603779208187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87623699109756805038944249 65717774332317603779208187)
  ·
    refine ⟨98576661498476405668812281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65717774332317603779208187 98576661498476405668812281)
    ·
      refine ⟨73932496123857304251609211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98576661498476405668812281 73932496123857304251609211)
      ·
        refine ⟨110898744185785956377413817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73932496123857304251609211 110898744185785956377413817)
        ·
          refine ⟨83174058139339467283060363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110898744185785956377413817 83174058139339467283060363)
          ·
            refine ⟨124761087209009200924590545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83174058139339467283060363 124761087209009200924590545)
            ·
              refine ⟨93570815406756900693442909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124761087209009200924590545 93570815406756900693442909)
              ·
                refine ⟨35089055777533837760041091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93570815406756900693442909 35089055777533837760041091)
                ·
                  refine ⟨52633583666300756640061637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35089055777533837760041091 52633583666300756640061637)
                  ·
                    refine ⟨9868796937431391870011557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52633583666300756640061637 9868796937431391870011557)
                    ·
                      refine ⟨1850399425768385975627167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9868796937431391870011557 1850399425768385975627167)
                      ·
                        rfl

theorem cell23_3603640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 3, 1, 4, 4].length) (baseStart_3603640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3603640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3603640 prefixEnd_3603640 := by exact prefixLift 3603640
  have htrace : WordTrace (prefixWord ++ tailWord_3603640) baseStart_3603640 baseEnd_3603640 := by
    simpa [prefixWord, tailWord_3603640, baseEnd_3603640] using wordTrace_append hprefix tailTrace_3603640
  have hstable : (prefixWord ++ tailWord_3603640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3603640).length < 2 ^ (prefixWord ++ tailWord_3603640).sum := by decide
  have hdescent : baseEnd_3603640 < baseStart_3603640 := by decide
  rcases family_descends (prefixWord ++ tailWord_3603640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3603695 : List Nat := [1, 1, 2, 1, 7, 2, 2, 1, 2, 2, 2]
def baseStart_3603695 : Nat := 118140960795 + 3603695 * 2 ^ 59
def prefixEnd_3603695 : Nat := 4983230072969 + 3 ^ 40 * 3603695 * 2
def baseEnd_3603695 : Nat := 1850427667204383260439415

theorem tailTrace_3603695 : CollatzResearch.WordTrace tailWord_3603695 prefixEnd_3603695 1850427667204383260439415 := by
  unfold tailWord_3603695
  simp only [CollatzResearch.WordTrace]
  refine ⟨131437554679435951951668539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87625036452957301301112359 131437554679435951951668539)
  ·
    refine ⟨197156332019153927927502809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131437554679435951951668539 197156332019153927927502809)
    ·
      refine ⟨147867249014365445945627107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197156332019153927927502809 147867249014365445945627107)
      ·
        refine ⟨221800873521548168918440661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147867249014365445945627107 221800873521548168918440661)
        ·
          refine ⟨5198457973161285209025953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 221800873521548168918440661 5198457973161285209025953)
          ·
            refine ⟨3898843479870963906769465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5198457973161285209025953 3898843479870963906769465)
            ·
              refine ⟨2924132609903222930077099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3898843479870963906769465 2924132609903222930077099)
              ·
                refine ⟨4386198914854834395115649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2924132609903222930077099 4386198914854834395115649)
                ·
                  refine ⟨3289649186141125796336737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4386198914854834395115649 3289649186141125796336737)
                  ·
                    refine ⟨2467236889605844347252553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3289649186141125796336737 2467236889605844347252553)
                    ·
                      refine ⟨1850427667204383260439415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2467236889605844347252553 1850427667204383260439415)
                      ·
                        rfl

theorem cell23_3603695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 2, 1, 2, 2, 2].length) (baseStart_3603695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3603695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3603695 prefixEnd_3603695 := by exact prefixLift 3603695
  have htrace : WordTrace (prefixWord ++ tailWord_3603695) baseStart_3603695 baseEnd_3603695 := by
    simpa [prefixWord, tailWord_3603695, baseEnd_3603695] using wordTrace_append hprefix tailTrace_3603695
  have hstable : (prefixWord ++ tailWord_3603695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3603695).length < 2 ^ (prefixWord ++ tailWord_3603695).sum := by decide
  have hdescent : baseEnd_3603695 < baseStart_3603695 := by decide
  rcases family_descends (prefixWord ++ tailWord_3603695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3603784 : List Nat := [2, 1, 3, 1, 1, 2, 1, 1, 7, 1, 3]
def baseStart_3603784 : Nat := 118140960795 + 3603784 * 2 ^ 59
def prefixEnd_3603784 : Nat := 4983230072969 + 3 ^ 40 * 3603784 * 2
def baseEnd_3603784 : Nat := 1850473366982633412226505

theorem tailTrace_3603784 : CollatzResearch.WordTrace tailWord_3603784 prefixEnd_3603784 1850473366982633412226505 := by
  unfold tailWord_3603784
  simp only [CollatzResearch.WordTrace]
  refine ⟨65720400388056760075829203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87627200517409013434438937 65720400388056760075829203)
  ·
    refine ⟨98580600582085140113743805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65720400388056760075829203 98580600582085140113743805)
    ·
      refine ⟨36967725218281927542653927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98580600582085140113743805 36967725218281927542653927)
      ·
        refine ⟨55451587827422891313980891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36967725218281927542653927 55451587827422891313980891)
        ·
          refine ⟨83177381741134336970971337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55451587827422891313980891 83177381741134336970971337)
          ·
            refine ⟨62383036305850752728228503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83177381741134336970971337 62383036305850752728228503)
            ·
              refine ⟨93574554458776129092342755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62383036305850752728228503 93574554458776129092342755)
              ·
                refine ⟨140361831688164193638514133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93574554458776129092342755 140361831688164193638514133)
                ·
                  refine ⟨3289730430191348288402675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 140361831688164193638514133 3289730430191348288402675)
                  ·
                    refine ⟨4934595645287022432604013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3289730430191348288402675 4934595645287022432604013)
                    ·
                      refine ⟨1850473366982633412226505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4934595645287022432604013 1850473366982633412226505)
                      ·
                        rfl

theorem cell23_3603784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 7, 1, 3].length) (baseStart_3603784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3603784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3603784 prefixEnd_3603784 := by exact prefixLift 3603784
  have htrace : WordTrace (prefixWord ++ tailWord_3603784) baseStart_3603784 baseEnd_3603784 := by
    simpa [prefixWord, tailWord_3603784, baseEnd_3603784] using wordTrace_append hprefix tailTrace_3603784
  have hstable : (prefixWord ++ tailWord_3603784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3603784).length < 2 ^ (prefixWord ++ tailWord_3603784).sum := by decide
  have hdescent : baseEnd_3603784 < baseStart_3603784 := by decide
  rcases family_descends (prefixWord ++ tailWord_3603784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3603817 : List Nat := [1, 2, 1, 1, 1, 3, 2, 5, 1, 6]
def baseStart_3603817 : Nat := 118140960795 + 3603817 * 2 ^ 59
def prefixEnd_3603817 : Nat := 4983230072969 + 3 ^ 40 * 3603817 * 2
def baseEnd_3603817 : Nat := 616830103948077261037951

theorem tailTrace_3603817 : CollatzResearch.WordTrace tailWord_3603817 prefixEnd_3603817 616830103948077261037951 := by
  unfold tailWord_3603817
  simp only [CollatzResearch.WordTrace]
  refine ⟨131442004384993966787609705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87628002923329311191739803 131442004384993966787609705)
  ·
    refine ⟨98581503288745475090707279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131442004384993966787609705 98581503288745475090707279)
    ·
      refine ⟨147872254933118212636060919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98581503288745475090707279 147872254933118212636060919)
      ·
        refine ⟨221808382399677318954091379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147872254933118212636060919 221808382399677318954091379)
        ·
          refine ⟨332712573599515978431137069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221808382399677318954091379 332712573599515978431137069)
          ·
            refine ⟨124767215099818491911676401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 332712573599515978431137069 124767215099818491911676401)
            ·
              refine ⟨93575411324863868933757301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124767215099818491911676401 93575411324863868933757301)
              ·
                refine ⟨8772694811705987712539747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 93575411324863868933757301 8772694811705987712539747)
                ·
                  refine ⟨13159042217558981568809621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8772694811705987712539747 13159042217558981568809621)
                  ·
                    refine ⟨616830103948077261037951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13159042217558981568809621 616830103948077261037951)
                    ·
                      rfl

theorem cell23_3603817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 5, 1, 6].length) (baseStart_3603817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3603817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3603817 prefixEnd_3603817 := by exact prefixLift 3603817
  have htrace : WordTrace (prefixWord ++ tailWord_3603817) baseStart_3603817 baseEnd_3603817 := by
    simpa [prefixWord, tailWord_3603817, baseEnd_3603817] using wordTrace_append hprefix tailTrace_3603817
  have hstable : (prefixWord ++ tailWord_3603817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3603817).length < 2 ^ (prefixWord ++ tailWord_3603817).sum := by decide
  have hdescent : baseEnd_3603817 < baseStart_3603817 := by decide
  rcases family_descends (prefixWord ++ tailWord_3603817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3603821 : List Nat := [1, 5, 1, 1, 1, 4, 2, 2, 1, 5]
def baseStart_3603821 : Nat := 118140960795 + 3603821 * 2 ^ 59
def prefixEnd_3603821 : Nat := 4983230072969 + 3 ^ 40 * 3603821 * 2
def baseEnd_3603821 : Nat := 616830788588949922487945

theorem tailTrace_3603821 : CollatzResearch.WordTrace tailWord_3603821 prefixEnd_3603821 616830788588949922487945 := by
  unfold tailWord_3603821
  simp only [CollatzResearch.WordTrace]
  refine ⟨131442150276979475470755317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87628100184652983647170211 131442150276979475470755317)
  ·
    refine ⟨12322701588466825825383311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 131442150276979475470755317 12322701588466825825383311)
    ·
      refine ⟨18484052382700238738074967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12322701588466825825383311 18484052382700238738074967)
      ·
        refine ⟨27726078574050358107112451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18484052382700238738074967 27726078574050358107112451)
        ·
          refine ⟨41589117861075537160668677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27726078574050358107112451 41589117861075537160668677)
          ·
            refine ⟨7797959598951663217625377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41589117861075537160668677 7797959598951663217625377)
            ·
              refine ⟨5848469699213747413219033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7797959598951663217625377 5848469699213747413219033)
              ·
                refine ⟨4386352274410310559914275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5848469699213747413219033 4386352274410310559914275)
                ·
                  refine ⟨6579528411615465839871413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4386352274410310559914275 6579528411615465839871413)
                  ·
                    refine ⟨616830788588949922487945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6579528411615465839871413 616830788588949922487945)
                    ·
                      rfl

theorem cell23_3603821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2, 2, 1, 5].length) (baseStart_3603821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3603821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3603821 prefixEnd_3603821 := by exact prefixLift 3603821
  have htrace : WordTrace (prefixWord ++ tailWord_3603821) baseStart_3603821 baseEnd_3603821 := by
    simpa [prefixWord, tailWord_3603821, baseEnd_3603821] using wordTrace_append hprefix tailTrace_3603821
  have hstable : (prefixWord ++ tailWord_3603821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3603821).length < 2 ^ (prefixWord ++ tailWord_3603821).sum := by decide
  have hdescent : baseEnd_3603821 < baseStart_3603821 := by decide
  rcases family_descends (prefixWord ++ tailWord_3603821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3603824 : List Nat := [2, 1, 1, 1, 4, 2, 1, 1, 2, 6, 2]
def baseStart_3603824 : Nat := 118140960795 + 3603824 * 2 ^ 59
def prefixEnd_3603824 : Nat := 4983230072969 + 3 ^ 40 * 3603824 * 2
def baseEnd_3603824 : Nat := 1850493906208813255726321

theorem tailTrace_3603824 : CollatzResearch.WordTrace tailWord_3603824 prefixEnd_3603824 1850493906208813255726321 := by
  unfold tailWord_3603824
  simp only [CollatzResearch.WordTrace]
  refine ⟨65721129847984303491557263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87628173130645737988743017 65721129847984303491557263)
  ·
    refine ⟨98581694771976455237335895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65721129847984303491557263 98581694771976455237335895)
    ·
      refine ⟨147872542157964682856003843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98581694771976455237335895 147872542157964682856003843)
      ·
        refine ⟨221808813236947024284005765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147872542157964682856003843 221808813236947024284005765)
        ·
          refine ⟨41589152481927567053251081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 221808813236947024284005765 41589152481927567053251081)
          ·
            refine ⟨31191864361445675289938311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41589152481927567053251081 31191864361445675289938311)
            ·
              refine ⟨46787796542168512934907467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31191864361445675289938311 46787796542168512934907467)
              ·
                refine ⟨70181694813252769402361201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46787796542168512934907467 70181694813252769402361201)
                ·
                  refine ⟨52636271109939577051770901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70181694813252769402361201 52636271109939577051770901)
                  ·
                    refine ⟨2467325208278417674301761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 52636271109939577051770901 2467325208278417674301761)
                    ·
                      refine ⟨1850493906208813255726321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2467325208278417674301761 1850493906208813255726321)
                      ·
                        rfl

theorem cell23_3603824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 2, 6, 2].length) (baseStart_3603824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3603824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3603824 prefixEnd_3603824 := by exact prefixLift 3603824
  have htrace : WordTrace (prefixWord ++ tailWord_3603824) baseStart_3603824 baseEnd_3603824 := by
    simpa [prefixWord, tailWord_3603824, baseEnd_3603824] using wordTrace_append hprefix tailTrace_3603824
  have hstable : (prefixWord ++ tailWord_3603824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3603824).length < 2 ^ (prefixWord ++ tailWord_3603824).sum := by decide
  have hdescent : baseEnd_3603824 < baseStart_3603824 := by decide
  rcases family_descends (prefixWord ++ tailWord_3603824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3603844 : List Nat := [2, 3, 2, 1, 1, 3, 1, 3, 1, 1, 5]
def baseStart_3603844 : Nat := 118140960795 + 3603844 * 2 ^ 59
def prefixEnd_3603844 : Nat := 4983230072969 + 3 ^ 40 * 3603844 * 2
def baseEnd_3603844 : Nat := 1850504175821903177476229

theorem tailTrace_3603844 : CollatzResearch.WordTrace tailWord_3603844 prefixEnd_3603844 1850504175821903177476229 := by
  unfold tailWord_3603844
  simp only [CollatzResearch.WordTrace]
  refine ⟨65721494577948075199421293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87628659437264100265895057 65721494577948075199421293)
  ·
    refine ⟨24645560466730528199782985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65721494577948075199421293 24645560466730528199782985)
    ·
      refine ⟨18484170350047896149837239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24645560466730528199782985 18484170350047896149837239)
      ·
        refine ⟨27726255525071844224755859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18484170350047896149837239 27726255525071844224755859)
        ·
          refine ⟨41589383287607766337133789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27726255525071844224755859 41589383287607766337133789)
          ·
            refine ⟨15596018732852912376425171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41589383287607766337133789 15596018732852912376425171)
            ·
              refine ⟨23394028099279368564637757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15596018732852912376425171 23394028099279368564637757)
              ·
                refine ⟨8772760537229763211739159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23394028099279368564637757 8772760537229763211739159)
                ·
                  refine ⟨13159140805844644817608739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8772760537229763211739159 13159140805844644817608739)
                  ·
                    refine ⟨19738711208766967226413109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13159140805844644817608739 19738711208766967226413109)
                    ·
                      refine ⟨1850504175821903177476229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19738711208766967226413109 1850504175821903177476229)
                      ·
                        rfl

theorem cell23_3603844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 3, 1, 1, 5].length) (baseStart_3603844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3603844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3603844 prefixEnd_3603844 := by exact prefixLift 3603844
  have htrace : WordTrace (prefixWord ++ tailWord_3603844) baseStart_3603844 baseEnd_3603844 := by
    simpa [prefixWord, tailWord_3603844, baseEnd_3603844] using wordTrace_append hprefix tailTrace_3603844
  have hstable : (prefixWord ++ tailWord_3603844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3603844).length < 2 ^ (prefixWord ++ tailWord_3603844).sum := by decide
  have hdescent : baseEnd_3603844 < baseStart_3603844 := by decide
  rcases family_descends (prefixWord ++ tailWord_3603844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3603847 : List Nat := [1, 1, 4, 2, 2, 2, 11]
def baseStart_3603847 : Nat := 118140960795 + 3603847 * 2 ^ 59
def prefixEnd_3603847 : Nat := 4983230072969 + 3 ^ 40 * 3603847 * 2
def baseEnd_3603847 : Nat := 22845749583504526737515

theorem tailTrace_3603847 : CollatzResearch.WordTrace tailWord_3603847 prefixEnd_3603847 22845749583504526737515 := by
  unfold tailWord_3603847
  simp only [CollatzResearch.WordTrace]
  refine ⟨131443098574885281911201795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87628732383256854607467863 131443098574885281911201795)
  ·
    refine ⟨197164647862327922866802693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131443098574885281911201795 197164647862327922866802693)
    ·
      refine ⟨36968371474186485537525505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 197164647862327922866802693 36968371474186485537525505)
      ·
        refine ⟨27726278605639864153144129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36968371474186485537525505 27726278605639864153144129)
        ·
          refine ⟨20794708954229898114858097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27726278605639864153144129 20794708954229898114858097)
          ·
            refine ⟨15596031715672423586143573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20794708954229898114858097 15596031715672423586143573)
            ·
              refine ⟨22845749583504526737515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 15596031715672423586143573 22845749583504526737515)
              ·
                rfl

theorem cell23_3603847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 11].length) (baseStart_3603847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3603847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3603847 prefixEnd_3603847 := by exact prefixLift 3603847
  have htrace : WordTrace (prefixWord ++ tailWord_3603847) baseStart_3603847 baseEnd_3603847 := by
    simpa [prefixWord, tailWord_3603847, baseEnd_3603847] using wordTrace_append hprefix tailTrace_3603847
  have hstable : (prefixWord ++ tailWord_3603847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3603847).length < 2 ^ (prefixWord ++ tailWord_3603847).sum := by decide
  have hdescent : baseEnd_3603847 < baseStart_3603847 := by decide
  rcases family_descends (prefixWord ++ tailWord_3603847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3603877 : List Nat := [1, 3, 1, 2, 1, 1, 2, 1, 4, 7]
def baseStart_3603877 : Nat := 118140960795 + 3603877 * 2 ^ 59
def prefixEnd_3603877 : Nat := 4983230072969 + 3 ^ 40 * 3603877 * 2
def baseEnd_3603877 : Nat := 616840373561167182787859

theorem tailTrace_3603877 : CollatzResearch.WordTrace tailWord_3603877 prefixEnd_3603877 616840373561167182787859 := by
  unfold tailWord_3603877
  simp only [CollatzResearch.WordTrace]
  refine ⟨131444192764776597034793885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87629461843184398023195923 131444192764776597034793885)
  ·
    refine ⟨49291572286791223888047707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131444192764776597034793885 49291572286791223888047707)
    ·
      refine ⟨73937358430186835832071561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49291572286791223888047707 73937358430186835832071561)
      ·
        refine ⟨55453018822640126874053671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73937358430186835832071561 55453018822640126874053671)
        ·
          refine ⟨83179528233960190311080507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55453018822640126874053671 83179528233960190311080507)
          ·
            refine ⟨124769292350940285466620761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83179528233960190311080507 124769292350940285466620761)
            ·
              refine ⟨93576969263205214099965571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124769292350940285466620761 93576969263205214099965571)
              ·
                refine ⟨140365453894807821149948357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93576969263205214099965571 140365453894807821149948357)
                ·
                  refine ⟨26318522605276466465615317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 140365453894807821149948357 26318522605276466465615317)
                  ·
                    refine ⟨616840373561167182787859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26318522605276466465615317 616840373561167182787859)
                    ·
                      rfl

theorem cell23_3603877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 4, 7].length) (baseStart_3603877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3603877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3603877 prefixEnd_3603877 := by exact prefixLift 3603877
  have htrace : WordTrace (prefixWord ++ tailWord_3603877) baseStart_3603877 baseEnd_3603877 := by
    simpa [prefixWord, tailWord_3603877, baseEnd_3603877] using wordTrace_append hprefix tailTrace_3603877
  have hstable : (prefixWord ++ tailWord_3603877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3603877).length < 2 ^ (prefixWord ++ tailWord_3603877).sum := by decide
  have hdescent : baseEnd_3603877 < baseStart_3603877 := by decide
  rcases family_descends (prefixWord ++ tailWord_3603877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3603887 : List Nat := [1, 1, 2, 1, 2, 2, 1, 3, 1, 4, 5]
def baseStart_3603887 : Nat := 118140960795 + 3603887 * 2 ^ 59
def prefixEnd_3603887 : Nat := 4983230072969 + 3 ^ 40 * 3603887 * 2
def baseEnd_3603887 : Nat := 1850526255490046509238531

theorem tailTrace_3603887 : CollatzResearch.WordTrace tailWord_3603887 prefixEnd_3603887 1850526255490046509238531 := by
  unfold tailWord_3603887
  simp only [CollatzResearch.WordTrace]
  refine ⟨131444557494740368742657915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87629704996493579161771943 131444557494740368742657915)
  ·
    refine ⟨197166836242110553113986873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131444557494740368742657915 197166836242110553113986873)
    ·
      refine ⟨147875127181582914835490155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197166836242110553113986873 147875127181582914835490155)
      ·
        refine ⟨221812690772374372253235233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147875127181582914835490155 221812690772374372253235233)
        ·
          refine ⟨166359518079280779189926425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 221812690772374372253235233 166359518079280779189926425)
          ·
            refine ⟨124769638559460584392444819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166359518079280779189926425 124769638559460584392444819)
            ·
              refine ⟨187154457839190876588667229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124769638559460584392444819 187154457839190876588667229)
              ·
                refine ⟨70182921689696578720750211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 187154457839190876588667229 70182921689696578720750211)
                ·
                  refine ⟨105274382534544868081125317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70182921689696578720750211 105274382534544868081125317)
                  ·
                    refine ⟨19738946725227162765210997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 105274382534544868081125317 19738946725227162765210997)
                    ·
                      refine ⟨1850526255490046509238531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19738946725227162765210997 1850526255490046509238531)
                      ·
                        rfl

theorem cell23_3603887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 4, 5].length) (baseStart_3603887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3603887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3603887 prefixEnd_3603887 := by exact prefixLift 3603887
  have htrace : WordTrace (prefixWord ++ tailWord_3603887) baseStart_3603887 baseEnd_3603887 := by
    simpa [prefixWord, tailWord_3603887, baseEnd_3603887] using wordTrace_append hprefix tailTrace_3603887
  have hstable : (prefixWord ++ tailWord_3603887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3603887).length < 2 ^ (prefixWord ++ tailWord_3603887).sum := by decide
  have hdescent : baseEnd_3603887 < baseStart_3603887 := by decide
  rcases family_descends (prefixWord ++ tailWord_3603887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3603914 : List Nat := [3, 1, 2, 1, 2, 3, 1, 1, 2, 3, 4]
def baseStart_3603914 : Nat := 118140960795 + 3603914 * 2 ^ 59
def prefixEnd_3603914 : Nat := 4983230072969 + 3 ^ 40 * 3603914 * 2
def baseEnd_3603914 : Nat := 1850540119467717903600907

theorem tailTrace_3603914 : CollatzResearch.WordTrace tailWord_3603914 prefixEnd_3603914 1850540119467717903600907 := by
  unfold tailWord_3603914
  simp only [CollatzResearch.WordTrace]
  refine ⟨32861385566410638088472699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87630361510428368235927197 32861385566410638088472699)
  ·
    refine ⟨49292078349615957132709049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32861385566410638088472699 49292078349615957132709049)
    ·
      refine ⟨36969058762211967849531787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49292078349615957132709049 36969058762211967849531787)
      ·
        refine ⟨55453588143317951774297681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36969058762211967849531787 55453588143317951774297681)
        ·
          refine ⟨41590191107488463830723261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55453588143317951774297681 41590191107488463830723261)
          ·
            refine ⟨15596321665308173936521223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41590191107488463830723261 15596321665308173936521223)
            ·
              refine ⟨23394482497962260904781835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15596321665308173936521223 23394482497962260904781835)
              ·
                refine ⟨35091723746943391357172753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23394482497962260904781835 35091723746943391357172753)
                ·
                  refine ⟨26318792810207543517879565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35091723746943391357172753 26318792810207543517879565)
                  ·
                    refine ⟨9869547303827828819204837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26318792810207543517879565 9869547303827828819204837)
                    ·
                      refine ⟨1850540119467717903600907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9869547303827828819204837 1850540119467717903600907)
                      ·
                        rfl

theorem cell23_3603914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 1, 2, 3, 4].length) (baseStart_3603914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3603914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3603914 prefixEnd_3603914 := by exact prefixLift 3603914
  have htrace : WordTrace (prefixWord ++ tailWord_3603914) baseStart_3603914 baseEnd_3603914 := by
    simpa [prefixWord, tailWord_3603914, baseEnd_3603914] using wordTrace_append hprefix tailTrace_3603914
  have hstable : (prefixWord ++ tailWord_3603914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3603914).length < 2 ^ (prefixWord ++ tailWord_3603914).sum := by decide
  have hdescent : baseEnd_3603914 < baseStart_3603914 := by decide
  rcases family_descends (prefixWord ++ tailWord_3603914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3603944 : List Nat := [2, 1, 4, 1, 1, 2, 1, 2, 1, 4, 4]
def baseStart_3603944 : Nat := 118140960795 + 3603944 * 2 ^ 59
def prefixEnd_3603944 : Nat := 4983230072969 + 3 ^ 40 * 3603944 * 2
def baseEnd_3603944 : Nat := 1850555523887352786225769

theorem tailTrace_3603944 : CollatzResearch.WordTrace tailWord_3603944 prefixEnd_3603944 1850555523887352786225769 := by
  unfold tailWord_3603944
  simp only [CollatzResearch.WordTrace]
  refine ⟨65723318227766933738741443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87631090970355911651655257 65723318227766933738741443)
  ·
    refine ⟨98584977341650400608112165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65723318227766933738741443 98584977341650400608112165)
    ·
      refine ⟨18484683251559450114021031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98584977341650400608112165 18484683251559450114021031)
      ·
        refine ⟨27727024877339175171031547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18484683251559450114021031 27727024877339175171031547)
        ·
          refine ⟨41590537316008762756547321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27727024877339175171031547 41590537316008762756547321)
          ·
            refine ⟨31192902987006572067410491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41590537316008762756547321 31192902987006572067410491)
            ·
              refine ⟨46789354480509858101115737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31192902987006572067410491 46789354480509858101115737)
              ·
                refine ⟨35092015860382393575836803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46789354480509858101115737 35092015860382393575836803)
                ·
                  refine ⟨52638023790573590363755205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35092015860382393575836803 52638023790573590363755205)
                  ·
                    refine ⟨9869629460732548193204101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52638023790573590363755205 9869629460732548193204101)
                    ·
                      refine ⟨1850555523887352786225769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9869629460732548193204101 1850555523887352786225769)
                      ·
                        rfl

theorem cell23_3603944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 2, 1, 4, 4].length) (baseStart_3603944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3603944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3603944 prefixEnd_3603944 := by exact prefixLift 3603944
  have htrace : WordTrace (prefixWord ++ tailWord_3603944) baseStart_3603944 baseEnd_3603944 := by
    simpa [prefixWord, tailWord_3603944, baseEnd_3603944] using wordTrace_append hprefix tailTrace_3603944
  have hstable : (prefixWord ++ tailWord_3603944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3603944).length < 2 ^ (prefixWord ++ tailWord_3603944).sum := by decide
  have hdescent : baseEnd_3603944 < baseStart_3603944 := by decide
  rcases family_descends (prefixWord ++ tailWord_3603944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3603965 : List Nat := [1, 4, 1, 1, 1, 4, 3, 2, 2, 2, 2]
def baseStart_3603965 : Nat := 118140960795 + 3603965 * 2 ^ 59
def prefixEnd_3603965 : Nat := 4983230072969 + 3 ^ 40 * 3603965 * 2
def baseEnd_3603965 : Nat := 1850566306981097204063173

theorem tailTrace_3603965 : CollatzResearch.WordTrace tailWord_3603965 prefixEnd_3603965 1850566306981097204063173 := by
  unfold tailWord_3603965
  simp only [CollatzResearch.WordTrace]
  refine ⟨131447402388457788063997349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87631601592305192042664899 131447402388457788063997349)
  ·
    refine ⟨24646387947835835261999503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131447402388457788063997349 24646387947835835261999503)
    ·
      refine ⟨36969581921753752892999255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24646387947835835261999503 36969581921753752892999255)
      ·
        refine ⟨55454372882630629339498883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36969581921753752892999255 55454372882630629339498883)
        ·
          refine ⟨83181559323945944009248325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55454372882630629339498883 83181559323945944009248325)
          ·
            refine ⟨15596542373239864501734061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83181559323945944009248325 15596542373239864501734061)
            ·
              refine ⟨5848703389964949188150273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15596542373239864501734061 5848703389964949188150273)
              ·
                refine ⟨4386527542473711891112705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5848703389964949188150273 4386527542473711891112705)
                ·
                  refine ⟨3289895656855283918334529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4386527542473711891112705 3289895656855283918334529)
                  ·
                    refine ⟨2467421742641462938750897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3289895656855283918334529 2467421742641462938750897)
                    ·
                      refine ⟨1850566306981097204063173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2467421742641462938750897 1850566306981097204063173)
                      ·
                        rfl

theorem cell23_3603965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3, 2, 2, 2, 2].length) (baseStart_3603965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3603965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3603965 prefixEnd_3603965 := by exact prefixLift 3603965
  have htrace : WordTrace (prefixWord ++ tailWord_3603965) baseStart_3603965 baseEnd_3603965 := by
    simpa [prefixWord, tailWord_3603965, baseEnd_3603965] using wordTrace_append hprefix tailTrace_3603965
  have hstable : (prefixWord ++ tailWord_3603965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3603965).length < 2 ^ (prefixWord ++ tailWord_3603965).sum := by decide
  have hdescent : baseEnd_3603965 < baseStart_3603965 := by decide
  rcases family_descends (prefixWord ++ tailWord_3603965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3603982 : List Nat := [4, 1, 1, 2, 5, 1, 1, 1, 1, 4, 2]
def baseStart_3603982 : Nat := 118140960795 + 3603982 * 2 ^ 59
def prefixEnd_3603982 : Nat := 4983230072969 + 3 ^ 40 * 3603982 * 2
def baseEnd_3603982 : Nat := 1850575036152223637550595

theorem tailTrace_3603982 : CollatzResearch.WordTrace tailWord_3603982 prefixEnd_3603982 1850575036152223637550595 := by
  unfold tailWord_3603982
  simp only [CollatzResearch.WordTrace]
  refine ⟨16431002803674524995920775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87632014952930799978244133 16431002803674524995920775)
  ·
    refine ⟨24646504205511787493881163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16431002803674524995920775 24646504205511787493881163)
    ·
      refine ⟨36969756308267681240821745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24646504205511787493881163 36969756308267681240821745)
      ·
        refine ⟨27727317231200760930616309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36969756308267681240821745 27727317231200760930616309)
        ·
          refine ⟨2599435990425071337245279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27727317231200760930616309 2599435990425071337245279)
          ·
            refine ⟨3899153985637607005867919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2599435990425071337245279 3899153985637607005867919)
            ·
              refine ⟨5848730978456410508801879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3899153985637607005867919 5848730978456410508801879)
              ·
                refine ⟨8773096467684615763202819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5848730978456410508801879 8773096467684615763202819)
                ·
                  refine ⟨13159644701526923644804229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8773096467684615763202819 13159644701526923644804229)
                  ·
                    refine ⟨2467433381536298183400793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13159644701526923644804229 2467433381536298183400793)
                    ·
                      refine ⟨1850575036152223637550595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2467433381536298183400793 1850575036152223637550595)
                      ·
                        rfl

theorem cell23_3603982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 1, 1, 1, 4, 2].length) (baseStart_3603982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3603982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3603982 prefixEnd_3603982 := by exact prefixLift 3603982
  have htrace : WordTrace (prefixWord ++ tailWord_3603982) baseStart_3603982 baseEnd_3603982 := by
    simpa [prefixWord, tailWord_3603982, baseEnd_3603982] using wordTrace_append hprefix tailTrace_3603982
  have hstable : (prefixWord ++ tailWord_3603982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3603982).length < 2 ^ (prefixWord ++ tailWord_3603982).sum := by decide
  have hdescent : baseEnd_3603982 < baseStart_3603982 := by decide
  rcases family_descends (prefixWord ++ tailWord_3603982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3603994 : List Nat := [3, 1, 1, 3, 1, 1, 1, 2, 3, 2, 5]
def baseStart_3603994 : Nat := 118140960795 + 3603994 * 2 ^ 59
def prefixEnd_3603994 : Nat := 4983230072969 + 3 ^ 40 * 3603994 * 2
def baseEnd_3603994 : Nat := 1850581197920077590600539

theorem tailTrace_3603994 : CollatzResearch.WordTrace tailWord_3603994 prefixEnd_3603994 1850581197920077590600539 := by
  unfold tailWord_3603994
  simp only [CollatzResearch.WordTrace]
  refine ⟨32862115026338181504200759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87632306736901817344535357 32862115026338181504200759)
  ·
    refine ⟨49293172539507272256301139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32862115026338181504200759 49293172539507272256301139)
    ·
      refine ⟨73939758809260908384451709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49293172539507272256301139 73939758809260908384451709)
      ·
        refine ⟨27727409553472840644169391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73939758809260908384451709 27727409553472840644169391)
        ·
          refine ⟨41591114330209260966254087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27727409553472840644169391 41591114330209260966254087)
          ·
            refine ⟨62386671495313891449381131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41591114330209260966254087 62386671495313891449381131)
            ·
              refine ⟨93580007242970837174071697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62386671495313891449381131 93580007242970837174071697)
              ·
                refine ⟨70185005432228127880553773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93580007242970837174071697 70185005432228127880553773)
                ·
                  refine ⟨26319377037085547955207665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70185005432228127880553773 26319377037085547955207665)
                  ·
                    refine ⟨19739532777814160966405749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26319377037085547955207665 19739532777814160966405749)
                    ·
                      refine ⟨1850581197920077590600539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19739532777814160966405749 1850581197920077590600539)
                      ·
                        rfl

theorem cell23_3603994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_3603994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3603994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3603994 prefixEnd_3603994 := by exact prefixLift 3603994
  have htrace : WordTrace (prefixWord ++ tailWord_3603994) baseStart_3603994 baseEnd_3603994 := by
    simpa [prefixWord, tailWord_3603994, baseEnd_3603994] using wordTrace_append hprefix tailTrace_3603994
  have hstable : (prefixWord ++ tailWord_3603994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3603994).length < 2 ^ (prefixWord ++ tailWord_3603994).sum := by decide
  have hdescent : baseEnd_3603994 < baseStart_3603994 := by decide
  rcases family_descends (prefixWord ++ tailWord_3603994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3604021 : List Nat := [1, 3, 3, 1, 1, 3, 1, 1, 4, 1, 4]
def baseStart_3604021 : Nat := 118140960795 + 3604021 * 2 ^ 59
def prefixEnd_3604021 : Nat := 4983230072969 + 3 ^ 40 * 3604021 * 2
def baseEnd_3604021 : Nat := 1850595061897748984962915

theorem tailTrace_3604021 : CollatzResearch.WordTrace tailWord_3604021 prefixEnd_3604021 1850595061897748984962915 := by
  unfold tailWord_3604021
  simp only [CollatzResearch.WordTrace]
  refine ⟨131449444876254909628035917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87632963250836606418690611 131449444876254909628035917)
  ·
    refine ⟨49293541828595591110513469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131449444876254909628035917 49293541828595591110513469)
    ·
      refine ⟨18485078185723346666442551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49293541828595591110513469 18485078185723346666442551)
      ·
        refine ⟨27727617278585019999663827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18485078185723346666442551 27727617278585019999663827)
        ·
          refine ⟨41591425917877529999495741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27727617278585019999663827 41591425917877529999495741)
          ·
            refine ⟨15596784719204073749810903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41591425917877529999495741 15596784719204073749810903)
            ·
              refine ⟨23395177078806110624716355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15596784719204073749810903 23395177078806110624716355)
              ·
                refine ⟨35092765618209165937074533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23395177078806110624716355 35092765618209165937074533)
                ·
                  refine ⟨6579893553414218613201475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35092765618209165937074533 6579893553414218613201475)
                  ·
                    refine ⟨9869840330121327919802213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6579893553414218613201475 9869840330121327919802213)
                    ·
                      refine ⟨1850595061897748984962915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9869840330121327919802213 1850595061897748984962915)
                      ·
                        rfl

theorem cell23_3604021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 1, 4, 1, 4].length) (baseStart_3604021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3604021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3604021 prefixEnd_3604021 := by exact prefixLift 3604021
  have htrace : WordTrace (prefixWord ++ tailWord_3604021) baseStart_3604021 baseEnd_3604021 := by
    simpa [prefixWord, tailWord_3604021, baseEnd_3604021] using wordTrace_append hprefix tailTrace_3604021
  have hstable : (prefixWord ++ tailWord_3604021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3604021).length < 2 ^ (prefixWord ++ tailWord_3604021).sum := by decide
  have hdescent : baseEnd_3604021 < baseStart_3604021 := by decide
  rcases family_descends (prefixWord ++ tailWord_3604021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3604022 : List Nat := [5, 1, 2, 1, 3, 1, 3, 2, 5]
def baseStart_3604022 : Nat := 118140960795 + 3604022 * 2 ^ 59
def prefixEnd_3604022 : Nat := 4983230072969 + 3 ^ 40 * 3604022 * 2
def baseEnd_3604022 : Nat := 205621730597600386783379

theorem tailTrace_3604022 : CollatzResearch.WordTrace tailWord_3604022 prefixEnd_3604022 205621730597600386783379 := by
  unfold tailWord_3604022
  simp only [CollatzResearch.WordTrace]
  refine ⟨8215592584328205424926395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 87632987566167524532548213 8215592584328205424926395)
  ·
    refine ⟨12323388876492308137389593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8215592584328205424926395 12323388876492308137389593)
    ·
      refine ⟨9242541657369231103042195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12323388876492308137389593 9242541657369231103042195)
      ·
        refine ⟨13863812486053846654563293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9242541657369231103042195 13863812486053846654563293)
        ·
          refine ⟨5198929682270192495461235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13863812486053846654563293 5198929682270192495461235)
          ·
            refine ⟨7798394523405288743191853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5198929682270192495461235 7798394523405288743191853)
            ·
              refine ⟨2924397946276983278696945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7798394523405288743191853 2924397946276983278696945)
              ·
                refine ⟨2193298459707737459022709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2924397946276983278696945 2193298459707737459022709)
                ·
                  refine ⟨205621730597600386783379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2193298459707737459022709 205621730597600386783379)
                  ·
                    rfl

theorem cell23_3604022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 3, 2, 5].length) (baseStart_3604022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3604022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3604022 prefixEnd_3604022 := by exact prefixLift 3604022
  have htrace : WordTrace (prefixWord ++ tailWord_3604022) baseStart_3604022 baseEnd_3604022 := by
    simpa [prefixWord, tailWord_3604022, baseEnd_3604022] using wordTrace_append hprefix tailTrace_3604022
  have hstable : (prefixWord ++ tailWord_3604022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3604022).length < 2 ^ (prefixWord ++ tailWord_3604022).sum := by decide
  have hdescent : baseEnd_3604022 < baseStart_3604022 := by decide
  rcases family_descends (prefixWord ++ tailWord_3604022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3604064 : List Nat := [2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 8]
def baseStart_3604064 : Nat := 118140960795 + 3604064 * 2 ^ 59
def prefixEnd_3604064 : Nat := 4983230072969 + 3 ^ 40 * 3604064 * 2
def baseEnd_3604064 : Nat := 1850617141565892316725217

theorem tailTrace_3604064 : CollatzResearch.WordTrace tailWord_3604064 prefixEnd_3604064 1850617141565892316725217 := by
  unfold tailWord_3604064
  simp only [CollatzResearch.WordTrace]
  refine ⟨65725506607549563985925623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87634008810066085314567497 65725506607549563985925623)
  ·
    refine ⟨98588259911324345978888435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65725506607549563985925623 98588259911324345978888435)
    ·
      refine ⟨147882389866986518968332653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98588259911324345978888435 147882389866986518968332653)
      ·
        refine ⟨55455896200119944613124745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147882389866986518968332653 55455896200119944613124745)
        ·
          refine ⟨41591922150089958459843559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55455896200119944613124745 41591922150089958459843559)
          ·
            refine ⟨62387883225134937689765339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41591922150089958459843559 62387883225134937689765339)
            ·
              refine ⟨93581824837702406534648009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62387883225134937689765339 93581824837702406534648009)
              ·
                refine ⟨70186368628276804900986007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93581824837702406534648009 70186368628276804900986007)
                ·
                  refine ⟨105279552942415207351479011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70186368628276804900986007 105279552942415207351479011)
                  ·
                    refine ⟨157919329413622811027218517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 105279552942415207351479011 157919329413622811027218517)
                    ·
                      refine ⟨1850617141565892316725217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 157919329413622811027218517 1850617141565892316725217)
                      ·
                        rfl

theorem cell23_3604064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 8].length) (baseStart_3604064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3604064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3604064 prefixEnd_3604064 := by exact prefixLift 3604064
  have htrace : WordTrace (prefixWord ++ tailWord_3604064) baseStart_3604064 baseEnd_3604064 := by
    simpa [prefixWord, tailWord_3604064, baseEnd_3604064] using wordTrace_append hprefix tailTrace_3604064
  have hstable : (prefixWord ++ tailWord_3604064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3604064).length < 2 ^ (prefixWord ++ tailWord_3604064).sum := by decide
  have hdescent : baseEnd_3604064 < baseStart_3604064 := by decide
  rcases family_descends (prefixWord ++ tailWord_3604064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3604082 : List Nat := [3, 2, 1, 2, 3, 1, 4, 2, 1, 4]
def baseStart_3604082 : Nat := 118140960795 + 3604082 * 2 ^ 59
def prefixEnd_3604082 : Nat := 4983230072969 + 3 ^ 40 * 3604082 * 2
def baseEnd_3604082 : Nat := 616875461405891082100045

theorem tailTrace_3604082 : CollatzResearch.WordTrace tailWord_3604082 prefixEnd_3604082 616875461405891082100045 := by
  unfold tailWord_3604082
  simp only [CollatzResearch.WordTrace]
  refine ⟨32862917432258479261501625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87634446486022611364004333 32862917432258479261501625)
  ·
    refine ⟨24647188074193859446126219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32862917432258479261501625 24647188074193859446126219)
    ·
      refine ⟨36970782111290789169189329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24647188074193859446126219 36970782111290789169189329)
      ·
        refine ⟨27728086583468091876891997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36970782111290789169189329 27728086583468091876891997)
        ·
          refine ⟨10398032468800534453834499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27728086583468091876891997 10398032468800534453834499)
          ·
            refine ⟨15597048703200801680751749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10398032468800534453834499 15597048703200801680751749)
            ·
              refine ⟨2924446631850150315140953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15597048703200801680751749 2924446631850150315140953)
              ·
                refine ⟨2193334973887612736355715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2924446631850150315140953 2193334973887612736355715)
                ·
                  refine ⟨3290002460831419104533573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2193334973887612736355715 3290002460831419104533573)
                  ·
                    refine ⟨616875461405891082100045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3290002460831419104533573 616875461405891082100045)
                    ·
                      rfl

theorem cell23_3604082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 4, 2, 1, 4].length) (baseStart_3604082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3604082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3604082 prefixEnd_3604082 := by exact prefixLift 3604082
  have htrace : WordTrace (prefixWord ++ tailWord_3604082) baseStart_3604082 baseEnd_3604082 := by
    simpa [prefixWord, tailWord_3604082, baseEnd_3604082] using wordTrace_append hprefix tailTrace_3604082
  have hstable : (prefixWord ++ tailWord_3604082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3604082).length < 2 ^ (prefixWord ++ tailWord_3604082).sum := by decide
  have hdescent : baseEnd_3604082 < baseStart_3604082 := by decide
  rcases family_descends (prefixWord ++ tailWord_3604082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3604131 : List Nat := [1, 1, 1, 4, 1, 1, 4, 3, 1, 1, 5]
def baseStart_3604131 : Nat := 118140960795 + 3604131 * 2 ^ 59
def prefixEnd_3604131 : Nat := 4983230072969 + 3 ^ 40 * 3604131 * 2
def baseEnd_3604131 : Nat := 1850651544769743554587409

theorem tailTrace_3604131 : CollatzResearch.WordTrace tailWord_3604131 prefixEnd_3604131 1850651544769743554587409 := by
  unfold tailWord_3604131
  simp only [CollatzResearch.WordTrace]
  refine ⟨131453456905856398414540247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87635637937237598943026831 131453456905856398414540247)
  ·
    refine ⟨197180185358784597621810371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131453456905856398414540247 197180185358784597621810371)
    ·
      refine ⟨295770278038176896432715557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197180185358784597621810371 295770278038176896432715557)
      ·
        refine ⟨55456927132158168081134167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 295770278038176896432715557 55456927132158168081134167)
        ·
          refine ⟨83185390698237252121701251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55456927132158168081134167 83185390698237252121701251)
          ·
            refine ⟨124778086047355878182551877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83185390698237252121701251 124778086047355878182551877)
            ·
              refine ⟨23395891133879227159228477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 124778086047355878182551877 23395891133879227159228477)
              ·
                refine ⟨8773459175204710184710679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23395891133879227159228477 8773459175204710184710679)
                ·
                  refine ⟨13160188762807065277066019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8773459175204710184710679 13160188762807065277066019)
                  ·
                    refine ⟨19740283144210597915599029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13160188762807065277066019 19740283144210597915599029)
                    ·
                      refine ⟨1850651544769743554587409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19740283144210597915599029 1850651544769743554587409)
                      ·
                        rfl

theorem cell23_3604131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 3, 1, 1, 5].length) (baseStart_3604131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3604131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3604131 prefixEnd_3604131 := by exact prefixLift 3604131
  have htrace : WordTrace (prefixWord ++ tailWord_3604131) baseStart_3604131 baseEnd_3604131 := by
    simpa [prefixWord, tailWord_3604131, baseEnd_3604131] using wordTrace_append hprefix tailTrace_3604131
  have hstable : (prefixWord ++ tailWord_3604131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3604131).length < 2 ^ (prefixWord ++ tailWord_3604131).sum := by decide
  have hdescent : baseEnd_3604131 < baseStart_3604131 := by decide
  rcases family_descends (prefixWord ++ tailWord_3604131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3604158 : List Nat := [4, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6]
def baseStart_3604158 : Nat := 118140960795 + 3604158 * 2 ^ 59
def prefixEnd_3604158 : Nat := 4983230072969 + 3 ^ 40 * 3604158 * 2
def baseEnd_3604158 : Nat := 1850665408747414948949785

theorem tailTrace_3604158 : CollatzResearch.WordTrace tailWord_3604158 prefixEnd_3604158 1850665408747414948949785 := by
  unfold tailWord_3604158
  simp only [CollatzResearch.WordTrace]
  refine ⟨16431805209594822753221641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87636294451172388017182085 16431805209594822753221641)
  ·
    refine ⟨12323853907196117064916231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16431805209594822753221641 12323853907196117064916231)
    ·
      refine ⟨18485780860794175597374347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12323853907196117064916231 18485780860794175597374347)
      ·
        refine ⟨27728671291191263396061521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18485780860794175597374347 27728671291191263396061521)
        ·
          refine ⟨20796503468393447547046141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27728671291191263396061521 20796503468393447547046141)
          ·
            refine ⟨7798688800647542830142303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20796503468393447547046141 7798688800647542830142303)
            ·
              refine ⟨11698033200971314245213455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7798688800647542830142303 11698033200971314245213455)
              ·
                refine ⟨17547049801456971367820183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11698033200971314245213455 17547049801456971367820183)
                ·
                  refine ⟨26320574702185457051730275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17547049801456971367820183 26320574702185457051730275)
                  ·
                    refine ⟨39480862053278185577595413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26320574702185457051730275 39480862053278185577595413)
                    ·
                      refine ⟨1850665408747414948949785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39480862053278185577595413 1850665408747414948949785)
                      ·
                        rfl

theorem cell23_3604158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6].length) (baseStart_3604158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3604158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3604158 prefixEnd_3604158 := by exact prefixLift 3604158
  have htrace : WordTrace (prefixWord ++ tailWord_3604158) baseStart_3604158 baseEnd_3604158 := by
    simpa [prefixWord, tailWord_3604158, baseEnd_3604158] using wordTrace_append hprefix tailTrace_3604158
  have hstable : (prefixWord ++ tailWord_3604158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3604158).length < 2 ^ (prefixWord ++ tailWord_3604158).sum := by decide
  have hdescent : baseEnd_3604158 < baseStart_3604158 := by decide
  rcases family_descends (prefixWord ++ tailWord_3604158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3604191 : List Nat := [1, 1, 2, 3, 2, 2, 1, 2, 2, 2, 5]
def baseStart_3604191 : Nat := 118140960795 + 3604191 * 2 ^ 59
def prefixEnd_3604191 : Nat := 4983230072969 + 3 ^ 40 * 3604191 * 2
def baseEnd_3604191 : Nat := 1850682353609013319837133

theorem tailTrace_3604191 : CollatzResearch.WordTrace tailWord_3604191 prefixEnd_3604191 1850682353609013319837133 := by
  unfold tailWord_3604191
  simp only [CollatzResearch.WordTrace]
  refine ⟨131455645285639028661724427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87637096857092685774482951 131455645285639028661724427)
  ·
    refine ⟨197183467928458542992586641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131455645285639028661724427 197183467928458542992586641)
    ·
      refine ⟨147887600946343907244439981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197183467928458542992586641 147887600946343907244439981)
      ·
        refine ⟨55457850354878965216664993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147887600946343907244439981 55457850354878965216664993)
        ·
          refine ⟨41593387766159223912498745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55457850354878965216664993 41593387766159223912498745)
          ·
            refine ⟨31195040824619417934374059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41593387766159223912498745 31195040824619417934374059)
            ·
              refine ⟨46792561236929126901561089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31195040824619417934374059 46792561236929126901561089)
              ·
                refine ⟨35094420927696845176170817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46792561236929126901561089 35094420927696845176170817)
                ·
                  refine ⟨26320815695772633882128113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35094420927696845176170817 26320815695772633882128113)
                  ·
                    refine ⟨19740611771829475411596085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26320815695772633882128113 19740611771829475411596085)
                    ·
                      refine ⟨1850682353609013319837133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19740611771829475411596085 1850682353609013319837133)
                      ·
                        rfl

theorem cell23_3604191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 2, 2, 2, 5].length) (baseStart_3604191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3604191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3604191 prefixEnd_3604191 := by exact prefixLift 3604191
  have htrace : WordTrace (prefixWord ++ tailWord_3604191) baseStart_3604191 baseEnd_3604191 := by
    simpa [prefixWord, tailWord_3604191, baseEnd_3604191] using wordTrace_append hprefix tailTrace_3604191
  have hstable : (prefixWord ++ tailWord_3604191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3604191).length < 2 ^ (prefixWord ++ tailWord_3604191).sum := by decide
  have hdescent : baseEnd_3604191 < baseStart_3604191 := by decide
  rcases family_descends (prefixWord ++ tailWord_3604191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3604201 : List Nat := [1, 2, 1, 1, 1, 2, 3, 3, 2, 3, 4]
def baseStart_3604201 : Nat := 118140960795 + 3604201 * 2 ^ 59
def prefixEnd_3604201 : Nat := 4983230072969 + 3 ^ 40 * 3604201 * 2
def baseEnd_3604201 : Nat := 1850687488415558280712087

theorem tailTrace_3604201 : CollatzResearch.WordTrace tailWord_3604201 prefixEnd_3604201 1850687488415558280712087 := by
  unfold tailWord_3604201
  simp only [CollatzResearch.WordTrace]
  refine ⟨131456010015602800369588457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87637340010401866913058971 131456010015602800369588457)
  ·
    refine ⟨98592007511702100277191343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131456010015602800369588457 98592007511702100277191343)
    ·
      refine ⟨147888011267553150415787015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98592007511702100277191343 147888011267553150415787015)
      ·
        refine ⟨221832016901329725623680523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147888011267553150415787015 221832016901329725623680523)
        ·
          refine ⟨332748025351994588435520785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221832016901329725623680523 332748025351994588435520785)
          ·
            refine ⟨249561019013995941326640589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 332748025351994588435520785 249561019013995941326640589)
            ·
              refine ⟨93585382130248477997490221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 249561019013995941326640589 93585382130248477997490221)
              ·
                refine ⟨35094518298843179249058833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93585382130248477997490221 35094518298843179249058833)
                ·
                  refine ⟨26320888724132384436794125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35094518298843179249058833 26320888724132384436794125)
                  ·
                    refine ⟨9870333271549644163797797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26320888724132384436794125 9870333271549644163797797)
                    ·
                      refine ⟨1850687488415558280712087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9870333271549644163797797 1850687488415558280712087)
                      ·
                        rfl

theorem cell23_3604201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 3, 2, 3, 4].length) (baseStart_3604201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3604201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3604201 prefixEnd_3604201 := by exact prefixLift 3604201
  have htrace : WordTrace (prefixWord ++ tailWord_3604201) baseStart_3604201 baseEnd_3604201 := by
    simpa [prefixWord, tailWord_3604201, baseEnd_3604201] using wordTrace_append hprefix tailTrace_3604201
  have hstable : (prefixWord ++ tailWord_3604201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3604201).length < 2 ^ (prefixWord ++ tailWord_3604201).sum := by decide
  have hdescent : baseEnd_3604201 < baseStart_3604201 := by decide
  rcases family_descends (prefixWord ++ tailWord_3604201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3604211 : List Nat := [1, 1, 1, 2, 2, 3, 2, 3, 2, 6]
def baseStart_3604211 : Nat := 118140960795 + 3604211 * 2 ^ 59
def prefixEnd_3604211 : Nat := 4983230072969 + 3 ^ 40 * 3604211 * 2
def baseEnd_3604211 : Nat := 616897541074034413862347

theorem tailTrace_3604211 : CollatzResearch.WordTrace tailWord_3604211 prefixEnd_3604211 616897541074034413862347 := by
  unfold tailWord_3604211
  simp only [CollatzResearch.WordTrace]
  refine ⟨131456374745566572077452487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87637583163711048051634991 131456374745566572077452487)
  ·
    refine ⟨197184562118349858116178731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131456374745566572077452487 197184562118349858116178731)
    ·
      refine ⟨295776843177524787174268097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197184562118349858116178731 295776843177524787174268097)
      ·
        refine ⟨221832632383143590380701073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 295776843177524787174268097 221832632383143590380701073)
        ·
          refine ⟨166374474287357692785525805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 221832632383143590380701073 166374474287357692785525805)
          ·
            refine ⟨62390427857759134794572177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 166374474287357692785525805 62390427857759134794572177)
            ·
              refine ⟨46792820893319351095929133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62390427857759134794572177 46792820893319351095929133)
              ·
                refine ⟨17547307834994756660973425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46792820893319351095929133 17547307834994756660973425)
                ·
                  refine ⟨13160480876246067495730069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17547307834994756660973425 13160480876246067495730069)
                  ·
                    refine ⟨616897541074034413862347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13160480876246067495730069 616897541074034413862347)
                    ·
                      rfl

theorem cell23_3604211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 3, 2, 6].length) (baseStart_3604211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3604211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3604211 prefixEnd_3604211 := by exact prefixLift 3604211
  have htrace : WordTrace (prefixWord ++ tailWord_3604211) baseStart_3604211 baseEnd_3604211 := by
    simpa [prefixWord, tailWord_3604211, baseEnd_3604211] using wordTrace_append hprefix tailTrace_3604211
  have hstable : (prefixWord ++ tailWord_3604211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3604211).length < 2 ^ (prefixWord ++ tailWord_3604211).sum := by decide
  have hdescent : baseEnd_3604211 < baseStart_3604211 := by decide
  rcases family_descends (prefixWord ++ tailWord_3604211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3604230 : List Nat := [6, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4]
def baseStart_3604230 : Nat := 118140960795 + 3604230 * 2 ^ 59
def prefixEnd_3604230 : Nat := 4983230072969 + 3 ^ 40 * 3604230 * 2
def baseEnd_3604230 : Nat := 1850702379354538667249455

theorem tailTrace_3604230 : CollatzResearch.WordTrace tailWord_3604230 prefixEnd_3604230 1850702379354538667249455 := by
  unfold tailWord_3604230
  simp only [CollatzResearch.WordTrace]
  refine ⟨4108033366640554322574817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 87638045154998492214929429 4108033366640554322574817)
  ·
    refine ⟨3081025024980415741931113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4108033366640554322574817 3081025024980415741931113)
    ·
      refine ⟨2310768768735311806448335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3081025024980415741931113 2310768768735311806448335)
      ·
        refine ⟨3466153153102967709672503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2310768768735311806448335 3466153153102967709672503)
        ·
          refine ⟨5199229729654451564508755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3466153153102967709672503 5199229729654451564508755)
          ·
            refine ⟨7798844594481677346763133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5199229729654451564508755 7798844594481677346763133)
            ·
              refine ⟨2924566722930629005036175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7798844594481677346763133 2924566722930629005036175)
              ·
                refine ⟨4386850084395943507554263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2924566722930629005036175 4386850084395943507554263)
                ·
                  refine ⟨6580275126593915261331395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4386850084395943507554263 6580275126593915261331395)
                  ·
                    refine ⟨9870412689890872891997093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6580275126593915261331395 9870412689890872891997093)
                    ·
                      refine ⟨1850702379354538667249455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9870412689890872891997093 1850702379354538667249455)
                      ·
                        rfl

theorem cell23_3604230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_3604230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3604230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3604230 prefixEnd_3604230 := by exact prefixLift 3604230
  have htrace : WordTrace (prefixWord ++ tailWord_3604230) baseStart_3604230 baseEnd_3604230 := by
    simpa [prefixWord, tailWord_3604230, baseEnd_3604230] using wordTrace_append hprefix tailTrace_3604230
  have hstable : (prefixWord ++ tailWord_3604230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3604230).length < 2 ^ (prefixWord ++ tailWord_3604230).sum := by decide
  have hdescent : baseEnd_3604230 < baseStart_3604230 := by decide
  rcases family_descends (prefixWord ++ tailWord_3604230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3604235 : List Nat := [1, 1, 1, 1, 5, 1, 2, 1, 6, 2, 2]
def baseStart_3604235 : Nat := 118140960795 + 3604235 * 2 ^ 59
def prefixEnd_3604235 : Nat := 4983230072969 + 3 ^ 40 * 3604235 * 2
def baseEnd_3604235 : Nat := 1850704946757811147686931

theorem tailTrace_3604235 : CollatzResearch.WordTrace tailWord_3604235 prefixEnd_3604235 1850704946757811147686931 := by
  unfold tailWord_3604235
  simp only [CollatzResearch.WordTrace]
  refine ⟨131457250097479624176326159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87638166731653082784217439 131457250097479624176326159)
  ·
    refine ⟨197185875146219436264489239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131457250097479624176326159 197185875146219436264489239)
    ·
      refine ⟨295778812719329154396733859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197185875146219436264489239 295778812719329154396733859)
      ·
        refine ⟨443668219078993731595100789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295778812719329154396733859 443668219078993731595100789)
        ·
          refine ⟨41593895538655662337040699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 443668219078993731595100789 41593895538655662337040699)
          ·
            refine ⟨62390843307983493505561049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41593895538655662337040699 62390843307983493505561049)
            ·
              refine ⟨46793132480987620129170787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62390843307983493505561049 46793132480987620129170787)
              ·
                refine ⟨70189698721481430193756181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46793132480987620129170787 70189698721481430193756181)
                ·
                  refine ⟨3290142127569442040332321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 70189698721481430193756181 3290142127569442040332321)
                  ·
                    refine ⟨2467606595677081530249241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3290142127569442040332321 2467606595677081530249241)
                    ·
                      refine ⟨1850704946757811147686931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2467606595677081530249241 1850704946757811147686931)
                      ·
                        rfl

theorem cell23_3604235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 6, 2, 2].length) (baseStart_3604235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3604235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3604235 prefixEnd_3604235 := by exact prefixLift 3604235
  have htrace : WordTrace (prefixWord ++ tailWord_3604235) baseStart_3604235 baseEnd_3604235 := by
    simpa [prefixWord, tailWord_3604235, baseEnd_3604235] using wordTrace_append hprefix tailTrace_3604235
  have hstable : (prefixWord ++ tailWord_3604235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3604235).length < 2 ^ (prefixWord ++ tailWord_3604235).sum := by decide
  have hdescent : baseEnd_3604235 < baseStart_3604235 := by decide
  rcases family_descends (prefixWord ++ tailWord_3604235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3604238 : List Nat := [4, 1, 1, 2, 1, 1, 4, 1, 2, 1, 5]
def baseStart_3604238 : Nat := 118140960795 + 3604238 * 2 ^ 59
def prefixEnd_3604238 : Nat := 4983230072969 + 3 ^ 40 * 3604238 * 2
def baseEnd_3604238 : Nat := 1850706487199774635949417

theorem tailTrace_3604238 : CollatzResearch.WordTrace tailWord_3604238 prefixEnd_3604238 1850706487199774635949417 := by
  unfold tailWord_3604238
  simp only [CollatzResearch.WordTrace]
  refine ⟨16432169939558594461085671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87638239677645837125790245 16432169939558594461085671)
  ·
    refine ⟨24648254909337891691628507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16432169939558594461085671 24648254909337891691628507)
    ·
      refine ⟨36972382364006837537442761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24648254909337891691628507 36972382364006837537442761)
      ·
        refine ⟨27729286773005128153082071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36972382364006837537442761 27729286773005128153082071)
        ·
          refine ⟨41593930159507692229623107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27729286773005128153082071 41593930159507692229623107)
          ·
            refine ⟨62390895239261538344434661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41593930159507692229623107 62390895239261538344434661)
            ·
              refine ⟨11698292857361538439581499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62390895239261538344434661 11698292857361538439581499)
              ·
                refine ⟨17547439286042307659372249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11698292857361538439581499 17547439286042307659372249)
                ·
                  refine ⟨13160579464531730744529187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17547439286042307659372249 13160579464531730744529187)
                  ·
                    refine ⟨19740869196797596116793781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13160579464531730744529187 19740869196797596116793781)
                    ·
                      refine ⟨1850706487199774635949417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19740869196797596116793781 1850706487199774635949417)
                      ·
                        rfl

theorem cell23_3604238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 1, 2, 1, 5].length) (baseStart_3604238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3604238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3604238 prefixEnd_3604238 := by exact prefixLift 3604238
  have htrace : WordTrace (prefixWord ++ tailWord_3604238) baseStart_3604238 baseEnd_3604238 := by
    simpa [prefixWord, tailWord_3604238, baseEnd_3604238] using wordTrace_append hprefix tailTrace_3604238
  have hstable : (prefixWord ++ tailWord_3604238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3604238).length < 2 ^ (prefixWord ++ tailWord_3604238).sum := by decide
  have hdescent : baseEnd_3604238 < baseStart_3604238 := by decide
  rcases family_descends (prefixWord ++ tailWord_3604238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3604258 : List Nat := [3, 3, 1, 1, 2, 1, 2, 3, 7]
def baseStart_3604258 : Nat := 118140960795 + 3604258 * 2 ^ 59
def prefixEnd_3604258 : Nat := 4983230072969 + 3 ^ 40 * 3604258 * 2
def baseEnd_3604258 : Nat := 205635195201429395299925

theorem tailTrace_3604258 : CollatzResearch.WordTrace tailWord_3604258 prefixEnd_3604258 205635195201429395299925 := by
  unfold tailWord_3604258
  simp only [CollatzResearch.WordTrace]
  refine ⟨32864522244099074776103357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87638725984264199402942285 32864522244099074776103357)
  ·
    refine ⟨12324195841537153041038759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32864522244099074776103357 12324195841537153041038759)
    ·
      refine ⟨18486293762305729561558139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12324195841537153041038759 18486293762305729561558139)
      ·
        refine ⟨27729440643458594342337209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18486293762305729561558139 27729440643458594342337209)
        ·
          refine ⟨20797080482593945756752907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27729440643458594342337209 20797080482593945756752907)
          ·
            refine ⟨31195620723890918635129361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20797080482593945756752907 31195620723890918635129361)
            ·
              refine ⟨23396715542918188976347021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31195620723890918635129361 23396715542918188976347021)
              ·
                refine ⟨8773768328594320866130133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23396715542918188976347021 8773768328594320866130133)
                ·
                  refine ⟨205635195201429395299925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8773768328594320866130133 205635195201429395299925)
                  ·
                    rfl

theorem cell23_3604258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 3, 7].length) (baseStart_3604258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3604258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3604258 prefixEnd_3604258 := by exact prefixLift 3604258
  have htrace : WordTrace (prefixWord ++ tailWord_3604258) baseStart_3604258 baseEnd_3604258 := by
    simpa [prefixWord, tailWord_3604258, baseEnd_3604258] using wordTrace_append hprefix tailTrace_3604258
  have hstable : (prefixWord ++ tailWord_3604258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3604258).length < 2 ^ (prefixWord ++ tailWord_3604258).sum := by decide
  have hdescent : baseEnd_3604258 < baseStart_3604258 := by decide
  rcases family_descends (prefixWord ++ tailWord_3604258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3604268 : List Nat := [2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 3]
def baseStart_3604268 : Nat := 118140960795 + 3604268 * 2 ^ 59
def prefixEnd_3604268 : Nat := 4983230072969 + 3 ^ 40 * 3604268 * 2
def baseEnd_3604268 : Nat := 1850721891619409518574279

theorem tailTrace_3604268 : CollatzResearch.WordTrace tailWord_3604268 prefixEnd_3604268 1850721891619409518574279 := by
  unfold tailWord_3604268
  simp only [CollatzResearch.WordTrace]
  refine ⟨65729226853180035406138729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87638969137573380541518305 65729226853180035406138729)
  ·
    refine ⟨49296920139885026554604047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65729226853180035406138729 49296920139885026554604047)
    ·
      refine ⟨73945380209827539831906071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49296920139885026554604047 73945380209827539831906071)
      ·
        refine ⟨110918070314741309747859107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73945380209827539831906071 110918070314741309747859107)
        ·
          refine ⟨166377105472111964621788661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110918070314741309747859107 166377105472111964621788661)
          ·
            refine ⟨15597853638010496683292687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 166377105472111964621788661 15597853638010496683292687)
            ·
              refine ⟨23396780457015745024939031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15597853638010496683292687 23396780457015745024939031)
              ·
                refine ⟨35095170685523617537408547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23396780457015745024939031 35095170685523617537408547)
                ·
                  refine ⟨52642756028285426306112821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35095170685523617537408547 52642756028285426306112821)
                  ·
                    refine ⟨4935258377651758716198077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52642756028285426306112821 4935258377651758716198077)
                    ·
                      refine ⟨1850721891619409518574279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4935258377651758716198077 1850721891619409518574279)
                      ·
                        rfl

theorem cell23_3604268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 3].length) (baseStart_3604268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3604268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3604268 prefixEnd_3604268 := by exact prefixLift 3604268
  have htrace : WordTrace (prefixWord ++ tailWord_3604268) baseStart_3604268 baseEnd_3604268 := by
    simpa [prefixWord, tailWord_3604268, baseEnd_3604268] using wordTrace_append hprefix tailTrace_3604268
  have hstable : (prefixWord ++ tailWord_3604268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3604268).length < 2 ^ (prefixWord ++ tailWord_3604268).sum := by decide
  have hdescent : baseEnd_3604268 < baseStart_3604268 := by decide
  rcases family_descends (prefixWord ++ tailWord_3604268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3604271 : List Nat := [1, 1, 2, 1, 2, 1, 2, 3, 3, 7]
def baseStart_3604271 : Nat := 118140960795 + 3604271 * 2 ^ 59
def prefixEnd_3604271 : Nat := 4983230072969 + 3 ^ 40 * 3604271 * 2
def baseEnd_3604271 : Nat := 616907810687124335612255

theorem tailTrace_3604271 : CollatzResearch.WordTrace tailWord_3604271 prefixEnd_3604271 616907810687124335612255 := by
  unfold tailWord_3604271
  simp only [CollatzResearch.WordTrace]
  refine ⟨131458563125349202324636667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87639042083566134883091111 131458563125349202324636667)
  ·
    refine ⟨197187844688023803486955001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131458563125349202324636667 197187844688023803486955001)
    ·
      refine ⟨147890883516017852615216251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197187844688023803486955001 147890883516017852615216251)
      ·
        refine ⟨221836325274026778922824377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147890883516017852615216251 221836325274026778922824377)
        ·
          refine ⟨166377243955520084192118283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 221836325274026778922824377 166377243955520084192118283)
          ·
            refine ⟨249565865933280126288177425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166377243955520084192118283 249565865933280126288177425)
            ·
              refine ⟨187174399449960094716133069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 249565865933280126288177425 187174399449960094716133069)
              ·
                refine ⟨70190399793735035518549901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 187174399449960094716133069 70190399793735035518549901)
                ·
                  refine ⟨26321399922650638319456213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70190399793735035518549901 26321399922650638319456213)
                  ·
                    refine ⟨616907810687124335612255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26321399922650638319456213 616907810687124335612255)
                    ·
                      rfl

theorem cell23_3604271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 3, 7].length) (baseStart_3604271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3604271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3604271 prefixEnd_3604271 := by exact prefixLift 3604271
  have htrace : WordTrace (prefixWord ++ tailWord_3604271) baseStart_3604271 baseEnd_3604271 := by
    simpa [prefixWord, tailWord_3604271, baseEnd_3604271] using wordTrace_append hprefix tailTrace_3604271
  have hstable : (prefixWord ++ tailWord_3604271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3604271).length < 2 ^ (prefixWord ++ tailWord_3604271).sum := by decide
  have hdescent : baseEnd_3604271 < baseStart_3604271 := by decide
  rcases family_descends (prefixWord ++ tailWord_3604271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3604338 : List Nat := [3, 2, 1, 2, 1, 1, 1, 1, 1, 6, 4]
def baseStart_3604338 : Nat := 118140960795 + 3604338 * 2 ^ 59
def prefixEnd_3604338 : Nat := 4983230072969 + 3 ^ 40 * 3604338 * 2
def baseEnd_3604338 : Nat := 1850757835265224244698957

theorem tailTrace_3604338 : CollatzResearch.WordTrace tailWord_3604338 prefixEnd_3604338 1850757835265224244698957 := by
  unfold tailWord_3604338
  simp only [CollatzResearch.WordTrace]
  refine ⟨32865251704026618191831417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87640671210737648511550445 32865251704026618191831417)
  ·
    refine ⟨24648938778019963643873563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32865251704026618191831417 24648938778019963643873563)
    ·
      refine ⟨36973408167029945465810345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24648938778019963643873563 36973408167029945465810345)
      ·
        refine ⟨27730056125272459099357759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36973408167029945465810345 27730056125272459099357759)
        ·
          refine ⟨41595084187908688649036639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27730056125272459099357759 41595084187908688649036639)
          ·
            refine ⟨62392626281863032973554959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41595084187908688649036639 62392626281863032973554959)
            ·
              refine ⟨93588939422794549460332439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62392626281863032973554959 93588939422794549460332439)
              ·
                refine ⟨140383409134191824190498659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93588939422794549460332439 140383409134191824190498659)
                ·
                  refine ⟨210575113701287736285747989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 140383409134191824190498659 210575113701287736285747989)
                  ·
                    refine ⟨9870708454747862638394437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 210575113701287736285747989 9870708454747862638394437)
                    ·
                      refine ⟨1850757835265224244698957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9870708454747862638394437 1850757835265224244698957)
                      ·
                        rfl

theorem cell23_3604338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 1, 6, 4].length) (baseStart_3604338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3604338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3604338 prefixEnd_3604338 := by exact prefixLift 3604338
  have htrace : WordTrace (prefixWord ++ tailWord_3604338) baseStart_3604338 baseEnd_3604338 := by
    simpa [prefixWord, tailWord_3604338, baseEnd_3604338] using wordTrace_append hprefix tailTrace_3604338
  have hstable : (prefixWord ++ tailWord_3604338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3604338).length < 2 ^ (prefixWord ++ tailWord_3604338).sum := by decide
  have hdescent : baseEnd_3604338 < baseStart_3604338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3604338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3604345 : List Nat := [1, 2, 1, 3, 2, 2, 2, 3, 2, 2, 3]
def baseStart_3604345 : Nat := 118140960795 + 3604345 * 2 ^ 59
def prefixEnd_3604345 : Nat := 4983230072969 + 3 ^ 40 * 3604345 * 2
def baseEnd_3604345 : Nat := 1850761429629805717311425

theorem tailTrace_3604345 : CollatzResearch.WordTrace tailWord_3604345 prefixEnd_3604345 1850761429629805717311425 := by
  unfold tailWord_3604345
  simp only [CollatzResearch.WordTrace]
  refine ⟨131461262127081112962830489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87640841418054075308553659 131461262127081112962830489)
  ·
    refine ⟨98595946595310834722122867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131461262127081112962830489 98595946595310834722122867)
    ·
      refine ⟨147893919892966252083184301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98595946595310834722122867 147893919892966252083184301)
      ·
        refine ⟨55460219959862344531194113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147893919892966252083184301 55460219959862344531194113)
        ·
          refine ⟨41595164969896758398395585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55460219959862344531194113 41595164969896758398395585)
          ·
            refine ⟨31196373727422568798796689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41595164969896758398395585 31196373727422568798796689)
            ·
              refine ⟨23397280295566926599097517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31196373727422568798796689 23397280295566926599097517)
              ·
                refine ⟨8773980110837597474661569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23397280295566926599097517 8773980110837597474661569)
                ·
                  refine ⟨6580485083128198105996177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8773980110837597474661569 6580485083128198105996177)
                  ·
                    refine ⟨4935363812346148579497133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6580485083128198105996177 4935363812346148579497133)
                    ·
                      refine ⟨1850761429629805717311425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4935363812346148579497133 1850761429629805717311425)
                      ·
                        rfl

theorem cell23_3604345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 3, 2, 2, 3].length) (baseStart_3604345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3604345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3604345 prefixEnd_3604345 := by exact prefixLift 3604345
  have htrace : WordTrace (prefixWord ++ tailWord_3604345) baseStart_3604345 baseEnd_3604345 := by
    simpa [prefixWord, tailWord_3604345, baseEnd_3604345] using wordTrace_append hprefix tailTrace_3604345
  have hstable : (prefixWord ++ tailWord_3604345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3604345).length < 2 ^ (prefixWord ++ tailWord_3604345).sum := by decide
  have hdescent : baseEnd_3604345 < baseStart_3604345 := by decide
  rcases family_descends (prefixWord ++ tailWord_3604345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3604409 : List Nat := [1, 2, 1, 4, 2, 1, 2, 5, 1, 1, 3]
def baseStart_3604409 : Nat := 118140960795 + 3604409 * 2 ^ 59
def prefixEnd_3604409 : Nat := 4983230072969 + 3 ^ 40 * 3604409 * 2
def baseEnd_3604409 : Nat := 1850794292391693466911131

theorem tailTrace_3604409 : CollatzResearch.WordTrace tailWord_3604409 prefixEnd_3604409 1850794292391693466911131 := by
  unfold tailWord_3604409
  simp only [CollatzResearch.WordTrace]
  refine ⟨131463596398849251893160281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87642397599232834595440187 131463596398849251893160281)
  ·
    refine ⟨98597697299136938919870211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131463596398849251893160281 98597697299136938919870211)
    ·
      refine ⟨147896545948705408379805317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98597697299136938919870211 147896545948705408379805317)
      ·
        refine ⟨27730602365382264071213497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 147896545948705408379805317 27730602365382264071213497)
        ·
          refine ⟨20797951774036698053410123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27730602365382264071213497 20797951774036698053410123)
          ·
            refine ⟨31196927661055047080115185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20797951774036698053410123 31196927661055047080115185)
            ·
              refine ⟨23397695745791285310086389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31196927661055047080115185 23397695745791285310086389)
              ·
                refine ⟨2193533976167932997820599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23397695745791285310086389 2193533976167932997820599)
                ·
                  refine ⟨3290300964251899496730899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2193533976167932997820599 3290300964251899496730899)
                  ·
                    refine ⟨4935451446377849245096349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3290300964251899496730899 4935451446377849245096349)
                    ·
                      refine ⟨1850794292391693466911131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4935451446377849245096349 1850794292391693466911131)
                      ·
                        rfl

theorem cell23_3604409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 5, 1, 1, 3].length) (baseStart_3604409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3604409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3604409 prefixEnd_3604409 := by exact prefixLift 3604409
  have htrace : WordTrace (prefixWord ++ tailWord_3604409) baseStart_3604409 baseEnd_3604409 := by
    simpa [prefixWord, tailWord_3604409, baseEnd_3604409] using wordTrace_append hprefix tailTrace_3604409
  have hstable : (prefixWord ++ tailWord_3604409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3604409).length < 2 ^ (prefixWord ++ tailWord_3604409).sum := by decide
  have hdescent : baseEnd_3604409 < baseStart_3604409 := by decide
  rcases family_descends (prefixWord ++ tailWord_3604409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3604426 : List Nat := [3, 1, 2, 1, 2, 1, 6, 2, 1, 1, 3]
def baseStart_3604426 : Nat := 118140960795 + 3604426 * 2 ^ 59
def prefixEnd_3604426 : Nat := 4983230072969 + 3 ^ 40 * 3604426 * 2
def baseEnd_3604426 : Nat := 1850803021562819900398553

theorem tailTrace_3604426 : CollatzResearch.WordTrace tailWord_3604426 prefixEnd_3604426 1850803021562819900398553 := by
  unfold tailWord_3604426
  simp only [CollatzResearch.WordTrace]
  refine ⟨32866054109946915949132283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87642810959858442531019421 32866054109946915949132283)
  ·
    refine ⟨49299081164920373923698425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32866054109946915949132283 49299081164920373923698425)
    ·
      refine ⟨36974310873690280442773819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49299081164920373923698425 36974310873690280442773819)
      ·
        refine ⟨55461466310535420664160729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36974310873690280442773819 55461466310535420664160729)
        ·
          refine ⟨41596099732901565498120547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55461466310535420664160729 41596099732901565498120547)
          ·
            refine ⟨62394149599352348247180821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41596099732901565498120547 62394149599352348247180821)
            ·
              refine ⟨2924725762469641324086601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 62394149599352348247180821 2924725762469641324086601)
              ·
                refine ⟨2193544321852230993064951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2924725762469641324086601 2193544321852230993064951)
                ·
                  refine ⟨3290316482778346489597427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2193544321852230993064951 3290316482778346489597427)
                  ·
                    refine ⟨4935474724167519734396141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3290316482778346489597427 4935474724167519734396141)
                    ·
                      refine ⟨1850803021562819900398553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4935474724167519734396141 1850803021562819900398553)
                      ·
                        rfl

theorem cell23_3604426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 6, 2, 1, 1, 3].length) (baseStart_3604426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3604426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3604426 prefixEnd_3604426 := by exact prefixLift 3604426
  have htrace : WordTrace (prefixWord ++ tailWord_3604426) baseStart_3604426 baseEnd_3604426 := by
    simpa [prefixWord, tailWord_3604426, baseEnd_3604426] using wordTrace_append hprefix tailTrace_3604426
  have hstable : (prefixWord ++ tailWord_3604426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3604426).length < 2 ^ (prefixWord ++ tailWord_3604426).sum := by decide
  have hdescent : baseEnd_3604426 < baseStart_3604426 := by decide
  rcases family_descends (prefixWord ++ tailWord_3604426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3604442 : List Nat := [3, 1, 1, 2, 5, 1, 2, 1, 1, 6]
def baseStart_3604442 : Nat := 118140960795 + 3604442 * 2 ^ 59
def prefixEnd_3604442 : Nat := 4983230072969 + 3 ^ 40 * 3604442 * 2
def baseEnd_3604442 : Nat := 616937079084430612599493

theorem tailTrace_3604442 : CollatzResearch.WordTrace tailWord_3604442 prefixEnd_3604442 616937079084430612599493 := by
  unfold tailWord_3604442
  simp only [CollatzResearch.WordTrace]
  refine ⟨32866200001932424632277895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87643200005153132352741053 32866200001932424632277895)
  ·
    refine ⟨49299300002898636948416843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32866200001932424632277895 49299300002898636948416843)
    ·
      refine ⟨73948950004347955422625265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49299300002898636948416843 73948950004347955422625265)
      ·
        refine ⟨55461712503260966566968949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73948950004347955422625265 55461712503260966566968949)
        ·
          refine ⟨5199535547180715615653339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 55461712503260966566968949 5199535547180715615653339)
          ·
            refine ⟨7799303320771073423480009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5199535547180715615653339 7799303320771073423480009)
            ·
              refine ⟨5849477490578305067610007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7799303320771073423480009 5849477490578305067610007)
              ·
                refine ⟨8774216235867457601415011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5849477490578305067610007 8774216235867457601415011)
                ·
                  refine ⟨13161324353801186402122517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8774216235867457601415011 13161324353801186402122517)
                  ·
                    refine ⟨616937079084430612599493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13161324353801186402122517 616937079084430612599493)
                    ·
                      rfl

theorem cell23_3604442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 2, 1, 1, 6].length) (baseStart_3604442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3604442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3604442 prefixEnd_3604442 := by exact prefixLift 3604442
  have htrace : WordTrace (prefixWord ++ tailWord_3604442) baseStart_3604442 baseEnd_3604442 := by
    simpa [prefixWord, tailWord_3604442, baseEnd_3604442] using wordTrace_append hprefix tailTrace_3604442
  have hstable : (prefixWord ++ tailWord_3604442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3604442).length < 2 ^ (prefixWord ++ tailWord_3604442).sum := by decide
  have hdescent : baseEnd_3604442 < baseStart_3604442 := by decide
  rcases family_descends (prefixWord ++ tailWord_3604442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3604448 : List Nat := [2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 7]
def baseStart_3604448 : Nat := 118140960795 + 3604448 * 2 ^ 59
def prefixEnd_3604448 : Nat := 4983230072969 + 3 ^ 40 * 3604448 * 2
def baseEnd_3604448 : Nat := 1850814318137218814323451

theorem tailTrace_3604448 : CollatzResearch.WordTrace tailWord_3604448 prefixEnd_3604448 1850814318137218814323451 := by
  unfold tailWord_3604448
  simp only [CollatzResearch.WordTrace]
  refine ⟨65732509422853980776914999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87643345897138641035886665 65732509422853980776914999)
  ·
    refine ⟨98598764134280971165372499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65732509422853980776914999 98598764134280971165372499)
    ·
      refine ⟨147898146201421456748058749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98598764134280971165372499 147898146201421456748058749)
      ·
        refine ⟨55461804825533046280522031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147898146201421456748058749 55461804825533046280522031)
        ·
          refine ⟨83192707238299569420783047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55461804825533046280522031 83192707238299569420783047)
          ·
            refine ⟨124789060857449354131174571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83192707238299569420783047 124789060857449354131174571)
            ·
              refine ⟨187183591286174031196761857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124789060857449354131174571 187183591286174031196761857)
              ·
                refine ⟨140387693464630523397571393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 187183591286174031196761857 140387693464630523397571393)
                ·
                  refine ⟨105290770098472892548178545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 140387693464630523397571393 105290770098472892548178545)
                  ·
                    refine ⟨78968077573854669411133909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 105290770098472892548178545 78968077573854669411133909)
                    ·
                      refine ⟨1850814318137218814323451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 78968077573854669411133909 1850814318137218814323451)
                      ·
                        rfl

theorem cell23_3604448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 7].length) (baseStart_3604448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3604448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3604448 prefixEnd_3604448 := by exact prefixLift 3604448
  have htrace : WordTrace (prefixWord ++ tailWord_3604448) baseStart_3604448 baseEnd_3604448 := by
    simpa [prefixWord, tailWord_3604448, baseEnd_3604448] using wordTrace_append hprefix tailTrace_3604448
  have hstable : (prefixWord ++ tailWord_3604448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3604448).length < 2 ^ (prefixWord ++ tailWord_3604448).sum := by decide
  have hdescent : baseEnd_3604448 < baseStart_3604448 := by decide
  rcases family_descends (prefixWord ++ tailWord_3604448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3604452 : List Nat := [2, 3, 1, 1, 1, 1, 4, 4, 1, 2, 3]
def baseStart_3604452 : Nat := 118140960795 + 3604452 * 2 ^ 59
def prefixEnd_3604452 : Nat := 4983230072969 + 3 ^ 40 * 3604452 * 2
def baseEnd_3604452 : Nat := 1850816372059836798673433

theorem tailTrace_3604452 : CollatzResearch.WordTrace tailWord_3604452 prefixEnd_3604452 1850816372059836798673433 := by
  unfold tailWord_3604452
  simp only [CollatzResearch.WordTrace]
  refine ⟨65732582368846735118487805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87643443158462313491317073 65732582368846735118487805)
  ·
    refine ⟨24649718388317525669432927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65732582368846735118487805 24649718388317525669432927)
    ·
      refine ⟨36974577582476288504149391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24649718388317525669432927 36974577582476288504149391)
      ·
        refine ⟨55461866373714432756224087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36974577582476288504149391 55461866373714432756224087)
        ·
          refine ⟨83192799560571649134336131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55461866373714432756224087 83192799560571649134336131)
          ·
            refine ⟨124789199340857473701504197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83192799560571649134336131 124789199340857473701504197)
            ·
              refine ⟨23397974876410776319032037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 124789199340857473701504197 23397974876410776319032037)
              ·
                refine ⟨4387120289327020559818507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23397974876410776319032037 4387120289327020559818507)
                ·
                  refine ⟨6580680433990530839727761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4387120289327020559818507 6580680433990530839727761)
                  ·
                    refine ⟨4935510325492898129795821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6580680433990530839727761 4935510325492898129795821)
                    ·
                      refine ⟨1850816372059836798673433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4935510325492898129795821 1850816372059836798673433)
                      ·
                        rfl

theorem cell23_3604452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 4, 1, 2, 3].length) (baseStart_3604452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3604452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3604452 prefixEnd_3604452 := by exact prefixLift 3604452
  have htrace : WordTrace (prefixWord ++ tailWord_3604452) baseStart_3604452 baseEnd_3604452 := by
    simpa [prefixWord, tailWord_3604452, baseEnd_3604452] using wordTrace_append hprefix tailTrace_3604452
  have hstable : (prefixWord ++ tailWord_3604452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3604452).length < 2 ^ (prefixWord ++ tailWord_3604452).sum := by decide
  have hdescent : baseEnd_3604452 < baseStart_3604452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3604452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3604462 : List Nat := [4, 1, 2, 1, 3, 1, 2, 2, 1, 2, 4]
def baseStart_3604462 : Nat := 118140960795 + 3604462 * 2 ^ 59
def prefixEnd_3604462 : Nat := 4983230072969 + 3 ^ 40 * 3604462 * 2
def baseEnd_3604462 : Nat := 1850821506866381759548387

theorem tailTrace_3604462 : CollatzResearch.WordTrace tailWord_3604462 prefixEnd_3604462 1850821506866381759548387 := by
  unfold tailWord_3604462
  simp only [CollatzResearch.WordTrace]
  refine ⟨16433191183457155243104955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87643686311771494629893093 16433191183457155243104955)
  ·
    refine ⟨24649786775185732864657433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16433191183457155243104955 24649786775185732864657433)
    ·
      refine ⟨18487340081389299648493075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24649786775185732864657433 18487340081389299648493075)
      ·
        refine ⟨27731010122083949472739613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18487340081389299648493075 27731010122083949472739613)
        ·
          refine ⟨10399128795781481052277355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27731010122083949472739613 10399128795781481052277355)
          ·
            refine ⟨15598693193672221578416033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10399128795781481052277355 15598693193672221578416033)
            ·
              refine ⟨11699019895254166183812025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15598693193672221578416033 11699019895254166183812025)
              ·
                refine ⟨8774264921440624637859019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11699019895254166183812025 8774264921440624637859019)
                ·
                  refine ⟨13161397382160936956788529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8774264921440624637859019 13161397382160936956788529)
                  ·
                    refine ⟨9871048036620702717591397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13161397382160936956788529 9871048036620702717591397)
                    ·
                      refine ⟨1850821506866381759548387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9871048036620702717591397 1850821506866381759548387)
                      ·
                        rfl

theorem cell23_3604462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 2, 1, 2, 4].length) (baseStart_3604462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3604462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3604462 prefixEnd_3604462 := by exact prefixLift 3604462
  have htrace : WordTrace (prefixWord ++ tailWord_3604462) baseStart_3604462 baseEnd_3604462 := by
    simpa [prefixWord, tailWord_3604462, baseEnd_3604462] using wordTrace_append hprefix tailTrace_3604462
  have hstable : (prefixWord ++ tailWord_3604462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3604462).length < 2 ^ (prefixWord ++ tailWord_3604462).sum := by decide
  have hdescent : baseEnd_3604462 < baseStart_3604462 := by decide
  rcases family_descends (prefixWord ++ tailWord_3604462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3604493 : List Nat := [1, 7, 1, 2, 1, 2, 1, 1, 1, 6]
def baseStart_3604493 : Nat := 118140960795 + 3604493 * 2 ^ 59
def prefixEnd_3604493 : Nat := 4983230072969 + 3 ^ 40 * 3604493 * 2
def baseEnd_3604493 : Nat := 616945808255557046086915

theorem tailTrace_3604493 : CollatzResearch.WordTrace tailWord_3604493 prefixEnd_3604493 616945808255557046086915 := by
  unfold tailWord_3604493
  simp only [CollatzResearch.WordTrace]
  refine ⟨131466660130544934239218133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87644440087029956159478755 131466660130544934239218133)
  ·
    refine ⟨3081249846809646896231675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 131466660130544934239218133 3081249846809646896231675)
    ·
      refine ⟨4621874770214470344347513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3081249846809646896231675 4621874770214470344347513)
      ·
        refine ⟨3466406077660852758260635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4621874770214470344347513 3466406077660852758260635)
        ·
          refine ⟨5199609116491279137390953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3466406077660852758260635 5199609116491279137390953)
          ·
            refine ⟨3899706837368459353043215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5199609116491279137390953 3899706837368459353043215)
            ·
              refine ⟨5849560256052689029564823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3899706837368459353043215 5849560256052689029564823)
              ·
                refine ⟨8774340384079033544347235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5849560256052689029564823 8774340384079033544347235)
                ·
                  refine ⟨13161510576118550316520853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8774340384079033544347235 13161510576118550316520853)
                  ·
                    refine ⟨616945808255557046086915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13161510576118550316520853 616945808255557046086915)
                    ·
                      rfl

theorem cell23_3604493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_3604493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3604493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3604493 prefixEnd_3604493 := by exact prefixLift 3604493
  have htrace : WordTrace (prefixWord ++ tailWord_3604493) baseStart_3604493 baseEnd_3604493 := by
    simpa [prefixWord, tailWord_3604493, baseEnd_3604493] using wordTrace_append hprefix tailTrace_3604493
  have hstable : (prefixWord ++ tailWord_3604493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3604493).length < 2 ^ (prefixWord ++ tailWord_3604493).sum := by decide
  have hdescent : baseEnd_3604493 < baseStart_3604493 := by decide
  rcases family_descends (prefixWord ++ tailWord_3604493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3604526 : List Nat := [4, 1, 3, 1, 1, 2, 2, 3, 1, 3, 2]
def baseStart_3604526 : Nat := 118140960795 + 3604526 * 2 ^ 59
def prefixEnd_3604526 : Nat := 4983230072969 + 3 ^ 40 * 3604526 * 2
def baseEnd_3604526 : Nat := 1850854369628269509148093

theorem tailTrace_3604526 : CollatzResearch.WordTrace tailWord_3604526 prefixEnd_3604526 1850854369628269509148093 := by
  unfold tailWord_3604526
  simp only [CollatzResearch.WordTrace]
  refine ⟨16433482967428172609396179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87645242492950253916779621 16433482967428172609396179)
  ·
    refine ⟨24650224451142258914094269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16433482967428172609396179 24650224451142258914094269)
    ·
      refine ⟨9243834169178347092785351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24650224451142258914094269 9243834169178347092785351)
      ·
        refine ⟨13865751253767520639178027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9243834169178347092785351 13865751253767520639178027)
        ·
          refine ⟨20798626880651280958767041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13865751253767520639178027 20798626880651280958767041)
          ·
            refine ⟨15598970160488460719075281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20798626880651280958767041 15598970160488460719075281)
            ·
              refine ⟨11699227620366345539306461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15598970160488460719075281 11699227620366345539306461)
              ·
                refine ⟨4387210357637379577239923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11699227620366345539306461 4387210357637379577239923)
                ·
                  refine ⟨6580815536456069365859885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4387210357637379577239923 6580815536456069365859885)
                  ·
                    refine ⟨2467805826171026012197457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6580815536456069365859885 2467805826171026012197457)
                    ·
                      refine ⟨1850854369628269509148093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2467805826171026012197457 1850854369628269509148093)
                      ·
                        rfl

theorem cell23_3604526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 3, 1, 3, 2].length) (baseStart_3604526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3604526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3604526 prefixEnd_3604526 := by exact prefixLift 3604526
  have htrace : WordTrace (prefixWord ++ tailWord_3604526) baseStart_3604526 baseEnd_3604526 := by
    simpa [prefixWord, tailWord_3604526, baseEnd_3604526] using wordTrace_append hprefix tailTrace_3604526
  have hstable : (prefixWord ++ tailWord_3604526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3604526).length < 2 ^ (prefixWord ++ tailWord_3604526).sum := by decide
  have hdescent : baseEnd_3604526 < baseStart_3604526 := by decide
  rcases family_descends (prefixWord ++ tailWord_3604526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3604535 : List Nat := [1, 1, 3, 1, 2, 2, 2, 1, 4, 2, 4]
def baseStart_3604535 : Nat := 118140960795 + 3604535 * 2 ^ 59
def prefixEnd_3604535 : Nat := 4983230072969 + 3 ^ 40 * 3604535 * 2
def baseEnd_3604535 : Nat := 1850858990954159973935551

theorem tailTrace_3604535 : CollatzResearch.WordTrace tailWord_3604535 prefixEnd_3604535 1850858990954159973935551 := by
  unfold tailWord_3604535
  simp only [CollatzResearch.WordTrace]
  refine ⟨131468191996392775412247059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87645461330928516941498039 131468191996392775412247059)
  ·
    refine ⟨197202287994589163118370589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131468191996392775412247059 197202287994589163118370589)
    ·
      refine ⟨73950857997970936169388971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197202287994589163118370589 73950857997970936169388971)
      ·
        refine ⟨110926286996956404254083457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73950857997970936169388971 110926286996956404254083457)
        ·
          refine ⟨83194715247717303190562593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110926286996956404254083457 83194715247717303190562593)
          ·
            refine ⟨62396036435787977392921945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83194715247717303190562593 62396036435787977392921945)
            ·
              refine ⟨46797027326840983044691459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62396036435787977392921945 46797027326840983044691459)
              ·
                refine ⟨70195540990261474567037189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46797027326840983044691459 70195540990261474567037189)
                ·
                  refine ⟨13161663935674026481319473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70195540990261474567037189 13161663935674026481319473)
                  ·
                    refine ⟨9871247951755519860989605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13161663935674026481319473 9871247951755519860989605)
                    ·
                      refine ⟨1850858990954159973935551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9871247951755519860989605 1850858990954159973935551)
                      ·
                        rfl

theorem cell23_3604535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 4, 2, 4].length) (baseStart_3604535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3604535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3604535 prefixEnd_3604535 := by exact prefixLift 3604535
  have htrace : WordTrace (prefixWord ++ tailWord_3604535) baseStart_3604535 baseEnd_3604535 := by
    simpa [prefixWord, tailWord_3604535, baseEnd_3604535] using wordTrace_append hprefix tailTrace_3604535
  have hstable : (prefixWord ++ tailWord_3604535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3604535).length < 2 ^ (prefixWord ++ tailWord_3604535).sum := by decide
  have hdescent : baseEnd_3604535 < baseStart_3604535 := by decide
  rcases family_descends (prefixWord ++ tailWord_3604535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3604585 : List Nat := [1, 2, 1, 1, 1, 5, 1, 1, 3, 2, 5]
def baseStart_3604585 : Nat := 118140960795 + 3604585 * 2 ^ 59
def prefixEnd_3604585 : Nat := 4983230072969 + 3 ^ 40 * 3604585 * 2
def baseEnd_3604585 : Nat := 1850884664986884778310321

theorem tailTrace_3604585 : CollatzResearch.WordTrace tailWord_3604585 prefixEnd_3604585 1850884664986884778310321 := by
  unfold tailWord_3604585
  simp only [CollatzResearch.WordTrace]
  refine ⟨131470015646211633951567209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87646677097474422634378139 131470015646211633951567209)
  ·
    refine ⟨98602511734658725463675407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131470015646211633951567209 98602511734658725463675407)
    ·
      refine ⟨147903767601988088195513111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98602511734658725463675407 147903767601988088195513111)
      ·
        refine ⟨221855651402982132293269667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147903767601988088195513111 221855651402982132293269667)
        ·
          refine ⟨332783477104473198439904501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221855651402982132293269667 332783477104473198439904501)
          ·
            refine ⟨31198450978544362353741047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 332783477104473198439904501 31198450978544362353741047)
            ·
              refine ⟨46797676467816543530611571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31198450978544362353741047 46797676467816543530611571)
              ·
                refine ⟨70196514701724815295917357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46797676467816543530611571 70196514701724815295917357)
                ·
                  refine ⟨26323693013146805735969009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70196514701724815295917357 26323693013146805735969009)
                  ·
                    refine ⟨19742769759860104301976757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26323693013146805735969009 19742769759860104301976757)
                    ·
                      refine ⟨1850884664986884778310321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19742769759860104301976757 1850884664986884778310321)
                      ·
                        rfl

theorem cell23_3604585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 3, 2, 5].length) (baseStart_3604585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3604585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3604585 prefixEnd_3604585 := by exact prefixLift 3604585
  have htrace : WordTrace (prefixWord ++ tailWord_3604585) baseStart_3604585 baseEnd_3604585 := by
    simpa [prefixWord, tailWord_3604585, baseEnd_3604585] using wordTrace_append hprefix tailTrace_3604585
  have hstable : (prefixWord ++ tailWord_3604585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3604585).length < 2 ^ (prefixWord ++ tailWord_3604585).sum := by decide
  have hdescent : baseEnd_3604585 < baseStart_3604585 := by decide
  rcases family_descends (prefixWord ++ tailWord_3604585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3604592 : List Nat := [2, 1, 1, 1, 5, 2, 2, 2, 2, 5]
def baseStart_3604592 : Nat := 118140960795 + 3604592 * 2 ^ 59
def prefixEnd_3604592 : Nat := 4983230072969 + 3 ^ 40 * 3604592 * 2
def baseEnd_3604592 : Nat := 616962753117155416974263

theorem tailTrace_3604592 : CollatzResearch.WordTrace tailWord_3604592 prefixEnd_3604592 616962753117155416974263 := by
  unfold tailWord_3604592
  simp only [CollatzResearch.WordTrace]
  refine ⟨65735135478593137073536015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87646847304790849431381353 65735135478593137073536015)
  ·
    refine ⟨98602703217889705610304023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65735135478593137073536015 98602703217889705610304023)
    ·
      refine ⟨147904054826834558415456035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98602703217889705610304023 147904054826834558415456035)
      ·
        refine ⟨221856082240251837623184053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147904054826834558415456035 221856082240251837623184053)
        ·
          refine ⟨20799007710023609777173505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 221856082240251837623184053 20799007710023609777173505)
          ·
            refine ⟨15599255782517707332880129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20799007710023609777173505 15599255782517707332880129)
            ·
              refine ⟨11699441836888280499660097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15599255782517707332880129 11699441836888280499660097)
              ·
                refine ⟨8774581377666210374745073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11699441836888280499660097 8774581377666210374745073)
                ·
                  refine ⟨6580936033249657781058805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8774581377666210374745073 6580936033249657781058805)
                  ·
                    refine ⟨616962753117155416974263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6580936033249657781058805 616962753117155416974263)
                    ·
                      rfl

theorem cell23_3604592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 2, 2, 5].length) (baseStart_3604592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3604592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3604592 prefixEnd_3604592 := by exact prefixLift 3604592
  have htrace : WordTrace (prefixWord ++ tailWord_3604592) baseStart_3604592 baseEnd_3604592 := by
    simpa [prefixWord, tailWord_3604592, baseEnd_3604592] using wordTrace_append hprefix tailTrace_3604592
  have hstable : (prefixWord ++ tailWord_3604592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3604592).length < 2 ^ (prefixWord ++ tailWord_3604592).sum := by decide
  have hdescent : baseEnd_3604592 < baseStart_3604592 := by decide
  rcases family_descends (prefixWord ++ tailWord_3604592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3604612 : List Nat := [2, 3, 2, 1, 2, 1, 2, 2, 1, 3, 4]
def baseStart_3604612 : Nat := 118140960795 + 3604612 * 2 ^ 59
def prefixEnd_3604612 : Nat := 4983230072969 + 3 ^ 40 * 3604612 * 2
def baseEnd_3604612 : Nat := 1850898528964556172672697

theorem tailTrace_3604612 : CollatzResearch.WordTrace tailWord_3604612 prefixEnd_3604612 1850898528964556172672697 := by
  unfold tailWord_3604612
  simp only [CollatzResearch.WordTrace]
  refine ⟨65735500208556908781400045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87647333611409211708533393 65735500208556908781400045)
  ·
    refine ⟨24650812578208840793025017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65735500208556908781400045 24650812578208840793025017)
    ·
      refine ⟨18488109433656630594768763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24650812578208840793025017 18488109433656630594768763)
      ·
        refine ⟨27732164150484945892153145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18488109433656630594768763 27732164150484945892153145)
        ·
          refine ⟨20799123112863709419114859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27732164150484945892153145 20799123112863709419114859)
          ·
            refine ⟨31198684669295564128672289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20799123112863709419114859 31198684669295564128672289)
            ·
              refine ⟨23399013501971673096504217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31198684669295564128672289 23399013501971673096504217)
              ·
                refine ⟨17549260126478754822378163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23399013501971673096504217 17549260126478754822378163)
                ·
                  refine ⟨26323890189718132233567245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17549260126478754822378163 26323890189718132233567245)
                  ·
                    refine ⟨9871458821144299587587717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26323890189718132233567245 9871458821144299587587717)
                    ·
                      refine ⟨1850898528964556172672697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9871458821144299587587717 1850898528964556172672697)
                      ·
                        rfl

theorem cell23_3604612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 2, 1, 3, 4].length) (baseStart_3604612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3604612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3604612 prefixEnd_3604612 := by exact prefixLift 3604612
  have htrace : WordTrace (prefixWord ++ tailWord_3604612) baseStart_3604612 baseEnd_3604612 := by
    simpa [prefixWord, tailWord_3604612, baseEnd_3604612] using wordTrace_append hprefix tailTrace_3604612
  have hstable : (prefixWord ++ tailWord_3604612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3604612).length < 2 ^ (prefixWord ++ tailWord_3604612).sum := by decide
  have hdescent : baseEnd_3604612 < baseStart_3604612 := by decide
  rcases family_descends (prefixWord ++ tailWord_3604612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3604625 : List Nat := [1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 6]
def baseStart_3604625 : Nat := 118140960795 + 3604625 * 2 ^ 59
def prefixEnd_3604625 : Nat := 4983230072969 + 3 ^ 40 * 3604625 * 2
def baseEnd_3604625 : Nat := 1850905204213064621810137

theorem tailTrace_3604625 : CollatzResearch.WordTrace tailWord_3604625 prefixEnd_3604625 1850905204213064621810137 := by
  unfold tailWord_3604625
  simp only [CollatzResearch.WordTrace]
  refine ⟨131471474566066720783023329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87647649710711147188682219 131471474566066720783023329)
  ·
    refine ⟨98603605924550040587267497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131471474566066720783023329 98603605924550040587267497)
    ·
      refine ⟨73952704443412530440450623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98603605924550040587267497 73952704443412530440450623)
      ·
        refine ⟨110929056665118795660675935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73952704443412530440450623 110929056665118795660675935)
        ·
          refine ⟨166393584997678193491013903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110929056665118795660675935 166393584997678193491013903)
          ·
            refine ⟨249590377496517290236520855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166393584997678193491013903 249590377496517290236520855)
            ·
              refine ⟨374385566244775935354781283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249590377496517290236520855 374385566244775935354781283)
              ·
                refine ⟨561578349367163903032171925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 374385566244775935354781283 561578349367163903032171925)
                ·
                  refine ⟨26323985126585807954633059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 561578349367163903032171925 26323985126585807954633059)
                  ·
                    refine ⟨39485977689878711931949589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26323985126585807954633059 39485977689878711931949589)
                    ·
                      refine ⟨1850905204213064621810137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39485977689878711931949589 1850905204213064621810137)
                      ·
                        rfl

theorem cell23_3604625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 6].length) (baseStart_3604625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3604625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3604625 prefixEnd_3604625 := by exact prefixLift 3604625
  have htrace : WordTrace (prefixWord ++ tailWord_3604625) baseStart_3604625 baseEnd_3604625 := by
    simpa [prefixWord, tailWord_3604625, baseEnd_3604625] using wordTrace_append hprefix tailTrace_3604625
  have hstable : (prefixWord ++ tailWord_3604625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3604625).length < 2 ^ (prefixWord ++ tailWord_3604625).sum := by decide
  have hdescent : baseEnd_3604625 < baseStart_3604625 := by decide
  rcases family_descends (prefixWord ++ tailWord_3604625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3604689 : List Nat := [1, 2, 2, 1, 2, 2, 4, 1, 1, 5, 2]
def baseStart_3604689 : Nat := 118140960795 + 3604689 * 2 ^ 59
def prefixEnd_3604689 : Nat := 4983230072969 + 3 ^ 40 * 3604689 * 2
def baseEnd_3604689 : Nat := 1850938066974952371409843

theorem tailTrace_3604689 : CollatzResearch.WordTrace tailWord_3604689 prefixEnd_3604689 1850938066974952371409843 := by
  unfold tailWord_3604689
  simp only [CollatzResearch.WordTrace]
  refine ⟨131473808837834859713353121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87649205891889906475568747 131473808837834859713353121)
  ·
    refine ⟨98605356628376144785014841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131473808837834859713353121 98605356628376144785014841)
    ·
      refine ⟨73954017471282108588761131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98605356628376144785014841 73954017471282108588761131)
      ·
        refine ⟨110931026206923162883141697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73954017471282108588761131 110931026206923162883141697)
        ·
          refine ⟨83198269655192372162356273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110931026206923162883141697 83198269655192372162356273)
          ·
            refine ⟨62398702241394279121767205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83198269655192372162356273 62398702241394279121767205)
            ·
              refine ⟨11699756670261427335331351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62398702241394279121767205 11699756670261427335331351)
              ·
                refine ⟨17549635005392141002997027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11699756670261427335331351 17549635005392141002997027)
                ·
                  refine ⟨26324452508088211504495541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17549635005392141002997027 26324452508088211504495541)
                  ·
                    refine ⟨2467917422633269828546457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26324452508088211504495541 2467917422633269828546457)
                    ·
                      refine ⟨1850938066974952371409843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2467917422633269828546457 1850938066974952371409843)
                      ·
                        rfl

theorem cell23_3604689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 1, 1, 5, 2].length) (baseStart_3604689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3604689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3604689 prefixEnd_3604689 := by exact prefixLift 3604689
  have htrace : WordTrace (prefixWord ++ tailWord_3604689) baseStart_3604689 baseEnd_3604689 := by
    simpa [prefixWord, tailWord_3604689, baseEnd_3604689] using wordTrace_append hprefix tailTrace_3604689
  have hstable : (prefixWord ++ tailWord_3604689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3604689).length < 2 ^ (prefixWord ++ tailWord_3604689).sum := by decide
  have hdescent : baseEnd_3604689 < baseStart_3604689 := by decide
  rcases family_descends (prefixWord ++ tailWord_3604689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3604736 : List Nat := [2, 1, 1, 2, 1, 1, 4, 4, 3, 2, 2]
def baseStart_3604736 : Nat := 118140960795 + 3604736 * 2 ^ 59
def prefixEnd_3604736 : Nat := 4983230072969 + 3 ^ 40 * 3604736 * 2
def baseEnd_3604736 : Nat := 1850962200565713687522127

theorem tailTrace_3604736 : CollatzResearch.WordTrace tailWord_3604736 prefixEnd_3604736 1850962200565713687522127 := by
  unfold tailWord_3604736
  simp only [CollatzResearch.WordTrace]
  refine ⟨65737761534332293370157031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87650348712443057826876041 65737761534332293370157031)
  ·
    refine ⟨98606642301498440055235547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65737761534332293370157031 98606642301498440055235547)
    ·
      refine ⟨147909963452247660082853321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98606642301498440055235547 147909963452247660082853321)
      ·
        refine ⟨110932472589185745062139991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147909963452247660082853321 110932472589185745062139991)
        ·
          refine ⟨166398708883778617593209987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110932472589185745062139991 166398708883778617593209987)
          ·
            refine ⟨249598063325667926389814981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166398708883778617593209987 249598063325667926389814981)
            ·
              refine ⟨46799636873562736198090309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 249598063325667926389814981 46799636873562736198090309)
              ·
                refine ⟨8774931913793013037141933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46799636873562736198090309 8774931913793013037141933)
                ·
                  refine ⟨3290599467672379888928225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8774931913793013037141933 3290599467672379888928225)
                  ·
                    refine ⟨2467949600754284916696169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3290599467672379888928225 2467949600754284916696169)
                    ·
                      refine ⟨1850962200565713687522127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2467949600754284916696169 1850962200565713687522127)
                      ·
                        rfl

theorem cell23_3604736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 4, 3, 2, 2].length) (baseStart_3604736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3604736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3604736 prefixEnd_3604736 := by exact prefixLift 3604736
  have htrace : WordTrace (prefixWord ++ tailWord_3604736) baseStart_3604736 baseEnd_3604736 := by
    simpa [prefixWord, tailWord_3604736, baseEnd_3604736] using wordTrace_append hprefix tailTrace_3604736
  have hstable : (prefixWord ++ tailWord_3604736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3604736).length < 2 ^ (prefixWord ++ tailWord_3604736).sum := by decide
  have hdescent : baseEnd_3604736 < baseStart_3604736 := by decide
  rcases family_descends (prefixWord ++ tailWord_3604736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3604739 : List Nat := [1, 1, 1, 3, 2, 3, 3, 1, 3, 2, 3]
def baseStart_3604739 : Nat := 118140960795 + 3604739 * 2 ^ 59
def prefixEnd_3604739 : Nat := 4983230072969 + 3 ^ 40 * 3604739 * 2
def baseEnd_3604739 : Nat := 1850963741007677175784613

theorem tailTrace_3604739 : CollatzResearch.WordTrace tailWord_3604739 prefixEnd_3604739 1850963741007677175784613 := by
  unfold tailWord_3604739
  simp only [CollatzResearch.WordTrace]
  refine ⟨131475632487653718252673271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87650421658435812168448847 131475632487653718252673271)
  ·
    refine ⟨197213448731480577379009907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131475632487653718252673271 197213448731480577379009907)
    ·
      refine ⟨295820173097220866068514861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197213448731480577379009907 295820173097220866068514861)
      ·
        refine ⟨110932564911457824775693073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 295820173097220866068514861 110932564911457824775693073)
        ·
          refine ⟨83199423683593368581769805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110932564911457824775693073 83199423683593368581769805)
          ·
            refine ⟨31199783881347513218163677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83199423683593368581769805 31199783881347513218163677)
            ·
              refine ⟨11699918955505317456811379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31199783881347513218163677 11699918955505317456811379)
              ·
                refine ⟨17549878433257976185217069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11699918955505317456811379 17549878433257976185217069)
                ·
                  refine ⟨6581204412471741069456401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17549878433257976185217069 6581204412471741069456401)
                  ·
                    refine ⟨4935903309353805802092301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6581204412471741069456401 4935903309353805802092301)
                    ·
                      refine ⟨1850963741007677175784613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4935903309353805802092301 1850963741007677175784613)
                      ·
                        rfl

theorem cell23_3604739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 1, 3, 2, 3].length) (baseStart_3604739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3604739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3604739 prefixEnd_3604739 := by exact prefixLift 3604739
  have htrace : WordTrace (prefixWord ++ tailWord_3604739) baseStart_3604739 baseEnd_3604739 := by
    simpa [prefixWord, tailWord_3604739, baseEnd_3604739] using wordTrace_append hprefix tailTrace_3604739
  have hstable : (prefixWord ++ tailWord_3604739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3604739).length < 2 ^ (prefixWord ++ tailWord_3604739).sum := by decide
  have hdescent : baseEnd_3604739 < baseStart_3604739 := by decide
  rcases family_descends (prefixWord ++ tailWord_3604739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3604776 : List Nat := [2, 1, 5, 1, 3, 2, 1, 8]
def baseStart_3604776 : Nat := 118140960795 + 3604776 * 2 ^ 59
def prefixEnd_3604776 : Nat := 4983230072969 + 3 ^ 40 * 3604776 * 2
def baseEnd_3604776 : Nat := 68554916288588649297109

theorem tailTrace_3604776 : CollatzResearch.WordTrace tailWord_3604776 prefixEnd_3604776 68554916288588649297109 := by
  unfold tailWord_3604776
  simp only [CollatzResearch.WordTrace]
  refine ⟨65738490994259836785885091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87651321325679782381180121 65738490994259836785885091)
  ·
    refine ⟨98607736491389755178827637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65738490994259836785885091 98607736491389755178827637)
    ·
      refine ⟨9244475296067789548015091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 98607736491389755178827637 9244475296067789548015091)
      ·
        refine ⟨13866712944101684322022637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9244475296067789548015091 13866712944101684322022637)
        ·
          refine ⟨5200017354038131620758489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13866712944101684322022637 5200017354038131620758489)
          ·
            refine ⟨3900013015528598715568867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5200017354038131620758489 3900013015528598715568867)
            ·
              refine ⟨5850019523292898073353301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3900013015528598715568867 5850019523292898073353301)
              ·
                refine ⟨68554916288588649297109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5850019523292898073353301 68554916288588649297109)
                ·
                  rfl

theorem cell23_3604776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 1, 8].length) (baseStart_3604776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3604776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3604776 prefixEnd_3604776 := by exact prefixLift 3604776
  have htrace : WordTrace (prefixWord ++ tailWord_3604776) baseStart_3604776 baseEnd_3604776 := by
    simpa [prefixWord, tailWord_3604776, baseEnd_3604776] using wordTrace_append hprefix tailTrace_3604776
  have hstable : (prefixWord ++ tailWord_3604776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3604776).length < 2 ^ (prefixWord ++ tailWord_3604776).sum := by decide
  have hdescent : baseEnd_3604776 < baseStart_3604776 := by decide
  rcases family_descends (prefixWord ++ tailWord_3604776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3604796 : List Nat := [2, 2, 2, 2, 1, 2, 1, 3, 3, 3, 2]
def baseStart_3604796 : Nat := 118140960795 + 3604796 * 2 ^ 59
def prefixEnd_3604796 : Nat := 4983230072969 + 3 ^ 40 * 3604796 * 2
def baseEnd_3604796 : Nat := 1850993009404983452771851

theorem tailTrace_3604796 : CollatzResearch.WordTrace tailWord_3604796 prefixEnd_3604796 1850993009404983452771851 := by
  unfold tailWord_3604796
  simp only [CollatzResearch.WordTrace]
  refine ⟨65738855724223608493749121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87651807632298144658332161 65738855724223608493749121)
  ·
    refine ⟨49304141793167706370311841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65738855724223608493749121 49304141793167706370311841)
    ·
      refine ⟨36978106344875779777733881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49304141793167706370311841 36978106344875779777733881)
      ·
        refine ⟨27733579758656834833300411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36978106344875779777733881 27733579758656834833300411)
        ·
          refine ⟨41600369637985252249950617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27733579758656834833300411 41600369637985252249950617)
          ·
            refine ⟨31200277228488939187462963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41600369637985252249950617 31200277228488939187462963)
            ·
              refine ⟨46800415842733408781194445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31200277228488939187462963 46800415842733408781194445)
              ·
                refine ⟨17550155941025028292947917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46800415842733408781194445 17550155941025028292947917)
                ·
                  refine ⟨6581308477884385609855469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17550155941025028292947917 6581308477884385609855469)
                  ·
                    refine ⟨2467990679206644603695801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6581308477884385609855469 2467990679206644603695801)
                    ·
                      refine ⟨1850993009404983452771851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2467990679206644603695801 1850993009404983452771851)
                      ·
                        rfl

theorem cell23_3604796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 3, 3, 3, 2].length) (baseStart_3604796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3604796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3604796 prefixEnd_3604796 := by exact prefixLift 3604796
  have htrace : WordTrace (prefixWord ++ tailWord_3604796) baseStart_3604796 baseEnd_3604796 := by
    simpa [prefixWord, tailWord_3604796, baseEnd_3604796] using wordTrace_append hprefix tailTrace_3604796
  have hstable : (prefixWord ++ tailWord_3604796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3604796).length < 2 ^ (prefixWord ++ tailWord_3604796).sum := by decide
  have hdescent : baseEnd_3604796 < baseStart_3604796 := by decide
  rcases family_descends (prefixWord ++ tailWord_3604796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3604804 : List Nat := [2, 3, 4, 1, 2, 1, 2, 3, 1, 2, 2]
def baseStart_3604804 : Nat := 118140960795 + 3604804 * 2 ^ 59
def prefixEnd_3604804 : Nat := 4983230072969 + 3 ^ 40 * 3604804 * 2
def baseEnd_3604804 : Nat := 1850997117250219421471815

theorem tailTrace_3604804 : CollatzResearch.WordTrace tailWord_3604804 prefixEnd_3604804 1850997117250219421471815 := by
  unfold tailWord_3604804
  simp only [CollatzResearch.WordTrace]
  refine ⟨65739001616209117176894733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87652002154945489569192977 65739001616209117176894733)
  ·
    refine ⟨24652125606078418941335525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65739001616209117176894733 24652125606078418941335525)
    ·
      refine ⟨4622273551139703551500411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24652125606078418941335525 4622273551139703551500411)
      ·
        refine ⟨6933410326709555327250617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4622273551139703551500411 6933410326709555327250617)
        ·
          refine ⟨5200057745032166495437963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6933410326709555327250617 5200057745032166495437963)
          ·
            refine ⟨7800086617548249743156945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5200057745032166495437963 7800086617548249743156945)
            ·
              refine ⟨5850064963161187307367709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7800086617548249743156945 5850064963161187307367709)
              ·
                refine ⟨2193774361185445240262891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5850064963161187307367709 2193774361185445240262891)
                ·
                  refine ⟨3290661541778167860394337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2193774361185445240262891 3290661541778167860394337)
                  ·
                    refine ⟨2467996156333625895295753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3290661541778167860394337 2467996156333625895295753)
                    ·
                      refine ⟨1850997117250219421471815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2467996156333625895295753 1850997117250219421471815)
                      ·
                        rfl

theorem cell23_3604804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 2, 3, 1, 2, 2].length) (baseStart_3604804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3604804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3604804 prefixEnd_3604804 := by exact prefixLift 3604804
  have htrace : WordTrace (prefixWord ++ tailWord_3604804) baseStart_3604804 baseEnd_3604804 := by
    simpa [prefixWord, tailWord_3604804, baseEnd_3604804] using wordTrace_append hprefix tailTrace_3604804
  have hstable : (prefixWord ++ tailWord_3604804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3604804).length < 2 ^ (prefixWord ++ tailWord_3604804).sum := by decide
  have hdescent : baseEnd_3604804 < baseStart_3604804 := by decide
  rcases family_descends (prefixWord ++ tailWord_3604804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3604820 : List Nat := [2, 4, 1, 1, 2, 4, 1, 2, 2, 1, 3]
def baseStart_3604820 : Nat := 118140960795 + 3604820 * 2 ^ 59
def prefixEnd_3604820 : Nat := 4983230072969 + 3 ^ 40 * 3604820 * 2
def baseEnd_3604820 : Nat := 1851005332940691358871741

theorem tailTrace_3604820 : CollatzResearch.WordTrace tailWord_3604820 prefixEnd_3604820 1851005332940691358871741 := by
  unfold tailWord_3604820
  simp only [CollatzResearch.WordTrace]
  refine ⟨65739293400180134543185957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87652391200240179390914609 65739293400180134543185957)
  ·
    refine ⟨12326117512533775226847367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65739293400180134543185957 12326117512533775226847367)
    ·
      refine ⟨18489176268800662840271051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12326117512533775226847367 18489176268800662840271051)
      ·
        refine ⟨27733764403200994260406577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18489176268800662840271051 27733764403200994260406577)
        ·
          refine ⟨20800323302400745695304933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27733764403200994260406577 20800323302400745695304933)
          ·
            refine ⟨3900060619200139817869675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20800323302400745695304933 3900060619200139817869675)
            ·
              refine ⟨5850090928800209726804513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3900060619200139817869675 5850090928800209726804513)
              ·
                refine ⟨4387568196600157295103385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5850090928800209726804513 4387568196600157295103385)
                ·
                  refine ⟨3290676147450117971327539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4387568196600157295103385 3290676147450117971327539)
                  ·
                    refine ⟨4936014221175176956991309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3290676147450117971327539 4936014221175176956991309)
                    ·
                      refine ⟨1851005332940691358871741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4936014221175176956991309 1851005332940691358871741)
                      ·
                        rfl

theorem cell23_3604820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 1, 2, 2, 1, 3].length) (baseStart_3604820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3604820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3604820 prefixEnd_3604820 := by exact prefixLift 3604820
  have htrace : WordTrace (prefixWord ++ tailWord_3604820) baseStart_3604820 baseEnd_3604820 := by
    simpa [prefixWord, tailWord_3604820, baseEnd_3604820] using wordTrace_append hprefix tailTrace_3604820
  have hstable : (prefixWord ++ tailWord_3604820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3604820).length < 2 ^ (prefixWord ++ tailWord_3604820).sum := by decide
  have hdescent : baseEnd_3604820 < baseStart_3604820 := by decide
  rcases family_descends (prefixWord ++ tailWord_3604820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3604889 : List Nat := [1, 2, 1, 2, 1, 4, 3, 1, 1, 2, 5]
def baseStart_3604889 : Nat := 118140960795 + 3604889 * 2 ^ 59
def prefixEnd_3604889 : Nat := 4983230072969 + 3 ^ 40 * 3604889 * 2
def baseEnd_3604889 : Nat := 1851040763105851588908923

theorem tailTrace_3604889 : CollatzResearch.WordTrace tailWord_3604889 prefixEnd_3604889 1851040763105851588908923 := by
  unfold tailWord_3604889
  simp only [CollatzResearch.WordTrace]
  refine ⟨131481103437110293870633721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87654068958073529247089147 131481103437110293870633721)
  ·
    refine ⟨98610827577832720402975291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131481103437110293870633721 98610827577832720402975291)
    ·
      refine ⟨147916241366749080604462937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98610827577832720402975291 147916241366749080604462937)
      ·
        refine ⟨110937181025061810453347203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147916241366749080604462937 110937181025061810453347203)
        ·
          refine ⟨166405771537592715680020805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110937181025061810453347203 166405771537592715680020805)
          ·
            refine ⟨31201082163298634190003901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 166405771537592715680020805 31201082163298634190003901)
            ·
              refine ⟨11700405811236987821251463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31201082163298634190003901 11700405811236987821251463)
              ·
                refine ⟨17550608716855481731877195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11700405811236987821251463 17550608716855481731877195)
                ·
                  refine ⟨26325913075283222597815793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17550608716855481731877195 26325913075283222597815793)
                  ·
                    refine ⟨19744434806462416948361845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26325913075283222597815793 19744434806462416948361845)
                    ·
                      refine ⟨1851040763105851588908923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19744434806462416948361845 1851040763105851588908923)
                      ·
                        rfl

theorem cell23_3604889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 1, 1, 2, 5].length) (baseStart_3604889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3604889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3604889 prefixEnd_3604889 := by exact prefixLift 3604889
  have htrace : WordTrace (prefixWord ++ tailWord_3604889) baseStart_3604889 baseEnd_3604889 := by
    simpa [prefixWord, tailWord_3604889, baseEnd_3604889] using wordTrace_append hprefix tailTrace_3604889
  have hstable : (prefixWord ++ tailWord_3604889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3604889).length < 2 ^ (prefixWord ++ tailWord_3604889).sum := by decide
  have hdescent : baseEnd_3604889 < baseStart_3604889 := by decide
  rcases family_descends (prefixWord ++ tailWord_3604889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3604894 : List Nat := [4, 3, 1, 2, 1, 1, 4, 1, 2, 2, 2]
def baseStart_3604894 : Nat := 118140960795 + 3604894 * 2 ^ 59
def prefixEnd_3604894 : Nat := 4983230072969 + 3 ^ 40 * 3604894 * 2
def baseEnd_3604894 : Nat := 1851043330509124069346401

theorem tailTrace_3604894 : CollatzResearch.WordTrace tailWord_3604894 prefixEnd_3604894 1851043330509124069346401 := by
  unfold tailWord_3604894
  simp only [CollatzResearch.WordTrace]
  refine ⟨16435160725261522465570717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87654190534728119816377157 16435160725261522465570717)
  ·
    refine ⟨6163185271973070924589019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16435160725261522465570717 6163185271973070924589019)
    ·
      refine ⟨9244777907959606386883529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6163185271973070924589019 9244777907959606386883529)
      ·
        refine ⟨6933583430969704790162647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9244777907959606386883529 6933583430969704790162647)
        ·
          refine ⟨10400375146454557185243971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6933583430969704790162647 10400375146454557185243971)
          ·
            refine ⟨15600562719681835777865957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10400375146454557185243971 15600562719681835777865957)
            ·
              refine ⟨2925105509940344208349867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15600562719681835777865957 2925105509940344208349867)
              ·
                refine ⟨4387658264910516312524801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2925105509940344208349867 4387658264910516312524801)
                ·
                  refine ⟨3290743698682887234393601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4387658264910516312524801 3290743698682887234393601)
                  ·
                    refine ⟨2468057774012165425795201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3290743698682887234393601 2468057774012165425795201)
                    ·
                      refine ⟨1851043330509124069346401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2468057774012165425795201 1851043330509124069346401)
                      ·
                        rfl

theorem cell23_3604894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 4, 1, 2, 2, 2].length) (baseStart_3604894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3604894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3604894 prefixEnd_3604894 := by exact prefixLift 3604894
  have htrace : WordTrace (prefixWord ++ tailWord_3604894) baseStart_3604894 baseEnd_3604894 := by
    simpa [prefixWord, tailWord_3604894, baseEnd_3604894] using wordTrace_append hprefix tailTrace_3604894
  have hstable : (prefixWord ++ tailWord_3604894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3604894).length < 2 ^ (prefixWord ++ tailWord_3604894).sum := by decide
  have hdescent : baseEnd_3604894 < baseStart_3604894 := by decide
  rcases family_descends (prefixWord ++ tailWord_3604894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3604950 : List Nat := [5, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2]
def baseStart_3604950 : Nat := 118140960795 + 3604950 * 2 ^ 59
def prefixEnd_3604950 : Nat := 4983230072969 + 3 ^ 40 * 3604950 * 2
def baseEnd_3604950 : Nat := 1851072085425775850246143

theorem tailTrace_3604950 : CollatzResearch.WordTrace tailWord_3604950 prefixEnd_3604950 1851072085425775850246143 := by
  unfold tailWord_3604950
  simp only [CollatzResearch.WordTrace]
  refine ⟨8217708018118081330537769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 87655552193259534192402869 8217708018118081330537769)
  ·
    refine ⟨6163281013588560997903327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8217708018118081330537769 6163281013588560997903327)
    ·
      refine ⟨9244921520382841496854991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6163281013588560997903327 9244921520382841496854991)
      ·
        refine ⟨13867382280574262245282487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9244921520382841496854991 13867382280574262245282487)
        ·
          refine ⟨20801073420861393367923731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13867382280574262245282487 20801073420861393367923731)
          ·
            refine ⟨31201610131292090051885597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20801073420861393367923731 31201610131292090051885597)
            ·
              refine ⟨11700603799234533769457099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31201610131292090051885597 11700603799234533769457099)
              ·
                refine ⟨17550905698851800654185649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11700603799234533769457099 17550905698851800654185649)
                ·
                  refine ⟨13163179274138850490639237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17550905698851800654185649 13163179274138850490639237)
                  ·
                    refine ⟨2468096113901034466994857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13163179274138850490639237 2468096113901034466994857)
                    ·
                      refine ⟨1851072085425775850246143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2468096113901034466994857 1851072085425775850246143)
                      ·
                        rfl

theorem cell23_3604950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2].length) (baseStart_3604950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3604950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3604950 prefixEnd_3604950 := by exact prefixLift 3604950
  have htrace : WordTrace (prefixWord ++ tailWord_3604950) baseStart_3604950 baseEnd_3604950 := by
    simpa [prefixWord, tailWord_3604950, baseEnd_3604950] using wordTrace_append hprefix tailTrace_3604950
  have hstable : (prefixWord ++ tailWord_3604950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3604950).length < 2 ^ (prefixWord ++ tailWord_3604950).sum := by decide
  have hdescent : baseEnd_3604950 < baseStart_3604950 := by decide
  rcases family_descends (prefixWord ++ tailWord_3604950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3604970 : List Nat := [3, 1, 3, 1, 3, 3, 1, 1, 2, 2, 3]
def baseStart_3604970 : Nat := 118140960795 + 3604970 * 2 ^ 59
def prefixEnd_3604970 : Nat := 4983230072969 + 3 ^ 40 * 3604970 * 2
def baseEnd_3604970 : Nat := 1851082355038865771996051

theorem tailTrace_3604970 : CollatzResearch.WordTrace tailWord_3604970 prefixEnd_3604970 1851082355038865771996051 := by
  unfold tailWord_3604970
  simp only [CollatzResearch.WordTrace]
  refine ⟨32871014437454211176083091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87656038499877896469554909 32871014437454211176083091)
  ·
    refine ⟨49306521656181316764124637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32871014437454211176083091 49306521656181316764124637)
    ·
      refine ⟨18489945621067993786546739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49306521656181316764124637 18489945621067993786546739)
      ·
        refine ⟨27734918431601990679820109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18489945621067993786546739 27734918431601990679820109)
        ·
          refine ⟨10400594411850746504932541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27734918431601990679820109 10400594411850746504932541)
          ·
            refine ⟨3900222904444029939349703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10400594411850746504932541 3900222904444029939349703)
            ·
              refine ⟨5850334356666044909024555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3900222904444029939349703 5850334356666044909024555)
              ·
                refine ⟨8775501534999067363536833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5850334356666044909024555 8775501534999067363536833)
                ·
                  refine ⟨6581626151249300522652625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8775501534999067363536833 6581626151249300522652625)
                  ·
                    refine ⟨4936219613436975391989469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6581626151249300522652625 4936219613436975391989469)
                    ·
                      refine ⟨1851082355038865771996051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4936219613436975391989469 1851082355038865771996051)
                      ·
                        rfl

theorem cell23_3604970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 1, 1, 2, 2, 3].length) (baseStart_3604970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3604970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3604970 prefixEnd_3604970 := by exact prefixLift 3604970
  have htrace : WordTrace (prefixWord ++ tailWord_3604970) baseStart_3604970 baseEnd_3604970 := by
    simpa [prefixWord, tailWord_3604970, baseEnd_3604970] using wordTrace_append hprefix tailTrace_3604970
  have hstable : (prefixWord ++ tailWord_3604970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3604970).length < 2 ^ (prefixWord ++ tailWord_3604970).sum := by decide
  have hdescent : baseEnd_3604970 < baseStart_3604970 := by decide
  rcases family_descends (prefixWord ++ tailWord_3604970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3605026 : List Nat := [3, 3, 1, 1, 1, 1, 1, 1, 5, 1, 5]
def baseStart_3605026 : Nat := 118140960795 + 3605026 * 2 ^ 59
def prefixEnd_3605026 : Nat := 4983230072969 + 3 ^ 40 * 3605026 * 2
def baseEnd_3605026 : Nat := 1851111109955517552895793

theorem tailTrace_3605026 : CollatzResearch.WordTrace tailWord_3605026 prefixEnd_3605026 1851111109955517552895793 := by
  unfold tailWord_3605026
  simp only [CollatzResearch.WordTrace]
  refine ⟨32871525059403491567092733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87657400158409310845580621 32871525059403491567092733)
  ·
    refine ⟨12326821897276309337659775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32871525059403491567092733 12326821897276309337659775)
    ·
      refine ⟨18490232845914464006489663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12326821897276309337659775 18490232845914464006489663)
      ·
        refine ⟨27735349268871696009734495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18490232845914464006489663 27735349268871696009734495)
        ·
          refine ⟨41603023903307544014601743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27735349268871696009734495 41603023903307544014601743)
          ·
            refine ⟨62404535854961316021902615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41603023903307544014601743 62404535854961316021902615)
            ·
              refine ⟨93606803782441974032853923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62404535854961316021902615 93606803782441974032853923)
              ·
                refine ⟨140410205673662961049280885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93606803782441974032853923 140410205673662961049280885)
                ·
                  refine ⟨13163456781905902598370083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 140410205673662961049280885 13163456781905902598370083)
                  ·
                    refine ⟨19745185172858853897555125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13163456781905902598370083 19745185172858853897555125)
                    ·
                      refine ⟨1851111109955517552895793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19745185172858853897555125 1851111109955517552895793)
                      ·
                        rfl

theorem cell23_3605026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 5, 1, 5].length) (baseStart_3605026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3605026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3605026 prefixEnd_3605026 := by exact prefixLift 3605026
  have htrace : WordTrace (prefixWord ++ tailWord_3605026) baseStart_3605026 baseEnd_3605026 := by
    simpa [prefixWord, tailWord_3605026, baseEnd_3605026] using wordTrace_append hprefix tailTrace_3605026
  have hstable : (prefixWord ++ tailWord_3605026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3605026).length < 2 ^ (prefixWord ++ tailWord_3605026).sum := by decide
  have hdescent : baseEnd_3605026 < baseStart_3605026 := by decide
  rcases family_descends (prefixWord ++ tailWord_3605026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3605034 : List Nat := [3, 1, 4, 1, 1, 4, 1, 3, 1, 1, 3]
def baseStart_3605034 : Nat := 118140960795 + 3605034 * 2 ^ 59
def prefixEnd_3605034 : Nat := 4983230072969 + 3 ^ 40 * 3605034 * 2
def baseEnd_3605034 : Nat := 1851115217800753521595757

theorem tailTrace_3605034 : CollatzResearch.WordTrace tailWord_3605034 prefixEnd_3605034 1851115217800753521595757 := by
  unfold tailWord_3605034
  simp only [CollatzResearch.WordTrace]
  refine ⟨32871598005396245908665539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87657594681056655756441437 32871598005396245908665539)
  ·
    refine ⟨49307397008094368862998309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32871598005396245908665539 49307397008094368862998309)
    ·
      refine ⟨9245136939017694161812183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49307397008094368862998309 9245136939017694161812183)
      ·
        refine ⟨13867705408526541242718275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9245136939017694161812183 13867705408526541242718275)
        ·
          refine ⟨20801558112789811864077413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13867705408526541242718275 20801558112789811864077413)
          ·
            refine ⟨3900292146148089724514515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20801558112789811864077413 3900292146148089724514515)
            ·
              refine ⟨5850438219222134586771773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3900292146148089724514515 5850438219222134586771773)
              ·
                refine ⟨2193914332208300470039415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5850438219222134586771773 2193914332208300470039415)
                ·
                  refine ⟨3290871498312450705059123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2193914332208300470039415 3290871498312450705059123)
                  ·
                    refine ⟨4936307247468676057588685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3290871498312450705059123 4936307247468676057588685)
                    ·
                      refine ⟨1851115217800753521595757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4936307247468676057588685 1851115217800753521595757)
                      ·
                        rfl

theorem cell23_3605034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 1, 3, 1, 1, 3].length) (baseStart_3605034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3605034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3605034 prefixEnd_3605034 := by exact prefixLift 3605034
  have htrace : WordTrace (prefixWord ++ tailWord_3605034) baseStart_3605034 baseEnd_3605034 := by
    simpa [prefixWord, tailWord_3605034, baseEnd_3605034] using wordTrace_append hprefix tailTrace_3605034
  have hstable : (prefixWord ++ tailWord_3605034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3605034).length < 2 ^ (prefixWord ++ tailWord_3605034).sum := by decide
  have hdescent : baseEnd_3605034 < baseStart_3605034 := by decide
  rcases family_descends (prefixWord ++ tailWord_3605034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3605036 : List Nat := [2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 4]
def baseStart_3605036 : Nat := 118140960795 + 3605036 * 2 ^ 59
def prefixEnd_3605036 : Nat := 4983230072969 + 3 ^ 40 * 3605036 * 2
def baseEnd_3605036 : Nat := 1851116244762062513770747

theorem tailTrace_3605036 : CollatzResearch.WordTrace tailWord_3605036 prefixEnd_3605036 1851116244762062513770747 := by
  unfold tailWord_3605036
  simp only [CollatzResearch.WordTrace]
  refine ⟨65743232483788868988117481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87657643311718491984156641 65743232483788868988117481)
  ·
    refine ⟨49307424362841651741088111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65743232483788868988117481 49307424362841651741088111)
    ·
      refine ⟨73961136544262477611632167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49307424362841651741088111 73961136544262477611632167)
      ·
        refine ⟨110941704816393716417448251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73961136544262477611632167 110941704816393716417448251)
        ·
          refine ⟨166412557224590574626172377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110941704816393716417448251 166412557224590574626172377)
          ·
            refine ⟨124809417918442930969629283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166412557224590574626172377 124809417918442930969629283)
            ·
              refine ⟨187214126877664396454443925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124809417918442930969629283 187214126877664396454443925)
              ·
                refine ⟨8775662197390518583802059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 187214126877664396454443925 8775662197390518583802059)
                ·
                  refine ⟨13163493296085777875703089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8775662197390518583802059 13163493296085777875703089)
                  ·
                    refine ⟨9872619972064333406777317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13163493296085777875703089 9872619972064333406777317)
                    ·
                      refine ⟨1851116244762062513770747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9872619972064333406777317 1851116244762062513770747)
                      ·
                        rfl

theorem cell23_3605036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 4].length) (baseStart_3605036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3605036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3605036 prefixEnd_3605036 := by exact prefixLift 3605036
  have htrace : WordTrace (prefixWord ++ tailWord_3605036) baseStart_3605036 baseEnd_3605036 := by
    simpa [prefixWord, tailWord_3605036, baseEnd_3605036] using wordTrace_append hprefix tailTrace_3605036
  have hstable : (prefixWord ++ tailWord_3605036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3605036).length < 2 ^ (prefixWord ++ tailWord_3605036).sum := by decide
  have hdescent : baseEnd_3605036 < baseStart_3605036 := by decide
  rcases family_descends (prefixWord ++ tailWord_3605036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3605043 : List Nat := [1, 1, 1, 2, 4, 2, 1, 5, 1, 2, 3]
def baseStart_3605043 : Nat := 118140960795 + 3605043 * 2 ^ 59
def prefixEnd_3605043 : Nat := 4983230072969 + 3 ^ 40 * 3605043 * 2
def baseEnd_3605043 : Nat := 1851119839126643986383215

theorem tailTrace_3605043 : CollatzResearch.WordTrace tailWord_3605043 prefixEnd_3605043 1851119839126643986383215 := by
  unfold tailWord_3605043
  simp only [CollatzResearch.WordTrace]
  refine ⟨131486720278552378171739783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87657813519034918781159855 131486720278552378171739783)
  ·
    refine ⟨197230080417828567257609675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131486720278552378171739783 197230080417828567257609675)
    ·
      refine ⟨295845120626742850886414513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197230080417828567257609675 295845120626742850886414513)
      ·
        refine ⟨221883840470057138164810885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 295845120626742850886414513 221883840470057138164810885)
        ·
          refine ⟨41603220088135713405902041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 221883840470057138164810885 41603220088135713405902041)
          ·
            refine ⟨31202415066101785054426531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41603220088135713405902041 31202415066101785054426531)
            ·
              refine ⟨46803622599152677581639797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31202415066101785054426531 46803622599152677581639797)
              ·
                refine ⟨4387839618670563523278731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46803622599152677581639797 4387839618670563523278731)
                ·
                  refine ⟨6581759428005845284918097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4387839618670563523278731 6581759428005845284918097)
                  ·
                    refine ⟨4936319571004383963688573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6581759428005845284918097 4936319571004383963688573)
                    ·
                      refine ⟨1851119839126643986383215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4936319571004383963688573 1851119839126643986383215)
                      ·
                        rfl

theorem cell23_3605043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 5, 1, 2, 3].length) (baseStart_3605043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3605043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3605043 prefixEnd_3605043 := by exact prefixLift 3605043
  have htrace : WordTrace (prefixWord ++ tailWord_3605043) baseStart_3605043 baseEnd_3605043 := by
    simpa [prefixWord, tailWord_3605043, baseEnd_3605043] using wordTrace_append hprefix tailTrace_3605043
  have hstable : (prefixWord ++ tailWord_3605043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3605043).length < 2 ^ (prefixWord ++ tailWord_3605043).sum := by decide
  have hdescent : baseEnd_3605043 < baseStart_3605043 := by decide
  rcases family_descends (prefixWord ++ tailWord_3605043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3605044 : List Nat := [2, 5, 1, 3, 1, 1, 1, 2, 2, 3, 2]
def baseStart_3605044 : Nat := 118140960795 + 3605044 * 2 ^ 59
def prefixEnd_3605044 : Nat := 4983230072969 + 3 ^ 40 * 3605044 * 2
def baseEnd_3605044 : Nat := 1851120352607298482470711

theorem tailTrace_3605044 : CollatzResearch.WordTrace tailWord_3605044 prefixEnd_3605044 1851120352607298482470711 := by
  unfold tailWord_3605044
  simp only [CollatzResearch.WordTrace]
  refine ⟨65743378375774377671263093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87657837834365836895017457 65743378375774377671263093)
  ·
    refine ⟨6163441722728847906680915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 65743378375774377671263093 6163441722728847906680915)
    ·
      refine ⟨9245162584093271860021373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6163441722728847906680915 9245162584093271860021373)
      ·
        refine ⟨3466935969034976947508015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9245162584093271860021373 3466935969034976947508015)
        ·
          refine ⟨5200403953552465421262023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3466935969034976947508015 5200403953552465421262023)
          ·
            refine ⟨7800605930328698131893035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5200403953552465421262023 7800605930328698131893035)
            ·
              refine ⟨11700908895493047197839553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7800605930328698131893035 11700908895493047197839553)
              ·
                refine ⟨8775681671619785398379665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11700908895493047197839553 8775681671619785398379665)
                ·
                  refine ⟨6581761253714839048784749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8775681671619785398379665 6581761253714839048784749)
                  ·
                    refine ⟨2468160470143064643294281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6581761253714839048784749 2468160470143064643294281)
                    ·
                      refine ⟨1851120352607298482470711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2468160470143064643294281 1851120352607298482470711)
                      ·
                        rfl

theorem cell23_3605044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_3605044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3605044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3605044 prefixEnd_3605044 := by exact prefixLift 3605044
  have htrace : WordTrace (prefixWord ++ tailWord_3605044) baseStart_3605044 baseEnd_3605044 := by
    simpa [prefixWord, tailWord_3605044, baseEnd_3605044] using wordTrace_append hprefix tailTrace_3605044
  have hstable : (prefixWord ++ tailWord_3605044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3605044).length < 2 ^ (prefixWord ++ tailWord_3605044).sum := by decide
  have hdescent : baseEnd_3605044 < baseStart_3605044 := by decide
  rcases family_descends (prefixWord ++ tailWord_3605044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3605057 : List Nat := [1, 2, 5, 1, 1, 2, 3, 1, 3, 2, 2]
def baseStart_3605057 : Nat := 118140960795 + 3605057 * 2 ^ 59
def prefixEnd_3605057 : Nat := 4983230072969 + 3 ^ 40 * 3605057 * 2
def baseEnd_3605057 : Nat := 1851127027855806931608151

theorem tailTrace_3605057 : CollatzResearch.WordTrace tailWord_3605057 prefixEnd_3605057 1851127027855806931608151 := by
  unfold tailWord_3605057
  simp only [CollatzResearch.WordTrace]
  refine ⟨131487230900501658562749425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87658153933667772375166283 131487230900501658562749425)
  ·
    refine ⟨98615423175376243922062069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131487230900501658562749425 98615423175376243922062069)
    ·
      refine ⟨9245195922691522867693319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 98615423175376243922062069 9245195922691522867693319)
      ·
        refine ⟨13867793884037284301539979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9245195922691522867693319 13867793884037284301539979)
        ·
          refine ⟨20801690826055926452309969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13867793884037284301539979 20801690826055926452309969)
          ·
            refine ⟨15601268119541944839232477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20801690826055926452309969 15601268119541944839232477)
            ·
              refine ⟨5850475544828229314712179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15601268119541944839232477 5850475544828229314712179)
              ·
                refine ⟨8775713317242343972068269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5850475544828229314712179 8775713317242343972068269)
                ·
                  refine ⟨3290892493965878989525601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8775713317242343972068269 3290892493965878989525601)
                  ·
                    refine ⟨2468169370474409242144201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3290892493965878989525601 2468169370474409242144201)
                    ·
                      refine ⟨1851127027855806931608151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2468169370474409242144201 1851127027855806931608151)
                      ·
                        rfl

theorem cell23_3605057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3, 1, 3, 2, 2].length) (baseStart_3605057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3605057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3605057 prefixEnd_3605057 := by exact prefixLift 3605057
  have htrace : WordTrace (prefixWord ++ tailWord_3605057) baseStart_3605057 baseEnd_3605057 := by
    simpa [prefixWord, tailWord_3605057, baseEnd_3605057] using wordTrace_append hprefix tailTrace_3605057
  have hstable : (prefixWord ++ tailWord_3605057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3605057).length < 2 ^ (prefixWord ++ tailWord_3605057).sum := by decide
  have hdescent : baseEnd_3605057 < baseStart_3605057 := by decide
  rcases family_descends (prefixWord ++ tailWord_3605057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3605100 : List Nat := [2, 2, 1, 1, 3, 1, 2, 5, 1, 3, 2]
def baseStart_3605100 : Nat := 118140960795 + 3605100 * 2 ^ 59
def prefixEnd_3605100 : Nat := 4983230072969 + 3 ^ 40 * 3605100 * 2
def baseEnd_3605100 : Nat := 1851149107523950263370453

theorem tailTrace_3605100 : CollatzResearch.WordTrace tailWord_3605100 prefixEnd_3605100 1851149107523950263370453 := by
  unfold tailWord_3605100
  simp only [CollatzResearch.WordTrace]
  refine ⟨65744399619672938453282377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87659199492897251271043169 65744399619672938453282377)
  ·
    refine ⟨49308299714754703839961783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65744399619672938453282377 49308299714754703839961783)
    ·
      refine ⟨73962449572132055759942675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49308299714754703839961783 73962449572132055759942675)
      ·
        refine ⟨110943674358198083639914013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73962449572132055759942675 110943674358198083639914013)
        ·
          refine ⟨41603877884324281364967755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110943674358198083639914013 41603877884324281364967755)
          ·
            refine ⟨62405816826486422047451633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41603877884324281364967755 62405816826486422047451633)
            ·
              refine ⟨46804362619864816535588725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62405816826486422047451633 46804362619864816535588725)
              ·
                refine ⟨4387908995612326550211443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46804362619864816535588725 4387908995612326550211443)
                ·
                  refine ⟨6581863493418489825317165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4387908995612326550211443 6581863493418489825317165)
                  ·
                    refine ⟨2468198810031933684493937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6581863493418489825317165 2468198810031933684493937)
                    ·
                      refine ⟨1851149107523950263370453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2468198810031933684493937 1851149107523950263370453)
                      ·
                        rfl

theorem cell23_3605100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 3, 2].length) (baseStart_3605100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3605100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3605100 prefixEnd_3605100 := by exact prefixLift 3605100
  have htrace : WordTrace (prefixWord ++ tailWord_3605100) baseStart_3605100 baseEnd_3605100 := by
    simpa [prefixWord, tailWord_3605100, baseEnd_3605100] using wordTrace_append hprefix tailTrace_3605100
  have hstable : (prefixWord ++ tailWord_3605100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3605100).length < 2 ^ (prefixWord ++ tailWord_3605100).sum := by decide
  have hdescent : baseEnd_3605100 < baseStart_3605100 := by decide
  rcases family_descends (prefixWord ++ tailWord_3605100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3605116 : List Nat := [2, 2, 2, 1, 1, 2, 2, 2, 1, 3, 5]
def baseStart_3605116 : Nat := 118140960795 + 3605116 * 2 ^ 59
def prefixEnd_3605116 : Nat := 4983230072969 + 3 ^ 40 * 3605116 * 2
def baseEnd_3605116 : Nat := 1851157323214422200770379

theorem tailTrace_3605116 : CollatzResearch.WordTrace tailWord_3605116 prefixEnd_3605116 1851157323214422200770379 := by
  unfold tailWord_3605116
  simp only [CollatzResearch.WordTrace]
  refine ⟨65744691403643955819573601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87659588538191941092764801 65744691403643955819573601)
  ·
    refine ⟨49308518552732966864680201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65744691403643955819573601 49308518552732966864680201)
    ·
      refine ⟨36981388914549725148510151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49308518552732966864680201 36981388914549725148510151)
      ·
        refine ⟨55472083371824587722765227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36981388914549725148510151 55472083371824587722765227)
        ·
          refine ⟨83208125057736881584147841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55472083371824587722765227 83208125057736881584147841)
          ·
            refine ⟨62406093793302661188110881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83208125057736881584147841 62406093793302661188110881)
            ·
              refine ⟨46804570344976995891083161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62406093793302661188110881 46804570344976995891083161)
              ·
                refine ⟨35103427758732746918312371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46804570344976995891083161 35103427758732746918312371)
                ·
                  refine ⟨52655141638099120377468557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35103427758732746918312371 52655141638099120377468557)
                  ·
                    refine ⟨19745678114287170141550709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52655141638099120377468557 19745678114287170141550709)
                    ·
                      refine ⟨1851157323214422200770379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19745678114287170141550709 1851157323214422200770379)
                      ·
                        rfl

theorem cell23_3605116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 1, 3, 5].length) (baseStart_3605116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3605116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3605116 prefixEnd_3605116 := by exact prefixLift 3605116
  have htrace : WordTrace (prefixWord ++ tailWord_3605116) baseStart_3605116 baseEnd_3605116 := by
    simpa [prefixWord, tailWord_3605116, baseEnd_3605116] using wordTrace_append hprefix tailTrace_3605116
  have hstable : (prefixWord ++ tailWord_3605116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3605116).length < 2 ^ (prefixWord ++ tailWord_3605116).sum := by decide
  have hdescent : baseEnd_3605116 < baseStart_3605116 := by decide
  rcases family_descends (prefixWord ++ tailWord_3605116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3605204 : List Nat := [2, 4, 1, 3, 2, 2, 1, 3, 5]
def baseStart_3605204 : Nat := 118140960795 + 3605204 * 2 ^ 59
def prefixEnd_3605204 : Nat := 4983230072969 + 3 ^ 40 * 3605204 * 2
def baseEnd_3605204 : Nat := 205689167723557539607775

theorem tailTrace_3605204 : CollatzResearch.WordTrace tailWord_3605204 prefixEnd_3605204 205689167723557539607775 := by
  unfold tailWord_3605204
  simp only [CollatzResearch.WordTrace]
  refine ⟨65746296215484551334175333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87661728287312735112233777 65746296215484551334175333)
  ·
    refine ⟨12327430540403353375157875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65746296215484551334175333 12327430540403353375157875)
    ·
      refine ⟨18491145810605030062736813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12327430540403353375157875 18491145810605030062736813)
      ·
        refine ⟨6934179678976886273526305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18491145810605030062736813 6934179678976886273526305)
        ·
          refine ⟨5200634759232664705144729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6934179678976886273526305 5200634759232664705144729)
          ·
            refine ⟨3900476069424498528858547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5200634759232664705144729 3900476069424498528858547)
            ·
              refine ⟨5850714104136747793287821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3900476069424498528858547 5850714104136747793287821)
              ·
                refine ⟨2194017789051280422482933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5850714104136747793287821 2194017789051280422482933)
                ·
                  refine ⟨205689167723557539607775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2194017789051280422482933 205689167723557539607775)
                  ·
                    rfl

theorem cell23_3605204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 1, 3, 5].length) (baseStart_3605204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3605204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3605204 prefixEnd_3605204 := by exact prefixLift 3605204
  have htrace : WordTrace (prefixWord ++ tailWord_3605204) baseStart_3605204 baseEnd_3605204 := by
    simpa [prefixWord, tailWord_3605204, baseEnd_3605204] using wordTrace_append hprefix tailTrace_3605204
  have hstable : (prefixWord ++ tailWord_3605204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3605204).length < 2 ^ (prefixWord ++ tailWord_3605204).sum := by decide
  have hdescent : baseEnd_3605204 < baseStart_3605204 := by decide
  rcases family_descends (prefixWord ++ tailWord_3605204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3605220 : List Nat := [2, 3, 1, 1, 1, 5, 1, 2, 2, 1, 4]
def baseStart_3605220 : Nat := 118140960795 + 3605220 * 2 ^ 59
def prefixEnd_3605220 : Nat := 4983230072969 + 3 ^ 40 * 3605220 * 2
def baseEnd_3605220 : Nat := 1851210725202489793869901

theorem tailTrace_3605220 : CollatzResearch.WordTrace tailWord_3605220 prefixEnd_3605220 1851210725202489793869901 := by
  unfold tailWord_3605220
  simp only [CollatzResearch.WordTrace]
  refine ⟨65746587999455568700466557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87662117332607424933955409 65746587999455568700466557)
  ·
    refine ⟨24654970499795838262674959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65746587999455568700466557 24654970499795838262674959)
    ·
      refine ⟨36982455749693757394012439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24654970499795838262674959 36982455749693757394012439)
      ·
        refine ⟨55473683624540636091018659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36982455749693757394012439 55473683624540636091018659)
        ·
          refine ⟨83210525436810954136527989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55473683624540636091018659 83210525436810954136527989)
          ·
            refine ⟨7800986759701026950299499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 83210525436810954136527989 7800986759701026950299499)
            ·
              refine ⟨11701480139551540425449249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7800986759701026950299499 11701480139551540425449249)
              ·
                refine ⟨8776110104663655319086937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11701480139551540425449249 8776110104663655319086937)
                ·
                  refine ⟨6582082578497741489315203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8776110104663655319086937 6582082578497741489315203)
                  ·
                    refine ⟨9873123867746612233972805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6582082578497741489315203 9873123867746612233972805)
                    ·
                      refine ⟨1851210725202489793869901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9873123867746612233972805 1851210725202489793869901)
                      ·
                        rfl

theorem cell23_3605220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 2, 2, 1, 4].length) (baseStart_3605220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3605220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3605220 prefixEnd_3605220 := by exact prefixLift 3605220
  have htrace : WordTrace (prefixWord ++ tailWord_3605220) baseStart_3605220 baseEnd_3605220 := by
    simpa [prefixWord, tailWord_3605220, baseEnd_3605220] using wordTrace_append hprefix tailTrace_3605220
  have hstable : (prefixWord ++ tailWord_3605220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3605220).length < 2 ^ (prefixWord ++ tailWord_3605220).sum := by decide
  have hdescent : baseEnd_3605220 < baseStart_3605220 := by decide
  rcases family_descends (prefixWord ++ tailWord_3605220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3605253 : List Nat := [1, 3, 1, 1, 2, 1, 1, 3, 2, 5, 3]
def baseStart_3605253 : Nat := 118140960795 + 3605253 * 2 ^ 59
def prefixEnd_3605253 : Nat := 4983230072969 + 3 ^ 40 * 3605253 * 2
def baseEnd_3605253 : Nat := 1851227670064088164757249

theorem tailTrace_3605253 : CollatzResearch.WordTrace tailWord_3605253 prefixEnd_3605253 1851227670064088164757249 := by
  unfold tailWord_3605253
  simp only [CollatzResearch.WordTrace]
  refine ⟨131494379607791584036884413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87662919738527722691256275 131494379607791584036884413)
  ·
    refine ⟨49310392352921844013831655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131494379607791584036884413 49310392352921844013831655)
    ·
      refine ⟨73965588529382766020747483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49310392352921844013831655 73965588529382766020747483)
      ·
        refine ⟨110948382794074149031121225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73965588529382766020747483 110948382794074149031121225)
        ·
          refine ⟨83211287095555611773340919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110948382794074149031121225 83211287095555611773340919)
          ·
            refine ⟨124816930643333417660011379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83211287095555611773340919 124816930643333417660011379)
            ·
              refine ⟨187225395965000126490017069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124816930643333417660011379 187225395965000126490017069)
              ·
                refine ⟨70209523486875047433756401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 187225395965000126490017069 70209523486875047433756401)
                ·
                  refine ⟨52657142615156285575317301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70209523486875047433756401 52657142615156285575317301)
                  ·
                    refine ⟨4936607120170901772685997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52657142615156285575317301 4936607120170901772685997)
                    ·
                      refine ⟨1851227670064088164757249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4936607120170901772685997 1851227670064088164757249)
                      ·
                        rfl

theorem cell23_3605253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 2, 5, 3].length) (baseStart_3605253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3605253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3605253 prefixEnd_3605253 := by exact prefixLift 3605253
  have htrace : WordTrace (prefixWord ++ tailWord_3605253) baseStart_3605253 baseEnd_3605253 := by
    simpa [prefixWord, tailWord_3605253, baseEnd_3605253] using wordTrace_append hprefix tailTrace_3605253
  have hstable : (prefixWord ++ tailWord_3605253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3605253).length < 2 ^ (prefixWord ++ tailWord_3605253).sum := by decide
  have hdescent : baseEnd_3605253 < baseStart_3605253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3605253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3605320 : List Nat := [2, 1, 3, 1, 1, 3, 2, 2, 4, 4]
def baseStart_3605320 : Nat := 118140960795 + 3605320 * 2 ^ 59
def prefixEnd_3605320 : Nat := 4983230072969 + 3 ^ 40 * 3605320 * 2
def baseEnd_3605320 : Nat := 617087357755979800873147

theorem tailTrace_3605320 : CollatzResearch.WordTrace tailWord_3605320 prefixEnd_3605320 617087357755979800873147 := by
  unfold tailWord_3605320
  simp only [CollatzResearch.WordTrace]
  refine ⟨65748411649274427239786707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87664548865699236319715609 65748411649274427239786707)
  ·
    refine ⟨98622617473911640859680061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65748411649274427239786707 98622617473911640859680061)
    ·
      refine ⟨36983481552716865322380023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98622617473911640859680061 36983481552716865322380023)
      ·
        refine ⟨55475222329075297983570035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36983481552716865322380023 55475222329075297983570035)
        ·
          refine ⟨83212833493612946975355053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55475222329075297983570035 83212833493612946975355053)
          ·
            refine ⟨31204812560104855115758145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83212833493612946975355053 31204812560104855115758145)
            ·
              refine ⟨23403609420078641336818609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31204812560104855115758145 23403609420078641336818609)
              ·
                refine ⟨17552707065058981002613957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23403609420078641336818609 17552707065058981002613957)
                ·
                  refine ⟨3291132574698558937990117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17552707065058981002613957 3291132574698558937990117)
                  ·
                    refine ⟨617087357755979800873147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3291132574698558937990117 617087357755979800873147)
                    ·
                      rfl

theorem cell23_3605320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 2, 4, 4].length) (baseStart_3605320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3605320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3605320 prefixEnd_3605320 := by exact prefixLift 3605320
  have htrace : WordTrace (prefixWord ++ tailWord_3605320) baseStart_3605320 baseEnd_3605320 := by
    simpa [prefixWord, tailWord_3605320, baseEnd_3605320] using wordTrace_append hprefix tailTrace_3605320
  have hstable : (prefixWord ++ tailWord_3605320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3605320).length < 2 ^ (prefixWord ++ tailWord_3605320).sum := by decide
  have hdescent : baseEnd_3605320 < baseStart_3605320 := by decide
  rcases family_descends (prefixWord ++ tailWord_3605320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3605324 : List Nat := [2, 2, 1, 3, 3, 3, 2, 1, 1, 5]
def baseStart_3605324 : Nat := 118140960795 + 3605324 * 2 ^ 59
def prefixEnd_3605324 : Nat := 4983230072969 + 3 ^ 40 * 3605324 * 2
def baseEnd_3605324 : Nat := 617088042396852462323141

theorem tailTrace_3605324 : CollatzResearch.WordTrace tailWord_3605324 prefixEnd_3605324 617088042396852462323141 := by
  unfold tailWord_3605324
  simp only [CollatzResearch.WordTrace]
  refine ⟨65748484595267181581359513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87664646127022908775146017 65748484595267181581359513)
  ·
    refine ⟨49311363446450386186019635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65748484595267181581359513 49311363446450386186019635)
    ·
      refine ⟨73967045169675579279029453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49311363446450386186019635 73967045169675579279029453)
      ·
        refine ⟨27737641938628342229636045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73967045169675579279029453 27737641938628342229636045)
        ·
          refine ⟨10401615726985628336113517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27737641938628342229636045 10401615726985628336113517)
          ·
            refine ⟨3900605897619610626042569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10401615726985628336113517 3900605897619610626042569)
            ·
              refine ⟨2925454423214707969531927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3900605897619610626042569 2925454423214707969531927)
              ·
                refine ⟨4388181634822061954297891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2925454423214707969531927 4388181634822061954297891)
                ·
                  refine ⟨6582272452233092931446837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4388181634822061954297891 6582272452233092931446837)
                  ·
                    refine ⟨617088042396852462323141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6582272452233092931446837 617088042396852462323141)
                    ·
                      rfl

theorem cell23_3605324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 2, 1, 1, 5].length) (baseStart_3605324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3605324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3605324 prefixEnd_3605324 := by exact prefixLift 3605324
  have htrace : WordTrace (prefixWord ++ tailWord_3605324) baseStart_3605324 baseEnd_3605324 := by
    simpa [prefixWord, tailWord_3605324, baseEnd_3605324] using wordTrace_append hprefix tailTrace_3605324
  have hstable : (prefixWord ++ tailWord_3605324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3605324).length < 2 ^ (prefixWord ++ tailWord_3605324).sum := by decide
  have hdescent : baseEnd_3605324 < baseStart_3605324 := by decide
  rcases family_descends (prefixWord ++ tailWord_3605324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3605330 : List Nat := [3, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5]
def baseStart_3605330 : Nat := 118140960795 + 3605330 * 2 ^ 59
def prefixEnd_3605330 : Nat := 4983230072969 + 3 ^ 40 * 3605330 * 2
def baseEnd_3605330 : Nat := 1851267208074484363494395

theorem tailTrace_3605330 : CollatzResearch.WordTrace tailWord_3605330 prefixEnd_3605330 1851267208074484363494395 := by
  unfold tailWord_3605330
  simp only [CollatzResearch.WordTrace]
  refine ⟨32874297007128156546859361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87664792019008417458291629 32874297007128156546859361)
  ·
    refine ⟨24655722755346117410144521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32874297007128156546859361 24655722755346117410144521)
    ·
      refine ⟨18491792066509588057608391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24655722755346117410144521 18491792066509588057608391)
      ·
        refine ⟨27737688099764382086412587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18491792066509588057608391 27737688099764382086412587)
        ·
          refine ⟨41606532149646573129618881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27737688099764382086412587 41606532149646573129618881)
          ·
            refine ⟨31204899112234929847214161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41606532149646573129618881 31204899112234929847214161)
            ·
              refine ⟨23403674334176197385410621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31204899112234929847214161 23403674334176197385410621)
              ·
                refine ⟨8776377875316074019528983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23403674334176197385410621 8776377875316074019528983)
                ·
                  refine ⟨13164566812974111029293475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8776377875316074019528983 13164566812974111029293475)
                  ·
                    refine ⟨19746850219461166543940213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13164566812974111029293475 19746850219461166543940213)
                    ·
                      refine ⟨1851267208074484363494395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19746850219461166543940213 1851267208074484363494395)
                      ·
                        rfl

theorem cell23_3605330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5].length) (baseStart_3605330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3605330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3605330 prefixEnd_3605330 := by exact prefixLift 3605330
  have htrace : WordTrace (prefixWord ++ tailWord_3605330) baseStart_3605330 baseEnd_3605330 := by
    simpa [prefixWord, tailWord_3605330, baseEnd_3605330] using wordTrace_append hprefix tailTrace_3605330
  have hstable : (prefixWord ++ tailWord_3605330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3605330).length < 2 ^ (prefixWord ++ tailWord_3605330).sum := by decide
  have hdescent : baseEnd_3605330 < baseStart_3605330 := by decide
  rcases family_descends (prefixWord ++ tailWord_3605330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3605333 : List Nat := [1, 3, 2, 2, 2, 1, 12]
def baseStart_3605333 : Nat := 118140960795 + 3605333 * 2 ^ 59
def prefixEnd_3605333 : Nat := 4983230072969 + 3 ^ 40 * 3605333 * 2
def baseEnd_3605333 : Nat := 22855169734770961132801

theorem tailTrace_3605333 : CollatzResearch.WordTrace tailWord_3605333 prefixEnd_3605333 22855169734770961132801 := by
  unfold tailWord_3605333
  simp only [CollatzResearch.WordTrace]
  refine ⟨131497297447501757699796653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87664864965001171799864435 131497297447501757699796653)
  ·
    refine ⟨49311486542813159137423745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131497297447501757699796653 49311486542813159137423745)
    ·
      refine ⟨36983614907109869353067809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49311486542813159137423745 36983614907109869353067809)
      ·
        refine ⟨27737711180332402014800857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36983614907109869353067809 27737711180332402014800857)
        ·
          refine ⟨20803283385249301511100643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27737711180332402014800857 20803283385249301511100643)
          ·
            refine ⟨31204925077873952266650965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20803283385249301511100643 31204925077873952266650965)
            ·
              refine ⟨22855169734770961132801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 31204925077873952266650965 22855169734770961132801)
              ·
                rfl

theorem cell23_3605333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 12].length) (baseStart_3605333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3605333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3605333 prefixEnd_3605333 := by exact prefixLift 3605333
  have htrace : WordTrace (prefixWord ++ tailWord_3605333) baseStart_3605333 baseEnd_3605333 := by
    simpa [prefixWord, tailWord_3605333, baseEnd_3605333] using wordTrace_append hprefix tailTrace_3605333
  have hstable : (prefixWord ++ tailWord_3605333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3605333).length < 2 ^ (prefixWord ++ tailWord_3605333).sum := by decide
  have hdescent : baseEnd_3605333 < baseStart_3605333 := by decide
  rcases family_descends (prefixWord ++ tailWord_3605333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3605337 : List Nat := [1, 2, 1, 2, 2, 4, 3, 2, 2, 4]
def baseStart_3605337 : Nat := 118140960795 + 3605337 * 2 ^ 59
def prefixEnd_3605337 : Nat := 4983230072969 + 3 ^ 40 * 3605337 * 2
def baseEnd_3605337 : Nat := 617090267479688612035621

theorem tailTrace_3605337 : CollatzResearch.WordTrace tailWord_3605337 prefixEnd_3605337 617090267479688612035621 := by
  unfold tailWord_3605337
  simp only [CollatzResearch.WordTrace]
  refine ⟨131497443339487266382942265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87664962226324844255294843 131497443339487266382942265)
  ·
    refine ⟨98623082504615449787206699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131497443339487266382942265 98623082504615449787206699)
    ·
      refine ⟨147934623756923174680810049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98623082504615449787206699 147934623756923174680810049)
      ·
        refine ⟨110950967817692381010607537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147934623756923174680810049 110950967817692381010607537)
        ·
          refine ⟨83213225863269285757955653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110950967817692381010607537 83213225863269285757955653)
          ·
            refine ⟨15602479849362991079616685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83213225863269285757955653 15602479849362991079616685)
            ·
              refine ⟨5850929943511121654856257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15602479849362991079616685 5850929943511121654856257)
              ·
                refine ⟨4388197457633341241142193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5850929943511121654856257 4388197457633341241142193)
                ·
                  refine ⟨3291148093225005930856645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4388197457633341241142193 3291148093225005930856645)
                  ·
                    refine ⟨617090267479688612035621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3291148093225005930856645 617090267479688612035621)
                    ·
                      rfl

theorem cell23_3605337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3, 2, 2, 4].length) (baseStart_3605337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3605337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3605337 prefixEnd_3605337 := by exact prefixLift 3605337
  have htrace : WordTrace (prefixWord ++ tailWord_3605337) baseStart_3605337 baseEnd_3605337 := by
    simpa [prefixWord, tailWord_3605337, baseEnd_3605337] using wordTrace_append hprefix tailTrace_3605337
  have hstable : (prefixWord ++ tailWord_3605337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3605337).length < 2 ^ (prefixWord ++ tailWord_3605337).sum := by decide
  have hdescent : baseEnd_3605337 < baseStart_3605337 := by decide
  rcases family_descends (prefixWord ++ tailWord_3605337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3605344 : List Nat := [2, 1, 1, 3, 3, 1, 4, 1, 3, 2, 2]
def baseStart_3605344 : Nat := 118140960795 + 3605344 * 2 ^ 59
def prefixEnd_3605344 : Nat := 4983230072969 + 3 ^ 40 * 3605344 * 2
def baseEnd_3605344 : Nat := 1851274396803647308719331

theorem tailTrace_3605344 : CollatzResearch.WordTrace tailWord_3605344 prefixEnd_3605344 1851274396803647308719331 := by
  unfold tailWord_3605344
  simp only [CollatzResearch.WordTrace]
  refine ⟨65748849325230953289223543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87665132433641271052298057 65748849325230953289223543)
  ·
    refine ⟨98623273987846429933835315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65748849325230953289223543 98623273987846429933835315)
    ·
      refine ⟨147934910981769644900752973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98623273987846429933835315 147934910981769644900752973)
      ·
        refine ⟨55475591618163616837782365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147934910981769644900752973 55475591618163616837782365)
        ·
          refine ⟨20803346856811356314168387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55475591618163616837782365 20803346856811356314168387)
          ·
            refine ⟨31205020285217034471252581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20803346856811356314168387 31205020285217034471252581)
            ·
              refine ⟨5850941303478193963359859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31205020285217034471252581 5850941303478193963359859)
              ·
                refine ⟨8776411955217290945039789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5850941303478193963359859 8776411955217290945039789)
                ·
                  refine ⟨3291154483206484104389921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8776411955217290945039789 3291154483206484104389921)
                  ·
                    refine ⟨2468365862404863078292441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3291154483206484104389921 2468365862404863078292441)
                    ·
                      refine ⟨1851274396803647308719331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2468365862404863078292441 1851274396803647308719331)
                      ·
                        rfl

theorem cell23_3605344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4, 1, 3, 2, 2].length) (baseStart_3605344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3605344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3605344 prefixEnd_3605344 := by exact prefixLift 3605344
  have htrace : WordTrace (prefixWord ++ tailWord_3605344) baseStart_3605344 baseEnd_3605344 := by
    simpa [prefixWord, tailWord_3605344, baseEnd_3605344] using wordTrace_append hprefix tailTrace_3605344
  have hstable : (prefixWord ++ tailWord_3605344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3605344).length < 2 ^ (prefixWord ++ tailWord_3605344).sum := by decide
  have hdescent : baseEnd_3605344 < baseStart_3605344 := by decide
  rcases family_descends (prefixWord ++ tailWord_3605344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3605363 : List Nat := [1, 1, 1, 2, 2, 1, 4, 2, 2, 7]
def baseStart_3605363 : Nat := 118140960795 + 3605363 * 2 ^ 59
def prefixEnd_3605363 : Nat := 4983230072969 + 3 ^ 40 * 3605363 * 2
def baseEnd_3605363 : Nat := 617094717645360911460581

theorem tailTrace_3605363 : CollatzResearch.WordTrace tailWord_3605363 prefixEnd_3605363 617094717645360911460581 := by
  unfold tailWord_3605363
  simp only [CollatzResearch.WordTrace]
  refine ⟨131498391637393072823388743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87665594424928715215592495 131498391637393072823388743)
  ·
    refine ⟨197247587456089609235083115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131498391637393072823388743 197247587456089609235083115)
    ·
      refine ⟨295871381184134413852624673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197247587456089609235083115 295871381184134413852624673)
      ·
        refine ⟨221903535888100810389468505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 295871381184134413852624673 221903535888100810389468505)
        ·
          refine ⟨166427651916075607792101379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 221903535888100810389468505 166427651916075607792101379)
          ·
            refine ⟨249641477874113411688152069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166427651916075607792101379 249641477874113411688152069)
            ·
              refine ⟨46807777101396264691528513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 249641477874113411688152069 46807777101396264691528513)
              ·
                refine ⟨35105832826047198518646385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46807777101396264691528513 35105832826047198518646385)
                ·
                  refine ⟨26329374619535398888984789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35105832826047198518646385 26329374619535398888984789)
                  ·
                    refine ⟨617094717645360911460581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26329374619535398888984789 617094717645360911460581)
                    ·
                      rfl

theorem cell23_3605363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 2, 2, 7].length) (baseStart_3605363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3605363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3605363 prefixEnd_3605363 := by exact prefixLift 3605363
  have htrace : WordTrace (prefixWord ++ tailWord_3605363) baseStart_3605363 baseEnd_3605363 := by
    simpa [prefixWord, tailWord_3605363, baseEnd_3605363] using wordTrace_append hprefix tailTrace_3605363
  have hstable : (prefixWord ++ tailWord_3605363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3605363).length < 2 ^ (prefixWord ++ tailWord_3605363).sum := by decide
  have hdescent : baseEnd_3605363 < baseStart_3605363 := by decide
  rcases family_descends (prefixWord ++ tailWord_3605363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3605417 : List Nat := [1, 2, 1, 1, 1, 1, 6, 3, 1, 4, 2]
def baseStart_3605417 : Nat := 118140960795 + 3605417 * 2 ^ 59
def prefixEnd_3605417 : Nat := 4983230072969 + 3 ^ 40 * 3605417 * 2
def baseEnd_3605417 : Nat := 1851311880891425523106495

theorem tailTrace_3605417 : CollatzResearch.WordTrace tailWord_3605417 prefixEnd_3605417 1851311880891425523106495 := by
  unfold tailWord_3605417
  simp only [CollatzResearch.WordTrace]
  refine ⟨131500361179197440045854505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87666907452798293363903003 131500361179197440045854505)
  ·
    refine ⟨98625270884398080034390879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131500361179197440045854505 98625270884398080034390879)
    ·
      refine ⟨147937906326597120051586319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98625270884398080034390879 147937906326597120051586319)
      ·
        refine ⟨221906859489895680077379479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147937906326597120051586319 221906859489895680077379479)
        ·
          refine ⟨332860289234843520116069219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221906859489895680077379479 332860289234843520116069219)
          ·
            refine ⟨499290433852265280174103829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 332860289234843520116069219 499290433852265280174103829)
            ·
              refine ⟨23404239086824935008161117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 499290433852265280174103829 23404239086824935008161117)
              ·
                refine ⟨8776589657559350628060419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23404239086824935008161117 8776589657559350628060419)
                ·
                  refine ⟨13164884486339025942090629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8776589657559350628060419 13164884486339025942090629)
                  ·
                    refine ⟨2468415841188567364141993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13164884486339025942090629 2468415841188567364141993)
                    ·
                      refine ⟨1851311880891425523106495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2468415841188567364141993 1851311880891425523106495)
                      ·
                        rfl

theorem cell23_3605417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 3, 1, 4, 2].length) (baseStart_3605417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3605417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3605417 prefixEnd_3605417 := by exact prefixLift 3605417
  have htrace : WordTrace (prefixWord ++ tailWord_3605417) baseStart_3605417 baseEnd_3605417 := by
    simpa [prefixWord, tailWord_3605417, baseEnd_3605417] using wordTrace_append hprefix tailTrace_3605417
  have hstable : (prefixWord ++ tailWord_3605417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3605417).length < 2 ^ (prefixWord ++ tailWord_3605417).sum := by decide
  have hdescent : baseEnd_3605417 < baseStart_3605417 := by decide
  rcases family_descends (prefixWord ++ tailWord_3605417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3605420 : List Nat := [2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 3]
def baseStart_3605420 : Nat := 118140960795 + 3605420 * 2 ^ 59
def prefixEnd_3605420 : Nat := 4983230072969 + 3 ^ 40 * 3605420 * 2
def baseEnd_3605420 : Nat := 1851313421333389011368981

theorem tailTrace_3605420 : CollatzResearch.WordTrace tailWord_3605420 prefixEnd_3605420 1851313421333389011368981 := by
  unfold tailWord_3605420
  simp only [CollatzResearch.WordTrace]
  refine ⟨65750235299093285779106857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87666980398791047705475809 65750235299093285779106857)
  ·
    refine ⟨49312676474319964334330143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65750235299093285779106857 49312676474319964334330143)
    ·
      refine ⟨73969014711479946501495215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49312676474319964334330143 73969014711479946501495215)
      ·
        refine ⟨110953522067219919752242823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73969014711479946501495215 110953522067219919752242823)
        ·
          refine ⟨166430283100829879628364235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110953522067219919752242823 166430283100829879628364235)
          ·
            refine ⟨249645424651244819442546353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166430283100829879628364235 249645424651244819442546353)
            ·
              refine ⟨187234068488433614581909765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 249645424651244819442546353 187234068488433614581909765)
              ·
                refine ⟨35106387841581302734108081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 187234068488433614581909765 35106387841581302734108081)
                ·
                  refine ⟨26329790881185977050581061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35106387841581302734108081 26329790881185977050581061)
                  ·
                    refine ⟨4936835790222370696983949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26329790881185977050581061 4936835790222370696983949)
                    ·
                      refine ⟨1851313421333389011368981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4936835790222370696983949 1851313421333389011368981)
                      ·
                        rfl

theorem cell23_3605420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 3].length) (baseStart_3605420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3605420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3605420 prefixEnd_3605420 := by exact prefixLift 3605420
  have htrace : WordTrace (prefixWord ++ tailWord_3605420) baseStart_3605420 baseEnd_3605420 := by
    simpa [prefixWord, tailWord_3605420, baseEnd_3605420] using wordTrace_append hprefix tailTrace_3605420
  have hstable : (prefixWord ++ tailWord_3605420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3605420).length < 2 ^ (prefixWord ++ tailWord_3605420).sum := by decide
  have hdescent : baseEnd_3605420 < baseStart_3605420 := by decide
  rcases family_descends (prefixWord ++ tailWord_3605420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3605451 : List Nat := [1, 1, 1, 1, 3, 6, 2, 2, 2, 2, 2]
def baseStart_3605451 : Nat := 118140960795 + 3605451 * 2 ^ 59
def prefixEnd_3605451 : Nat := 4983230072969 + 3 ^ 40 * 3605451 * 2
def baseEnd_3605451 : Nat := 1851329339233678390081339

theorem tailTrace_3605451 : CollatzResearch.WordTrace tailWord_3605451 prefixEnd_3605451 1851329339233678390081339 := by
  unfold tailWord_3605451
  simp only [CollatzResearch.WordTrace]
  refine ⟨131501601261074263852592207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87667734174049509235061471 131501601261074263852592207)
  ·
    refine ⟨197252401891611395778888311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131501601261074263852592207 197252401891611395778888311)
    ·
      refine ⟨295878602837417093668332467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197252401891611395778888311 295878602837417093668332467)
      ·
        refine ⟨443817904256125640502498701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295878602837417093668332467 443817904256125640502498701)
        ·
          refine ⟨166431714096047115188437013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 443817904256125640502498701 166431714096047115188437013)
          ·
            refine ⟨7801486598252208524457985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 166431714096047115188437013 7801486598252208524457985)
            ·
              refine ⟨5851114948689156393343489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7801486598252208524457985 5851114948689156393343489)
              ·
                refine ⟨4388336211516867295007617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5851114948689156393343489 4388336211516867295007617)
                ·
                  refine ⟨3291252158637650471255713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4388336211516867295007617 3291252158637650471255713)
                  ·
                    refine ⟨2468439118978237853441785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3291252158637650471255713 2468439118978237853441785)
                    ·
                      refine ⟨1851329339233678390081339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2468439118978237853441785 1851329339233678390081339)
                      ·
                        rfl

theorem cell23_3605451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2, 2, 2, 2, 2].length) (baseStart_3605451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3605451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3605451 prefixEnd_3605451 := by exact prefixLift 3605451
  have htrace : WordTrace (prefixWord ++ tailWord_3605451) baseStart_3605451 baseEnd_3605451 := by
    simpa [prefixWord, tailWord_3605451, baseEnd_3605451] using wordTrace_append hprefix tailTrace_3605451
  have hstable : (prefixWord ++ tailWord_3605451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3605451).length < 2 ^ (prefixWord ++ tailWord_3605451).sum := by decide
  have hdescent : baseEnd_3605451 < baseStart_3605451 := by decide
  rcases family_descends (prefixWord ++ tailWord_3605451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3605457 : List Nat := [1, 2, 2, 1, 2, 1, 5, 4, 5]
def baseStart_3605457 : Nat := 118140960795 + 3605457 * 2 ^ 59
def prefixEnd_3605457 : Nat := 4983230072969 + 3 ^ 40 * 3605457 * 2
def baseEnd_3605457 : Nat := 205703602235289485178479

theorem tailTrace_3605457 : CollatzResearch.WordTrace tailWord_3605457 prefixEnd_3605457 205703602235289485178479 := by
  unfold tailWord_3605457
  simp only [CollatzResearch.WordTrace]
  refine ⟨131501820099052526877310625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87667880066035017918207083 131501820099052526877310625)
  ·
    refine ⟨98626365074289395157982969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131501820099052526877310625 98626365074289395157982969)
    ·
      refine ⟨73969773805717046368487227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98626365074289395157982969 73969773805717046368487227)
      ·
        refine ⟨110954660708575569552730841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73969773805717046368487227 110954660708575569552730841)
        ·
          refine ⟨83215995531431677164548131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110954660708575569552730841 83215995531431677164548131)
          ·
            refine ⟨124823993297147515746822197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83215995531431677164548131 124823993297147515746822197)
            ·
              refine ⟨11702249371607579601264581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 124823993297147515746822197 11702249371607579601264581)
              ·
                refine ⟨2194171757176421175237109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11702249371607579601264581 2194171757176421175237109)
                ·
                  refine ⟨205703602235289485178479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2194171757176421175237109 205703602235289485178479)
                  ·
                    rfl

theorem cell23_3605457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 4, 5].length) (baseStart_3605457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3605457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3605457 prefixEnd_3605457 := by exact prefixLift 3605457
  have htrace : WordTrace (prefixWord ++ tailWord_3605457) baseStart_3605457 baseEnd_3605457 := by
    simpa [prefixWord, tailWord_3605457, baseEnd_3605457] using wordTrace_append hprefix tailTrace_3605457
  have hstable : (prefixWord ++ tailWord_3605457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3605457).length < 2 ^ (prefixWord ++ tailWord_3605457).sum := by decide
  have hdescent : baseEnd_3605457 < baseStart_3605457 := by decide
  rcases family_descends (prefixWord ++ tailWord_3605457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3605474 : List Nat := [3, 3, 3, 1, 1, 2, 1, 2, 7]
def baseStart_3605474 : Nat := 118140960795 + 3605474 * 2 ^ 59
def prefixEnd_3605474 : Nat := 4983230072969 + 3 ^ 40 * 3605474 * 2
def baseEnd_3605474 : Nat := 205704572143192422232637

theorem tailTrace_3605474 : CollatzResearch.WordTrace tailWord_3605474 prefixEnd_3605474 205704572143192422232637 := by
  unfold tailWord_3605474
  simp only [CollatzResearch.WordTrace]
  refine ⟨32875610034997734695169869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87668293426660625853786317 32875610034997734695169869)
  ·
    refine ⟨12328353763124150510688701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32875610034997734695169869 12328353763124150510688701)
    ·
      refine ⟨4623132661171556441508263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12328353763124150510688701 4623132661171556441508263)
      ·
        refine ⟨6934698991757334662262395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4623132661171556441508263 6934698991757334662262395)
        ·
          refine ⟨10402048487636001993393593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6934698991757334662262395 10402048487636001993393593)
          ·
            refine ⟨7801536365727001495045195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10402048487636001993393593 7801536365727001495045195)
            ·
              refine ⟨11702304548590502242567793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7801536365727001495045195 11702304548590502242567793)
              ·
                refine ⟨8776728411442876681925845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11702304548590502242567793 8776728411442876681925845)
                ·
                  refine ⟨205704572143192422232637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8776728411442876681925845 205704572143192422232637)
                  ·
                    rfl

theorem cell23_3605474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 2, 7].length) (baseStart_3605474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3605474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3605474 prefixEnd_3605474 := by exact prefixLift 3605474
  have htrace : WordTrace (prefixWord ++ tailWord_3605474) baseStart_3605474 baseEnd_3605474 := by
    simpa [prefixWord, tailWord_3605474, baseEnd_3605474] using wordTrace_append hprefix tailTrace_3605474
  have hstable : (prefixWord ++ tailWord_3605474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3605474).length < 2 ^ (prefixWord ++ tailWord_3605474).sum := by decide
  have hdescent : baseEnd_3605474 < baseStart_3605474 := by decide
  rcases family_descends (prefixWord ++ tailWord_3605474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3605480 : List Nat := [2, 1, 4, 1, 1, 1, 2, 2, 1, 1, 7]
def baseStart_3605480 : Nat := 118140960795 + 3605480 * 2 ^ 59
def prefixEnd_3605480 : Nat := 4983230072969 + 3 ^ 40 * 3605480 * 2
def baseEnd_3605480 : Nat := 1851344230172658776618705

theorem tailTrace_3605480 : CollatzResearch.WordTrace tailWord_3605480 prefixEnd_3605480 1851344230172658776618705 := by
  unfold tailWord_3605480
  simp only [CollatzResearch.WordTrace]
  refine ⟨65751329488984600902698947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87668439318646134536931929 65751329488984600902698947)
  ·
    refine ⟨98626994233476901354048421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65751329488984600902698947 98626994233476901354048421)
    ·
      refine ⟨18492561418776919003884079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98626994233476901354048421 18492561418776919003884079)
      ·
        refine ⟨27738842128165378505826119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18492561418776919003884079 27738842128165378505826119)
        ·
          refine ⟨41608263192248067758739179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27738842128165378505826119 41608263192248067758739179)
          ·
            refine ⟨62412394788372101638108769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41608263192248067758739179 62412394788372101638108769)
            ·
              refine ⟨46809296091279076228581577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62412394788372101638108769 46809296091279076228581577)
              ·
                refine ⟨35106972068459307171436183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46809296091279076228581577 35106972068459307171436183)
                ·
                  refine ⟨52660458102688960757154275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35106972068459307171436183 52660458102688960757154275)
                  ·
                    refine ⟨78990687154033441135731413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52660458102688960757154275 78990687154033441135731413)
                    ·
                      refine ⟨1851344230172658776618705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 78990687154033441135731413 1851344230172658776618705)
                      ·
                        rfl

theorem cell23_3605480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_3605480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3605480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3605480 prefixEnd_3605480 := by exact prefixLift 3605480
  have htrace : WordTrace (prefixWord ++ tailWord_3605480) baseStart_3605480 baseEnd_3605480 := by
    simpa [prefixWord, tailWord_3605480, baseEnd_3605480] using wordTrace_append hprefix tailTrace_3605480
  have hstable : (prefixWord ++ tailWord_3605480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3605480).length < 2 ^ (prefixWord ++ tailWord_3605480).sum := by decide
  have hdescent : baseEnd_3605480 < baseStart_3605480 := by decide
  rcases family_descends (prefixWord ++ tailWord_3605480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3605487 : List Nat := [1, 1, 2, 1, 4, 3, 3, 1, 2, 5]
def baseStart_3605487 : Nat := 118140960795 + 3605487 * 2 ^ 59
def prefixEnd_3605487 : Nat := 4983230072969 + 3 ^ 40 * 3605487 * 2
def baseEnd_3605487 : Nat := 617115941512413416410391

theorem tailTrace_3605487 : CollatzResearch.WordTrace tailWord_3605487 prefixEnd_3605487 617115941512413416410391 := by
  unfold tailWord_3605487
  simp only [CollatzResearch.WordTrace]
  refine ⟨131502914288943842000902715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87668609525962561333935143 131502914288943842000902715)
  ·
    refine ⟨197254371433415763001354073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131502914288943842000902715 197254371433415763001354073)
    ·
      refine ⟨147940778575061822251015555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197254371433415763001354073 147940778575061822251015555)
      ·
        refine ⟨221911167862592733376523333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147940778575061822251015555 221911167862592733376523333)
        ·
          refine ⟨41608343974236137508098125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 221911167862592733376523333 41608343974236137508098125)
          ·
            refine ⟨15603128990338551565536797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41608343974236137508098125 15603128990338551565536797)
            ·
              refine ⟨5851173371376956837076299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15603128990338551565536797 5851173371376956837076299)
              ·
                refine ⟨8776760057065435255614449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5851173371376956837076299 8776760057065435255614449)
                ·
                  refine ⟨6582570042799076441710837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8776760057065435255614449 6582570042799076441710837)
                  ·
                    refine ⟨617115941512413416410391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6582570042799076441710837 617115941512413416410391)
                    ·
                      rfl

theorem cell23_3605487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3, 1, 2, 5].length) (baseStart_3605487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3605487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3605487 prefixEnd_3605487 := by exact prefixLift 3605487
  have htrace : WordTrace (prefixWord ++ tailWord_3605487) baseStart_3605487 baseEnd_3605487 := by
    simpa [prefixWord, tailWord_3605487, baseEnd_3605487] using wordTrace_append hprefix tailTrace_3605487
  have hstable : (prefixWord ++ tailWord_3605487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3605487).length < 2 ^ (prefixWord ++ tailWord_3605487).sum := by decide
  have hdescent : baseEnd_3605487 < baseStart_3605487 := by decide
  rcases family_descends (prefixWord ++ tailWord_3605487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3605502 : List Nat := [4, 2, 2, 2, 3, 1, 1, 2, 2, 2, 2]
def baseStart_3605502 : Nat := 118140960795 + 3605502 * 2 ^ 59
def prefixEnd_3605502 : Nat := 4983230072969 + 3 ^ 40 * 3605502 * 2
def baseEnd_3605502 : Nat := 1851355526747057690543605

theorem tailTrace_3605502 : CollatzResearch.WordTrace tailWord_3605502 prefixEnd_3605502 1851355526747057690543605 := by
  unfold tailWord_3605502
  simp only [CollatzResearch.WordTrace]
  refine ⟨16437932672986187445337345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87668974255926333041799173 16437932672986187445337345)
  ·
    refine ⟨12328449504739640584003009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16437932672986187445337345 12328449504739640584003009)
    ·
      refine ⟨9246337128554730438002257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12328449504739640584003009 9246337128554730438002257)
      ·
        refine ⟨6934752846416047828501693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9246337128554730438002257 6934752846416047828501693)
        ·
          refine ⟨2600532317406017935688135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6934752846416047828501693 2600532317406017935688135)
          ·
            refine ⟨3900798476109026903532203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2600532317406017935688135 3900798476109026903532203)
            ·
              refine ⟨5851197714163540355298305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3900798476109026903532203 5851197714163540355298305)
              ·
                refine ⟨4388398285622655266473729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5851197714163540355298305 4388398285622655266473729)
                ·
                  refine ⟨3291298714216991449855297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4388398285622655266473729 3291298714216991449855297)
                  ·
                    refine ⟨2468474035662743587391473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3291298714216991449855297 2468474035662743587391473)
                    ·
                      refine ⟨1851355526747057690543605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2468474035662743587391473 1851355526747057690543605)
                      ·
                        rfl

theorem cell23_3605502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 1, 2, 2, 2, 2].length) (baseStart_3605502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3605502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3605502 prefixEnd_3605502 := by exact prefixLift 3605502
  have htrace : WordTrace (prefixWord ++ tailWord_3605502) baseStart_3605502 baseEnd_3605502 := by
    simpa [prefixWord, tailWord_3605502, baseEnd_3605502] using wordTrace_append hprefix tailTrace_3605502
  have hstable : (prefixWord ++ tailWord_3605502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3605502).length < 2 ^ (prefixWord ++ tailWord_3605502).sum := by decide
  have hdescent : baseEnd_3605502 < baseStart_3605502 := by decide
  rcases family_descends (prefixWord ++ tailWord_3605502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3605520 : List Nat := [2, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4]
def baseStart_3605520 : Nat := 118140960795 + 3605520 * 2 ^ 59
def prefixEnd_3605520 : Nat := 4983230072969 + 3 ^ 40 * 3605520 * 2
def baseEnd_3605520 : Nat := 1851364769398838620118521

theorem tailTrace_3605520 : CollatzResearch.WordTrace tailWord_3605520 prefixEnd_3605520 1851364769398838620118521 := by
  unfold tailWord_3605520
  simp only [CollatzResearch.WordTrace]
  refine ⟨65752058948912144318427007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87669411931882859091236009 65752058948912144318427007)
  ·
    refine ⟨98628088423368216477640511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65752058948912144318427007 98628088423368216477640511)
    ·
      refine ⟨147942132635052324716460767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98628088423368216477640511 147942132635052324716460767)
      ·
        refine ⟨221913198952578487074691151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147942132635052324716460767 221913198952578487074691151)
        ·
          refine ⟨332869798428867730612036727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221913198952578487074691151 332869798428867730612036727)
          ·
            refine ⟨499304697643301595918055091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 332869798428867730612036727 499304697643301595918055091)
            ·
              refine ⟨748957046464952393877082637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 499304697643301595918055091 748957046464952393877082637)
              ·
                refine ⟨280858892424357147703905989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 748957046464952393877082637 280858892424357147703905989)
                ·
                  refine ⟨52661042329566965194482373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 280858892424357147703905989 52661042329566965194482373)
                  ·
                    refine ⟨9873945436793805973965445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52661042329566965194482373 9873945436793805973965445)
                    ·
                      refine ⟨1851364769398838620118521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9873945436793805973965445 1851364769398838620118521)
                      ·
                        rfl

theorem cell23_3605520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4, 4].length) (baseStart_3605520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3605520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3605520 prefixEnd_3605520 := by exact prefixLift 3605520
  have htrace : WordTrace (prefixWord ++ tailWord_3605520) baseStart_3605520 baseEnd_3605520 := by
    simpa [prefixWord, tailWord_3605520, baseEnd_3605520] using wordTrace_append hprefix tailTrace_3605520
  have hstable : (prefixWord ++ tailWord_3605520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3605520).length < 2 ^ (prefixWord ++ tailWord_3605520).sum := by decide
  have hdescent : baseEnd_3605520 < baseStart_3605520 := by decide
  rcases family_descends (prefixWord ++ tailWord_3605520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3605581 : List Nat := [1, 6, 1, 1, 1, 2, 4, 1, 6]
def baseStart_3605581 : Nat := 118140960795 + 3605581 * 2 ^ 59
def prefixEnd_3605581 : Nat := 4983230072969 + 3 ^ 40 * 3605581 * 2
def baseEnd_3605581 : Nat := 205710676857640320161749

theorem tailTrace_3605581 : CollatzResearch.WordTrace tailWord_3605581 prefixEnd_3605581 205710676857640320161749 := by
  unfold tailWord_3605581
  simp only [CollatzResearch.WordTrace]
  refine ⟨131506342750603296054824597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87670895167068864036549731 131506342750603296054824597)
  ·
    refine ⟨6164359816434529502569903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 131506342750603296054824597 6164359816434529502569903)
    ·
      refine ⟨9246539724651794253854855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6164359816434529502569903 9246539724651794253854855)
      ·
        refine ⟨13869809586977691380782283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9246539724651794253854855 13869809586977691380782283)
        ·
          refine ⟨20804714380466537071173425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13869809586977691380782283 20804714380466537071173425)
          ·
            refine ⟨15603535785349902803380069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20804714380466537071173425 15603535785349902803380069)
            ·
              refine ⟨2925662959753106775633763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15603535785349902803380069 2925662959753106775633763)
              ·
                refine ⟨4388494439629660163450645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2925662959753106775633763 4388494439629660163450645)
                ·
                  refine ⟨205710676857640320161749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4388494439629660163450645 205710676857640320161749)
                  ·
                    rfl

theorem cell23_3605581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 4, 1, 6].length) (baseStart_3605581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3605581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3605581 prefixEnd_3605581 := by exact prefixLift 3605581
  have htrace : WordTrace (prefixWord ++ tailWord_3605581) baseStart_3605581 baseEnd_3605581 := by
    simpa [prefixWord, tailWord_3605581, baseEnd_3605581] using wordTrace_append hprefix tailTrace_3605581
  have hstable : (prefixWord ++ tailWord_3605581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3605581).length < 2 ^ (prefixWord ++ tailWord_3605581).sum := by decide
  have hdescent : baseEnd_3605581 < baseStart_3605581 := by decide
  rcases family_descends (prefixWord ++ tailWord_3605581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3605607 : List Nat := [1, 1, 5, 1, 1, 3, 1, 1, 3, 6]
def baseStart_3605607 : Nat := 118140960795 + 3605607 * 2 ^ 59
def prefixEnd_3605607 : Nat := 4983230072969 + 3 ^ 40 * 3605607 * 2
def baseEnd_3605607 : Nat := 617136480738593259910207

theorem tailTrace_3605607 : CollatzResearch.WordTrace tailWord_3605607 prefixEnd_3605607 617136480738593259910207 := by
  unfold tailWord_3605607
  simp only [CollatzResearch.WordTrace]
  refine ⟨131507291048509102495271075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87671527365672734996847383 131507291048509102495271075)
  ·
    refine ⟨197260936572763653742906613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131507291048509102495271075 197260936572763653742906613)
    ·
      refine ⟨18493212803696592538397495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 197260936572763653742906613 18493212803696592538397495)
      ·
        refine ⟨27739819205544888807596243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18493212803696592538397495 27739819205544888807596243)
        ·
          refine ⟨41609728808317333211394365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27739819205544888807596243 41609728808317333211394365)
          ·
            refine ⟨15603648303118999954272887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41609728808317333211394365 15603648303118999954272887)
            ·
              refine ⟨23405472454678499931409331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15603648303118999954272887 23405472454678499931409331)
              ·
                refine ⟨35108208682017749897113997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23405472454678499931409331 35108208682017749897113997)
                ·
                  refine ⟨13165578255756656211417749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35108208682017749897113997 13165578255756656211417749)
                  ·
                    refine ⟨617136480738593259910207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13165578255756656211417749 617136480738593259910207)
                    ·
                      rfl

theorem cell23_3605607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 1, 3, 6].length) (baseStart_3605607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3605607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3605607 prefixEnd_3605607 := by exact prefixLift 3605607
  have htrace : WordTrace (prefixWord ++ tailWord_3605607) baseStart_3605607 baseEnd_3605607 := by
    simpa [prefixWord, tailWord_3605607, baseEnd_3605607] using wordTrace_append hprefix tailTrace_3605607
  have hstable : (prefixWord ++ tailWord_3605607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3605607).length < 2 ^ (prefixWord ++ tailWord_3605607).sum := by decide
  have hdescent : baseEnd_3605607 < baseStart_3605607 := by decide
  rcases family_descends (prefixWord ++ tailWord_3605607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3605617 : List Nat := [1, 2, 2, 2, 1, 1, 2, 5, 1, 1, 5]
def baseStart_3605617 : Nat := 118140960795 + 3605617 * 2 ^ 59
def prefixEnd_3605617 : Nat := 4983230072969 + 3 ^ 40 * 3605617 * 2
def baseEnd_3605617 : Nat := 1851414577022324740605575

theorem tailTrace_3605617 : CollatzResearch.WordTrace tailWord_3605617 prefixEnd_3605617 1851414577022324740605575 := by
  unfold tailWord_3605617
  simp only [CollatzResearch.WordTrace]
  refine ⟨131507655778472874203135105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87671770518981916135423403 131507655778472874203135105)
  ·
    refine ⟨98630741833854655652351329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131507655778472874203135105 98630741833854655652351329)
    ·
      refine ⟨73973056375390991739263497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98630741833854655652351329 73973056375390991739263497)
      ·
        refine ⟨55479792281543243804447623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73973056375390991739263497 55479792281543243804447623)
        ·
          refine ⟨83219688422314865706671435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55479792281543243804447623 83219688422314865706671435)
          ·
            refine ⟨124829532633472298560007153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83219688422314865706671435 124829532633472298560007153)
            ·
              refine ⟨93622149475104223920005365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124829532633472298560007153 93622149475104223920005365)
              ·
                refine ⟨8777076513291020992500503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 93622149475104223920005365 8777076513291020992500503)
                ·
                  refine ⟨13165614769936531488750755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8777076513291020992500503 13165614769936531488750755)
                  ·
                    refine ⟨19748422154904797233126133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13165614769936531488750755 19748422154904797233126133)
                    ·
                      refine ⟨1851414577022324740605575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19748422154904797233126133 1851414577022324740605575)
                      ·
                        rfl

theorem cell23_3605617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 5, 1, 1, 5].length) (baseStart_3605617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3605617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3605617 prefixEnd_3605617 := by exact prefixLift 3605617
  have htrace : WordTrace (prefixWord ++ tailWord_3605617) baseStart_3605617 baseEnd_3605617 := by
    simpa [prefixWord, tailWord_3605617, baseEnd_3605617] using wordTrace_append hprefix tailTrace_3605617
  have hstable : (prefixWord ++ tailWord_3605617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3605617).length < 2 ^ (prefixWord ++ tailWord_3605617).sum := by decide
  have hdescent : baseEnd_3605617 < baseStart_3605617 := by decide
  rcases family_descends (prefixWord ++ tailWord_3605617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3605624 : List Nat := [2, 1, 2, 1, 1, 1, 5, 4, 2, 4]
def baseStart_3605624 : Nat := 118140960795 + 3605624 * 2 ^ 59
def prefixEnd_3605624 : Nat := 4983230072969 + 3 ^ 40 * 3605624 * 2
def baseEnd_3605624 : Nat := 617139390462302071072681

theorem tailTrace_3605624 : CollatzResearch.WordTrace tailWord_3605624 prefixEnd_3605624 617139390462302071072681 := by
  unfold tailWord_3605624
  simp only [CollatzResearch.WordTrace]
  refine ⟨65753955544723757199319963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87671940726298342932426617 65753955544723757199319963)
  ·
    refine ⟨98630933317085635798979945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65753955544723757199319963 98630933317085635798979945)
    ·
      refine ⟨73973199987814226849234959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98630933317085635798979945 73973199987814226849234959)
      ·
        refine ⟨110959799981721340273852439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73973199987814226849234959 110959799981721340273852439)
        ·
          refine ⟨166439699972582010410778659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110959799981721340273852439 166439699972582010410778659)
          ·
            refine ⟨249659549958873015616167989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166439699972582010410778659 249659549958873015616167989)
            ·
              refine ⟨23405582808644345214015749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 249659549958873015616167989 23405582808644345214015749)
              ·
                refine ⟨4388546776620814727627953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23405582808644345214015749 4388546776620814727627953)
                ·
                  refine ⟨3291410082465611045720965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4388546776620814727627953 3291410082465611045720965)
                  ·
                    refine ⟨617139390462302071072681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3291410082465611045720965 617139390462302071072681)
                    ·
                      rfl

theorem cell23_3605624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 4, 2, 4].length) (baseStart_3605624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3605624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3605624 prefixEnd_3605624 := by exact prefixLift 3605624
  have htrace : WordTrace (prefixWord ++ tailWord_3605624) baseStart_3605624 baseEnd_3605624 := by
    simpa [prefixWord, tailWord_3605624, baseEnd_3605624] using wordTrace_append hprefix tailTrace_3605624
  have hstable : (prefixWord ++ tailWord_3605624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3605624).length < 2 ^ (prefixWord ++ tailWord_3605624).sum := by decide
  have hdescent : baseEnd_3605624 < baseStart_3605624 := by decide
  rcases family_descends (prefixWord ++ tailWord_3605624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3605664 : List Nat := [2, 1, 1, 4, 2, 1, 1, 4, 1, 3, 3]
def baseStart_3605664 : Nat := 118140960795 + 3605664 * 2 ^ 59
def prefixEnd_3605664 : Nat := 4983230072969 + 3 ^ 40 * 3605664 * 2
def baseEnd_3605664 : Nat := 1851438710613086056717859

theorem tailTrace_3605664 : CollatzResearch.WordTrace tailWord_3605664 prefixEnd_3605664 1851438710613086056717859 := by
  unfold tailWord_3605664
  simp only [CollatzResearch.WordTrace]
  refine ⟨65754685004651300615048023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87672913339535067486730697 65754685004651300615048023)
  ·
    refine ⟨98632027506976950922572035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65754685004651300615048023 98632027506976950922572035)
    ·
      refine ⟨147948041260465426383858053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98632027506976950922572035 147948041260465426383858053)
      ·
        refine ⟨27740257736337267446973385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 147948041260465426383858053 27740257736337267446973385)
        ·
          refine ⟨20805193302252950585230039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27740257736337267446973385 20805193302252950585230039)
          ·
            refine ⟨31207789953379425877845059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20805193302252950585230039 31207789953379425877845059)
            ·
              refine ⟨46811684930069138816767589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31207789953379425877845059 46811684930069138816767589)
              ·
                refine ⟨8777190924387963528143923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46811684930069138816767589 8777190924387963528143923)
                ·
                  refine ⟨13165786386581945292215885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8777190924387963528143923 13165786386581945292215885)
                  ·
                    refine ⟨4937169894968229484580957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13165786386581945292215885 4937169894968229484580957)
                    ·
                      refine ⟨1851438710613086056717859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4937169894968229484580957 1851438710613086056717859)
                      ·
                        rfl

theorem cell23_3605664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 4, 1, 3, 3].length) (baseStart_3605664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3605664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3605664 prefixEnd_3605664 := by exact prefixLift 3605664
  have htrace : WordTrace (prefixWord ++ tailWord_3605664) baseStart_3605664 baseEnd_3605664 := by
    simpa [prefixWord, tailWord_3605664, baseEnd_3605664] using wordTrace_append hprefix tailTrace_3605664
  have hstable : (prefixWord ++ tailWord_3605664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3605664).length < 2 ^ (prefixWord ++ tailWord_3605664).sum := by decide
  have hdescent : baseEnd_3605664 < baseStart_3605664 := by decide
  rcases family_descends (prefixWord ++ tailWord_3605664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3605665 : List Nat := [1, 2, 3, 3, 1, 1, 4, 3, 1, 2, 2]
def baseStart_3605665 : Nat := 118140960795 + 3605665 * 2 ^ 59
def prefixEnd_3605665 : Nat := 4983230072969 + 3 ^ 40 * 3605665 * 2
def baseEnd_3605665 : Nat := 1851439224093740552805355

theorem tailTrace_3605665 : CollatzResearch.WordTrace tailWord_3605665 prefixEnd_3605665 1851439224093740552805355 := by
  unfold tailWord_3605665
  simp only [CollatzResearch.WordTrace]
  refine ⟨131509406482298978400882449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87672937654865985600588299 131509406482298978400882449)
  ·
    refine ⟨98632054861724233800661837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131509406482298978400882449 98632054861724233800661837)
    ·
      refine ⟨36987020573146587675248189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98632054861724233800661837 36987020573146587675248189)
      ·
        refine ⟨13870132714929970378218071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36987020573146587675248189 13870132714929970378218071)
        ·
          refine ⟨20805199072394955567327107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13870132714929970378218071 20805199072394955567327107)
          ·
            refine ⟨31207798608592433350990661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20805199072394955567327107 31207798608592433350990661)
            ·
              refine ⟨5851462239111081253310749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31207798608592433350990661 5851462239111081253310749)
              ·
                refine ⟨2194298339666655469991531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5851462239111081253310749 2194298339666655469991531)
                ·
                  refine ⟨3291447509499983204987297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2194298339666655469991531 3291447509499983204987297)
                  ·
                    refine ⟨2468585632124987403740473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3291447509499983204987297 2468585632124987403740473)
                    ·
                      refine ⟨1851439224093740552805355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2468585632124987403740473 1851439224093740552805355)
                      ·
                        rfl

theorem cell23_3605665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4, 3, 1, 2, 2].length) (baseStart_3605665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3605665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3605665 prefixEnd_3605665 := by exact prefixLift 3605665
  have htrace : WordTrace (prefixWord ++ tailWord_3605665) baseStart_3605665 baseEnd_3605665 := by
    simpa [prefixWord, tailWord_3605665, baseEnd_3605665] using wordTrace_append hprefix tailTrace_3605665
  have hstable : (prefixWord ++ tailWord_3605665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3605665).length < 2 ^ (prefixWord ++ tailWord_3605665).sum := by decide
  have hdescent : baseEnd_3605665 < baseStart_3605665 := by decide
  rcases family_descends (prefixWord ++ tailWord_3605665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3605668 : List Nat := [2, 3, 1, 2, 3, 1, 4, 1, 1, 2, 3]
def baseStart_3605668 : Nat := 118140960795 + 3605668 * 2 ^ 59
def prefixEnd_3605668 : Nat := 4983230072969 + 3 ^ 40 * 3605668 * 2
def baseEnd_3605668 : Nat := 1851440764535704041067841

theorem tailTrace_3605668 : CollatzResearch.WordTrace tailWord_3605668 prefixEnd_3605668 1851440764535704041067841 := by
  unfold tailWord_3605668
  simp only [CollatzResearch.WordTrace]
  refine ⟨65754757950644054956620829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87673010600858739942161105 65754757950644054956620829)
  ·
    refine ⟨24658034231491520608732811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65754757950644054956620829 24658034231491520608732811)
    ·
      refine ⟨36987051347237280913099217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24658034231491520608732811 36987051347237280913099217)
      ·
        refine ⟨27740288510427960684824413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36987051347237280913099217 27740288510427960684824413)
        ·
          refine ⟨10402608191410485256809155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27740288510427960684824413 10402608191410485256809155)
          ·
            refine ⟨15603912287115727885213733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10402608191410485256809155 15603912287115727885213733)
            ·
              refine ⟨2925733553834198978477575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15603912287115727885213733 2925733553834198978477575)
              ·
                refine ⟨4388600330751298467716363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2925733553834198978477575 4388600330751298467716363)
                ·
                  refine ⟨6582900496126947701574545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4388600330751298467716363 6582900496126947701574545)
                  ·
                    refine ⟨4937175372095210776180909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6582900496126947701574545 4937175372095210776180909)
                    ·
                      refine ⟨1851440764535704041067841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4937175372095210776180909 1851440764535704041067841)
                      ·
                        rfl

theorem cell23_3605668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 4, 1, 1, 2, 3].length) (baseStart_3605668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3605668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3605668 prefixEnd_3605668 := by exact prefixLift 3605668
  have htrace : WordTrace (prefixWord ++ tailWord_3605668) baseStart_3605668 baseEnd_3605668 := by
    simpa [prefixWord, tailWord_3605668, baseEnd_3605668] using wordTrace_append hprefix tailTrace_3605668
  have hstable : (prefixWord ++ tailWord_3605668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3605668).length < 2 ^ (prefixWord ++ tailWord_3605668).sum := by decide
  have hdescent : baseEnd_3605668 < baseStart_3605668 := by decide
  rcases family_descends (prefixWord ++ tailWord_3605668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3605716 : List Nat := [2, 4, 1, 4, 2, 1, 1, 3, 1, 2, 2]
def baseStart_3605716 : Nat := 118140960795 + 3605716 * 2 ^ 59
def prefixEnd_3605716 : Nat := 4983230072969 + 3 ^ 40 * 3605716 * 2
def baseEnd_3605716 : Nat := 1851465411607119853267621

theorem tailTrace_3605716 : CollatzResearch.WordTrace tailWord_3605716 prefixEnd_3605716 1851465411607119853267621 := by
  unfold tailWord_3605716
  simp only [CollatzResearch.WordTrace]
  refine ⟨65755633302557107055494501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87674177736742809407326001 65755633302557107055494501)
  ·
    refine ⟨12329181244229457572905219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65755633302557107055494501 12329181244229457572905219)
    ·
      refine ⟨18493771866344186359357829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12329181244229457572905219 18493771866344186359357829)
      ·
        refine ⟨3467582224939534942379593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18493771866344186359357829 3467582224939534942379593)
        ·
          refine ⟨2600686668704651206784695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3467582224939534942379593 2600686668704651206784695)
          ·
            refine ⟨3901030003056976810177043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2600686668704651206784695 3901030003056976810177043)
            ·
              refine ⟨5851545004585465215265565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3901030003056976810177043 5851545004585465215265565)
              ·
                refine ⟨2194329376719549455724587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5851545004585465215265565 2194329376719549455724587)
                ·
                  refine ⟨3291494065079324183586881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2194329376719549455724587 3291494065079324183586881)
                  ·
                    refine ⟨2468620548809493137690161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3291494065079324183586881 2468620548809493137690161)
                    ·
                      refine ⟨1851465411607119853267621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2468620548809493137690161 1851465411607119853267621)
                      ·
                        rfl

theorem cell23_3605716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_3605716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3605716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3605716 prefixEnd_3605716 := by exact prefixLift 3605716
  have htrace : WordTrace (prefixWord ++ tailWord_3605716) baseStart_3605716 baseEnd_3605716 := by
    simpa [prefixWord, tailWord_3605716, baseEnd_3605716] using wordTrace_append hprefix tailTrace_3605716
  have hstable : (prefixWord ++ tailWord_3605716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3605716).length < 2 ^ (prefixWord ++ tailWord_3605716).sum := by decide
  have hdescent : baseEnd_3605716 < baseStart_3605716 := by decide
  rcases family_descends (prefixWord ++ tailWord_3605716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3605727 : List Nat := [1, 1, 2, 3, 2, 1, 2, 2, 9]
def baseStart_3605727 : Nat := 118140960795 + 3605727 * 2 ^ 59
def prefixEnd_3605727 : Nat := 4983230072969 + 3 ^ 40 * 3605727 * 2
def baseEnd_3605727 : Nat := 205719006654924367803341

theorem tailTrace_3605727 : CollatzResearch.WordTrace tailWord_3605727 prefixEnd_3605727 205719006654924367803341 := by
  unfold tailWord_3605727
  simp only [CollatzResearch.WordTrace]
  refine ⟨131511667808074362989639435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87674445205382908659759623 131511667808074362989639435)
  ·
    refine ⟨197267501712111544484459153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131511667808074362989639435 197267501712111544484459153)
    ·
      refine ⟨147950626284083658363344365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197267501712111544484459153 147950626284083658363344365)
      ·
        refine ⟨55481484856531371886254137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147950626284083658363344365 55481484856531371886254137)
        ·
          refine ⟨41611113642398528914690603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55481484856531371886254137 41611113642398528914690603)
          ·
            refine ⟨62416670463597793372035905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41611113642398528914690603 62416670463597793372035905)
            ·
              refine ⟨46812502847698345029026929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62416670463597793372035905 46812502847698345029026929)
              ·
                refine ⟨35109377135773758771770197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46812502847698345029026929 35109377135773758771770197)
                ·
                  refine ⟨205719006654924367803341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 35109377135773758771770197 205719006654924367803341)
                  ·
                    rfl

theorem cell23_3605727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 2, 9].length) (baseStart_3605727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3605727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3605727 prefixEnd_3605727 := by exact prefixLift 3605727
  have htrace : WordTrace (prefixWord ++ tailWord_3605727) baseStart_3605727 baseEnd_3605727 := by
    simpa [prefixWord, tailWord_3605727, baseEnd_3605727] using wordTrace_append hprefix tailTrace_3605727
  have hstable : (prefixWord ++ tailWord_3605727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3605727).length < 2 ^ (prefixWord ++ tailWord_3605727).sum := by decide
  have hdescent : baseEnd_3605727 < baseStart_3605727 := by decide
  rcases family_descends (prefixWord ++ tailWord_3605727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3605738 : List Nat := [3, 1, 3, 1, 1, 3, 2, 1, 4, 2, 2]
def baseStart_3605738 : Nat := 118140960795 + 3605738 * 2 ^ 59
def prefixEnd_3605738 : Nat := 4983230072969 + 3 ^ 40 * 3605738 * 2
def baseEnd_3605738 : Nat := 1851476708181518767192519

theorem tailTrace_3605738 : CollatzResearch.WordTrace tailWord_3605738 prefixEnd_3605738 1851476708181518767192519 := by
  unfold tailWord_3605738
  simp only [CollatzResearch.WordTrace]
  refine ⟨32878017252758627967072467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87674712674023007912193245 32878017252758627967072467)
  ·
    refine ⟨49317025879137941950608701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32878017252758627967072467 49317025879137941950608701)
    ·
      refine ⟨18493884704676728231478263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49317025879137941950608701 18493884704676728231478263)
      ·
        refine ⟨27740827057015092347217395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18493884704676728231478263 27740827057015092347217395)
        ·
          refine ⟨41611240585522638520826093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27740827057015092347217395 41611240585522638520826093)
          ·
            refine ⟨15604215219570989445309785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41611240585522638520826093 15604215219570989445309785)
            ·
              refine ⟨11703161414678242083982339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15604215219570989445309785 11703161414678242083982339)
              ·
                refine ⟨17554742122017363125973509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11703161414678242083982339 17554742122017363125973509)
                ·
                  refine ⟨3291514147878255586120033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17554742122017363125973509 3291514147878255586120033)
                  ·
                    refine ⟨2468635610908691689590025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3291514147878255586120033 2468635610908691689590025)
                    ·
                      refine ⟨1851476708181518767192519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2468635610908691689590025 1851476708181518767192519)
                      ·
                        rfl

theorem cell23_3605738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 1, 4, 2, 2].length) (baseStart_3605738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3605738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3605738 prefixEnd_3605738 := by exact prefixLift 3605738
  have htrace : WordTrace (prefixWord ++ tailWord_3605738) baseStart_3605738 baseEnd_3605738 := by
    simpa [prefixWord, tailWord_3605738, baseEnd_3605738] using wordTrace_append hprefix tailTrace_3605738
  have hstable : (prefixWord ++ tailWord_3605738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3605738).length < 2 ^ (prefixWord ++ tailWord_3605738).sum := by decide
  have hdescent : baseEnd_3605738 < baseStart_3605738 := by decide
  rcases family_descends (prefixWord ++ tailWord_3605738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3605754 : List Nat := [3, 1, 1, 1, 1, 4, 2, 1, 1, 5, 3]
def baseStart_3605754 : Nat := 118140960795 + 3605754 * 2 ^ 59
def prefixEnd_3605754 : Nat := 4983230072969 + 3 ^ 40 * 3605754 * 2
def baseEnd_3605754 : Nat := 1851484923871990704592445

theorem tailTrace_3605754 : CollatzResearch.WordTrace tailWord_3605754 prefixEnd_3605754 1851484923871990704592445 := by
  unfold tailWord_3605754
  simp only [CollatzResearch.WordTrace]
  refine ⟨32878163144744136650218079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87675101719317697733914877 32878163144744136650218079)
  ·
    refine ⟨49317244717116204975327119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32878163144744136650218079 49317244717116204975327119)
    ·
      refine ⟨73975867075674307462990679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49317244717116204975327119 73975867075674307462990679)
      ·
        refine ⟨110963800613511461194486019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73975867075674307462990679 110963800613511461194486019)
        ·
          refine ⟨166445700920267191791729029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110963800613511461194486019 166445700920267191791729029)
          ·
            refine ⟨31208568922550098460949193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 166445700920267191791729029 31208568922550098460949193)
            ·
              refine ⟨23406426691912573845711895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31208568922550098460949193 23406426691912573845711895)
              ·
                refine ⟨35109640037868860768567843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23406426691912573845711895 35109640037868860768567843)
                ·
                  refine ⟨52664460056803291152851765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35109640037868860768567843 52664460056803291152851765)
                  ·
                    refine ⟨4937293130325308545579853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52664460056803291152851765 4937293130325308545579853)
                    ·
                      refine ⟨1851484923871990704592445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4937293130325308545579853 1851484923871990704592445)
                      ·
                        rfl

theorem cell23_3605754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 1, 1, 5, 3].length) (baseStart_3605754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3605754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3605754 prefixEnd_3605754 := by exact prefixLift 3605754
  have htrace : WordTrace (prefixWord ++ tailWord_3605754) baseStart_3605754 baseEnd_3605754 := by
    simpa [prefixWord, tailWord_3605754, baseEnd_3605754] using wordTrace_append hprefix tailTrace_3605754
  have hstable : (prefixWord ++ tailWord_3605754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3605754).length < 2 ^ (prefixWord ++ tailWord_3605754).sum := by decide
  have hdescent : baseEnd_3605754 < baseStart_3605754 := by decide
  rcases family_descends (prefixWord ++ tailWord_3605754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3605784 : List Nat := [2, 1, 2, 3, 1, 3, 1, 2, 1, 2, 5]
def baseStart_3605784 : Nat := 118140960795 + 3605784 * 2 ^ 59
def prefixEnd_3605784 : Nat := 4983230072969 + 3 ^ 40 * 3605784 * 2
def baseEnd_3605784 : Nat := 1851500328291625587217307

theorem tailTrace_3605784 : CollatzResearch.WordTrace tailWord_3605784 prefixEnd_3605784 1851500328291625587217307 := by
  unfold tailWord_3605784
  simp only [CollatzResearch.WordTrace]
  refine ⟨65756873384433930862232203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87675831179245241149642937 65756873384433930862232203)
  ·
    refine ⟨98635310076650896293348305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65756873384433930862232203 98635310076650896293348305)
    ·
      refine ⟨73976482557488172220011229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98635310076650896293348305 73976482557488172220011229)
      ·
        refine ⟨27741180959058064582504211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73976482557488172220011229 27741180959058064582504211)
        ·
          refine ⟨41611771438587096873756317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27741180959058064582504211 41611771438587096873756317)
          ·
            refine ⟨15604414289470161327658619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41611771438587096873756317 15604414289470161327658619)
            ·
              refine ⟨23406621434205241991487929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15604414289470161327658619 23406621434205241991487929)
              ·
                refine ⟨17554966075653931493615947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23406621434205241991487929 17554966075653931493615947)
                ·
                  refine ⟨26332449113480897240423921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17554966075653931493615947 26332449113480897240423921)
                  ·
                    refine ⟨19749336835110672930317941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26332449113480897240423921 19749336835110672930317941)
                    ·
                      refine ⟨1851500328291625587217307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19749336835110672930317941 1851500328291625587217307)
                      ·
                        rfl

theorem cell23_3605784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 2, 1, 2, 5].length) (baseStart_3605784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3605784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3605784 prefixEnd_3605784 := by exact prefixLift 3605784
  have htrace : WordTrace (prefixWord ++ tailWord_3605784) baseStart_3605784 baseEnd_3605784 := by
    simpa [prefixWord, tailWord_3605784, baseEnd_3605784] using wordTrace_append hprefix tailTrace_3605784
  have hstable : (prefixWord ++ tailWord_3605784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3605784).length < 2 ^ (prefixWord ++ tailWord_3605784).sum := by decide
  have hdescent : baseEnd_3605784 < baseStart_3605784 := by decide
  rcases family_descends (prefixWord ++ tailWord_3605784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3605811 : List Nat := [1, 1, 1, 2, 5, 2, 1, 1, 1, 6, 2]
def baseStart_3605811 : Nat := 118140960795 + 3605811 * 2 ^ 59
def prefixEnd_3605811 : Nat := 4983230072969 + 3 ^ 40 * 3605811 * 2
def baseEnd_3605811 : Nat := 1851514192269296981579683

theorem tailTrace_3605811 : CollatzResearch.WordTrace tailWord_3605811 prefixEnd_3605811 1851514192269296981579683 := by
  unfold tailWord_3605811
  simp only [CollatzResearch.WordTrace]
  refine ⟨131514731539770045335697287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87676487693180030223798191 131514731539770045335697287)
  ·
    refine ⟨197272097309655068003545931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131514731539770045335697287 197272097309655068003545931)
    ·
      refine ⟨295908145964482602005318897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197272097309655068003545931 295908145964482602005318897)
      ·
        refine ⟨221931109473361951503989173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 295908145964482602005318897 221931109473361951503989173)
        ·
          refine ⟨20806041513127682953498985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 221931109473361951503989173 20806041513127682953498985)
          ·
            refine ⟨15604531134845762215124239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20806041513127682953498985 15604531134845762215124239)
            ·
              refine ⟨23406796702268643322686359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15604531134845762215124239 23406796702268643322686359)
              ·
                refine ⟨35110195053402964984029539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23406796702268643322686359 35110195053402964984029539)
                ·
                  refine ⟨52665292580104447476044309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35110195053402964984029539 52665292580104447476044309)
                  ·
                    refine ⟨2468685589692395975439577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 52665292580104447476044309 2468685589692395975439577)
                    ·
                      refine ⟨1851514192269296981579683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2468685589692395975439577 1851514192269296981579683)
                      ·
                        rfl

theorem cell23_3605811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 1, 1, 6, 2].length) (baseStart_3605811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3605811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3605811 prefixEnd_3605811 := by exact prefixLift 3605811
  have htrace : WordTrace (prefixWord ++ tailWord_3605811) baseStart_3605811 baseEnd_3605811 := by
    simpa [prefixWord, tailWord_3605811, baseEnd_3605811] using wordTrace_append hprefix tailTrace_3605811
  have hstable : (prefixWord ++ tailWord_3605811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3605811).length < 2 ^ (prefixWord ++ tailWord_3605811).sum := by decide
  have hdescent : baseEnd_3605811 < baseStart_3605811 := by decide
  rcases family_descends (prefixWord ++ tailWord_3605811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3605828 : List Nat := [2, 3, 4, 1, 1, 2, 1, 1, 1, 3, 4]
def baseStart_3605828 : Nat := 118140960795 + 3605828 * 2 ^ 59
def prefixEnd_3605828 : Nat := 4983230072969 + 3 ^ 40 * 3605828 * 2
def baseEnd_3605828 : Nat := 1851522921440423415067105

theorem tailTrace_3605828 : CollatzResearch.WordTrace tailWord_3605828 prefixEnd_3605828 1851522921440423415067105 := by
  unfold tailWord_3605828
  simp only [CollatzResearch.WordTrace]
  refine ⟨65757675790354228619533069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87676901053805638159377425 65757675790354228619533069)
  ·
    refine ⟨24659128421382835732324901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65757675790354228619533069 24659128421382835732324901)
    ·
      refine ⟨4623586579009281699810919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24659128421382835732324901 4623586579009281699810919)
      ·
        refine ⟨6935379868513922549716379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4623586579009281699810919 6935379868513922549716379)
        ·
          refine ⟨10403069802770883824574569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6935379868513922549716379 10403069802770883824574569)
          ·
            refine ⟨7802302352078162868430927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10403069802770883824574569 7802302352078162868430927)
            ·
              refine ⟨11703453528117244302646391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7802302352078162868430927 11703453528117244302646391)
              ·
                refine ⟨17555180292175866453969587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11703453528117244302646391 17555180292175866453969587)
                ·
                  refine ⟨26332770438263799680954381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17555180292175866453969587 26332770438263799680954381)
                  ·
                    refine ⟨9874788914348924880357893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26332770438263799680954381 9874788914348924880357893)
                    ·
                      refine ⟨1851522921440423415067105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9874788914348924880357893 1851522921440423415067105)
                      ·
                        rfl

theorem cell23_3605828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_3605828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3605828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3605828 prefixEnd_3605828 := by exact prefixLift 3605828
  have htrace : WordTrace (prefixWord ++ tailWord_3605828) baseStart_3605828 baseEnd_3605828 := by
    simpa [prefixWord, tailWord_3605828, baseEnd_3605828] using wordTrace_append hprefix tailTrace_3605828
  have hstable : (prefixWord ++ tailWord_3605828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3605828).length < 2 ^ (prefixWord ++ tailWord_3605828).sum := by decide
  have hdescent : baseEnd_3605828 < baseStart_3605828 := by decide
  rcases family_descends (prefixWord ++ tailWord_3605828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3605831 : List Nat := [1, 1, 4, 1, 2, 4, 1, 1, 1, 4, 3]
def baseStart_3605831 : Nat := 118140960795 + 3605831 * 2 ^ 59
def prefixEnd_3605831 : Nat := 4983230072969 + 3 ^ 40 * 3605831 * 2
def baseEnd_3605831 : Nat := 1851524461882386903329591

theorem tailTrace_3605831 : CollatzResearch.WordTrace tailWord_3605831 prefixEnd_3605831 1851524461882386903329591 := by
  unfold tailWord_3605831
  simp only [CollatzResearch.WordTrace]
  refine ⟨131515460999697588751425347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87676973999798392500950231 131515460999697588751425347)
  ·
    refine ⟨197273191499546383127138021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131515460999697588751425347 197273191499546383127138021)
    ·
      refine ⟨36988723406164946836338379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 197273191499546383127138021 36988723406164946836338379)
      ·
        refine ⟨55483085109247420254507569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36988723406164946836338379 55483085109247420254507569)
        ·
          refine ⟨41612313831935565190880677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55483085109247420254507569 41612313831935565190880677)
          ·
            refine ⟨7802308843487918473290127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41612313831935565190880677 7802308843487918473290127)
            ·
              refine ⟨11703463265231877709935191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7802308843487918473290127 11703463265231877709935191)
              ·
                refine ⟨17555194897847816564902787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11703463265231877709935191 17555194897847816564902787)
                ·
                  refine ⟨26332792346771724847354181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17555194897847816564902787 26332792346771724847354181)
                  ·
                    refine ⟨4937398565019698408878909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26332792346771724847354181 4937398565019698408878909)
                    ·
                      refine ⟨1851524461882386903329591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4937398565019698408878909 1851524461882386903329591)
                      ·
                        rfl

theorem cell23_3605831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 1, 1, 4, 3].length) (baseStart_3605831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3605831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3605831 prefixEnd_3605831 := by exact prefixLift 3605831
  have htrace : WordTrace (prefixWord ++ tailWord_3605831) baseStart_3605831 baseEnd_3605831 := by
    simpa [prefixWord, tailWord_3605831, baseEnd_3605831] using wordTrace_append hprefix tailTrace_3605831
  have hstable : (prefixWord ++ tailWord_3605831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3605831).length < 2 ^ (prefixWord ++ tailWord_3605831).sum := by decide
  have hdescent : baseEnd_3605831 < baseStart_3605831 := by decide
  rcases family_descends (prefixWord ++ tailWord_3605831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3605868 : List Nat := [2, 2, 1, 1, 5, 2, 3, 1, 6]
def baseStart_3605868 : Nat := 118140960795 + 3605868 * 2 ^ 59
def prefixEnd_3605868 : Nat := 4983230072969 + 3 ^ 40 * 3605868 * 2
def baseEnd_3605868 : Nat := 205727051185178139840769

theorem tailTrace_3605868 : CollatzResearch.WordTrace tailWord_3605868 prefixEnd_3605868 205727051185178139840769 := by
  unfold tailWord_3605868
  simp only [CollatzResearch.WordTrace]
  refine ⟨65758405250281772035261129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87677873667042362713681505 65758405250281772035261129)
  ·
    refine ⟨49318803937711329026445847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65758405250281772035261129 49318803937711329026445847)
    ·
      refine ⟨73978205906566993539668771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49318803937711329026445847 73978205906566993539668771)
      ·
        refine ⟨110967308859850490309503157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73978205906566993539668771 110967308859850490309503157)
        ·
          refine ⟨10403185205610983466515921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 110967308859850490309503157 10403185205610983466515921)
          ·
            refine ⟨7802388904208237599886941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10403185205610983466515921 7802388904208237599886941)
            ·
              refine ⟨2925895839078089099957603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7802388904208237599886941 2925895839078089099957603)
              ·
                refine ⟨4388843758617133649936405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2925895839078089099957603 4388843758617133649936405)
                ·
                  refine ⟨205727051185178139840769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4388843758617133649936405 205727051185178139840769)
                  ·
                    rfl

theorem cell23_3605868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 6].length) (baseStart_3605868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3605868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3605868 prefixEnd_3605868 := by exact prefixLift 3605868
  have htrace : WordTrace (prefixWord ++ tailWord_3605868) baseStart_3605868 baseEnd_3605868 := by
    simpa [prefixWord, tailWord_3605868, baseEnd_3605868] using wordTrace_append hprefix tailTrace_3605868
  have hstable : (prefixWord ++ tailWord_3605868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3605868).length < 2 ^ (prefixWord ++ tailWord_3605868).sum := by decide
  have hdescent : baseEnd_3605868 < baseStart_3605868 := by decide
  rcases family_descends (prefixWord ++ tailWord_3605868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3605871 : List Nat := [1, 1, 2, 1, 3, 1, 3, 1, 3, 5, 2]
def baseStart_3605871 : Nat := 118140960795 + 3605871 * 2 ^ 59
def prefixEnd_3605871 : Nat := 4983230072969 + 3 ^ 40 * 3605871 * 2
def baseEnd_3605871 : Nat := 1851545001108566746829407

theorem tailTrace_3605871 : CollatzResearch.WordTrace tailWord_3605871 prefixEnd_3605871 1851545001108566746829407 := by
  unfold tailWord_3605871
  simp only [CollatzResearch.WordTrace]
  refine ⟨131516919919552675582881467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87677946613035117055254311 131516919919552675582881467)
  ·
    refine ⟨197275379879329013374322201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131516919919552675582881467 197275379879329013374322201)
    ·
      refine ⟨147956534909496760030741651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197275379879329013374322201 147956534909496760030741651)
      ·
        refine ⟨221934802364245140046112477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147956534909496760030741651 221934802364245140046112477)
        ·
          refine ⟨83225550886591927517292179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 221934802364245140046112477 83225550886591927517292179)
          ·
            refine ⟨124838326329887891275938269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83225550886591927517292179 124838326329887891275938269)
            ·
              refine ⟨46814372373707959228476851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124838326329887891275938269 46814372373707959228476851)
              ·
                refine ⟨70221558560561938842715277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46814372373707959228476851 70221558560561938842715277)
                ·
                  refine ⟨26333084460210727066018229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70221558560561938842715277 26333084460210727066018229)
                  ·
                    refine ⟨2468726668144755662439209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26333084460210727066018229 2468726668144755662439209)
                    ·
                      refine ⟨1851545001108566746829407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2468726668144755662439209 1851545001108566746829407)
                      ·
                        rfl

theorem cell23_3605871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 3, 5, 2].length) (baseStart_3605871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3605871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3605871 prefixEnd_3605871 := by exact prefixLift 3605871
  have htrace : WordTrace (prefixWord ++ tailWord_3605871) baseStart_3605871 baseEnd_3605871 := by
    simpa [prefixWord, tailWord_3605871, baseEnd_3605871] using wordTrace_append hprefix tailTrace_3605871
  have hstable : (prefixWord ++ tailWord_3605871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3605871).length < 2 ^ (prefixWord ++ tailWord_3605871).sum := by decide
  have hdescent : baseEnd_3605871 < baseStart_3605871 := by decide
  rcases family_descends (prefixWord ++ tailWord_3605871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3605881 : List Nat := [1, 2, 1, 3, 2, 1, 3, 4, 1, 5]
def baseStart_3605881 : Nat := 118140960795 + 3605881 * 2 ^ 59
def prefixEnd_3605881 : Nat := 4983230072969 + 3 ^ 40 * 3605881 * 2
def baseEnd_3605881 : Nat := 617183378638370569234787

theorem tailTrace_3605881 : CollatzResearch.WordTrace tailWord_3605881 prefixEnd_3605881 617183378638370569234787 := by
  unfold tailWord_3605881
  simp only [CollatzResearch.WordTrace]
  refine ⟨131517284649516447290745497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87678189766344298193830331 131517284649516447290745497)
  ·
    refine ⟨98637963487137335468059123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131517284649516447290745497 98637963487137335468059123)
    ·
      refine ⟨147956945230706003202088685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98637963487137335468059123 147956945230706003202088685)
      ·
        refine ⟨55483854461514751200783257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147956945230706003202088685 55483854461514751200783257)
        ·
          refine ⟨41612890846136063400587443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55483854461514751200783257 41612890846136063400587443)
          ·
            refine ⟨62419336269204095100881165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41612890846136063400587443 62419336269204095100881165)
            ·
              refine ⟨23407251100951535662830437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62419336269204095100881165 23407251100951535662830437)
              ·
                refine ⟨4388859581428412936780707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23407251100951535662830437 4388859581428412936780707)
                ·
                  refine ⟨6583289372142619405171061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4388859581428412936780707 6583289372142619405171061)
                  ·
                    refine ⟨617183378638370569234787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6583289372142619405171061 617183378638370569234787)
                    ·
                      rfl

theorem cell23_3605881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 4, 1, 5].length) (baseStart_3605881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3605881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3605881 prefixEnd_3605881 := by exact prefixLift 3605881
  have htrace : WordTrace (prefixWord ++ tailWord_3605881) baseStart_3605881 baseEnd_3605881 := by
    simpa [prefixWord, tailWord_3605881, baseEnd_3605881] using wordTrace_append hprefix tailTrace_3605881
  have hstable : (prefixWord ++ tailWord_3605881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3605881).length < 2 ^ (prefixWord ++ tailWord_3605881).sum := by decide
  have hdescent : baseEnd_3605881 < baseStart_3605881 := by decide
  rcases family_descends (prefixWord ++ tailWord_3605881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3605889 : List Nat := [1, 2, 4, 3, 3, 1, 1, 3, 1, 4]
def baseStart_3605889 : Nat := 118140960795 + 3605889 * 2 ^ 59
def prefixEnd_3605889 : Nat := 4983230072969 + 3 ^ 40 * 3605889 * 2
def baseEnd_3605889 : Nat := 617184747920115892134775

theorem tailTrace_3605889 : CollatzResearch.WordTrace tailWord_3605889 prefixEnd_3605889 617184747920115892134775 := by
  unfold tailWord_3605889
  simp only [CollatzResearch.WordTrace]
  refine ⟨131517576433487464657036721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87678384288991643104691147 131517576433487464657036721)
  ·
    refine ⟨98638182325115598492777541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131517576433487464657036721 98638182325115598492777541)
    ·
      refine ⟨18494659185959174717395789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98638182325115598492777541 18494659185959174717395789)
      ·
        refine ⟨6935497194734690519023421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18494659185959174717395789 6935497194734690519023421)
        ·
          refine ⟨2600811448025508944633783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6935497194734690519023421 2600811448025508944633783)
          ·
            refine ⟨3901217172038263416950675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2600811448025508944633783 3901217172038263416950675)
            ·
              refine ⟨5851825758057395125426013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3901217172038263416950675 5851825758057395125426013)
              ·
                refine ⟨2194434659271523172034755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5851825758057395125426013 2194434659271523172034755)
                ·
                  refine ⟨3291651988907284758052133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2194434659271523172034755 3291651988907284758052133)
                  ·
                    refine ⟨617184747920115892134775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3291651988907284758052133 617184747920115892134775)
                    ·
                      rfl

theorem cell23_3605889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 1, 3, 1, 4].length) (baseStart_3605889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3605889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3605889 prefixEnd_3605889 := by exact prefixLift 3605889
  have htrace : WordTrace (prefixWord ++ tailWord_3605889) baseStart_3605889 baseEnd_3605889 := by
    simpa [prefixWord, tailWord_3605889, baseEnd_3605889] using wordTrace_append hprefix tailTrace_3605889
  have hstable : (prefixWord ++ tailWord_3605889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3605889).length < 2 ^ (prefixWord ++ tailWord_3605889).sum := by decide
  have hdescent : baseEnd_3605889 < baseStart_3605889 := by decide
  rcases family_descends (prefixWord ++ tailWord_3605889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3605912 : List Nat := [2, 1, 2, 5, 2, 2, 1, 1, 3, 1, 3]
def baseStart_3605912 : Nat := 118140960795 + 3605912 * 2 ^ 59
def prefixEnd_3605912 : Nat := 4983230072969 + 3 ^ 40 * 3605912 * 2
def baseEnd_3605912 : Nat := 1851566053815401086416719

theorem tailTrace_3605912 : CollatzResearch.WordTrace tailWord_3605912 prefixEnd_3605912 1851566053815401086416719 := by
  unfold tailWord_3605912
  simp only [CollatzResearch.WordTrace]
  refine ⟨65759207656202069792561995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87678943541602759723415993 65759207656202069792561995)
  ·
    refine ⟨98638811484303104688842993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65759207656202069792561995 98638811484303104688842993)
    ·
      refine ⟨73979108613227328516632245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98638811484303104688842993 73979108613227328516632245)
      ·
        refine ⟨6935541432490062048434273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 73979108613227328516632245 6935541432490062048434273)
        ·
          refine ⟨5201656074367546536325705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6935541432490062048434273 5201656074367546536325705)
          ·
            refine ⟨3901242055775659902244279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5201656074367546536325705 3901242055775659902244279)
            ·
              refine ⟨5851863083663489853366419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3901242055775659902244279 5851863083663489853366419)
              ·
                refine ⟨8777794625495234780049629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5851863083663489853366419 8777794625495234780049629)
                ·
                  refine ⟨3291672984560713042518611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8777794625495234780049629 3291672984560713042518611)
                  ·
                    refine ⟨4937509476841069563777917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3291672984560713042518611 4937509476841069563777917)
                    ·
                      refine ⟨1851566053815401086416719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4937509476841069563777917 1851566053815401086416719)
                      ·
                        rfl

theorem cell23_3605912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_3605912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3605912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3605912 prefixEnd_3605912 := by exact prefixLift 3605912
  have htrace : WordTrace (prefixWord ++ tailWord_3605912) baseStart_3605912 baseEnd_3605912 := by
    simpa [prefixWord, tailWord_3605912, baseEnd_3605912] using wordTrace_append hprefix tailTrace_3605912
  have hstable : (prefixWord ++ tailWord_3605912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3605912).length < 2 ^ (prefixWord ++ tailWord_3605912).sum := by decide
  have hdescent : baseEnd_3605912 < baseStart_3605912 := by decide
  rcases family_descends (prefixWord ++ tailWord_3605912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3605938 : List Nat := [3, 2, 1, 1, 1, 1, 2, 6, 1, 2, 3]
def baseStart_3605938 : Nat := 118140960795 + 3605938 * 2 ^ 59
def prefixEnd_3605938 : Nat := 4983230072969 + 3 ^ 40 * 3605938 * 2
def baseEnd_3605938 : Nat := 1851579404312417984691599

theorem tailTrace_3605938 : CollatzResearch.WordTrace tailWord_3605938 prefixEnd_3605938 1851579404312417984691599 := by
  unfold tailWord_3605938
  simp only [CollatzResearch.WordTrace]
  refine ⟨32879840902577486506392617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87679575740206630683713645 32879840902577486506392617)
  ·
    refine ⟨24659880676933114879794463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32879840902577486506392617 24659880676933114879794463)
    ·
      refine ⟨36989821015399672319691695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24659880676933114879794463 36989821015399672319691695)
      ·
        refine ⟨55484731523099508479537543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36989821015399672319691695 55484731523099508479537543)
        ·
          refine ⟨83227097284649262719306315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55484731523099508479537543 83227097284649262719306315)
          ·
            refine ⟨124840645926973894078959473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83227097284649262719306315 124840645926973894078959473)
            ·
              refine ⟨93630484445230420559219605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124840645926973894078959473 93630484445230420559219605)
              ·
                refine ⟨4388928958370175963713419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 93630484445230420559219605 4388928958370175963713419)
                ·
                  refine ⟨6583393437555263945570129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4388928958370175963713419 6583393437555263945570129)
                  ·
                    refine ⟨4937545078166447959177597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6583393437555263945570129 4937545078166447959177597)
                    ·
                      refine ⟨1851579404312417984691599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4937545078166447959177597 1851579404312417984691599)
                      ·
                        rfl

theorem cell23_3605938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 6, 1, 2, 3].length) (baseStart_3605938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3605938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3605938 prefixEnd_3605938 := by exact prefixLift 3605938
  have htrace : WordTrace (prefixWord ++ tailWord_3605938) baseStart_3605938 baseEnd_3605938 := by
    simpa [prefixWord, tailWord_3605938, baseEnd_3605938] using wordTrace_append hprefix tailTrace_3605938
  have hstable : (prefixWord ++ tailWord_3605938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3605938).length < 2 ^ (prefixWord ++ tailWord_3605938).sum := by decide
  have hdescent : baseEnd_3605938 < baseStart_3605938 := by decide
  rcases family_descends (prefixWord ++ tailWord_3605938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3605941 : List Nat := [1, 3, 3, 2, 2, 1, 2, 9]
def baseStart_3605941 : Nat := 118140960795 + 3605941 * 2 ^ 59
def prefixEnd_3605941 : Nat := 4983230072969 + 3 ^ 40 * 3605941 * 2
def baseEnd_3605941 : Nat := 68577072027940054553855

theorem tailTrace_3605941 : CollatzResearch.WordTrace tailWord_3605941 prefixEnd_3605941 68577072027940054553855 := by
  unfold tailWord_3605941
  simp only [CollatzResearch.WordTrace]
  refine ⟨131519473029299077537929677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87679648686199385025286451 131519473029299077537929677)
  ·
    refine ⟨49319802385987154076723629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131519473029299077537929677 49319802385987154076723629)
    ·
      refine ⟨18494925894745182778771361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49319802385987154076723629 18494925894745182778771361)
      ·
        refine ⟨13871194421058887084078521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18494925894745182778771361 13871194421058887084078521)
        ·
          refine ⟨10403395815794165313058891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13871194421058887084078521 10403395815794165313058891)
          ·
            refine ⟨15605093723691247969588337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10403395815794165313058891 15605093723691247969588337)
            ·
              refine ⟨11703820292768435977191253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15605093723691247969588337 11703820292768435977191253)
              ·
                refine ⟨68577072027940054553855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11703820292768435977191253 68577072027940054553855)
                ·
                  rfl

theorem cell23_3605941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 9].length) (baseStart_3605941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3605941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3605941 prefixEnd_3605941 := by exact prefixLift 3605941
  have htrace : WordTrace (prefixWord ++ tailWord_3605941) baseStart_3605941 baseEnd_3605941 := by
    simpa [prefixWord, tailWord_3605941, baseEnd_3605941] using wordTrace_append hprefix tailTrace_3605941
  have hstable : (prefixWord ++ tailWord_3605941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3605941).length < 2 ^ (prefixWord ++ tailWord_3605941).sum := by decide
  have hdescent : baseEnd_3605941 < baseStart_3605941 := by decide
  rcases family_descends (prefixWord ++ tailWord_3605941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3605985 : List Nat := [1, 2, 3, 1, 2, 3, 2, 3, 2, 1, 3]
def baseStart_3605985 : Nat := 118140960795 + 3605985 * 2 ^ 59
def prefixEnd_3605985 : Nat := 4983230072969 + 3 ^ 40 * 3605985 * 2
def baseEnd_3605985 : Nat := 1851603537903179300803883

theorem tailTrace_3605985 : CollatzResearch.WordTrace tailWord_3605985 prefixEnd_3605985 1851603537903179300803883 := by
  unfold tailWord_3605985
  simp only [CollatzResearch.WordTrace]
  refine ⟨131521077841139673052531409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87680718560759782035020939 131521077841139673052531409)
  ·
    refine ⟨98640808380854754789398557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131521077841139673052531409 98640808380854754789398557)
    ·
      refine ⟨36990303142820533046024459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98640808380854754789398557 36990303142820533046024459)
      ·
        refine ⟨55485454714230799569036689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36990303142820533046024459 55485454714230799569036689)
        ·
          refine ⟨41614091035673099676777517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55485454714230799569036689 41614091035673099676777517)
          ·
            refine ⟨15605284138377412378791569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41614091035673099676777517 15605284138377412378791569)
            ·
              refine ⟨11703963103783059284093677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15605284138377412378791569 11703963103783059284093677)
              ·
                refine ⟨4388986163918647231535129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11703963103783059284093677 4388986163918647231535129)
                ·
                  refine ⟨3291739622938985423651347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4388986163918647231535129 3291739622938985423651347)
                  ·
                    refine ⟨4937609434408478135477021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3291739622938985423651347 4937609434408478135477021)
                    ·
                      refine ⟨1851603537903179300803883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4937609434408478135477021 1851603537903179300803883)
                      ·
                        rfl

theorem cell23_3605985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 3, 2, 1, 3].length) (baseStart_3605985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3605985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3605985 prefixEnd_3605985 := by exact prefixLift 3605985
  have htrace : WordTrace (prefixWord ++ tailWord_3605985) baseStart_3605985 baseEnd_3605985 := by
    simpa [prefixWord, tailWord_3605985, baseEnd_3605985] using wordTrace_append hprefix tailTrace_3605985
  have hstable : (prefixWord ++ tailWord_3605985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3605985).length < 2 ^ (prefixWord ++ tailWord_3605985).sum := by decide
  have hdescent : baseEnd_3605985 < baseStart_3605985 := by decide
  rcases family_descends (prefixWord ++ tailWord_3605985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3606011 : List Nat := [1, 1, 1, 1, 1, 3, 2, 2, 4, 4, 3]
def baseStart_3606011 : Nat := 118140960795 + 3606011 * 2 ^ 59
def prefixEnd_3606011 : Nat := 4983230072969 + 3 ^ 40 * 3606011 * 2
def baseEnd_3606011 : Nat := 1851616888400196199078763

theorem tailTrace_3606011 : CollatzResearch.WordTrace tailWord_3606011 prefixEnd_3606011 1851616888400196199078763 := by
  unfold tailWord_3606011
  simp only [CollatzResearch.WordTrace]
  refine ⟨131522026139045479492977887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87681350759363652995318591 131522026139045479492977887)
  ·
    refine ⟨197283039208568219239466831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131522026139045479492977887 197283039208568219239466831)
    ·
      refine ⟨295924558812852328859200247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197283039208568219239466831 295924558812852328859200247)
      ·
        refine ⟨443886838219278493288800371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295924558812852328859200247 443886838219278493288800371)
        ·
          refine ⟨665830257328917739933200557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 443886838219278493288800371 665830257328917739933200557)
          ·
            refine ⟨249686346498344152474950209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 665830257328917739933200557 249686346498344152474950209)
            ·
              refine ⟨187264759873758114356212657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 249686346498344152474950209 187264759873758114356212657)
              ·
                refine ⟨140448569905318585767159493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 187264759873758114356212657 140448569905318585767159493)
                ·
                  refine ⟨26334106857247234831342405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 140448569905318585767159493 26334106857247234831342405)
                  ·
                    refine ⟨4937645035733856530876701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26334106857247234831342405 4937645035733856530876701)
                    ·
                      refine ⟨1851616888400196199078763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4937645035733856530876701 1851616888400196199078763)
                      ·
                        rfl

theorem cell23_3606011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 4, 4, 3].length) (baseStart_3606011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3606011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3606011 prefixEnd_3606011 := by exact prefixLift 3606011
  have htrace : WordTrace (prefixWord ++ tailWord_3606011) baseStart_3606011 baseEnd_3606011 := by
    simpa [prefixWord, tailWord_3606011, baseEnd_3606011] using wordTrace_append hprefix tailTrace_3606011
  have hstable : (prefixWord ++ tailWord_3606011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3606011).length < 2 ^ (prefixWord ++ tailWord_3606011).sum := by decide
  have hdescent : baseEnd_3606011 < baseStart_3606011 := by decide
  rcases family_descends (prefixWord ++ tailWord_3606011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3606012 : List Nat := [2, 2, 2, 1, 2, 1, 6, 1, 1, 3, 2]
def baseStart_3606012 : Nat := 118140960795 + 3606012 * 2 ^ 59
def prefixEnd_3606012 : Nat := 4983230072969 + 3 ^ 40 * 3606012 * 2
def baseEnd_3606012 : Nat := 1851617401880850695166259

theorem tailTrace_3606012 : CollatzResearch.WordTrace tailWord_3606012 prefixEnd_3606012 1851617401880850695166259 := by
  unfold tailWord_3606012
  simp only [CollatzResearch.WordTrace]
  refine ⟨65761031306020928331882145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87681375074694571109176193 65761031306020928331882145)
  ·
    refine ⟨49320773479515696248911609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65761031306020928331882145 49320773479515696248911609)
    ·
      refine ⟨36990580109636772186683707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49320773479515696248911609 36990580109636772186683707)
      ·
        refine ⟨55485870164455158280025561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36990580109636772186683707 55485870164455158280025561)
        ·
          refine ⟨41614402623341368710019171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55485870164455158280025561 41614402623341368710019171)
          ·
            refine ⟨62421603935012053065028757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41614402623341368710019171 62421603935012053065028757)
            ·
              refine ⟨2926012684453689987423223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 62421603935012053065028757 2926012684453689987423223)
              ·
                refine ⟨4389019026680534981134835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2926012684453689987423223 4389019026680534981134835)
                ·
                  refine ⟨6583528540020802471702253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4389019026680534981134835 6583528540020802471702253)
                  ·
                    refine ⟨2468823202507800926888345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6583528540020802471702253 2468823202507800926888345)
                    ·
                      refine ⟨1851617401880850695166259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2468823202507800926888345 1851617401880850695166259)
                      ·
                        rfl

theorem cell23_3606012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 6, 1, 1, 3, 2].length) (baseStart_3606012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3606012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3606012 prefixEnd_3606012 := by exact prefixLift 3606012
  have htrace : WordTrace (prefixWord ++ tailWord_3606012) baseStart_3606012 baseEnd_3606012 := by
    simpa [prefixWord, tailWord_3606012, baseEnd_3606012] using wordTrace_append hprefix tailTrace_3606012
  have hstable : (prefixWord ++ tailWord_3606012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3606012).length < 2 ^ (prefixWord ++ tailWord_3606012).sum := by decide
  have hdescent : baseEnd_3606012 < baseStart_3606012 := by decide
  rcases family_descends (prefixWord ++ tailWord_3606012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3606025 : List Nat := [1, 2, 1, 1, 3, 1, 5, 1, 4, 2, 2]
def baseStart_3606025 : Nat := 118140960795 + 3606025 * 2 ^ 59
def prefixEnd_3606025 : Nat := 4983230072969 + 3 ^ 40 * 3606025 * 2
def baseEnd_3606025 : Nat := 1851624077129359144303699

theorem tailTrace_3606025 : CollatzResearch.WordTrace tailWord_3606025 prefixEnd_3606025 1851624077129359144303699 := by
  unfold tailWord_3606025
  simp only [CollatzResearch.WordTrace]
  refine ⟨131522536760994759883987529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87681691173996506589325019 131522536760994759883987529)
  ·
    refine ⟨98641902570746069912990647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131522536760994759883987529 98641902570746069912990647)
    ·
      refine ⟨147962853856119104869485971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98641902570746069912990647 147962853856119104869485971)
      ·
        refine ⟨221944280784178657304228957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147962853856119104869485971 221944280784178657304228957)
        ·
          refine ⟨83229105294066996489085859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 221944280784178657304228957 83229105294066996489085859)
          ·
            refine ⟨124843657941100494733628789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83229105294066996489085859 124843657941100494733628789)
            ·
              refine ⟨11704092931978171381277699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 124843657941100494733628789 11704092931978171381277699)
              ·
                refine ⟨17556139397967257071916549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11704092931978171381277699 17556139397967257071916549)
                ·
                  refine ⟨3291776137118860700984353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17556139397967257071916549 3291776137118860700984353)
                  ·
                    refine ⟨2468832102839145525738265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3291776137118860700984353 2468832102839145525738265)
                    ·
                      refine ⟨1851624077129359144303699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2468832102839145525738265 1851624077129359144303699)
                      ·
                        rfl

theorem cell23_3606025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 1, 4, 2, 2].length) (baseStart_3606025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3606025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3606025 prefixEnd_3606025 := by exact prefixLift 3606025
  have htrace : WordTrace (prefixWord ++ tailWord_3606025) baseStart_3606025 baseEnd_3606025 := by
    simpa [prefixWord, tailWord_3606025, baseEnd_3606025] using wordTrace_append hprefix tailTrace_3606025
  have hstable : (prefixWord ++ tailWord_3606025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3606025).length < 2 ^ (prefixWord ++ tailWord_3606025).sum := by decide
  have hdescent : baseEnd_3606025 < baseStart_3606025 := by decide
  rcases family_descends (prefixWord ++ tailWord_3606025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3606036 : List Nat := [2, 4, 3, 1, 2, 1, 3, 1, 2, 1, 3]
def baseStart_3606036 : Nat := 118140960795 + 3606036 * 2 ^ 59
def prefixEnd_3606036 : Nat := 4983230072969 + 3 ^ 40 * 3606036 * 2
def baseEnd_3606036 : Nat := 1851629725416558601266149

theorem tailTrace_3606036 : CollatzResearch.WordTrace tailWord_3606036 prefixEnd_3606036 1851629725416558601266149 := by
  unfold tailWord_3606036
  simp only [CollatzResearch.WordTrace]
  refine ⟨65761468981977454381318981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87681958642636605841758641 65761468981977454381318981)
  ·
    refine ⟨12330275434120772696497309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65761468981977454381318981 12330275434120772696497309)
    ·
      refine ⟨4623853287795289761186491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12330275434120772696497309 4623853287795289761186491)
      ·
        refine ⟨6935779931692934641779737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4623853287795289761186491 6935779931692934641779737)
        ·
          refine ⟨5201834948769700981334803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6935779931692934641779737 5201834948769700981334803)
          ·
            refine ⟨7802752423154551472002205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5201834948769700981334803 7802752423154551472002205)
            ·
              refine ⟨2926032158682956802000827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7802752423154551472002205 2926032158682956802000827)
              ·
                refine ⟨4389048238024435203001241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2926032158682956802000827 4389048238024435203001241)
                ·
                  refine ⟨3291786178518326402250931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4389048238024435203001241 3291786178518326402250931)
                  ·
                    refine ⟨4937679267777489603376397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3291786178518326402250931 4937679267777489603376397)
                    ·
                      refine ⟨1851629725416558601266149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4937679267777489603376397 1851629725416558601266149)
                      ·
                        rfl

theorem cell23_3606036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 3, 1, 2, 1, 3].length) (baseStart_3606036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3606036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3606036 prefixEnd_3606036 := by exact prefixLift 3606036
  have htrace : WordTrace (prefixWord ++ tailWord_3606036) baseStart_3606036 baseEnd_3606036 := by
    simpa [prefixWord, tailWord_3606036, baseEnd_3606036] using wordTrace_append hprefix tailTrace_3606036
  have hstable : (prefixWord ++ tailWord_3606036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3606036).length < 2 ^ (prefixWord ++ tailWord_3606036).sum := by decide
  have hdescent : baseEnd_3606036 < baseStart_3606036 := by decide
  rcases family_descends (prefixWord ++ tailWord_3606036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3606048 : List Nat := [2, 1, 1, 6, 1, 1, 2, 2, 7]
def baseStart_3606048 : Nat := 118140960795 + 3606048 * 2 ^ 59
def prefixEnd_3606048 : Nat := 4983230072969 + 3 ^ 40 * 3606048 * 2
def baseEnd_3606048 : Nat := 205737320798268061590677

theorem tailTrace_3606048 : CollatzResearch.WordTrace tailWord_3606048 prefixEnd_3606048 205737320798268061590677 := by
  unfold tailWord_3606048
  simp only [CollatzResearch.WordTrace]
  refine ⟨65761687819955717406037399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87682250426607623208049865 65761687819955717406037399)
  ·
    refine ⟨98642531729933576109056099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65761687819955717406037399 98642531729933576109056099)
    ·
      refine ⟨147963797594900364163584149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98642531729933576109056099 147963797594900364163584149)
      ·
        refine ⟨6935803012260954570168007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 147963797594900364163584149 6935803012260954570168007)
        ·
          refine ⟨10403704518391431855252011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6935803012260954570168007 10403704518391431855252011)
          ·
            refine ⟨15605556777587147782878017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10403704518391431855252011 15605556777587147782878017)
            ·
              refine ⟨11704167583190360837158513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15605556777587147782878017 11704167583190360837158513)
              ·
                refine ⟨8778125687392770627868885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11704167583190360837158513 8778125687392770627868885)
                ·
                  refine ⟨205737320798268061590677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8778125687392770627868885 205737320798268061590677)
                  ·
                    rfl

theorem cell23_3606048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 2, 7].length) (baseStart_3606048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3606048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3606048 prefixEnd_3606048 := by exact prefixLift 3606048
  have htrace : WordTrace (prefixWord ++ tailWord_3606048) baseStart_3606048 baseEnd_3606048 := by
    simpa [prefixWord, tailWord_3606048, baseEnd_3606048] using wordTrace_append hprefix tailTrace_3606048
  have hstable : (prefixWord ++ tailWord_3606048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3606048).length < 2 ^ (prefixWord ++ tailWord_3606048).sum := by decide
  have hdescent : baseEnd_3606048 < baseStart_3606048 := by decide
  rcases family_descends (prefixWord ++ tailWord_3606048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3606093 : List Nat := [1, 6, 1, 1, 3, 2, 2, 1, 2, 2, 2]
def baseStart_3606093 : Nat := 118140960795 + 3606093 * 2 ^ 59
def prefixEnd_3606093 : Nat := 4983230072969 + 3 ^ 40 * 3606093 * 2
def baseEnd_3606093 : Nat := 1851658993813864878253387

theorem tailTrace_3606093 : CollatzResearch.WordTrace tailWord_3606093 prefixEnd_3606093 1851658993813864878253387 := by
  unfold tailWord_3606093
  simp only [CollatzResearch.WordTrace]
  refine ⟨131525016924748407497462933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87683344616498938331641955 131525016924748407497462933)
  ·
    refine ⟨6165235168347581601443575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 131525016924748407497462933 6165235168347581601443575)
    ·
      refine ⟨9247852752521372402165363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6165235168347581601443575 9247852752521372402165363)
      ·
        refine ⟨13871779128782058603248045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9247852752521372402165363 13871779128782058603248045)
        ·
          refine ⟨5201917173293271976218017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13871779128782058603248045 5201917173293271976218017)
          ·
            refine ⟨3901437879969953982163513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5201917173293271976218017 3901437879969953982163513)
            ·
              refine ⟨2926078409977465486622635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3901437879969953982163513 2926078409977465486622635)
              ·
                refine ⟨4389117614966198229933953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2926078409977465486622635 4389117614966198229933953)
                ·
                  refine ⟨3291838211224648672450465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4389117614966198229933953 3291838211224648672450465)
                  ·
                    refine ⟨2468878658418486504337849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3291838211224648672450465 2468878658418486504337849)
                    ·
                      refine ⟨1851658993813864878253387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2468878658418486504337849 1851658993813864878253387)
                      ·
                        rfl

theorem cell23_3606093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 2, 1, 2, 2, 2].length) (baseStart_3606093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3606093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3606093 prefixEnd_3606093 := by exact prefixLift 3606093
  have htrace : WordTrace (prefixWord ++ tailWord_3606093) baseStart_3606093 baseEnd_3606093 := by
    simpa [prefixWord, tailWord_3606093, baseEnd_3606093] using wordTrace_append hprefix tailTrace_3606093
  have hstable : (prefixWord ++ tailWord_3606093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3606093).length < 2 ^ (prefixWord ++ tailWord_3606093).sum := by decide
  have hdescent : baseEnd_3606093 < baseStart_3606093 := by decide
  rcases family_descends (prefixWord ++ tailWord_3606093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3606111 : List Nat := [1, 1, 2, 3, 1, 1, 1, 1, 3, 3, 6]
def baseStart_3606111 : Nat := 118140960795 + 3606111 * 2 ^ 59
def prefixEnd_3606111 : Nat := 4983230072969 + 3 ^ 40 * 3606111 * 2
def baseEnd_3606111 : Nat := 1851668236465645807828303

theorem tailTrace_3606111 : CollatzResearch.WordTrace tailWord_3606111 prefixEnd_3606111 1851668236465645807828303 := by
  unfold tailWord_3606111
  simp only [CollatzResearch.WordTrace]
  refine ⟨131525673438683196571618187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87683782292455464381078791 131525673438683196571618187)
  ·
    refine ⟨197288510158024794857427281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131525673438683196571618187 197288510158024794857427281)
    ·
      refine ⟨147966382618518596143070461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197288510158024794857427281 147966382618518596143070461)
      ·
        refine ⟨55487393481944473553651423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147966382618518596143070461 55487393481944473553651423)
        ·
          refine ⟨83231090222916710330477135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55487393481944473553651423 83231090222916710330477135)
          ·
            refine ⟨124846635334375065495715703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83231090222916710330477135 124846635334375065495715703)
            ·
              refine ⟨187269953001562598243573555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124846635334375065495715703 187269953001562598243573555)
              ·
                refine ⟨280904929502343897365360333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 187269953001562598243573555 280904929502343897365360333)
                ·
                  refine ⟨105339348563378961512010125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 280904929502343897365360333 105339348563378961512010125)
                  ·
                    refine ⟨39502255711267110567003797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 105339348563378961512010125 39502255711267110567003797)
                    ·
                      refine ⟨1851668236465645807828303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39502255711267110567003797 1851668236465645807828303)
                      ·
                        rfl

theorem cell23_3606111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 3, 6].length) (baseStart_3606111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3606111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3606111 prefixEnd_3606111 := by exact prefixLift 3606111
  have htrace : WordTrace (prefixWord ++ tailWord_3606111) baseStart_3606111 baseEnd_3606111 := by
    simpa [prefixWord, tailWord_3606111, baseEnd_3606111] using wordTrace_append hprefix tailTrace_3606111
  have hstable : (prefixWord ++ tailWord_3606111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3606111).length < 2 ^ (prefixWord ++ tailWord_3606111).sum := by decide
  have hdescent : baseEnd_3606111 < baseStart_3606111 := by decide
  rcases family_descends (prefixWord ++ tailWord_3606111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3606115 : List Nat := [1, 1, 1, 5, 1, 4, 2, 1, 2, 1, 4]
def baseStart_3606115 : Nat := 118140960795 + 3606115 * 2 ^ 59
def prefixEnd_3606115 : Nat := 4983230072969 + 3 ^ 40 * 3606115 * 2
def baseEnd_3606115 : Nat := 1851670290388263792178285

theorem tailTrace_3606115 : CollatzResearch.WordTrace tailWord_3606115 prefixEnd_3606115 1851670290388263792178285 := by
  unfold tailWord_3606115
  simp only [CollatzResearch.WordTrace]
  refine ⟨131525819330668705254763799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87683879553779136836509199 131525819330668705254763799)
  ·
    refine ⟨197288728996003057882145699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131525819330668705254763799 197288728996003057882145699)
    ·
      refine ⟨295933093494004586823218549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197288728996003057882145699 295933093494004586823218549)
      ·
        refine ⟨27743727515062930014676739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 295933093494004586823218549 27743727515062930014676739)
        ·
          refine ⟨41615591272594395022015109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27743727515062930014676739 41615591272594395022015109)
          ·
            refine ⟨7802923363611449066627833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41615591272594395022015109 7802923363611449066627833)
            ·
              refine ⟨5852192522708586799970875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7802923363611449066627833 5852192522708586799970875)
              ·
                refine ⟨8778288784062880199956313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5852192522708586799970875 8778288784062880199956313)
                ·
                  refine ⟨6583716588047160149967235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8778288784062880199956313 6583716588047160149967235)
                  ·
                    refine ⟨9875574882070740224950853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6583716588047160149967235 9875574882070740224950853)
                    ·
                      refine ⟨1851670290388263792178285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9875574882070740224950853 1851670290388263792178285)
                      ·
                        rfl

theorem cell23_3606115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2, 1, 2, 1, 4].length) (baseStart_3606115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3606115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3606115 prefixEnd_3606115 := by exact prefixLift 3606115
  have htrace : WordTrace (prefixWord ++ tailWord_3606115) baseStart_3606115 baseEnd_3606115 := by
    simpa [prefixWord, tailWord_3606115, baseEnd_3606115] using wordTrace_append hprefix tailTrace_3606115
  have hstable : (prefixWord ++ tailWord_3606115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3606115).length < 2 ^ (prefixWord ++ tailWord_3606115).sum := by decide
  have hdescent : baseEnd_3606115 < baseStart_3606115 := by decide
  rcases family_descends (prefixWord ++ tailWord_3606115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3606121 : List Nat := [1, 2, 1, 1, 1, 4, 2, 1, 10]
def baseStart_3606121 : Nat := 118140960795 + 3606121 * 2 ^ 59
def prefixEnd_3606121 : Nat := 4983230072969 + 3 ^ 40 * 3606121 * 2
def baseEnd_3606121 : Nat := 205741485696910085411473

theorem tailTrace_3606121 : CollatzResearch.WordTrace tailWord_3606121 prefixEnd_3606121 205741485696910085411473 := by
  unfold tailWord_3606121
  simp only [CollatzResearch.WordTrace]
  refine ⟨131526038168646968279482217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87684025445764645519654811 131526038168646968279482217)
  ·
    refine ⟨98644528626485226209611663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131526038168646968279482217 98644528626485226209611663)
    ·
      refine ⟨147966792939727839314417495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98644528626485226209611663 147966792939727839314417495)
      ·
        refine ⟨221950189409591758971626243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147966792939727839314417495 221950189409591758971626243)
        ·
          refine ⟨332925284114387638457439365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221950189409591758971626243 332925284114387638457439365)
          ·
            refine ⟨62423490771447682210769881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 332925284114387638457439365 62423490771447682210769881)
            ·
              refine ⟨46817618078585761658077411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62423490771447682210769881 46817618078585761658077411)
              ·
                refine ⟨70226427117878642487116117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46817618078585761658077411 70226427117878642487116117)
                ·
                  refine ⟨205741485696910085411473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 70226427117878642487116117 205741485696910085411473)
                  ·
                    rfl

theorem cell23_3606121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 10].length) (baseStart_3606121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3606121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3606121 prefixEnd_3606121 := by exact prefixLift 3606121
  have htrace : WordTrace (prefixWord ++ tailWord_3606121) baseStart_3606121 baseEnd_3606121 := by
    simpa [prefixWord, tailWord_3606121, baseEnd_3606121] using wordTrace_append hprefix tailTrace_3606121
  have hstable : (prefixWord ++ tailWord_3606121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3606121).length < 2 ^ (prefixWord ++ tailWord_3606121).sum := by decide
  have hdescent : baseEnd_3606121 < baseStart_3606121 := by decide
  rcases family_descends (prefixWord ++ tailWord_3606121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3606199 : List Nat := [1, 1, 3, 1, 5, 1, 2, 4, 1, 1, 3]
def baseStart_3606199 : Nat := 118140960795 + 3606199 * 2 ^ 59
def prefixEnd_3606199 : Nat := 4983230072969 + 3 ^ 40 * 3606199 * 2
def baseEnd_3606199 : Nat := 1851713422763241463527899

theorem tailTrace_3606199 : CollatzResearch.WordTrace tailWord_3606199 prefixEnd_3606199 1851713422763241463527899 := by
  unfold tailWord_3606199
  simp only [CollatzResearch.WordTrace]
  refine ⟨131528883062364387600821651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87685922041576258400547767 131528883062364387600821651)
  ·
    refine ⟨197293324593546581401232477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131528883062364387600821651 197293324593546581401232477)
    ·
      refine ⟨73984996722579968025462179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197293324593546581401232477 73984996722579968025462179)
      ·
        refine ⟨110977495083869952038193269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73984996722579968025462179 110977495083869952038193269)
        ·
          refine ⟨10404140164112808003580619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 110977495083869952038193269 10404140164112808003580619)
          ·
            refine ⟨15606210246169212005370929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10404140164112808003580619 15606210246169212005370929)
            ·
              refine ⟨11704657684626909004028197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15606210246169212005370929 11704657684626909004028197)
              ·
                refine ⟨2194623315867545438255287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11704657684626909004028197 2194623315867545438255287)
                ·
                  refine ⟨3291934973801318157382931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2194623315867545438255287 3291934973801318157382931)
                  ·
                    refine ⟨4937902460701977236074397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3291934973801318157382931 4937902460701977236074397)
                    ·
                      refine ⟨1851713422763241463527899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4937902460701977236074397 1851713422763241463527899)
                      ·
                        rfl

theorem cell23_3606199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 4, 1, 1, 3].length) (baseStart_3606199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3606199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3606199 prefixEnd_3606199 := by exact prefixLift 3606199
  have htrace : WordTrace (prefixWord ++ tailWord_3606199) baseStart_3606199 baseEnd_3606199 := by
    simpa [prefixWord, tailWord_3606199, baseEnd_3606199] using wordTrace_append hprefix tailTrace_3606199
  have hstable : (prefixWord ++ tailWord_3606199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3606199).length < 2 ^ (prefixWord ++ tailWord_3606199).sum := by decide
  have hdescent : baseEnd_3606199 < baseStart_3606199 := by decide
  rcases family_descends (prefixWord ++ tailWord_3606199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3606222 : List Nat := [4, 1, 1, 1, 3, 1, 4, 2, 1, 1, 4]
def baseStart_3606222 : Nat := 118140960795 + 3606222 * 2 ^ 59
def prefixEnd_3606222 : Nat := 4983230072969 + 3 ^ 40 * 3606222 * 2
def baseEnd_3606222 : Nat := 1851725232818294873540293

theorem tailTrace_3606222 : CollatzResearch.WordTrace tailWord_3606222 prefixEnd_3606222 1851725232818294873540293 := by
  unfold tailWord_3606222
  simp only [CollatzResearch.WordTrace]
  refine ⟨16441215242660132816113615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87686481294187375019272613 16441215242660132816113615)
  ·
    refine ⟨24661822863990199224170423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16441215242660132816113615 24661822863990199224170423)
    ·
      refine ⟨36992734295985298836255635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24661822863990199224170423 36992734295985298836255635)
      ·
        refine ⟨55489101443977948254383453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36992734295985298836255635 55489101443977948254383453)
        ·
          refine ⟨20808413041491730595393795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55489101443977948254383453 20808413041491730595393795)
          ·
            refine ⟨31212619562237595893090693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20808413041491730595393795 31212619562237595893090693)
            ·
              refine ⟨5852366167919549229954505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31212619562237595893090693 5852366167919549229954505)
              ·
                refine ⟨4389274625939661922465879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5852366167919549229954505 4389274625939661922465879)
                ·
                  refine ⟨6583911938909492883698819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4389274625939661922465879 6583911938909492883698819)
                  ·
                    refine ⟨9875867908364239325548229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6583911938909492883698819 9875867908364239325548229)
                    ·
                      refine ⟨1851725232818294873540293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9875867908364239325548229 1851725232818294873540293)
                      ·
                        rfl

theorem cell23_3606222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4, 2, 1, 1, 4].length) (baseStart_3606222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3606222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3606222 prefixEnd_3606222 := by exact prefixLift 3606222
  have htrace : WordTrace (prefixWord ++ tailWord_3606222) baseStart_3606222 baseEnd_3606222 := by
    simpa [prefixWord, tailWord_3606222, baseEnd_3606222] using wordTrace_append hprefix tailTrace_3606222
  have hstable : (prefixWord ++ tailWord_3606222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3606222).length < 2 ^ (prefixWord ++ tailWord_3606222).sum := by decide
  have hdescent : baseEnd_3606222 < baseStart_3606222 := by decide
  rcases family_descends (prefixWord ++ tailWord_3606222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3606265 : List Nat := [1, 2, 1, 3, 1, 1, 1, 1, 1, 9, 2]
def baseStart_3606265 : Nat := 118140960795 + 3606265 * 2 ^ 59
def prefixEnd_3606265 : Nat := 4983230072969 + 3 ^ 40 * 3606265 * 2
def baseEnd_3606265 : Nat := 1851747312486438205302595

theorem tailTrace_3606265 : CollatzResearch.WordTrace tailWord_3606265 prefixEnd_3606265 1851747312486438205302595 := by
  unfold tailWord_3606265
  simp only [CollatzResearch.WordTrace]
  refine ⟨131531290280125280872724249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87687526853416853915149499 131531290280125280872724249)
  ·
    refine ⟨98648467710093960654543187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131531290280125280872724249 98648467710093960654543187)
    ·
      refine ⟨147972701565140940981814781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98648467710093960654543187 147972701565140940981814781)
      ·
        refine ⟨55489763086927852868180543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147972701565140940981814781 55489763086927852868180543)
        ·
          refine ⟨83234644630391779302270815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55489763086927852868180543 83234644630391779302270815)
          ·
            refine ⟨124851966945587668953406223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83234644630391779302270815 124851966945587668953406223)
            ·
              refine ⟨187277950418381503430109335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124851966945587668953406223 187277950418381503430109335)
              ·
                refine ⟨280916925627572255145164003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 187277950418381503430109335 280916925627572255145164003)
                ·
                  refine ⟨421375388441358382717746005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 280916925627572255145164003 421375388441358382717746005)
                  ·
                    refine ⟨2468996416648584273736793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 421375388441358382717746005 2468996416648584273736793)
                    ·
                      refine ⟨1851747312486438205302595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2468996416648584273736793 1851747312486438205302595)
                      ·
                        rfl

theorem cell23_3606265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 9, 2].length) (baseStart_3606265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3606265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3606265 prefixEnd_3606265 := by exact prefixLift 3606265
  have htrace : WordTrace (prefixWord ++ tailWord_3606265) baseStart_3606265 baseEnd_3606265 := by
    simpa [prefixWord, tailWord_3606265, baseEnd_3606265] using wordTrace_append hprefix tailTrace_3606265
  have hstable : (prefixWord ++ tailWord_3606265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3606265).length < 2 ^ (prefixWord ++ tailWord_3606265).sum := by decide
  have hdescent : baseEnd_3606265 < baseStart_3606265 := by decide
  rcases family_descends (prefixWord ++ tailWord_3606265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3606272 : List Nat := [2, 1, 1, 2, 1, 1, 2, 7, 2, 1, 3]
def baseStart_3606272 : Nat := 118140960795 + 3606272 * 2 ^ 59
def prefixEnd_3606272 : Nat := 4983230072969 + 3 ^ 40 * 3606272 * 2
def baseEnd_3606272 : Nat := 1851750906851019677915063

theorem tailTrace_3606272 : CollatzResearch.WordTrace tailWord_3606272 prefixEnd_3606272 1851750906851019677915063 := by
  unfold tailWord_3606272
  simp only [CollatzResearch.WordTrace]
  refine ⟨65765772795549960534114535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87687697060733280712152713 65765772795549960534114535)
  ·
    refine ⟨98648659193324940801171803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65765772795549960534114535 98648659193324940801171803)
    ·
      refine ⟨147972988789987411201757705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98648659193324940801171803 147972988789987411201757705)
      ·
        refine ⟨110979741592490558401318279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147972988789987411201757705 110979741592490558401318279)
        ·
          refine ⟨166469612388735837601977419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110979741592490558401318279 166469612388735837601977419)
          ·
            refine ⟨249704418583103756402966129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166469612388735837601977419 249704418583103756402966129)
            ·
              refine ⟨187278313937327817302224597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 249704418583103756402966129 187278313937327817302224597)
              ·
                refine ⟨4389335482906120718020889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 187278313937327817302224597 4389335482906120718020889)
                ·
                  refine ⟨3292001612179590538515667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4389335482906120718020889 3292001612179590538515667)
                  ·
                    refine ⟨4938002418269385807773501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3292001612179590538515667 4938002418269385807773501)
                    ·
                      refine ⟨1851750906851019677915063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4938002418269385807773501 1851750906851019677915063)
                      ·
                        rfl

theorem cell23_3606272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 7, 2, 1, 3].length) (baseStart_3606272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3606272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3606272 prefixEnd_3606272 := by exact prefixLift 3606272
  have htrace : WordTrace (prefixWord ++ tailWord_3606272) baseStart_3606272 baseEnd_3606272 := by
    simpa [prefixWord, tailWord_3606272, baseEnd_3606272] using wordTrace_append hprefix tailTrace_3606272
  have hstable : (prefixWord ++ tailWord_3606272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3606272).length < 2 ^ (prefixWord ++ tailWord_3606272).sum := by decide
  have hdescent : baseEnd_3606272 < baseStart_3606272 := by decide
  rcases family_descends (prefixWord ++ tailWord_3606272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3606345 : List Nat := [1, 2, 1, 1, 2, 4, 1, 2, 1, 5, 3]
def baseStart_3606345 : Nat := 118140960795 + 3606345 * 2 ^ 59
def prefixEnd_3606345 : Nat := 4983230072969 + 3 ^ 40 * 3606345 * 2
def baseEnd_3606345 : Nat := 1851788390938797892302227

theorem tailTrace_3606345 : CollatzResearch.WordTrace tailWord_3606345 prefixEnd_3606345 1851788390938797892302227 := by
  unfold tailWord_3606345
  simp only [CollatzResearch.WordTrace]
  refine ⟨131534208119835454535636489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87689472079890303023757659 131534208119835454535636489)
  ·
    refine ⟨98650656089876590901727367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131534208119835454535636489 98650656089876590901727367)
    ·
      refine ⟨147975984134814886352591051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98650656089876590901727367 147975984134814886352591051)
      ·
        refine ⟨221963976202222329528886577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147975984134814886352591051 221963976202222329528886577)
        ·
          refine ⟨166472982151666747146664933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 221963976202222329528886577 166472982151666747146664933)
          ·
            refine ⟨31213684153437515089999675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 166472982151666747146664933 31213684153437515089999675)
            ·
              refine ⟨46820526230156272634999513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31213684153437515089999675 46820526230156272634999513)
              ·
                refine ⟨35115394672617204476249635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46820526230156272634999513 35115394672617204476249635)
                ·
                  refine ⟨52673092008925806714374453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35115394672617204476249635 52673092008925806714374453)
                  ·
                    refine ⟨4938102375836794379472605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52673092008925806714374453 4938102375836794379472605)
                    ·
                      refine ⟨1851788390938797892302227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4938102375836794379472605 1851788390938797892302227)
                      ·
                        rfl

theorem cell23_3606345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 5, 3].length) (baseStart_3606345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3606345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3606345 prefixEnd_3606345 := by exact prefixLift 3606345
  have htrace : WordTrace (prefixWord ++ tailWord_3606345) baseStart_3606345 baseEnd_3606345 := by
    simpa [prefixWord, tailWord_3606345, baseEnd_3606345] using wordTrace_append hprefix tailTrace_3606345
  have hstable : (prefixWord ++ tailWord_3606345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3606345).length < 2 ^ (prefixWord ++ tailWord_3606345).sum := by decide
  have hdescent : baseEnd_3606345 < baseStart_3606345 := by decide
  rcases family_descends (prefixWord ++ tailWord_3606345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3606375 : List Nat := [1, 1, 5, 1, 2, 1, 2, 1, 1, 1, 7]
def baseStart_3606375 : Nat := 118140960795 + 3606375 * 2 ^ 59
def prefixEnd_3606375 : Nat := 4983230072969 + 3 ^ 40 * 3606375 * 2
def baseEnd_3606375 : Nat := 1851803795358432774927089

theorem tailTrace_3606375 : CollatzResearch.WordTrace tailWord_3606375 prefixEnd_3606375 1851803795358432774927089 := by
  unfold tailWord_3606375
  simp only [CollatzResearch.WordTrace]
  refine ⟨131535302309726769659228579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87690201539817846439485719 131535302309726769659228579)
  ·
    refine ⟨197302953464590154488842869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131535302309726769659228579 197302953464590154488842869)
    ·
      refine ⟨18497151887305326983329019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 197302953464590154488842869 18497151887305326983329019)
      ·
        refine ⟨27745727830957990474993529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18497151887305326983329019 27745727830957990474993529)
        ·
          refine ⟨20809295873218492856245147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27745727830957990474993529 20809295873218492856245147)
          ·
            refine ⟨31213943809827739284367721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20809295873218492856245147 31213943809827739284367721)
            ·
              refine ⟨23410457857370804463275791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31213943809827739284367721 23410457857370804463275791)
              ·
                refine ⟨35115686786056206694913687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23410457857370804463275791 35115686786056206694913687)
                ·
                  refine ⟨52673530179084310042370531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35115686786056206694913687 52673530179084310042370531)
                  ·
                    refine ⟨79010295268626465063555797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52673530179084310042370531 79010295268626465063555797)
                    ·
                      refine ⟨1851803795358432774927089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 79010295268626465063555797 1851803795358432774927089)
                      ·
                        rfl

theorem cell23_3606375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_3606375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3606375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3606375 prefixEnd_3606375 := by exact prefixLift 3606375
  have htrace : WordTrace (prefixWord ++ tailWord_3606375) baseStart_3606375 baseEnd_3606375 := by
    simpa [prefixWord, tailWord_3606375, baseEnd_3606375] using wordTrace_append hprefix tailTrace_3606375
  have hstable : (prefixWord ++ tailWord_3606375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3606375).length < 2 ^ (prefixWord ++ tailWord_3606375).sum := by decide
  have hdescent : baseEnd_3606375 < baseStart_3606375 := by decide
  rcases family_descends (prefixWord ++ tailWord_3606375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3606382 : List Nat := [4, 1, 2, 3, 1, 1, 1, 2, 1, 7]
def baseStart_3606382 : Nat := 118140960795 + 3606382 * 2 ^ 59
def prefixEnd_3606382 : Nat := 4983230072969 + 3 ^ 40 * 3606382 * 2
def baseEnd_3606382 : Nat := 617269129907671415846519

theorem tailTrace_3606382 : CollatzResearch.WordTrace tailWord_3606382 prefixEnd_3606382 617269129907671415846519 := by
  unfold tailWord_3606382
  simp only [CollatzResearch.WordTrace]
  refine ⟨16441944702587676231841675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87690371747134273236488933 16441944702587676231841675)
  ·
    refine ⟨24662917053881514347762513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16441944702587676231841675 24662917053881514347762513)
    ·
      refine ⟨18497187790411135760821885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24662917053881514347762513 18497187790411135760821885)
      ·
        refine ⟨6936445421404175910308207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18497187790411135760821885 6936445421404175910308207)
        ·
          refine ⟨10404668132106263865462311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6936445421404175910308207 10404668132106263865462311)
          ·
            refine ⟨15607002198159395798193467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10404668132106263865462311 15607002198159395798193467)
            ·
              refine ⟨23410503297239093697290201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15607002198159395798193467 23410503297239093697290201)
              ·
                refine ⟨17557877472929320272967651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23410503297239093697290201 17557877472929320272967651)
                ·
                  refine ⟨26336816209393980409451477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17557877472929320272967651 26336816209393980409451477)
                  ·
                    refine ⟨617269129907671415846519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26336816209393980409451477 617269129907671415846519)
                    ·
                      rfl

theorem cell23_3606382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 2, 1, 7].length) (baseStart_3606382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3606382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3606382 prefixEnd_3606382 := by exact prefixLift 3606382
  have htrace : WordTrace (prefixWord ++ tailWord_3606382) baseStart_3606382 baseEnd_3606382 := by
    simpa [prefixWord, tailWord_3606382, baseEnd_3606382] using wordTrace_append hprefix tailTrace_3606382
  have hstable : (prefixWord ++ tailWord_3606382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3606382).length < 2 ^ (prefixWord ++ tailWord_3606382).sum := by decide
  have hdescent : baseEnd_3606382 < baseStart_3606382 := by decide
  rcases family_descends (prefixWord ++ tailWord_3606382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3606385 : List Nat := [1, 2, 2, 2, 1, 3, 1, 1, 3, 3, 4]
def baseStart_3606385 : Nat := 118140960795 + 3606385 * 2 ^ 59
def prefixEnd_3606385 : Nat := 4983230072969 + 3 ^ 40 * 3606385 * 2
def baseEnd_3606385 : Nat := 1851808930164977735802043

theorem tailTrace_3606385 : CollatzResearch.WordTrace tailWord_3606385 prefixEnd_3606385 1851808930164977735802043 := by
  unfold tailWord_3606385
  simp only [CollatzResearch.WordTrace]
  refine ⟨131535667039690541367092609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87690444693127027578061739 131535667039690541367092609)
  ·
    refine ⟨98651750279767906025319457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131535667039690541367092609 98651750279767906025319457)
    ·
      refine ⟨73988812709825929518989593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98651750279767906025319457 73988812709825929518989593)
      ·
        refine ⟨55491609532369447139242195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73988812709825929518989593 55491609532369447139242195)
        ·
          refine ⟨83237414298554170708863293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55491609532369447139242195 83237414298554170708863293)
          ·
            refine ⟨31214030361957814015823735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83237414298554170708863293 31214030361957814015823735)
            ·
              refine ⟨46821045542936721023735603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31214030361957814015823735 46821045542936721023735603)
              ·
                refine ⟨70231568314405081535603405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46821045542936721023735603 70231568314405081535603405)
                ·
                  refine ⟨26336838117901905575851277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70231568314405081535603405 26336838117901905575851277)
                  ·
                    refine ⟨9876314294213214590944229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26336838117901905575851277 9876314294213214590944229)
                    ·
                      refine ⟨1851808930164977735802043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9876314294213214590944229 1851808930164977735802043)
                      ·
                        rfl

theorem cell23_3606385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 3, 3, 4].length) (baseStart_3606385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3606385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3606385 prefixEnd_3606385 := by exact prefixLift 3606385
  have htrace : WordTrace (prefixWord ++ tailWord_3606385) baseStart_3606385 baseEnd_3606385 := by
    simpa [prefixWord, tailWord_3606385, baseEnd_3606385] using wordTrace_append hprefix tailTrace_3606385
  have hstable : (prefixWord ++ tailWord_3606385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3606385).length < 2 ^ (prefixWord ++ tailWord_3606385).sum := by decide
  have hdescent : baseEnd_3606385 < baseStart_3606385 := by decide
  rcases family_descends (prefixWord ++ tailWord_3606385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3606425 : List Nat := [1, 2, 1, 2, 1, 3, 4, 1, 8]
def baseStart_3606425 : Nat := 118140960795 + 3606425 * 2 ^ 59
def prefixEnd_3606425 : Nat := 4983230072969 + 3 ^ 40 * 3606425 * 2
def baseEnd_3606425 : Nat := 205758829932350842144651

theorem tailTrace_3606425 : CollatzResearch.WordTrace tailWord_3606425 prefixEnd_3606425 205758829932350842144651 := by
  unfold tailWord_3606425
  simp only [CollatzResearch.WordTrace]
  refine ⟨131537125959545628198548729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87691417306363752132365819 131537125959545628198548729)
  ·
    refine ⟨98652844469659221148911547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131537125959545628198548729 98652844469659221148911547)
    ·
      refine ⟨147979266704488831723367321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98652844469659221148911547 147979266704488831723367321)
      ·
        refine ⟨110984450028366623792525491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147979266704488831723367321 110984450028366623792525491)
        ·
          refine ⟨166476675042549935688788237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110984450028366623792525491 166476675042549935688788237)
          ·
            refine ⟨62428753140956225883295589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 166476675042549935688788237 62428753140956225883295589)
            ·
              refine ⟨11705391213929292353117923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62428753140956225883295589 11705391213929292353117923)
              ·
                refine ⟨17558086820893938529676885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11705391213929292353117923 17558086820893938529676885)
                ·
                  refine ⟨205758829932350842144651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17558086820893938529676885 205758829932350842144651)
                  ·
                    rfl

theorem cell23_3606425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 1, 8].length) (baseStart_3606425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3606425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3606425 prefixEnd_3606425 := by exact prefixLift 3606425
  have htrace : WordTrace (prefixWord ++ tailWord_3606425) baseStart_3606425 baseEnd_3606425 := by
    simpa [prefixWord, tailWord_3606425, baseEnd_3606425] using wordTrace_append hprefix tailTrace_3606425
  have hstable : (prefixWord ++ tailWord_3606425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3606425).length < 2 ^ (prefixWord ++ tailWord_3606425).sum := by decide
  have hdescent : baseEnd_3606425 < baseStart_3606425 := by decide
  rcases family_descends (prefixWord ++ tailWord_3606425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3606429 : List Nat := [1, 4, 2, 1, 2, 2, 3, 1, 3, 4]
def baseStart_3606429 : Nat := 118140960795 + 3606429 * 2 ^ 59
def prefixEnd_3606429 : Nat := 4983230072969 + 3 ^ 40 * 3606429 * 2
def baseEnd_3606429 : Nat := 617277174437925187883947

theorem tailTrace_3606429 : CollatzResearch.WordTrace tailWord_3606429 prefixEnd_3606429 617277174437925187883947 := by
  unfold tailWord_3606429
  simp only [CollatzResearch.WordTrace]
  refine ⟨131537271851531136881694341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87691514567687424587796227 131537271851531136881694341)
  ·
    refine ⟨24663238472162088165317689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131537271851531136881694341 24663238472162088165317689)
    ·
      refine ⟨18497428854121566123988267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24663238472162088165317689 18497428854121566123988267)
      ·
        refine ⟨27746143281182349185982401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18497428854121566123988267 27746143281182349185982401)
        ·
          refine ⟨20809607460886761889486801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27746143281182349185982401 20809607460886761889486801)
          ·
            refine ⟨15607205595665071417115101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20809607460886761889486801 15607205595665071417115101)
            ·
              refine ⟨5852702098374401781418163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15607205595665071417115101 5852702098374401781418163)
              ·
                refine ⟨8779053147561602672127245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5852702098374401781418163 8779053147561602672127245)
                ·
                  refine ⟨3292144930335601002047717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8779053147561602672127245 3292144930335601002047717)
                  ·
                    refine ⟨617277174437925187883947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3292144930335601002047717 617277174437925187883947)
                    ·
                      rfl

theorem cell23_3606429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3, 1, 3, 4].length) (baseStart_3606429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3606429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3606429 prefixEnd_3606429 := by exact prefixLift 3606429
  have htrace : WordTrace (prefixWord ++ tailWord_3606429) baseStart_3606429 baseEnd_3606429 := by
    simpa [prefixWord, tailWord_3606429, baseEnd_3606429] using wordTrace_append hprefix tailTrace_3606429
  have hstable : (prefixWord ++ tailWord_3606429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3606429).length < 2 ^ (prefixWord ++ tailWord_3606429).sum := by decide
  have hdescent : baseEnd_3606429 < baseStart_3606429 := by decide
  rcases family_descends (prefixWord ++ tailWord_3606429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3606479 : List Nat := [1, 1, 2, 1, 1, 5, 1, 4, 2, 3, 2]
def baseStart_3606479 : Nat := 118140960795 + 3606479 * 2 ^ 59
def prefixEnd_3606479 : Nat := 4983230072969 + 3 ^ 40 * 3606479 * 2
def baseEnd_3606479 : Nat := 1851857197346500368026611

theorem tailTrace_3606479 : CollatzResearch.WordTrace tailWord_3606479 prefixEnd_3606479 1851857197346500368026611 := by
  unfold tailWord_3606479
  simp only [CollatzResearch.WordTrace]
  refine ⟨131539095501349995421014491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87692730334233330280676327 131539095501349995421014491)
  ·
    refine ⟨197308643252024993131521737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131539095501349995421014491 197308643252024993131521737)
    ·
      refine ⟨147981482439018744848641303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197308643252024993131521737 147981482439018744848641303)
      ·
        refine ⟨221972223658528117272961955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147981482439018744848641303 221972223658528117272961955)
        ·
          refine ⟨332958335487792175909442933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221972223658528117272961955 332958335487792175909442933)
          ·
            refine ⟨31214843951980516491510275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 332958335487792175909442933 31214843951980516491510275)
            ·
              refine ⟨46822265927970774737265413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31214843951980516491510275 46822265927970774737265413)
              ·
                refine ⟨8779174861494520263237265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46822265927970774737265413 8779174861494520263237265)
                ·
                  refine ⟨6584381146120890197427949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8779174861494520263237265 6584381146120890197427949)
                  ·
                    refine ⟨2469142929795333824035481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6584381146120890197427949 2469142929795333824035481)
                    ·
                      refine ⟨1851857197346500368026611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2469142929795333824035481 1851857197346500368026611)
                      ·
                        rfl

theorem cell23_3606479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 4, 2, 3, 2].length) (baseStart_3606479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3606479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3606479 prefixEnd_3606479 := by exact prefixLift 3606479
  have htrace : WordTrace (prefixWord ++ tailWord_3606479) baseStart_3606479 baseEnd_3606479 := by
    simpa [prefixWord, tailWord_3606479, baseEnd_3606479] using wordTrace_append hprefix tailTrace_3606479
  have hstable : (prefixWord ++ tailWord_3606479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3606479).length < 2 ^ (prefixWord ++ tailWord_3606479).sum := by decide
  have hdescent : baseEnd_3606479 < baseStart_3606479 := by decide
  rcases family_descends (prefixWord ++ tailWord_3606479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3606513 : List Nat := [1, 2, 2, 2, 5, 2, 1, 1, 2, 3, 2]
def baseStart_3606513 : Nat := 118140960795 + 3606513 * 2 ^ 59
def prefixEnd_3606513 : Nat := 4983230072969 + 3 ^ 40 * 3606513 * 2
def baseEnd_3606513 : Nat := 1851874655688753235001455

theorem tailTrace_3606513 : CollatzResearch.WordTrace tailWord_3606513 prefixEnd_3606513 1851874655688753235001455 := by
  unfold tailWord_3606513
  simp only [CollatzResearch.WordTrace]
  refine ⟨131540335583226819227752193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87693557055484546151834795 131540335583226819227752193)
  ·
    refine ⟨98655251687420114420814145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131540335583226819227752193 98655251687420114420814145)
    ·
      refine ⟨73991438765565085815610609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98655251687420114420814145 73991438765565085815610609)
      ·
        refine ⟨55493579074173814361707957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73991438765565085815610609 55493579074173814361707957)
        ·
          refine ⟨5202523038203795096410121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 55493579074173814361707957 5202523038203795096410121)
          ·
            refine ⟨3901892278652846322307591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5202523038203795096410121 3901892278652846322307591)
            ·
              refine ⟨5852838417979269483461387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3901892278652846322307591 5852838417979269483461387)
              ·
                refine ⟨8779257626968904225192081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5852838417979269483461387 8779257626968904225192081)
                ·
                  refine ⟨6584443220226678168894061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8779257626968904225192081 6584443220226678168894061)
                  ·
                    refine ⟨2469166207585004313335273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6584443220226678168894061 2469166207585004313335273)
                    ·
                      refine ⟨1851874655688753235001455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2469166207585004313335273 1851874655688753235001455)
                      ·
                        rfl

theorem cell23_3606513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 1, 1, 2, 3, 2].length) (baseStart_3606513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3606513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3606513 prefixEnd_3606513 := by exact prefixLift 3606513
  have htrace : WordTrace (prefixWord ++ tailWord_3606513) baseStart_3606513 baseEnd_3606513 := by
    simpa [prefixWord, tailWord_3606513, baseEnd_3606513] using wordTrace_append hprefix tailTrace_3606513
  have hstable : (prefixWord ++ tailWord_3606513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3606513).length < 2 ^ (prefixWord ++ tailWord_3606513).sum := by decide
  have hdescent : baseEnd_3606513 < baseStart_3606513 := by decide
  rcases family_descends (prefixWord ++ tailWord_3606513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3606515 : List Nat := [1, 1, 1, 2, 2, 2, 1, 13]
def baseStart_3606515 : Nat := 118140960795 + 3606515 * 2 ^ 59
def prefixEnd_3606515 : Nat := 4983230072969 + 3 ^ 40 * 3606515 * 2
def baseEnd_3606515 : Nat := 68587988246298601006535

theorem tailTrace_3606515 : CollatzResearch.WordTrace tailWord_3606515 prefixEnd_3606515 68587988246298601006535 := by
  unfold tailWord_3606515
  simp only [CollatzResearch.WordTrace]
  refine ⟨131540408529219573569324999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87693605686146382379549999 131540408529219573569324999)
  ·
    refine ⟨197310612793829360353987499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131540408529219573569324999 197310612793829360353987499)
    ·
      refine ⟨295965919190744040530981249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197310612793829360353987499 295965919190744040530981249)
      ·
        refine ⟨221974439393058030398235937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 295965919190744040530981249 221974439393058030398235937)
        ·
          refine ⟨166480829544793522798676953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 221974439393058030398235937 166480829544793522798676953)
          ·
            refine ⟨124860622158595142099007715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166480829544793522798676953 124860622158595142099007715)
            ·
              refine ⟨187290933237892713148511573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124860622158595142099007715 187290933237892713148511573)
              ·
                refine ⟨68587988246298601006535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 187290933237892713148511573 68587988246298601006535)
                ·
                  rfl

theorem cell23_3606515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 13].length) (baseStart_3606515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3606515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3606515 prefixEnd_3606515 := by exact prefixLift 3606515
  have htrace : WordTrace (prefixWord ++ tailWord_3606515) baseStart_3606515 baseEnd_3606515 := by
    simpa [prefixWord, tailWord_3606515, baseEnd_3606515] using wordTrace_append hprefix tailTrace_3606515
  have hstable : (prefixWord ++ tailWord_3606515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3606515).length < 2 ^ (prefixWord ++ tailWord_3606515).sum := by decide
  have hdescent : baseEnd_3606515 < baseStart_3606515 := by decide
  rcases family_descends (prefixWord ++ tailWord_3606515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3606556 : List Nat := [2, 2, 3, 1, 3, 3, 1, 1, 1, 2, 4]
def baseStart_3606556 : Nat := 118140960795 + 3606556 * 2 ^ 59
def prefixEnd_3606556 : Nat := 4983230072969 + 3 ^ 40 * 3606556 * 2
def baseEnd_3606556 : Nat := 1851896735356896566763757

theorem tailTrace_3606556 : CollatzResearch.WordTrace tailWord_3606556 prefixEnd_3606556 1851896735356896566763757 := by
  unfold tailWord_3606556
  simp only [CollatzResearch.WordTrace]
  refine ⟨65770951961035518785783761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87694602614714025047711681 65770951961035518785783761)
  ·
    refine ⟨49328213970776639089337821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65770951961035518785783761 49328213970776639089337821)
    ·
      refine ⟨18498080239041239658501683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49328213970776639089337821 18498080239041239658501683)
      ·
        refine ⟨27747120358561859487752525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18498080239041239658501683 27747120358561859487752525)
        ·
          refine ⟨10405170134460697307907197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27747120358561859487752525 10405170134460697307907197)
          ·
            refine ⟨3901938800422761490465199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10405170134460697307907197 3901938800422761490465199)
            ·
              refine ⟨5852908200634142235697799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3901938800422761490465199 5852908200634142235697799)
              ·
                refine ⟨8779362300951213353546699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5852908200634142235697799 8779362300951213353546699)
                ·
                  refine ⟨13169043451426820030320049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8779362300951213353546699 13169043451426820030320049)
                  ·
                    refine ⟨9876782588570115022740037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13169043451426820030320049 9876782588570115022740037)
                    ·
                      refine ⟨1851896735356896566763757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9876782588570115022740037 1851896735356896566763757)
                      ·
                        rfl

theorem cell23_3606556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 1, 1, 1, 2, 4].length) (baseStart_3606556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3606556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3606556 prefixEnd_3606556 := by exact prefixLift 3606556
  have htrace : WordTrace (prefixWord ++ tailWord_3606556) baseStart_3606556 baseEnd_3606556 := by
    simpa [prefixWord, tailWord_3606556, baseEnd_3606556] using wordTrace_append hprefix tailTrace_3606556
  have hstable : (prefixWord ++ tailWord_3606556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3606556).length < 2 ^ (prefixWord ++ tailWord_3606556).sum := by decide
  have hdescent : baseEnd_3606556 < baseStart_3606556 := by decide
  rcases family_descends (prefixWord ++ tailWord_3606556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3606569 : List Nat := [1, 2, 1, 1, 1, 1, 1, 1, 9, 3, 2]
def baseStart_3606569 : Nat := 118140960795 + 3606569 * 2 ^ 59
def prefixEnd_3606569 : Nat := 4983230072969 + 3 ^ 40 * 3606569 * 2
def baseEnd_3606569 : Nat := 1851903410605405015901197

theorem tailTrace_3606569 : CollatzResearch.WordTrace tailWord_3606569 prefixEnd_3606569 1851903410605405015901197 := by
  unfold tailWord_3606569
  simp only [CollatzResearch.WordTrace]
  refine ⟨131542378071023940791790761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87694918714015960527860507 131542378071023940791790761)
  ·
    refine ⟨98656783553267955593843071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131542378071023940791790761 98656783553267955593843071)
    ·
      refine ⟨147985175329901933390764607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98656783553267955593843071 147985175329901933390764607)
      ·
        refine ⟨221977762994852900086146911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147985175329901933390764607 221977762994852900086146911)
        ·
          refine ⟨332966644492279350129220367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221977762994852900086146911 332966644492279350129220367)
          ·
            refine ⟨499449966738419025193830551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 332966644492279350129220367 499449966738419025193830551)
            ·
              refine ⟨749174950107628537790745827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 499449966738419025193830551 749174950107628537790745827)
              ·
                refine ⟨1123762425161442806686118741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 749174950107628537790745827 1123762425161442806686118741)
                ·
                  refine ⟨6584545459930328945426477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 1123762425161442806686118741 6584545459930328945426477)
                  ·
                    refine ⟨2469204547473873354534929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6584545459930328945426477 2469204547473873354534929)
                    ·
                      refine ⟨1851903410605405015901197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2469204547473873354534929 1851903410605405015901197)
                      ·
                        rfl

theorem cell23_3606569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 9, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 9, 3, 2].length) (baseStart_3606569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3606569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3606569 prefixEnd_3606569 := by exact prefixLift 3606569
  have htrace : WordTrace (prefixWord ++ tailWord_3606569) baseStart_3606569 baseEnd_3606569 := by
    simpa [prefixWord, tailWord_3606569, baseEnd_3606569] using wordTrace_append hprefix tailTrace_3606569
  have hstable : (prefixWord ++ tailWord_3606569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3606569).length < 2 ^ (prefixWord ++ tailWord_3606569).sum := by decide
  have hdescent : baseEnd_3606569 < baseStart_3606569 := by decide
  rcases family_descends (prefixWord ++ tailWord_3606569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3606602 : List Nat := [3, 1, 2, 1, 1, 2, 1, 1, 3, 3, 5]
def baseStart_3606602 : Nat := 118140960795 + 3606602 * 2 ^ 59
def prefixEnd_3606602 : Nat := 4983230072969 + 3 ^ 40 * 3606602 * 2
def baseEnd_3606602 : Nat := 1851920355467003386788545

theorem tailTrace_3606602 : CollatzResearch.WordTrace tailWord_3606602 prefixEnd_3606602 1851920355467003386788545 := by
  unfold tailWord_3606602
  simp only [CollatzResearch.WordTrace]
  refine ⟨32885895419976096856935515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87695721119936258285161373 32885895419976096856935515)
  ·
    refine ⟨49328843129964145285403273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32885895419976096856935515 49328843129964145285403273)
    ·
      refine ⟨36996632347473108964052455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49328843129964145285403273 36996632347473108964052455)
      ·
        refine ⟨55494948521209663446078683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36996632347473108964052455 55494948521209663446078683)
        ·
          refine ⟨83242422781814495169118025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55494948521209663446078683 83242422781814495169118025)
          ·
            refine ⟨62431817086360871376838519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83242422781814495169118025 62431817086360871376838519)
            ·
              refine ⟨93647725629541307065257779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62431817086360871376838519 93647725629541307065257779)
              ·
                refine ⟨140471588444311960597886669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93647725629541307065257779 140471588444311960597886669)
                ·
                  refine ⟨52676845666616985224207501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 140471588444311960597886669 52676845666616985224207501)
                  ·
                    refine ⟨19753817124981369459077813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52676845666616985224207501 19753817124981369459077813)
                    ·
                      refine ⟨1851920355467003386788545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19753817124981369459077813 1851920355467003386788545)
                      ·
                        rfl

theorem cell23_3606602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 3, 3, 5].length) (baseStart_3606602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3606602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3606602 prefixEnd_3606602 := by exact prefixLift 3606602
  have htrace : WordTrace (prefixWord ++ tailWord_3606602) baseStart_3606602 baseEnd_3606602 := by
    simpa [prefixWord, tailWord_3606602, baseEnd_3606602] using wordTrace_append hprefix tailTrace_3606602
  have hstable : (prefixWord ++ tailWord_3606602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3606602).length < 2 ^ (prefixWord ++ tailWord_3606602).sum := by decide
  have hdescent : baseEnd_3606602 < baseStart_3606602 := by decide
  rcases family_descends (prefixWord ++ tailWord_3606602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3606620 : List Nat := [2, 2, 4, 1, 1, 4, 1, 2, 1, 3, 2]
def baseStart_3606620 : Nat := 118140960795 + 3606620 * 2 ^ 59
def prefixEnd_3606620 : Nat := 4983230072969 + 3 ^ 40 * 3606620 * 2
def baseEnd_3606620 : Nat := 1851929598118784316363463

theorem tailTrace_3606620 : CollatzResearch.WordTrace tailWord_3606620 prefixEnd_3606620 1851929598118784316363463 := by
  unfold tailWord_3606620
  simp only [CollatzResearch.WordTrace]
  refine ⟨65772119096919588250948657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87696158795892784334598209 65772119096919588250948657)
  ·
    refine ⟨49329089322689691188211493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65772119096919588250948657 49329089322689691188211493)
    ·
      refine ⟨9249204248004317097789655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49329089322689691188211493 9249204248004317097789655)
      ·
        refine ⟨13873806372006475646684483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9249204248004317097789655 13873806372006475646684483)
        ·
          refine ⟨20810709558009713470026725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13873806372006475646684483 20810709558009713470026725)
          ·
            refine ⟨3902008042126821275630011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20810709558009713470026725 3902008042126821275630011)
            ·
              refine ⟨5853012063190231913445017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3902008042126821275630011 5853012063190231913445017)
              ·
                refine ⟨4389759047392673935083763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5853012063190231913445017 4389759047392673935083763)
                ·
                  refine ⟨6584638571089010902625645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4389759047392673935083763 6584638571089010902625645)
                  ·
                    refine ⟨2469239464158379088484617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6584638571089010902625645 2469239464158379088484617)
                    ·
                      refine ⟨1851929598118784316363463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2469239464158379088484617 1851929598118784316363463)
                      ·
                        rfl

theorem cell23_3606620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 1, 2, 1, 3, 2].length) (baseStart_3606620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3606620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3606620 prefixEnd_3606620 := by exact prefixLift 3606620
  have htrace : WordTrace (prefixWord ++ tailWord_3606620) baseStart_3606620 baseEnd_3606620 := by
    simpa [prefixWord, tailWord_3606620, baseEnd_3606620] using wordTrace_append hprefix tailTrace_3606620
  have hstable : (prefixWord ++ tailWord_3606620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3606620).length < 2 ^ (prefixWord ++ tailWord_3606620).sum := by decide
  have hdescent : baseEnd_3606620 < baseStart_3606620 := by decide
  rcases family_descends (prefixWord ++ tailWord_3606620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3606666 : List Nat := [3, 1, 2, 3, 1, 3, 1, 1, 2, 3, 3]
def baseStart_3606666 : Nat := 118140960795 + 3606666 * 2 ^ 59
def prefixEnd_3606666 : Nat := 4983230072969 + 3 ^ 40 * 3606666 * 2
def baseEnd_3606666 : Nat := 1851953218228891136388251

theorem tailTrace_3606666 : CollatzResearch.WordTrace tailWord_3606666 prefixEnd_3606666 1851953218228891136388251 := by
  unfold tailWord_3606666
  simp only [CollatzResearch.WordTrace]
  refine ⟨32886478987918131589517963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87697277301115017572047901 32886478987918131589517963)
  ·
    refine ⟨49329718481877197384276945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32886478987918131589517963 49329718481877197384276945)
    ·
      refine ⟨36997288861407898038207709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49329718481877197384276945 36997288861407898038207709)
      ·
        refine ⟨13873983323027961764327891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36997288861407898038207709 13873983323027961764327891)
        ·
          refine ⟨20810974984541942646491837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13873983323027961764327891 20810974984541942646491837)
          ·
            refine ⟨7804115619203228492434439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20810974984541942646491837 7804115619203228492434439)
            ·
              refine ⟨11706173428804842738651659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7804115619203228492434439 11706173428804842738651659)
              ·
                refine ⟨17559260143207264107977489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11706173428804842738651659 17559260143207264107977489)
                ·
                  refine ⟨13169445107405448080983117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17559260143207264107977489 13169445107405448080983117)
                  ·
                    refine ⟨4938541915277043030368669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13169445107405448080983117 4938541915277043030368669)
                    ·
                      refine ⟨1851953218228891136388251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4938541915277043030368669 1851953218228891136388251)
                      ·
                        rfl

theorem cell23_3606666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 1, 2, 3, 3].length) (baseStart_3606666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3606666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3606666 prefixEnd_3606666 := by exact prefixLift 3606666
  have htrace : WordTrace (prefixWord ++ tailWord_3606666) baseStart_3606666 baseEnd_3606666 := by
    simpa [prefixWord, tailWord_3606666, baseEnd_3606666] using wordTrace_append hprefix tailTrace_3606666
  have hstable : (prefixWord ++ tailWord_3606666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3606666).length < 2 ^ (prefixWord ++ tailWord_3606666).sum := by decide
  have hdescent : baseEnd_3606666 < baseStart_3606666 := by decide
  rcases family_descends (prefixWord ++ tailWord_3606666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3606706 : List Nat := [3, 2, 1, 1, 1, 3, 1, 1, 4, 4, 2]
def baseStart_3606706 : Nat := 118140960795 + 3606706 * 2 ^ 59
def prefixEnd_3606706 : Nat := 4983230072969 + 3 ^ 40 * 3606706 * 2
def baseEnd_3606706 : Nat := 1851973757455070979888067

theorem tailTrace_3606706 : CollatzResearch.WordTrace tailWord_3606706 prefixEnd_3606706 1851973757455070979888067 := by
  unfold tailWord_3606706
  simp only [CollatzResearch.WordTrace]
  refine ⟨32886843717881903297381993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87698249914351742126351981 32886843717881903297381993)
  ·
    refine ⟨24665132788411427473036495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32886843717881903297381993 24665132788411427473036495)
    ·
      refine ⟨36997699182617141209554743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24665132788411427473036495 36997699182617141209554743)
      ·
        refine ⟨55496548773925711814332115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36997699182617141209554743 55496548773925711814332115)
        ·
          refine ⟨83244823160888567721498173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55496548773925711814332115 83244823160888567721498173)
          ·
            refine ⟨31216808685333212895561815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83244823160888567721498173 31216808685333212895561815)
            ·
              refine ⟨46825213027999819343342723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31216808685333212895561815 46825213027999819343342723)
              ·
                refine ⟨70237819541999729015014085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46825213027999819343342723 70237819541999729015014085)
                ·
                  refine ⟨13169591164124949190315141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70237819541999729015014085 13169591164124949190315141)
                  ·
                    refine ⟨2469298343273427973184089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13169591164124949190315141 2469298343273427973184089)
                    ·
                      refine ⟨1851973757455070979888067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2469298343273427973184089 1851973757455070979888067)
                      ·
                        rfl

theorem cell23_3606706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 4, 4, 2].length) (baseStart_3606706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3606706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3606706 prefixEnd_3606706 := by exact prefixLift 3606706
  have htrace : WordTrace (prefixWord ++ tailWord_3606706) baseStart_3606706 baseEnd_3606706 := by
    simpa [prefixWord, tailWord_3606706, baseEnd_3606706] using wordTrace_append hprefix tailTrace_3606706
  have hstable : (prefixWord ++ tailWord_3606706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3606706).length < 2 ^ (prefixWord ++ tailWord_3606706).sum := by decide
  have hdescent : baseEnd_3606706 < baseStart_3606706 := by decide
  rcases family_descends (prefixWord ++ tailWord_3606706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3606793 : List Nat := [1, 2, 1, 1, 3, 6, 1, 2, 1, 5]
def baseStart_3606793 : Nat := 118140960795 + 3606793 * 2 ^ 59
def prefixEnd_3606793 : Nat := 4983230072969 + 3 ^ 40 * 3606793 * 2
def baseEnd_3606793 : Nat := 617339476757337379833389

theorem tailTrace_3606793 : CollatzResearch.WordTrace tailWord_3606793 prefixEnd_3606793 617339476757337379833389 := by
  unfold tailWord_3606793
  simp only [CollatzResearch.WordTrace]
  refine ⟨131550548022212427047945033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87700365348141618031963355 131550548022212427047945033)
  ·
    refine ⟨98662911016659320285958775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131550548022212427047945033 98662911016659320285958775)
    ·
      refine ⟨147994366524988980428938163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98662911016659320285958775 147994366524988980428938163)
      ·
        refine ⟨221991549787483470643407245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147994366524988980428938163 221991549787483470643407245)
        ·
          refine ⟨83246831170306301491277717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 221991549787483470643407245 83246831170306301491277717)
          ·
            refine ⟨3902195211108107882403643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 83246831170306301491277717 3902195211108107882403643)
            ·
              refine ⟨5853292816662161823605465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3902195211108107882403643 5853292816662161823605465)
              ·
                refine ⟨4389969612496621367704099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5853292816662161823605465 4389969612496621367704099)
                ·
                  refine ⟨6584954418744932051556149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4389969612496621367704099 6584954418744932051556149)
                  ·
                    refine ⟨617339476757337379833389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6584954418744932051556149 617339476757337379833389)
                    ·
                      rfl

theorem cell23_3606793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 1, 2, 1, 5].length) (baseStart_3606793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3606793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3606793 prefixEnd_3606793 := by exact prefixLift 3606793
  have htrace : WordTrace (prefixWord ++ tailWord_3606793) baseStart_3606793 baseEnd_3606793 := by
    simpa [prefixWord, tailWord_3606793, baseEnd_3606793] using wordTrace_append hprefix tailTrace_3606793
  have hstable : (prefixWord ++ tailWord_3606793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3606793).length < 2 ^ (prefixWord ++ tailWord_3606793).sum := by decide
  have hdescent : baseEnd_3606793 < baseStart_3606793 := by decide
  rcases family_descends (prefixWord ++ tailWord_3606793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
