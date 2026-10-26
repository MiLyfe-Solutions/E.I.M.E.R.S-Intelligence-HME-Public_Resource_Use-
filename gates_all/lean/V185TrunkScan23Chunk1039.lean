import V185TrunkScan23Chunk1038

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6151489 : List Nat := [1, 2, 5, 2, 1, 2, 1, 1, 1, 7]
def baseStart_6151489 : Nat := 118140960795 + 6151489 * 2 ^ 59
def prefixEnd_6151489 : Nat := 4983230072969 + 3 ^ 40 * 6151489 * 2
def baseEnd_6151489 : Nat := 1052890199281862668232441

theorem tailTrace_6151489 : CollatzResearch.WordTrace tailWord_6151489 prefixEnd_6151489 1052890199281862668232441 := by
  unfold tailWord_6151489
  simp only [CollatzResearch.WordTrace]
  refine ⟨224363236011213418524513521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149575490674142279016342347 224363236011213418524513521)
  ·
    refine ⟨168272427008410063893385141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224363236011213418524513521 168272427008410063893385141)
    ·
      refine ⟨15775540032038443490004857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 168272427008410063893385141 15775540032038443490004857)
      ·
        refine ⟨11831655024028832617503643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15775540032038443490004857 11831655024028832617503643)
        ·
          refine ⟨17747482536043248926255465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11831655024028832617503643 17747482536043248926255465)
          ·
            refine ⟨13310611902032436694691599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17747482536043248926255465 13310611902032436694691599)
            ·
              refine ⟨19965917853048655042037399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13310611902032436694691599 19965917853048655042037399)
              ·
                refine ⟨29948876779572982563056099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19965917853048655042037399 29948876779572982563056099)
                ·
                  refine ⟨44923315169359473844584149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29948876779572982563056099 44923315169359473844584149)
                  ·
                    refine ⟨1052890199281862668232441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44923315169359473844584149 1052890199281862668232441)
                    ·
                      rfl

theorem cell23_6151489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_6151489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6151489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6151489 prefixEnd_6151489 := by exact prefixLift 6151489
  have htrace : WordTrace (prefixWord ++ tailWord_6151489) baseStart_6151489 baseEnd_6151489 := by
    simpa [prefixWord, tailWord_6151489, baseEnd_6151489] using wordTrace_append hprefix tailTrace_6151489
  have hstable : (prefixWord ++ tailWord_6151489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6151489).length < 2 ^ (prefixWord ++ tailWord_6151489).sum := by decide
  have hdescent : baseEnd_6151489 < baseStart_6151489 := by decide
  rcases family_descends (prefixWord ++ tailWord_6151489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6151510 : List Nat := [5, 2, 3, 1, 1, 1, 2, 1, 7]
def baseStart_6151510 : Nat := 118140960795 + 6151510 * 2 ^ 59
def prefixEnd_6151510 : Nat := 4983230072969 + 3 ^ 40 * 6151510 * 2
def baseEnd_6151510 : Nat := 350964597882148046948303

theorem tailTrace_6151510 : CollatzResearch.WordTrace tailWord_6151510 prefixEnd_6151510 350964597882148046948303 := by
  unfold tailWord_6151510
  simp only [CollatzResearch.WordTrace]
  refine ⟨14022750121508583694439249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 149576001296091559407351989 14022750121508583694439249)
  ·
    refine ⟨10517062591131437770829437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14022750121508583694439249 10517062591131437770829437)
    ·
      refine ⟨3943898471674289164061039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10517062591131437770829437 3943898471674289164061039)
      ·
        refine ⟨5915847707511433746091559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3943898471674289164061039 5915847707511433746091559)
        ·
          refine ⟨8873771561267150619137339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5915847707511433746091559 8873771561267150619137339)
          ·
            refine ⟨13310657341900725928706009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8873771561267150619137339 13310657341900725928706009)
            ·
              refine ⟨9982993006425544446529507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13310657341900725928706009 9982993006425544446529507)
              ·
                refine ⟨14974489509638316669794261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9982993006425544446529507 14974489509638316669794261)
                ·
                  refine ⟨350964597882148046948303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14974489509638316669794261 350964597882148046948303)
                  ·
                    rfl

theorem cell23_6151510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 2, 1, 7].length) (baseStart_6151510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6151510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6151510 prefixEnd_6151510 := by exact prefixLift 6151510
  have htrace : WordTrace (prefixWord ++ tailWord_6151510) baseStart_6151510 baseEnd_6151510 := by
    simpa [prefixWord, tailWord_6151510, baseEnd_6151510] using wordTrace_append hprefix tailTrace_6151510
  have hstable : (prefixWord ++ tailWord_6151510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6151510).length < 2 ^ (prefixWord ++ tailWord_6151510).sum := by decide
  have hdescent : baseEnd_6151510 < baseStart_6151510 := by decide
  rcases family_descends (prefixWord ++ tailWord_6151510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6151570 : List Nat := [3, 2, 3, 3, 1, 2, 1, 1, 3, 4]
def baseStart_6151570 : Nat := 118140960795 + 6151570 * 2 ^ 59
def prefixEnd_6151570 : Nat := 4983230072969 + 3 ^ 40 * 6151570 * 2
def baseEnd_6151570 : Nat := 1052904063259534062594817

theorem tailTrace_6151570 : CollatzResearch.WordTrace tailWord_6151570 prefixEnd_6151570 1052904063259534062594817 := by
  unfold tailWord_6151570
  simp only [CollatzResearch.WordTrace]
  refine ⟨56091547580979992339553041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149577460215946646238808109 56091547580979992339553041)
  ·
    refine ⟨42068660685734994254664781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56091547580979992339553041 42068660685734994254664781)
    ·
      refine ⟨15775747757150622845499293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42068660685734994254664781 15775747757150622845499293)
      ·
        refine ⟨5915905408931483567062235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15775747757150622845499293 5915905408931483567062235)
        ·
          refine ⟨8873858113397225350593353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5915905408931483567062235 8873858113397225350593353)
          ·
            refine ⟨6655393585047919012945015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8873858113397225350593353 6655393585047919012945015)
            ·
              refine ⟨9983090377571878519417523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6655393585047919012945015 9983090377571878519417523)
              ·
                refine ⟨14974635566357817779126285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9983090377571878519417523 14974635566357817779126285)
                ·
                  refine ⟨5615488337384181667172357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14974635566357817779126285 5615488337384181667172357)
                  ·
                    refine ⟨1052904063259534062594817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5615488337384181667172357 1052904063259534062594817)
                    ·
                      rfl

theorem cell23_6151570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 1, 1, 3, 4].length) (baseStart_6151570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6151570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6151570 prefixEnd_6151570 := by exact prefixLift 6151570
  have htrace : WordTrace (prefixWord ++ tailWord_6151570) baseStart_6151570 baseEnd_6151570 := by
    simpa [prefixWord, tailWord_6151570, baseEnd_6151570] using wordTrace_append hprefix tailTrace_6151570
  have hstable : (prefixWord ++ tailWord_6151570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6151570).length < 2 ^ (prefixWord ++ tailWord_6151570).sum := by decide
  have hdescent : baseEnd_6151570 < baseStart_6151570 := by decide
  rcases family_descends (prefixWord ++ tailWord_6151570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6151599 : List Nat := [1, 1, 2, 1, 2, 2, 1, 3, 2, 6, 2]
def baseStart_6151599 : Nat := 118140960795 + 6151599 * 2 ^ 59
def prefixEnd_6151599 : Nat := 4983230072969 + 3 ^ 40 * 6151599 * 2
def baseEnd_6151599 : Nat := 3158727080717582574321817

theorem tailTrace_6151599 : CollatzResearch.WordTrace tailWord_6151599 prefixEnd_6151599 3158727080717582574321817 := by
  unfold tailWord_6151599
  simp only [CollatzResearch.WordTrace]
  refine ⟨224367248040814907311017851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149578165360543271540678567 224367248040814907311017851)
  ·
    refine ⟨336550872061222360966526777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224367248040814907311017851 336550872061222360966526777)
    ·
      refine ⟨252413154045916770724895083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 336550872061222360966526777 252413154045916770724895083)
      ·
        refine ⟨378619731068875156087342625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252413154045916770724895083 378619731068875156087342625)
        ·
          refine ⟨283964798301656367065506969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 378619731068875156087342625 283964798301656367065506969)
          ·
            refine ⟨212973598726242275299130227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 283964798301656367065506969 212973598726242275299130227)
            ·
              refine ⟨319460398089363412948695341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 212973598726242275299130227 319460398089363412948695341)
              ·
                refine ⟨119797649283511279855760753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 319460398089363412948695341 119797649283511279855760753)
                ·
                  refine ⟨89848236962633459891820565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 119797649283511279855760753 89848236962633459891820565)
                  ·
                    refine ⟨4211636107623443432429089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 89848236962633459891820565 4211636107623443432429089)
                    ·
                      refine ⟨3158727080717582574321817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4211636107623443432429089 3158727080717582574321817)
                      ·
                        rfl

theorem cell23_6151599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 2, 6, 2].length) (baseStart_6151599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6151599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6151599 prefixEnd_6151599 := by exact prefixLift 6151599
  have htrace : WordTrace (prefixWord ++ tailWord_6151599) baseStart_6151599 baseEnd_6151599 := by
    simpa [prefixWord, tailWord_6151599, baseEnd_6151599] using wordTrace_append hprefix tailTrace_6151599
  have hstable : (prefixWord ++ tailWord_6151599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6151599).length < 2 ^ (prefixWord ++ tailWord_6151599).sum := by decide
  have hdescent : baseEnd_6151599 < baseStart_6151599 := by decide
  rcases family_descends (prefixWord ++ tailWord_6151599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6151619 : List Nat := [1, 1, 1, 3, 1, 1, 7, 1, 1, 1, 5]
def baseStart_6151619 : Nat := 118140960795 + 6151619 * 2 ^ 59
def prefixEnd_6151619 : Nat := 4983230072969 + 3 ^ 40 * 6151619 * 2
def baseEnd_6151619 : Nat := 3158737350330672496071725

theorem tailTrace_6151619 : CollatzResearch.WordTrace tailWord_6151619 prefixEnd_6151619 3158737350330672496071725 := by
  unfold tailWord_6151619
  simp only [CollatzResearch.WordTrace]
  refine ⟨224367977500742450726745911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149578651667161633817830607 224367977500742450726745911)
  ·
    refine ⟨336551966251113676090118867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224367977500742450726745911 336551966251113676090118867)
    ·
      refine ⟨504827949376670514135178301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 336551966251113676090118867 504827949376670514135178301)
      ·
        refine ⟨189310481016251442800691863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 504827949376670514135178301 189310481016251442800691863)
        ·
          refine ⟨283965721524377164201037795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189310481016251442800691863 283965721524377164201037795)
          ·
            refine ⟨425948582286565746301556693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 283965721524377164201037795 425948582286565746301556693)
            ·
              refine ⟨9983169897341384678942735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 425948582286565746301556693 9983169897341384678942735)
              ·
                refine ⟨14974754846012077018414103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9983169897341384678942735 14974754846012077018414103)
                ·
                  refine ⟨22462132269018115527621155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14974754846012077018414103 22462132269018115527621155)
                  ·
                    refine ⟨33693198403527173291431733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22462132269018115527621155 33693198403527173291431733)
                    ·
                      refine ⟨3158737350330672496071725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33693198403527173291431733 3158737350330672496071725)
                      ·
                        rfl

theorem cell23_6151619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7, 1, 1, 1, 5].length) (baseStart_6151619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6151619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6151619 prefixEnd_6151619 := by exact prefixLift 6151619
  have htrace : WordTrace (prefixWord ++ tailWord_6151619) baseStart_6151619 baseEnd_6151619 := by
    simpa [prefixWord, tailWord_6151619, baseEnd_6151619] using wordTrace_append hprefix tailTrace_6151619
  have hstable : (prefixWord ++ tailWord_6151619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6151619).length < 2 ^ (prefixWord ++ tailWord_6151619).sum := by decide
  have hdescent : baseEnd_6151619 < baseStart_6151619 := by decide
  rcases family_descends (prefixWord ++ tailWord_6151619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6151626 : List Nat := [3, 1, 2, 1, 2, 3, 1, 4, 2, 4]
def baseStart_6151626 : Nat := 118140960795 + 6151626 * 2 ^ 59
def prefixEnd_6151626 : Nat := 4983230072969 + 3 ^ 40 * 6151626 * 2
def baseEnd_6151626 : Nat := 1052913648231751322894731

theorem tailTrace_6151626 : CollatzResearch.WordTrace tailWord_6151626 prefixEnd_6151626 1052913648231751322894731 := by
  unfold tailWord_6151626
  simp only [CollatzResearch.WordTrace]
  refine ⟨56092058202929272730562683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149578821874478060614833821 56092058202929272730562683)
  ·
    refine ⟨84138087304393909095844025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56092058202929272730562683 84138087304393909095844025)
    ·
      refine ⟨63103565478295431821883019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84138087304393909095844025 63103565478295431821883019)
      ·
        refine ⟨94655348217443147732824529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63103565478295431821883019 94655348217443147732824529)
        ·
          refine ⟨70991511163082360799618397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94655348217443147732824529 70991511163082360799618397)
          ·
            refine ⟨26621816686155885299856899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70991511163082360799618397 26621816686155885299856899)
            ·
              refine ⟨39932725029233827949785349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26621816686155885299856899 39932725029233827949785349)
              ·
                refine ⟨7487385942981342740584753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39932725029233827949785349 7487385942981342740584753)
                ·
                  refine ⟨5615539457236007055438565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7487385942981342740584753 5615539457236007055438565)
                  ·
                    refine ⟨1052913648231751322894731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5615539457236007055438565 1052913648231751322894731)
                    ·
                      rfl

theorem cell23_6151626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 4, 2, 4].length) (baseStart_6151626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6151626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6151626 prefixEnd_6151626 := by exact prefixLift 6151626
  have htrace : WordTrace (prefixWord ++ tailWord_6151626) baseStart_6151626 baseEnd_6151626 := by
    simpa [prefixWord, tailWord_6151626, baseEnd_6151626] using wordTrace_append hprefix tailTrace_6151626
  have hstable : (prefixWord ++ tailWord_6151626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6151626).length < 2 ^ (prefixWord ++ tailWord_6151626).sum := by decide
  have hdescent : baseEnd_6151626 < baseStart_6151626 := by decide
  rcases family_descends (prefixWord ++ tailWord_6151626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6151670 : List Nat := [5, 1, 1, 1, 2, 2, 4, 1, 1, 2, 3]
def baseStart_6151670 : Nat := 118140960795 + 6151670 * 2 ^ 59
def prefixEnd_6151670 : Nat := 4983230072969 + 3 ^ 40 * 6151670 * 2
def baseEnd_6151670 : Nat := 3158763537844051796533991

theorem tailTrace_6151670 : CollatzResearch.WordTrace tailWord_6151670 prefixEnd_6151670 3158763537844051796533991 := by
  unfold tailWord_6151670
  simp only [CollatzResearch.WordTrace]
  refine ⟨14023114851472355402303279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 149579891749038457624568309 14023114851472355402303279)
  ·
    refine ⟨21034672277208533103454919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14023114851472355402303279 21034672277208533103454919)
    ·
      refine ⟨31552008415812799655182379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21034672277208533103454919 31552008415812799655182379)
      ·
        refine ⟨47328012623719199482773569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31552008415812799655182379 47328012623719199482773569)
        ·
          refine ⟨35496009467789399612080177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47328012623719199482773569 35496009467789399612080177)
          ·
            refine ⟨26622007100842049709060133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35496009467789399612080177 26622007100842049709060133)
            ·
              refine ⟨4991626331407884320448775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26622007100842049709060133 4991626331407884320448775)
              ·
                refine ⟨7487439497111826480673163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4991626331407884320448775 7487439497111826480673163)
                ·
                  refine ⟨11231159245667739721009745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7487439497111826480673163 11231159245667739721009745)
                  ·
                    refine ⟨8423369434250804790757309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11231159245667739721009745 8423369434250804790757309)
                    ·
                      refine ⟨3158763537844051796533991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8423369434250804790757309 3158763537844051796533991)
                      ·
                        rfl

theorem cell23_6151670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 4, 1, 1, 2, 3].length) (baseStart_6151670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6151670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6151670 prefixEnd_6151670 := by exact prefixLift 6151670
  have htrace : WordTrace (prefixWord ++ tailWord_6151670) baseStart_6151670 baseEnd_6151670 := by
    simpa [prefixWord, tailWord_6151670, baseEnd_6151670] using wordTrace_append hprefix tailTrace_6151670
  have hstable : (prefixWord ++ tailWord_6151670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6151670).length < 2 ^ (prefixWord ++ tailWord_6151670).sum := by decide
  have hdescent : baseEnd_6151670 < baseStart_6151670 := by decide
  rcases family_descends (prefixWord ++ tailWord_6151670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6151699 : List Nat := [1, 1, 1, 2, 1, 6, 2, 1, 2, 6]
def baseStart_6151699 : Nat := 118140960795 + 6151699 * 2 ^ 59
def prefixEnd_6151699 : Nat := 4983230072969 + 3 ^ 40 * 6151699 * 2
def baseEnd_6151699 : Nat := 1052926142927677394357119

theorem tailTrace_6151699 : CollatzResearch.WordTrace tailWord_6151699 prefixEnd_6151699 1052926142927677394357119 := by
  unfold tailWord_6151699
  simp only [CollatzResearch.WordTrace]
  refine ⟨224370895340452624389658151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149580596893635082926438767 224370895340452624389658151)
  ·
    refine ⟨336556343010678936584487227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224370895340452624389658151 336556343010678936584487227)
    ·
      refine ⟨504834514516018404876730841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 336556343010678936584487227 504834514516018404876730841)
      ·
        refine ⟨378625885887013803657548131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 504834514516018404876730841 378625885887013803657548131)
        ·
          refine ⟨567938828830520705486322197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 378625885887013803657548131 567938828830520705486322197)
          ·
            refine ⟨26622132601430658069671353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 567938828830520705486322197 26622132601430658069671353)
            ·
              refine ⟨19966599451072993552253515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26622132601430658069671353 19966599451072993552253515)
              ·
                refine ⟨29949899176609490328380273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19966599451072993552253515 29949899176609490328380273)
                ·
                  refine ⟨22462424382457117746285205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29949899176609490328380273 22462424382457117746285205)
                  ·
                    refine ⟨1052926142927677394357119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22462424382457117746285205 1052926142927677394357119)
                    ·
                      rfl

theorem cell23_6151699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 1, 2, 6].length) (baseStart_6151699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6151699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6151699 prefixEnd_6151699 := by exact prefixLift 6151699
  have htrace : WordTrace (prefixWord ++ tailWord_6151699) baseStart_6151699 baseEnd_6151699 := by
    simpa [prefixWord, tailWord_6151699, baseEnd_6151699] using wordTrace_append hprefix tailTrace_6151699
  have hstable : (prefixWord ++ tailWord_6151699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6151699).length < 2 ^ (prefixWord ++ tailWord_6151699).sum := by decide
  have hdescent : baseEnd_6151699 < baseStart_6151699 := by decide
  rcases family_descends (prefixWord ++ tailWord_6151699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6151726 : List Nat := [4, 1, 3, 1, 2, 1, 1, 1, 1, 3, 5]
def baseStart_6151726 : Nat := 118140960795 + 6151726 * 2 ^ 59
def prefixEnd_6151726 : Nat := 4983230072969 + 3 ^ 40 * 6151726 * 2
def baseEnd_6151726 : Nat := 3158792292760703577433733

theorem tailTrace_6151726 : CollatzResearch.WordTrace tailWord_6151726 prefixEnd_6151726 3158792292760703577433733 := by
  unfold tailWord_6151726
  simp only [CollatzResearch.WordTrace]
  refine ⟨28046485013919351000111379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149581253407569872000594021 28046485013919351000111379)
  ·
    refine ⟨42069727520879026500167069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28046485013919351000111379 42069727520879026500167069)
    ·
      refine ⟨15776147820329634937562651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42069727520879026500167069 15776147820329634937562651)
      ·
        refine ⟨23664221730494452406343977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15776147820329634937562651 23664221730494452406343977)
        ·
          refine ⟨17748166297870839304757983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23664221730494452406343977 17748166297870839304757983)
          ·
            refine ⟨26622249446806258957136975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17748166297870839304757983 26622249446806258957136975)
            ·
              refine ⟨39933374170209388435705463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26622249446806258957136975 39933374170209388435705463)
              ·
                refine ⟨59900061255314082653558195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39933374170209388435705463 59900061255314082653558195)
                ·
                  refine ⟨89850091882971123980337293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59900061255314082653558195 89850091882971123980337293)
                  ·
                    refine ⟨33693784456114171492626485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 89850091882971123980337293 33693784456114171492626485)
                    ·
                      refine ⟨3158792292760703577433733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33693784456114171492626485 3158792292760703577433733)
                      ·
                        rfl

theorem cell23_6151726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_6151726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6151726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6151726 prefixEnd_6151726 := by exact prefixLift 6151726
  have htrace : WordTrace (prefixWord ++ tailWord_6151726) baseStart_6151726 baseEnd_6151726 := by
    simpa [prefixWord, tailWord_6151726, baseEnd_6151726] using wordTrace_append hprefix tailTrace_6151726
  have hstable : (prefixWord ++ tailWord_6151726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6151726).length < 2 ^ (prefixWord ++ tailWord_6151726).sum := by decide
  have hdescent : baseEnd_6151726 < baseStart_6151726 := by decide
  rcases family_descends (prefixWord ++ tailWord_6151726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6151759 : List Nat := [1, 1, 2, 1, 1, 2, 3, 1, 6, 5]
def baseStart_6151759 : Nat := 118140960795 + 6151759 * 2 ^ 59
def prefixEnd_6151759 : Nat := 4983230072969 + 3 ^ 40 * 6151759 * 2
def baseEnd_6151759 : Nat := 1052936412540767316107027

theorem tailTrace_6151759 : CollatzResearch.WordTrace tailWord_6151759 prefixEnd_6151759 1052936412540767316107027 := by
  unfold tailWord_6151759
  simp only [CollatzResearch.WordTrace]
  refine ⟨224373083720235254636842331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149582055813490169757894887 224373083720235254636842331)
  ·
    refine ⟨336559625580352881955263497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224373083720235254636842331 336559625580352881955263497)
    ·
      refine ⟨252419719185264661466447623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 336559625580352881955263497 252419719185264661466447623)
      ·
        refine ⟨378629578777896992199671435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252419719185264661466447623 378629578777896992199671435)
        ·
          refine ⟨567944368166845488299507153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 378629578777896992199671435 567944368166845488299507153)
          ·
            refine ⟨425958276125134116224630365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 567944368166845488299507153 425958276125134116224630365)
            ·
              refine ⟨159734353546925293584236387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 425958276125134116224630365 159734353546925293584236387)
              ·
                refine ⟨239601530320387940376354581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 159734353546925293584236387 239601530320387940376354581)
                ·
                  refine ⟨11231321733768184705141621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 239601530320387940376354581 11231321733768184705141621)
                  ·
                    refine ⟨1052936412540767316107027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11231321733768184705141621 1052936412540767316107027)
                    ·
                      rfl

theorem cell23_6151759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 6, 5].length) (baseStart_6151759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6151759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6151759 prefixEnd_6151759 := by exact prefixLift 6151759
  have htrace : WordTrace (prefixWord ++ tailWord_6151759) baseStart_6151759 baseEnd_6151759 := by
    simpa [prefixWord, tailWord_6151759, baseEnd_6151759] using wordTrace_append hprefix tailTrace_6151759
  have hstable : (prefixWord ++ tailWord_6151759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6151759).length < 2 ^ (prefixWord ++ tailWord_6151759).sum := by decide
  have hdescent : baseEnd_6151759 < baseStart_6151759 := by decide
  rcases family_descends (prefixWord ++ tailWord_6151759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6151786 : List Nat := [3, 1, 3, 2, 1, 2, 1, 2, 1, 2, 5]
def baseStart_6151786 : Nat := 118140960795 + 6151786 * 2 ^ 59
def prefixEnd_6151786 : Nat := 4983230072969 + 3 ^ 40 * 6151786 * 2
def baseEnd_6151786 : Nat := 3158823101599973342683457

theorem tailTrace_6151786 : CollatzResearch.WordTrace tailWord_6151786 prefixEnd_6151786 3158823101599973342683457 := by
  unfold tailWord_6151786
  simp only [CollatzResearch.WordTrace]
  refine ⟨56093517122784359562018803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149582712327424958832050141 56093517122784359562018803)
  ·
    refine ⟨84140275684176539343028205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56093517122784359562018803 84140275684176539343028205)
    ·
      refine ⟨31552603381566202253635577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84140275684176539343028205 31552603381566202253635577)
      ·
        refine ⟨23664452536174651690226683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31552603381566202253635577 23664452536174651690226683)
        ·
          refine ⟨35496678804261977535340025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23664452536174651690226683 35496678804261977535340025)
          ·
            refine ⟨26622509103196483151505019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35496678804261977535340025 26622509103196483151505019)
            ·
              refine ⟨39933763654794724727257529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26622509103196483151505019 39933763654794724727257529)
              ·
                refine ⟨29950322741096043545443147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39933763654794724727257529 29950322741096043545443147)
                ·
                  refine ⟨44925484111644065318164721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29950322741096043545443147 44925484111644065318164721)
                  ·
                    refine ⟨33694113083733048988623541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44925484111644065318164721 33694113083733048988623541)
                    ·
                      refine ⟨3158823101599973342683457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33694113083733048988623541 3158823101599973342683457)
                      ·
                        rfl

theorem cell23_6151786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_6151786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6151786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6151786 prefixEnd_6151786 := by exact prefixLift 6151786
  have htrace : WordTrace (prefixWord ++ tailWord_6151786) baseStart_6151786 baseEnd_6151786 := by
    simpa [prefixWord, tailWord_6151786, baseEnd_6151786] using wordTrace_append hprefix tailTrace_6151786
  have hstable : (prefixWord ++ tailWord_6151786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6151786).length < 2 ^ (prefixWord ++ tailWord_6151786).sum := by decide
  have hdescent : baseEnd_6151786 < baseStart_6151786 := by decide
  rcases family_descends (prefixWord ++ tailWord_6151786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6151797 : List Nat := [1, 3, 4, 2, 1, 3, 2, 2, 5]
def baseStart_6151797 : Nat := 118140960795 + 6151797 * 2 ^ 59
def prefixEnd_6151797 : Nat := 4983230072969 + 3 ^ 40 * 6151797 * 2
def baseEnd_6151797 : Nat := 350980972209685866627323

theorem tailTrace_6151797 : CollatzResearch.WordTrace tailWord_6151797 prefixEnd_6151797 350980972209685866627323 := by
  unfold tailWord_6151797
  simp only [CollatzResearch.WordTrace]
  refine ⟨224374469694097587126725645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149582979796065058084483763 224374469694097587126725645)
  ·
    refine ⟨84140426135286595172522117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 224374469694097587126725645 84140426135286595172522117)
    ·
      refine ⟨15776329900366236594847897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84140426135286595172522117 15776329900366236594847897)
      ·
        refine ⟨11832247425274677446135923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15776329900366236594847897 11832247425274677446135923)
        ·
          refine ⟨17748371137912016169203885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11832247425274677446135923 17748371137912016169203885)
          ·
            refine ⟨6655639176717006063451457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17748371137912016169203885 6655639176717006063451457)
            ·
              refine ⟨4991729382537754547588593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6655639176717006063451457 4991729382537754547588593)
              ·
                refine ⟨3743797036903315910691445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4991729382537754547588593 3743797036903315910691445)
                ·
                  refine ⟨350980972209685866627323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3743797036903315910691445 350980972209685866627323)
                  ·
                    rfl

theorem cell23_6151797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 2, 2, 5].length) (baseStart_6151797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6151797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6151797 prefixEnd_6151797 := by exact prefixLift 6151797
  have htrace : WordTrace (prefixWord ++ tailWord_6151797) baseStart_6151797 baseEnd_6151797 := by
    simpa [prefixWord, tailWord_6151797, baseEnd_6151797] using wordTrace_append hprefix tailTrace_6151797
  have hstable : (prefixWord ++ tailWord_6151797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6151797).length < 2 ^ (prefixWord ++ tailWord_6151797).sum := by decide
  have hdescent : baseEnd_6151797 < baseStart_6151797 := by decide
  rcases family_descends (prefixWord ++ tailWord_6151797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6151799 : List Nat := [1, 1, 3, 1, 1, 3, 1, 1, 1, 5, 5]
def baseStart_6151799 : Nat := 118140960795 + 6151799 * 2 ^ 59
def prefixEnd_6151799 : Nat := 4983230072969 + 3 ^ 40 * 6151799 * 2
def baseEnd_6151799 : Nat := 3158829776848481791820897

theorem tailTrace_6151799 : CollatzResearch.WordTrace tailWord_6151799 prefixEnd_6151799 3158829776848481791820897 := by
  unfold tailWord_6151799
  simp only [CollatzResearch.WordTrace]
  refine ⟨224374542640090341468298451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149583028426726894312198967 224374542640090341468298451)
  ·
    refine ⟨336561813960135512202447677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224374542640090341468298451 336561813960135512202447677)
    ·
      refine ⟨126210680235050817075917879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 336561813960135512202447677 126210680235050817075917879)
      ·
        refine ⟨189316020352576225613876819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126210680235050817075917879 189316020352576225613876819)
        ·
          refine ⟨283974030528864338420815229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189316020352576225613876819 283974030528864338420815229)
          ·
            refine ⟨106490261448324126907805711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 283974030528864338420815229 106490261448324126907805711)
            ·
              refine ⟨159735392172486190361708567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106490261448324126907805711 159735392172486190361708567)
              ·
                refine ⟨239603088258729285542562851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 159735392172486190361708567 239603088258729285542562851)
                ·
                  refine ⟨359404632388093928313844277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 239603088258729285542562851 359404632388093928313844277)
                  ·
                    refine ⟨33694184286383805779422901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 359404632388093928313844277 33694184286383805779422901)
                    ·
                      refine ⟨3158829776848481791820897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33694184286383805779422901 3158829776848481791820897)
                      ·
                        rfl

theorem cell23_6151799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 5, 5].length) (baseStart_6151799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6151799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6151799 prefixEnd_6151799 := by exact prefixLift 6151799
  have htrace : WordTrace (prefixWord ++ tailWord_6151799) baseStart_6151799 baseEnd_6151799 := by
    simpa [prefixWord, tailWord_6151799, baseEnd_6151799] using wordTrace_append hprefix tailTrace_6151799
  have hstable : (prefixWord ++ tailWord_6151799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6151799).length < 2 ^ (prefixWord ++ tailWord_6151799).sum := by decide
  have hdescent : baseEnd_6151799 < baseStart_6151799 := by decide
  rcases family_descends (prefixWord ++ tailWord_6151799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6151813 : List Nat := [1, 3, 1, 1, 4, 1, 3, 1, 2, 4, 2]
def baseStart_6151813 : Nat := 118140960795 + 6151813 * 2 ^ 59
def prefixEnd_6151813 : Nat := 4983230072969 + 3 ^ 40 * 6151813 * 2
def baseEnd_6151813 : Nat := 3158836965577644737045833

theorem tailTrace_6151813 : CollatzResearch.WordTrace tailWord_6151813 prefixEnd_6151813 3158836965577644737045833 := by
  unfold tailWord_6151813
  simp only [CollatzResearch.WordTrace]
  refine ⟨224375053262039621859308093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149583368841359747906205395 224375053262039621859308093)
  ·
    refine ⟨84140644973264858197240535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 224375053262039621859308093 84140644973264858197240535)
    ·
      refine ⟨126210967459897287295860803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84140644973264858197240535 126210967459897287295860803)
      ·
        refine ⟨189316451189845930943791205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126210967459897287295860803 189316451189845930943791205)
        ·
          refine ⟨35496834598096112051960851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 189316451189845930943791205 35496834598096112051960851)
          ·
            refine ⟨53245251897144168077941277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35496834598096112051960851 53245251897144168077941277)
            ·
              refine ⟨19966969461429063029227979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53245251897144168077941277 19966969461429063029227979)
              ·
                refine ⟨29950454192143594543841969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19966969461429063029227979 29950454192143594543841969)
                ·
                  refine ⟨22462840644107695907881477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29950454192143594543841969 22462840644107695907881477)
                  ·
                    refine ⟨4211782620770192982727777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22462840644107695907881477 4211782620770192982727777)
                    ·
                      refine ⟨3158836965577644737045833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4211782620770192982727777 3158836965577644737045833)
                      ·
                        rfl

theorem cell23_6151813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 1, 2, 4, 2].length) (baseStart_6151813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6151813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6151813 prefixEnd_6151813 := by exact prefixLift 6151813
  have htrace : WordTrace (prefixWord ++ tailWord_6151813) baseStart_6151813 baseEnd_6151813 := by
    simpa [prefixWord, tailWord_6151813, baseEnd_6151813] using wordTrace_append hprefix tailTrace_6151813
  have hstable : (prefixWord ++ tailWord_6151813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6151813).length < 2 ^ (prefixWord ++ tailWord_6151813).sum := by decide
  have hdescent : baseEnd_6151813 < baseStart_6151813 := by decide
  rcases family_descends (prefixWord ++ tailWord_6151813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6151840 : List Nat := [2, 1, 1, 4, 3, 1, 1, 5, 1, 4]
def baseStart_6151840 : Nat := 118140960795 + 6151840 * 2 ^ 59
def prefixEnd_6151840 : Nat := 4983230072969 + 3 ^ 40 * 6151840 * 2
def baseEnd_6151840 : Nat := 1052950276518438710469403

theorem tailTrace_6151840 : CollatzResearch.WordTrace tailWord_6151840 prefixEnd_6151840 1052950276518438710469403 := by
  unfold tailWord_6151840
  simp only [CollatzResearch.WordTrace]
  refine ⟨112188019016470902735270487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149584025355294536980360649 112188019016470902735270487)
  ·
    refine ⟨168282028524706354102905731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112188019016470902735270487 168282028524706354102905731)
    ·
      refine ⟨252423042787059531154358597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168282028524706354102905731 252423042787059531154358597)
      ·
        refine ⟨47329320522573662091442237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 252423042787059531154358597 47329320522573662091442237)
        ·
          refine ⟨17748495195965123284290839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47329320522573662091442237 17748495195965123284290839)
          ·
            refine ⟨26622742793947684926436259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17748495195965123284290839 26622742793947684926436259)
            ·
              refine ⟨39934114190921527389654389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26622742793947684926436259 39934114190921527389654389)
              ·
                refine ⟨3743823205398893192780099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39934114190921527389654389 3743823205398893192780099)
                ·
                  refine ⟨5615734808098339789170149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3743823205398893192780099 5615734808098339789170149)
                  ·
                    refine ⟨1052950276518438710469403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5615734808098339789170149 1052950276518438710469403)
                    ·
                      rfl

theorem cell23_6151840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 5, 1, 4].length) (baseStart_6151840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6151840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6151840 prefixEnd_6151840 := by exact prefixLift 6151840
  have htrace : WordTrace (prefixWord ++ tailWord_6151840) baseStart_6151840 baseEnd_6151840 := by
    simpa [prefixWord, tailWord_6151840, baseEnd_6151840] using wordTrace_append hprefix tailTrace_6151840
  have hstable : (prefixWord ++ tailWord_6151840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6151840).length < 2 ^ (prefixWord ++ tailWord_6151840).sum := by decide
  have hdescent : baseEnd_6151840 < baseStart_6151840 := by decide
  rcases family_descends (prefixWord ++ tailWord_6151840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6151849 : List Nat := [1, 2, 1, 1, 1, 1, 2, 2, 1, 11]
def baseStart_6151849 : Nat := 118140960795 + 6151849 * 2 ^ 59
def prefixEnd_6151849 : Nat := 4983230072969 + 3 ^ 40 * 6151849 * 2
def baseEnd_6151849 : Nat := 1052951816960402198731889

theorem tailTrace_6151849 : CollatzResearch.WordTrace tailWord_6151849 prefixEnd_6151849 1052951816960402198731889 := by
  unfold tailWord_6151849
  simp only [CollatzResearch.WordTrace]
  refine ⟨224376366289909200007618601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149584244193272800005079067 224376366289909200007618601)
  ·
    refine ⟨168282274717431900005713951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224376366289909200007618601 168282274717431900005713951)
    ·
      refine ⟨252423412076147850008570927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168282274717431900005713951 252423412076147850008570927)
      ·
        refine ⟨378635118114221775012856391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252423412076147850008570927 378635118114221775012856391)
        ·
          refine ⟨567952677171332662519284587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 378635118114221775012856391 567952677171332662519284587)
          ·
            refine ⟨851929015756998993778926881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 567952677171332662519284587 851929015756998993778926881)
            ·
              refine ⟨638946761817749245334195161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 851929015756998993778926881 638946761817749245334195161)
              ·
                refine ⟨479210071363311934000646371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 638946761817749245334195161 479210071363311934000646371)
                ·
                  refine ⟨718815107044967901000969557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 479210071363311934000646371 718815107044967901000969557)
                  ·
                    refine ⟨1052951816960402198731889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 718815107044967901000969557 1052951816960402198731889)
                    ·
                      rfl

theorem cell23_6151849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 11].length) (baseStart_6151849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6151849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6151849 prefixEnd_6151849 := by exact prefixLift 6151849
  have htrace : WordTrace (prefixWord ++ tailWord_6151849) baseStart_6151849 baseEnd_6151849 := by
    simpa [prefixWord, tailWord_6151849, baseEnd_6151849] using wordTrace_append hprefix tailTrace_6151849
  have hstable : (prefixWord ++ tailWord_6151849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6151849).length < 2 ^ (prefixWord ++ tailWord_6151849).sum := by decide
  have hdescent : baseEnd_6151849 < baseStart_6151849 := by decide
  rcases family_descends (prefixWord ++ tailWord_6151849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6151870 : List Nat := [4, 2, 1, 1, 2, 3, 3, 1, 6]
def baseStart_6151870 : Nat := 118140960795 + 6151870 * 2 ^ 59
def prefixEnd_6151870 : Nat := 4983230072969 + 3 ^ 40 * 6151870 * 2
def baseEnd_6151870 : Nat := 350985137108327890448119

theorem tailTrace_6151870 : CollatzResearch.WordTrace tailWord_6151870 prefixEnd_6151870 350985137108327890448119 := by
  unfold tailWord_6151870
  simp only [CollatzResearch.WordTrace]
  refine ⟨28047141527854140074266633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149584754815222080396088709 28047141527854140074266633)
  ·
    refine ⟨21035356145890605055699975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28047141527854140074266633 21035356145890605055699975)
    ·
      refine ⟨31553034218835907583549963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21035356145890605055699975 31553034218835907583549963)
      ·
        refine ⟨47329551328253861375324945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31553034218835907583549963 47329551328253861375324945)
        ·
          refine ⟨35497163496190396031493709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47329551328253861375324945 35497163496190396031493709)
          ·
            refine ⟨13311436311071398511810141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35497163496190396031493709 13311436311071398511810141)
            ·
              refine ⟨4991788616651774441928803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13311436311071398511810141 4991788616651774441928803)
              ·
                refine ⟨7487682924977661662893205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4991788616651774441928803 7487682924977661662893205)
                ·
                  refine ⟨350985137108327890448119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7487682924977661662893205 350985137108327890448119)
                  ·
                    rfl

theorem cell23_6151870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 3, 1, 6].length) (baseStart_6151870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6151870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6151870 prefixEnd_6151870 := by exact prefixLift 6151870
  have htrace : WordTrace (prefixWord ++ tailWord_6151870) baseStart_6151870 baseEnd_6151870 := by
    simpa [prefixWord, tailWord_6151870, baseEnd_6151870] using wordTrace_append hprefix tailTrace_6151870
  have hstable : (prefixWord ++ tailWord_6151870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6151870).length < 2 ^ (prefixWord ++ tailWord_6151870).sum := by decide
  have hdescent : baseEnd_6151870 < baseStart_6151870 := by decide
  rcases family_descends (prefixWord ++ tailWord_6151870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6151890 : List Nat := [3, 2, 2, 2, 2, 1, 2, 1, 1, 5, 2]
def baseStart_6151890 : Nat := 118140960795 + 6151890 * 2 ^ 59
def prefixEnd_6151890 : Nat := 4983230072969 + 3 ^ 40 * 6151890 * 2
def baseEnd_6151890 : Nat := 3158876503588040935782979

theorem tailTrace_6151890 : CollatzResearch.WordTrace tailWord_6151890 prefixEnd_6151890 3158876503588040935782979 := by
  unfold tailWord_6151890
  simp only [CollatzResearch.WordTrace]
  refine ⟨56094465420690166002465281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149585241121840442673240749 56094465420690166002465281)
  ·
    refine ⟨42070849065517624501848961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56094465420690166002465281 42070849065517624501848961)
    ·
      refine ⟨31553136799138218376386721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42070849065517624501848961 31553136799138218376386721)
      ·
        refine ⟨23664852599353663782290041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31553136799138218376386721 23664852599353663782290041)
        ·
          refine ⟨17748639449515247836717531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23664852599353663782290041 17748639449515247836717531)
          ·
            refine ⟨26622959174272871755076297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17748639449515247836717531 26622959174272871755076297)
            ·
              refine ⟨19967219380704653816307223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26622959174272871755076297 19967219380704653816307223)
              ·
                refine ⟨29950829071056980724460835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19967219380704653816307223 29950829071056980724460835)
                ·
                  refine ⟨44926243606585471086691253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29950829071056980724460835 44926243606585471086691253)
                  ·
                    refine ⟨4211835338117387914377305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44926243606585471086691253 4211835338117387914377305)
                    ·
                      refine ⟨3158876503588040935782979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4211835338117387914377305 3158876503588040935782979)
                      ·
                        rfl

theorem cell23_6151890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 1, 1, 5, 2].length) (baseStart_6151890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6151890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6151890 prefixEnd_6151890 := by exact prefixLift 6151890
  have htrace : WordTrace (prefixWord ++ tailWord_6151890) baseStart_6151890 baseEnd_6151890 := by
    simpa [prefixWord, tailWord_6151890, baseEnd_6151890] using wordTrace_append hprefix tailTrace_6151890
  have hstable : (prefixWord ++ tailWord_6151890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6151890).length < 2 ^ (prefixWord ++ tailWord_6151890).sum := by decide
  have hdescent : baseEnd_6151890 < baseStart_6151890 := by decide
  rcases family_descends (prefixWord ++ tailWord_6151890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6151896 : List Nat := [2, 1, 2, 2, 3, 1, 2, 1, 3, 6]
def baseStart_6151896 : Nat := 118140960795 + 6151896 * 2 ^ 59
def prefixEnd_6151896 : Nat := 4983230072969 + 3 ^ 40 * 6151896 * 2
def baseEnd_6151896 : Nat := 1052959861490655970769317

theorem tailTrace_6151896 : CollatzResearch.WordTrace tailWord_6151896 prefixEnd_6151896 1052959861490655970769317 := by
  unfold tailWord_6151896
  simp only [CollatzResearch.WordTrace]
  refine ⟨112189040260369463517289771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149585387013825951356386361 112189040260369463517289771)
  ·
    refine ⟨168283560390554195275934657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112189040260369463517289771 168283560390554195275934657)
    ·
      refine ⟨126212670292915646456950993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168283560390554195275934657 126212670292915646456950993)
      ·
        refine ⟨94659502719686734842713245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126212670292915646456950993 94659502719686734842713245)
        ·
          refine ⟨35497313519882525566017467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94659502719686734842713245 35497313519882525566017467)
          ·
            refine ⟨53245970279823788349026201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35497313519882525566017467 53245970279823788349026201)
            ·
              refine ⟨39934477709867841261769651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53245970279823788349026201 39934477709867841261769651)
              ·
                refine ⟨59901716564801761892654477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39934477709867841261769651 59901716564801761892654477)
                ·
                  refine ⟨22463143711800660709745429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59901716564801761892654477 22463143711800660709745429)
                  ·
                    refine ⟨1052959861490655970769317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22463143711800660709745429 1052959861490655970769317)
                    ·
                      rfl

theorem cell23_6151896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 1, 3, 6].length) (baseStart_6151896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6151896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6151896 prefixEnd_6151896 := by exact prefixLift 6151896
  have htrace : WordTrace (prefixWord ++ tailWord_6151896) baseStart_6151896 baseEnd_6151896 := by
    simpa [prefixWord, tailWord_6151896, baseEnd_6151896] using wordTrace_append hprefix tailTrace_6151896
  have hstable : (prefixWord ++ tailWord_6151896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6151896).length < 2 ^ (prefixWord ++ tailWord_6151896).sum := by decide
  have hdescent : baseEnd_6151896 < baseStart_6151896 := by decide
  rcases family_descends (prefixWord ++ tailWord_6151896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6151897 : List Nat := [1, 2, 1, 2, 3, 3, 3, 3, 1, 1, 3]
def baseStart_6151897 : Nat := 118140960795 + 6151897 * 2 ^ 59
def prefixEnd_6151897 : Nat := 4983230072969 + 3 ^ 40 * 6151897 * 2
def baseEnd_6151897 : Nat := 3158880097952622408395447

theorem tailTrace_6151897 : CollatzResearch.WordTrace tailWord_6151897 prefixEnd_6151897 3158880097952622408395447 := by
  unfold tailWord_6151897
  simp only [CollatzResearch.WordTrace]
  refine ⟨224378116993735304205365945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149585411329156869470243963 224378116993735304205365945)
  ·
    refine ⟨168283587745301478154024459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224378116993735304205365945 168283587745301478154024459)
    ·
      refine ⟨252425381617952217231036689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168283587745301478154024459 252425381617952217231036689)
      ·
        refine ⟨189319036213464162923277517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 252425381617952217231036689 189319036213464162923277517)
        ·
          refine ⟨70994638580049061096229069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 189319036213464162923277517 70994638580049061096229069)
          ·
            refine ⟨26622989467518397911085901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70994638580049061096229069 26622989467518397911085901)
            ·
              refine ⟨9983621050319399216657213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26622989467518397911085901 9983621050319399216657213)
              ·
                refine ⟨3743857893869774706246455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9983621050319399216657213 3743857893869774706246455)
                ·
                  refine ⟨5615786840804662059369683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3743857893869774706246455 5615786840804662059369683)
                  ·
                    refine ⟨8423680261206993089054525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5615786840804662059369683 8423680261206993089054525)
                    ·
                      refine ⟨3158880097952622408395447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8423680261206993089054525 3158880097952622408395447)
                      ·
                        rfl

theorem cell23_6151897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3, 3, 1, 1, 3].length) (baseStart_6151897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6151897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6151897 prefixEnd_6151897 := by exact prefixLift 6151897
  have htrace : WordTrace (prefixWord ++ tailWord_6151897) baseStart_6151897 baseEnd_6151897 := by
    simpa [prefixWord, tailWord_6151897, baseEnd_6151897] using wordTrace_append hprefix tailTrace_6151897
  have hstable : (prefixWord ++ tailWord_6151897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6151897).length < 2 ^ (prefixWord ++ tailWord_6151897).sum := by decide
  have hdescent : baseEnd_6151897 < baseStart_6151897 := by decide
  rcases family_descends (prefixWord ++ tailWord_6151897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6151903 : List Nat := [1, 1, 2, 3, 2, 2, 1, 5, 1, 1, 4]
def baseStart_6151903 : Nat := 118140960795 + 6151903 * 2 ^ 59
def prefixEnd_6151903 : Nat := 4983230072969 + 3 ^ 40 * 6151903 * 2
def baseEnd_6151903 : Nat := 3158883178836549384920419

theorem tailTrace_6151903 : CollatzResearch.WordTrace tailWord_6151903 prefixEnd_6151903 3158883178836549384920419 := by
  unfold tailWord_6151903
  simp only [CollatzResearch.WordTrace]
  refine ⟨224378335831713567230084363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149585557221142378153389575 224378335831713567230084363)
  ·
    refine ⟨336567503747570350845126545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224378335831713567230084363 336567503747570350845126545)
    ·
      refine ⟨252425627810677763133844909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 336567503747570350845126545 252425627810677763133844909)
      ·
        refine ⟨94659610429004161175191841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 252425627810677763133844909 94659610429004161175191841)
        ·
          refine ⟨70994707821753120881393881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94659610429004161175191841 70994707821753120881393881)
          ·
            refine ⟨53246030866314840661045411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70994707821753120881393881 53246030866314840661045411)
            ·
              refine ⟨79869046299472260991568117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53246030866314840661045411 79869046299472260991568117)
              ·
                refine ⟨7487723090575524467959511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 79869046299472260991568117 7487723090575524467959511)
                ·
                  refine ⟨11231584635863286701939267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7487723090575524467959511 11231584635863286701939267)
                  ·
                    refine ⟨16847376953794930052908901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11231584635863286701939267 16847376953794930052908901)
                    ·
                      refine ⟨3158883178836549384920419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16847376953794930052908901 3158883178836549384920419)
                      ·
                        rfl

theorem cell23_6151903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 5, 1, 1, 4].length) (baseStart_6151903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6151903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6151903 prefixEnd_6151903 := by exact prefixLift 6151903
  have htrace : WordTrace (prefixWord ++ tailWord_6151903) baseStart_6151903 baseEnd_6151903 := by
    simpa [prefixWord, tailWord_6151903, baseEnd_6151903] using wordTrace_append hprefix tailTrace_6151903
  have hstable : (prefixWord ++ tailWord_6151903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6151903).length < 2 ^ (prefixWord ++ tailWord_6151903).sum := by decide
  have hdescent : baseEnd_6151903 < baseStart_6151903 := by decide
  rcases family_descends (prefixWord ++ tailWord_6151903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6151907 : List Nat := [1, 1, 1, 7, 2, 1, 1, 2, 2, 3, 2]
def baseStart_6151907 : Nat := 118140960795 + 6151907 * 2 ^ 59
def prefixEnd_6151907 : Nat := 4983230072969 + 3 ^ 40 * 6151907 * 2
def baseEnd_6151907 : Nat := 3158885232759167369270401

theorem tailTrace_6151907 : CollatzResearch.WordTrace tailWord_6151907 prefixEnd_6151907 3158885232759167369270401 := by
  unfold tailWord_6151907
  simp only [CollatzResearch.WordTrace]
  refine ⟨224378481723699075913229975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149585654482466050608819983 224378481723699075913229975)
  ·
    refine ⟨336567722585548613869844963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224378481723699075913229975 336567722585548613869844963)
    ·
      refine ⟨504851583878322920804767445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 336567722585548613869844963 504851583878322920804767445)
      ·
        refine ⟨11832458997148193456361737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 504851583878322920804767445 11832458997148193456361737)
        ·
          refine ⟨8874344247861145092271303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11832458997148193456361737 8874344247861145092271303)
          ·
            refine ⟨13311516371791717638406955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8874344247861145092271303 13311516371791717638406955)
            ·
              refine ⟨19967274557687576457610433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13311516371791717638406955 19967274557687576457610433)
              ·
                refine ⟨14975455918265682343207825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19967274557687576457610433 14975455918265682343207825)
                ·
                  refine ⟨11231591938699261757405869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14975455918265682343207825 11231591938699261757405869)
                  ·
                    refine ⟨4211846977012223159027201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11231591938699261757405869 4211846977012223159027201)
                    ·
                      refine ⟨3158885232759167369270401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4211846977012223159027201 3158885232759167369270401)
                      ·
                        rfl

theorem cell23_6151907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 2, 2, 3, 2].length) (baseStart_6151907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6151907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6151907 prefixEnd_6151907 := by exact prefixLift 6151907
  have htrace : WordTrace (prefixWord ++ tailWord_6151907) baseStart_6151907 baseEnd_6151907 := by
    simpa [prefixWord, tailWord_6151907, baseEnd_6151907] using wordTrace_append hprefix tailTrace_6151907
  have hstable : (prefixWord ++ tailWord_6151907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6151907).length < 2 ^ (prefixWord ++ tailWord_6151907).sum := by decide
  have hdescent : baseEnd_6151907 < baseStart_6151907 := by decide
  rcases family_descends (prefixWord ++ tailWord_6151907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6151913 : List Nat := [1, 2, 1, 1, 1, 2, 3, 6, 2, 4]
def baseStart_6151913 : Nat := 118140960795 + 6151913 * 2 ^ 59
def prefixEnd_6151913 : Nat := 4983230072969 + 3 ^ 40 * 6151913 * 2
def baseEnd_6151913 : Nat := 1052962771214364781931791

theorem tailTrace_6151913 : CollatzResearch.WordTrace tailWord_6151913 prefixEnd_6151913 1052962771214364781931791 := by
  unfold tailWord_6151913
  simp only [CollatzResearch.WordTrace]
  refine ⟨224378700561677338937948393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149585800374451559291965595 224378700561677338937948393)
  ·
    refine ⟨168284025421258004203461295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224378700561677338937948393 168284025421258004203461295)
    ·
      refine ⟨252426038131887006305191943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168284025421258004203461295 252426038131887006305191943)
      ·
        refine ⟨378639057197830509457787915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252426038131887006305191943 378639057197830509457787915)
        ·
          refine ⟨567958585796745764186681873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 378639057197830509457787915 567958585796745764186681873)
          ·
            refine ⟨425968939347559323140011405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 567958585796745764186681873 425968939347559323140011405)
            ·
              refine ⟨159738352255334746177504277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 425968939347559323140011405 159738352255334746177504277)
              ·
                refine ⟨7487735261968816227070513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 159738352255334746177504277 7487735261968816227070513)
                ·
                  refine ⟨5615801446476612170302885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7487735261968816227070513 5615801446476612170302885)
                  ·
                    refine ⟨1052962771214364781931791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5615801446476612170302885 1052962771214364781931791)
                    ·
                      rfl

theorem cell23_6151913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 6, 2, 4].length) (baseStart_6151913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6151913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6151913 prefixEnd_6151913 := by exact prefixLift 6151913
  have htrace : WordTrace (prefixWord ++ tailWord_6151913) baseStart_6151913 baseEnd_6151913 := by
    simpa [prefixWord, tailWord_6151913, baseEnd_6151913] using wordTrace_append hprefix tailTrace_6151913
  have hstable : (prefixWord ++ tailWord_6151913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6151913).length < 2 ^ (prefixWord ++ tailWord_6151913).sum := by decide
  have hdescent : baseEnd_6151913 < baseStart_6151913 := by decide
  rcases family_descends (prefixWord ++ tailWord_6151913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6151916 : List Nat := [2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 6]
def baseStart_6151916 : Nat := 118140960795 + 6151916 * 2 ^ 59
def prefixEnd_6151916 : Nat := 4983230072969 + 3 ^ 40 * 6151916 * 2
def baseEnd_6151916 : Nat := 3158889854085057834057859

theorem tailTrace_6151916 : CollatzResearch.WordTrace tailWord_6151916 prefixEnd_6151916 3158889854085057834057859 := by
  unfold tailWord_6151916
  simp only [CollatzResearch.WordTrace]
  refine ⟨112189404990333235225153801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149585873320444313633538401 112189404990333235225153801)
  ·
    refine ⟨84142053742749926418865351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112189404990333235225153801 84142053742749926418865351)
    ·
      refine ⟨126213080614124889628298027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84142053742749926418865351 126213080614124889628298027)
      ·
        refine ⟨189319620921187334442447041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126213080614124889628298027 189319620921187334442447041)
        ·
          refine ⟨141989715690890500831835281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189319620921187334442447041 141989715690890500831835281)
          ·
            refine ⟨106492286768167875623876461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141989715690890500831835281 106492286768167875623876461)
            ·
              refine ⟨39934607538062953358953673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106492286768167875623876461 39934607538062953358953673)
              ·
                refine ⟨29950955653547215019215255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39934607538062953358953673 29950955653547215019215255)
                ·
                  refine ⟨44926433480320822528822883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29950955653547215019215255 44926433480320822528822883)
                  ·
                    refine ⟨67389650220481233793234325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44926433480320822528822883 67389650220481233793234325)
                    ·
                      refine ⟨3158889854085057834057859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67389650220481233793234325 3158889854085057834057859)
                      ·
                        rfl

theorem cell23_6151916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 6].length) (baseStart_6151916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6151916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6151916 prefixEnd_6151916 := by exact prefixLift 6151916
  have htrace : WordTrace (prefixWord ++ tailWord_6151916) baseStart_6151916 baseEnd_6151916 := by
    simpa [prefixWord, tailWord_6151916, baseEnd_6151916] using wordTrace_append hprefix tailTrace_6151916
  have hstable : (prefixWord ++ tailWord_6151916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6151916).length < 2 ^ (prefixWord ++ tailWord_6151916).sum := by decide
  have hdescent : baseEnd_6151916 < baseStart_6151916 := by decide
  rcases family_descends (prefixWord ++ tailWord_6151916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6151920 : List Nat := [2, 1, 1, 1, 3, 1, 2, 5, 3, 2, 2]
def baseStart_6151920 : Nat := 118140960795 + 6151920 * 2 ^ 59
def prefixEnd_6151920 : Nat := 4983230072969 + 3 ^ 40 * 6151920 * 2
def baseEnd_6151920 : Nat := 3158891908007675818407841

theorem tailTrace_6151920 : CollatzResearch.WordTrace tailWord_6151920 prefixEnd_6151920 3158891908007675818407841 := by
  unfold tailWord_6151920
  simp only [CollatzResearch.WordTrace]
  refine ⟨112189477936325989566726607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149585970581767986088968809 112189477936325989566726607)
  ·
    refine ⟨168284216904488984350089911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112189477936325989566726607 168284216904488984350089911)
    ·
      refine ⟨252426325356733476525134867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168284216904488984350089911 252426325356733476525134867)
      ·
        refine ⟨378639488035100214787702301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252426325356733476525134867 378639488035100214787702301)
        ·
          refine ⟨141989808013162580545388363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 378639488035100214787702301 141989808013162580545388363)
          ·
            refine ⟨212984712019743870818082545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141989808013162580545388363 212984712019743870818082545)
            ·
              refine ⟨159738534014807903113561909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 212984712019743870818082545 159738534014807903113561909)
              ·
                refine ⟨14975487563888240916896429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 159738534014807903113561909 14975487563888240916896429)
                ·
                  refine ⟨5615807836458090343836161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14975487563888240916896429 5615807836458090343836161)
                  ·
                    refine ⟨4211855877343567757877121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5615807836458090343836161 4211855877343567757877121)
                    ·
                      refine ⟨3158891908007675818407841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4211855877343567757877121 3158891908007675818407841)
                      ·
                        rfl

theorem cell23_6151920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 5, 3, 2, 2].length) (baseStart_6151920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6151920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6151920 prefixEnd_6151920 := by exact prefixLift 6151920
  have htrace : WordTrace (prefixWord ++ tailWord_6151920) baseStart_6151920 baseEnd_6151920 := by
    simpa [prefixWord, tailWord_6151920, baseEnd_6151920] using wordTrace_append hprefix tailTrace_6151920
  have hstable : (prefixWord ++ tailWord_6151920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6151920).length < 2 ^ (prefixWord ++ tailWord_6151920).sum := by decide
  have hdescent : baseEnd_6151920 < baseStart_6151920 := by decide
  rcases family_descends (prefixWord ++ tailWord_6151920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6151934 : List Nat := [4, 2, 2, 1, 4, 1, 1, 2, 1, 5]
def baseStart_6151934 : Nat := 118140960795 + 6151934 * 2 ^ 59
def prefixEnd_6151934 : Nat := 4983230072969 + 3 ^ 40 * 6151934 * 2
def baseEnd_6151934 : Nat := 1052966365578946254544259

theorem tailTrace_6151934 : CollatzResearch.WordTrace tailWord_6151934 prefixEnd_6151934 1052966365578946254544259 := by
  unfold tailWord_6151934
  simp only [CollatzResearch.WordTrace]
  refine ⟨28047433311825157440557857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149586310996400839682975237 28047433311825157440557857)
  ·
    refine ⟨21035574983868868080418393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28047433311825157440557857 21035574983868868080418393)
    ·
      refine ⟨15776681237901651060313795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21035574983868868080418393 15776681237901651060313795)
      ·
        refine ⟨23665021856852476590470693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15776681237901651060313795 23665021856852476590470693)
        ·
          refine ⟨4437191598159839360713255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23665021856852476590470693 4437191598159839360713255)
          ·
            refine ⟨6655787397239759041069883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4437191598159839360713255 6655787397239759041069883)
            ·
              refine ⟨9983681095859638561604825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6655787397239759041069883 9983681095859638561604825)
              ·
                refine ⟨7487760821894728921203619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9983681095859638561604825 7487760821894728921203619)
                ·
                  refine ⟨11231641232842093381805429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7487760821894728921203619 11231641232842093381805429)
                  ·
                    refine ⟨1052966365578946254544259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11231641232842093381805429 1052966365578946254544259)
                    ·
                      rfl

theorem cell23_6151934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 1, 2, 1, 5].length) (baseStart_6151934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6151934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6151934 prefixEnd_6151934 := by exact prefixLift 6151934
  have htrace : WordTrace (prefixWord ++ tailWord_6151934) baseStart_6151934 baseEnd_6151934 := by
    simpa [prefixWord, tailWord_6151934, baseEnd_6151934] using wordTrace_append hprefix tailTrace_6151934
  have hstable : (prefixWord ++ tailWord_6151934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6151934).length < 2 ^ (prefixWord ++ tailWord_6151934).sum := by decide
  have hdescent : baseEnd_6151934 < baseStart_6151934 := by decide
  rcases family_descends (prefixWord ++ tailWord_6151934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6151940 : List Nat := [2, 3, 2, 2, 1, 3, 1, 1, 3, 2, 3]
def baseStart_6151940 : Nat := 118140960795 + 6151940 * 2 ^ 59
def prefixEnd_6151940 : Nat := 4983230072969 + 3 ^ 40 * 6151940 * 2
def baseEnd_6151940 : Nat := 3158902177620765740157749

theorem tailTrace_6151940 : CollatzResearch.WordTrace tailWord_6151940 prefixEnd_6151940 3158902177620765740157749 := by
  unfold tailWord_6151940
  simp only [CollatzResearch.WordTrace]
  refine ⟨112189842666289761274590637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149586456888386348366120849 112189842666289761274590637)
  ·
    refine ⟨42071190999858660477971489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112189842666289761274590637 42071190999858660477971489)
    ·
      refine ⟨31553393249893995358478617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42071190999858660477971489 31553393249893995358478617)
      ·
        refine ⟨23665044937420496518858963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31553393249893995358478617 23665044937420496518858963)
        ·
          refine ⟨35497567406130744778288445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23665044937420496518858963 35497567406130744778288445)
          ·
            refine ⟨13311587777299029291858167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35497567406130744778288445 13311587777299029291858167)
            ·
              refine ⟨19967381665948543937787251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13311587777299029291858167 19967381665948543937787251)
              ·
                refine ⟨29951072498922815906680877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19967381665948543937787251 29951072498922815906680877)
                ·
                  refine ⟨11231652187096055965005329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29951072498922815906680877 11231652187096055965005329)
                  ·
                    refine ⟨8423739140322041973753997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11231652187096055965005329 8423739140322041973753997)
                    ·
                      refine ⟨3158902177620765740157749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8423739140322041973753997 3158902177620765740157749)
                      ·
                        rfl

theorem cell23_6151940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 1, 3, 2, 3].length) (baseStart_6151940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6151940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6151940 prefixEnd_6151940 := by exact prefixLift 6151940
  have htrace : WordTrace (prefixWord ++ tailWord_6151940) baseStart_6151940 baseEnd_6151940 := by
    simpa [prefixWord, tailWord_6151940, baseEnd_6151940] using wordTrace_append hprefix tailTrace_6151940
  have hstable : (prefixWord ++ tailWord_6151940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6151940).length < 2 ^ (prefixWord ++ tailWord_6151940).sum := by decide
  have hdescent : baseEnd_6151940 < baseStart_6151940 := by decide
  rcases family_descends (prefixWord ++ tailWord_6151940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6151954 : List Nat := [3, 2, 4, 1, 1, 2, 3, 1, 1, 1, 4]
def baseStart_6151954 : Nat := 118140960795 + 6151954 * 2 ^ 59
def prefixEnd_6151954 : Nat := 4983230072969 + 3 ^ 40 * 6151954 * 2
def baseEnd_6151954 : Nat := 3158909366349928685382685

theorem tailTrace_6151954 : CollatzResearch.WordTrace tailWord_6151954 prefixEnd_6151954 3158909366349928685382685 := by
  unfold tailWord_6151954
  simp only [CollatzResearch.WordTrace]
  refine ⟨56095048988632200735047729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149586797303019201960127277 56095048988632200735047729)
  ·
    refine ⟨42071286741474150551285797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56095048988632200735047729 42071286741474150551285797)
    ·
      refine ⟨7888366264026403228366087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42071286741474150551285797 7888366264026403228366087)
      ·
        refine ⟨11832549396039604842549131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7888366264026403228366087 11832549396039604842549131)
        ·
          refine ⟨17748824094059407263823697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11832549396039604842549131 17748824094059407263823697)
          ·
            refine ⟨13311618070544555447867773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17748824094059407263823697 13311618070544555447867773)
            ·
              refine ⟨4991856776454208292950415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13311618070544555447867773 4991856776454208292950415)
              ·
                refine ⟨7487785164681312439425623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4991856776454208292950415 7487785164681312439425623)
                ·
                  refine ⟨11231677747021968659138435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7487785164681312439425623 11231677747021968659138435)
                  ·
                    refine ⟨16847516620532952988707653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11231677747021968659138435 16847516620532952988707653)
                    ·
                      refine ⟨3158909366349928685382685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16847516620532952988707653 3158909366349928685382685)
                      ·
                        rfl

theorem cell23_6151954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 3, 1, 1, 1, 4].length) (baseStart_6151954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6151954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6151954 prefixEnd_6151954 := by exact prefixLift 6151954
  have htrace : WordTrace (prefixWord ++ tailWord_6151954) baseStart_6151954 baseEnd_6151954 := by
    simpa [prefixWord, tailWord_6151954, baseEnd_6151954] using wordTrace_append hprefix tailTrace_6151954
  have hstable : (prefixWord ++ tailWord_6151954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6151954).length < 2 ^ (prefixWord ++ tailWord_6151954).sum := by decide
  have hdescent : baseEnd_6151954 < baseStart_6151954 := by decide
  rcases family_descends (prefixWord ++ tailWord_6151954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6151957 : List Nat := [1, 3, 2, 1, 2, 4, 3, 1, 1, 2, 3]
def baseStart_6151957 : Nat := 118140960795 + 6151957 * 2 ^ 59
def prefixEnd_6151957 : Nat := 4983230072969 + 3 ^ 40 * 6151957 * 2
def baseEnd_6151957 : Nat := 3158910906791892173645171

theorem tailTrace_6151957 : CollatzResearch.WordTrace tailWord_6151957 prefixEnd_6151957 3158910906791892173645171 := by
  unfold tailWord_6151957
  simp only [CollatzResearch.WordTrace]
  refine ⟨224380305373517934452550125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149586870249011956301700083 224380305373517934452550125)
  ·
    refine ⟨84142614515069225419706297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 224380305373517934452550125 84142614515069225419706297)
    ·
      refine ⟨63106960886301919064779723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84142614515069225419706297 63106960886301919064779723)
      ·
        refine ⟨94660441329452878597169585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63106960886301919064779723 94660441329452878597169585)
        ·
          refine ⟨70995330997089658947877189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94660441329452878597169585 70995330997089658947877189)
          ·
            refine ⟨13311624561954311052726973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70995330997089658947877189 13311624561954311052726973)
            ·
              refine ⟨4991859210732866644772615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13311624561954311052726973 4991859210732866644772615)
              ·
                refine ⟨7487788816099299967158923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4991859210732866644772615 7487788816099299967158923)
                ·
                  refine ⟨11231683224148949950738385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7487788816099299967158923 11231683224148949950738385)
                  ·
                    refine ⟨8423762418111712463053789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11231683224148949950738385 8423762418111712463053789)
                    ·
                      refine ⟨3158910906791892173645171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8423762418111712463053789 3158910906791892173645171)
                      ·
                        rfl

theorem cell23_6151957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 3, 1, 1, 2, 3].length) (baseStart_6151957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6151957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6151957 prefixEnd_6151957 := by exact prefixLift 6151957
  have htrace : WordTrace (prefixWord ++ tailWord_6151957) baseStart_6151957 baseEnd_6151957 := by
    simpa [prefixWord, tailWord_6151957, baseEnd_6151957] using wordTrace_append hprefix tailTrace_6151957
  have hstable : (prefixWord ++ tailWord_6151957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6151957).length < 2 ^ (prefixWord ++ tailWord_6151957).sum := by decide
  have hdescent : baseEnd_6151957 < baseStart_6151957 := by decide
  rcases family_descends (prefixWord ++ tailWord_6151957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6151980 : List Nat := [2, 2, 1, 1, 1, 5, 1, 2, 3, 3, 2]
def baseStart_6151980 : Nat := 118140960795 + 6151980 * 2 ^ 59
def prefixEnd_6151980 : Nat := 4983230072969 + 3 ^ 40 * 6151980 * 2
def baseEnd_6151980 : Nat := 3158922716846945583657565

theorem tailTrace_6151980 : CollatzResearch.WordTrace tailWord_6151980 prefixEnd_6151980 3158922716846945583657565 := by
  unfold tailWord_6151980
  simp only [CollatzResearch.WordTrace]
  refine ⟨112190572126217304690318697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149587429501623072920424929 112190572126217304690318697)
  ·
    refine ⟨84142929094662978517739023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112190572126217304690318697 84142929094662978517739023)
    ·
      refine ⟨126214393641994467776608535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84142929094662978517739023 126214393641994467776608535)
      ·
        refine ⟨189321590462991701664912803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126214393641994467776608535 189321590462991701664912803)
        ·
          refine ⟨283982385694487552497369205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189321590462991701664912803 283982385694487552497369205)
          ·
            refine ⟨26623348658858208046628363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 283982385694487552497369205 26623348658858208046628363)
            ·
              refine ⟨39935022988287312069942545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26623348658858208046628363 39935022988287312069942545)
              ·
                refine ⟨29951267241215484052456909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39935022988287312069942545 29951267241215484052456909)
                ·
                  refine ⟨11231725215455806519671341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29951267241215484052456909 11231725215455806519671341)
                  ·
                    refine ⟨4211896955795927444876753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11231725215455806519671341 4211896955795927444876753)
                    ·
                      refine ⟨3158922716846945583657565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4211896955795927444876753 3158922716846945583657565)
                      ·
                        rfl

theorem cell23_6151980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 3, 2].length) (baseStart_6151980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6151980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6151980 prefixEnd_6151980 := by exact prefixLift 6151980
  have htrace : WordTrace (prefixWord ++ tailWord_6151980) baseStart_6151980 baseEnd_6151980 := by
    simpa [prefixWord, tailWord_6151980, baseEnd_6151980] using wordTrace_append hprefix tailTrace_6151980
  have hstable : (prefixWord ++ tailWord_6151980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6151980).length < 2 ^ (prefixWord ++ tailWord_6151980).sum := by decide
  have hdescent : baseEnd_6151980 < baseStart_6151980 := by decide
  rcases family_descends (prefixWord ++ tailWord_6151980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6151997 : List Nat := [1, 4, 1, 4, 1, 1, 2, 1, 3, 3, 2]
def baseStart_6151997 : Nat := 118140960795 + 6151997 * 2 ^ 59
def prefixEnd_6151997 : Nat := 4983230072969 + 3 ^ 40 * 6151997 * 2
def baseEnd_6151997 : Nat := 3158931446018072017144987

theorem tailTrace_6151997 : CollatzResearch.WordTrace tailWord_6151997 prefixEnd_6151997 3158931446018072017144987 := by
  unfold tailWord_6151997
  simp only [CollatzResearch.WordTrace]
  refine ⟨224381764293373021284006245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149587842862248680856004163 224381764293373021284006245)
  ·
    refine ⟨42071580805007441490751171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 224381764293373021284006245 42071580805007441490751171)
    ·
      refine ⟨63107371207511162236126757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42071580805007441490751171 63107371207511162236126757)
      ·
        refine ⟨11832632101408342919273767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63107371207511162236126757 11832632101408342919273767)
        ·
          refine ⟨17748948152112514378910651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11832632101408342919273767 17748948152112514378910651)
          ·
            refine ⟨26623422228168771568365977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17748948152112514378910651 26623422228168771568365977)
            ·
              refine ⟨19967566671126578676274483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26623422228168771568365977 19967566671126578676274483)
              ·
                refine ⟨29951350006689868014411725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19967566671126578676274483 29951350006689868014411725)
                ·
                  refine ⟨11231756252508700505404397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29951350006689868014411725 11231756252508700505404397)
                  ·
                    refine ⟨4211908594690762689526649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11231756252508700505404397 4211908594690762689526649)
                    ·
                      refine ⟨3158931446018072017144987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4211908594690762689526649 3158931446018072017144987)
                      ·
                        rfl

theorem cell23_6151997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 1, 3, 3, 2].length) (baseStart_6151997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6151997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6151997 prefixEnd_6151997 := by exact prefixLift 6151997
  have htrace : WordTrace (prefixWord ++ tailWord_6151997) baseStart_6151997 baseEnd_6151997 := by
    simpa [prefixWord, tailWord_6151997, baseEnd_6151997] using wordTrace_append hprefix tailTrace_6151997
  have hstable : (prefixWord ++ tailWord_6151997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6151997).length < 2 ^ (prefixWord ++ tailWord_6151997).sum := by decide
  have hdescent : baseEnd_6151997 < baseStart_6151997 := by decide
  rcases family_descends (prefixWord ++ tailWord_6151997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6152010 : List Nat := [3, 1, 2, 1, 1, 1, 3, 4, 1, 4, 2]
def baseStart_6152010 : Nat := 118140960795 + 6152010 * 2 ^ 59
def prefixEnd_6152010 : Nat := 4983230072969 + 3 ^ 40 * 6152010 * 2
def baseEnd_6152010 : Nat := 3158938121266580466282427

theorem tailTrace_6152010 : CollatzResearch.WordTrace tailWord_6152010 prefixEnd_6152010 3158938121266580466282427 := by
  unfold tailWord_6152010
  simp only [CollatzResearch.WordTrace]
  refine ⟨56095559610581481126057371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149588158961550616336152989 56095559610581481126057371)
  ·
    refine ⟨84143339415872221689086057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56095559610581481126057371 84143339415872221689086057)
    ·
      refine ⟨63107504561904166266814543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84143339415872221689086057 63107504561904166266814543)
      ·
        refine ⟨94661256842856249400221815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63107504561904166266814543 94661256842856249400221815)
        ·
          refine ⟨141991885264284374100332723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94661256842856249400221815 141991885264284374100332723)
          ·
            refine ⟨212987827896426561150499085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141991885264284374100332723 212987827896426561150499085)
            ·
              refine ⟨79870435461159960431437157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 212987827896426561150499085 79870435461159960431437157)
              ·
                refine ⟨14975706648967492580894467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 79870435461159960431437157 14975706648967492580894467)
                ·
                  refine ⟨22463559973451238871341701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14975706648967492580894467 22463559973451238871341701)
                  ·
                    refine ⟨4211917495022107288376569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22463559973451238871341701 4211917495022107288376569)
                    ·
                      refine ⟨3158938121266580466282427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4211917495022107288376569 3158938121266580466282427)
                      ·
                        rfl

theorem cell23_6152010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 4, 1, 4, 2].length) (baseStart_6152010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6152010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6152010 prefixEnd_6152010 := by exact prefixLift 6152010
  have htrace : WordTrace (prefixWord ++ tailWord_6152010) baseStart_6152010 baseEnd_6152010 := by
    simpa [prefixWord, tailWord_6152010, baseEnd_6152010] using wordTrace_append hprefix tailTrace_6152010
  have hstable : (prefixWord ++ tailWord_6152010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6152010).length < 2 ^ (prefixWord ++ tailWord_6152010).sum := by decide
  have hdescent : baseEnd_6152010 < baseStart_6152010 := by decide
  rcases family_descends (prefixWord ++ tailWord_6152010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6152016 : List Nat := [2, 1, 1, 1, 1, 4, 1, 1, 11]
def baseStart_6152016 : Nat := 118140960795 + 6152016 * 2 ^ 59
def prefixEnd_6152016 : Nat := 4983230072969 + 3 ^ 40 * 6152016 * 2
def baseEnd_6152016 : Nat := 350993466905611938089711

theorem tailTrace_6152016 : CollatzResearch.WordTrace tailWord_6152016 prefixEnd_6152016 350993466905611938089711 := by
  unfold tailWord_6152016
  simp only [CollatzResearch.WordTrace]
  refine ⟨112191228640152093764473951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149588304853536125019298601 112191228640152093764473951)
  ·
    refine ⟨168286842960228140646710927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112191228640152093764473951 168286842960228140646710927)
    ·
      refine ⟨252430264440342210970066391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168286842960228140646710927 252430264440342210970066391)
      ·
        refine ⟨378645396660513316455099587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252430264440342210970066391 378645396660513316455099587)
        ·
          refine ⟨567968094990769974682649381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 378645396660513316455099587 567968094990769974682649381)
          ·
            refine ⟨106494017810769370252996759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 567968094990769974682649381 106494017810769370252996759)
            ·
              refine ⟨159741026716154055379495139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106494017810769370252996759 159741026716154055379495139)
              ·
                refine ⟨239611540074231083069242709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 159741026716154055379495139 239611540074231083069242709)
                ·
                  refine ⟨350993466905611938089711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 239611540074231083069242709 350993466905611938089711)
                  ·
                    rfl

theorem cell23_6152016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 11].length) (baseStart_6152016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6152016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6152016 prefixEnd_6152016 := by exact prefixLift 6152016
  have htrace : WordTrace (prefixWord ++ tailWord_6152016) baseStart_6152016 baseEnd_6152016 := by
    simpa [prefixWord, tailWord_6152016, baseEnd_6152016] using wordTrace_append hprefix tailTrace_6152016
  have hstable : (prefixWord ++ tailWord_6152016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6152016).length < 2 ^ (prefixWord ++ tailWord_6152016).sum := by decide
  have hdescent : baseEnd_6152016 < baseStart_6152016 := by decide
  rcases family_descends (prefixWord ++ tailWord_6152016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6152033 : List Nat := [1, 2, 3, 1, 1, 1, 6, 1, 7]
def baseStart_6152033 : Nat := 118140960795 + 6152033 * 2 ^ 59
def prefixEnd_6152033 : Nat := 4983230072969 + 3 ^ 40 * 6152033 * 2
def baseEnd_6152033 : Nat := 350994436813514875143869

theorem tailTrace_6152033 : CollatzResearch.WordTrace tailWord_6152033 prefixEnd_6152033 350994436813514875143869 := by
  unfold tailWord_6152033
  simp only [CollatzResearch.WordTrace]
  refine ⟨224383077321242599432316753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149588718214161732954877835 224383077321242599432316753)
  ·
    refine ⟨168287307990931949574237565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224383077321242599432316753 168287307990931949574237565)
    ·
      refine ⟨63107740496599481090339087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168287307990931949574237565 63107740496599481090339087)
      ·
        refine ⟨94661610744899221635508631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63107740496599481090339087 94661610744899221635508631)
        ·
          refine ⟨141992416117348832453262947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94661610744899221635508631 141992416117348832453262947)
          ·
            refine ⟨212988624176023248679894421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141992416117348832453262947 212988624176023248679894421)
            ·
              refine ⟨9983841758251089781870051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 212988624176023248679894421 9983841758251089781870051)
              ·
                refine ⟨14975762637376634672805077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9983841758251089781870051 14975762637376634672805077)
                ·
                  refine ⟨350994436813514875143869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14975762637376634672805077 350994436813514875143869)
                  ·
                    rfl

theorem cell23_6152033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6, 1, 7].length) (baseStart_6152033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6152033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6152033 prefixEnd_6152033 := by exact prefixLift 6152033
  have htrace : WordTrace (prefixWord ++ tailWord_6152033) baseStart_6152033 baseEnd_6152033 := by
    simpa [prefixWord, tailWord_6152033, baseEnd_6152033] using wordTrace_append hprefix tailTrace_6152033
  have hstable : (prefixWord ++ tailWord_6152033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6152033).length < 2 ^ (prefixWord ++ tailWord_6152033).sum := by decide
  have hdescent : baseEnd_6152033 < baseStart_6152033 := by decide
  rcases family_descends (prefixWord ++ tailWord_6152033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6152063 : List Nat := [1, 1, 2, 2, 1, 1, 3, 5, 2, 5]
def baseStart_6152063 : Nat := 118140960795 + 6152063 * 2 ^ 59
def prefixEnd_6152063 : Nat := 4983230072969 + 3 ^ 40 * 6152063 * 2
def baseEnd_6152063 : Nat := 1052988445247089586306561

theorem tailTrace_6152063 : CollatzResearch.WordTrace tailWord_6152063 prefixEnd_6152063 1052988445247089586306561 := by
  unfold tailWord_6152063
  simp only [CollatzResearch.WordTrace]
  refine ⟨224384171511133914555908843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149589447674089276370605895 224384171511133914555908843)
  ·
    refine ⟨336576257266700871833863265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224384171511133914555908843 336576257266700871833863265)
    ·
      refine ⟨252432192950025653875397449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 336576257266700871833863265 252432192950025653875397449)
      ·
        refine ⟨189324144712519240406548087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 252432192950025653875397449 189324144712519240406548087)
        ·
          refine ⟨283986217068778860609822131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189324144712519240406548087 283986217068778860609822131)
          ·
            refine ⟨425979325603168290914733197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 283986217068778860609822131 425979325603168290914733197)
            ·
              refine ⟨159742247101188109093024949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 425979325603168290914733197 159742247101188109093024949)
              ·
                refine ⟨14975835665736385227471089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 159742247101188109093024949 14975835665736385227471089)
                ·
                  refine ⟨11231876749302288920603317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14975835665736385227471089 11231876749302288920603317)
                  ·
                    refine ⟨1052988445247089586306561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11231876749302288920603317 1052988445247089586306561)
                    ·
                      rfl

theorem cell23_6152063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 5, 2, 5].length) (baseStart_6152063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6152063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6152063 prefixEnd_6152063 := by exact prefixLift 6152063
  have htrace : WordTrace (prefixWord ++ tailWord_6152063) baseStart_6152063 baseEnd_6152063 := by
    simpa [prefixWord, tailWord_6152063, baseEnd_6152063] using wordTrace_append hprefix tailTrace_6152063
  have hstable : (prefixWord ++ tailWord_6152063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6152063).length < 2 ^ (prefixWord ++ tailWord_6152063).sum := by decide
  have hdescent : baseEnd_6152063 < baseStart_6152063 := by decide
  rcases family_descends (prefixWord ++ tailWord_6152063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6152067 : List Nat := [1, 1, 1, 3, 4, 4, 1, 3, 5]
def baseStart_6152067 : Nat := 118140960795 + 6152067 * 2 ^ 59
def prefixEnd_6152067 : Nat := 4983230072969 + 3 ^ 40 * 6152067 * 2
def baseEnd_6152067 : Nat := 350996376629320749252185

theorem tailTrace_6152067 : CollatzResearch.WordTrace tailWord_6152067 prefixEnd_6152067 350996376629320749252185 := by
  unfold tailWord_6152067
  simp only [CollatzResearch.WordTrace]
  refine ⟨224384317403119423239054455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149589544935412948826036303 224384317403119423239054455)
  ·
    refine ⟨336576476104679134858581683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224384317403119423239054455 336576476104679134858581683)
    ·
      refine ⟨504864714157018702287872525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 336576476104679134858581683 504864714157018702287872525)
      ·
        refine ⟨189324267808882013357952197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 504864714157018702287872525 189324267808882013357952197)
        ·
          refine ⟨35498300214165377504616037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 189324267808882013357952197 35498300214165377504616037)
          ·
            refine ⟨6655931290156008282115507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35498300214165377504616037 6655931290156008282115507)
            ·
              refine ⟨9983896935234012423173261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6655931290156008282115507 9983896935234012423173261)
              ·
                refine ⟨3743961350712754658689973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9983896935234012423173261 3743961350712754658689973)
                ·
                  refine ⟨350996376629320749252185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3743961350712754658689973 350996376629320749252185)
                  ·
                    rfl

theorem cell23_6152067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 1, 3, 5].length) (baseStart_6152067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6152067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6152067 prefixEnd_6152067 := by exact prefixLift 6152067
  have htrace : WordTrace (prefixWord ++ tailWord_6152067) baseStart_6152067 baseEnd_6152067 := by
    simpa [prefixWord, tailWord_6152067, baseEnd_6152067] using wordTrace_append hprefix tailTrace_6152067
  have hstable : (prefixWord ++ tailWord_6152067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6152067).length < 2 ^ (prefixWord ++ tailWord_6152067).sum := by decide
  have hdescent : baseEnd_6152067 < baseStart_6152067 := by decide
  rcases family_descends (prefixWord ++ tailWord_6152067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6152073 : List Nat := [1, 2, 1, 1, 5, 1, 2, 2, 1, 2, 5]
def baseStart_6152073 : Nat := 118140960795 + 6152073 * 2 ^ 59
def prefixEnd_6152073 : Nat := 4983230072969 + 3 ^ 40 * 6152073 * 2
def baseEnd_6152073 : Nat := 3158970470547813719794637

theorem tailTrace_6152073 : CollatzResearch.WordTrace tailWord_6152073 prefixEnd_6152073 3158970470547813719794637 := by
  unfold tailWord_6152073
  simp only [CollatzResearch.WordTrace]
  refine ⟨224384536241097686263772873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149589690827398457509181915 224384536241097686263772873)
  ·
    refine ⟨168288402180823264697829655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224384536241097686263772873 168288402180823264697829655)
    ·
      refine ⟨252432603271234897046744483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168288402180823264697829655 252432603271234897046744483)
      ·
        refine ⟨378648904906852345570116725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252432603271234897046744483 378648904906852345570116725)
        ·
          refine ⟨35498334835017407397198443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 378648904906852345570116725 35498334835017407397198443)
          ·
            refine ⟨53247502252526111095797665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35498334835017407397198443 53247502252526111095797665)
            ·
              refine ⟨39935626689394583321848249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53247502252526111095797665 39935626689394583321848249)
              ·
                refine ⟨29951720017045937491386187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39935626689394583321848249 29951720017045937491386187)
                ·
                  refine ⟨44927580025568906237079281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29951720017045937491386187 44927580025568906237079281)
                  ·
                    refine ⟨33695685019176679677809461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44927580025568906237079281 33695685019176679677809461)
                    ·
                      refine ⟨3158970470547813719794637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33695685019176679677809461 3158970470547813719794637)
                      ·
                        rfl

theorem cell23_6152073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 2, 1, 2, 5].length) (baseStart_6152073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6152073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6152073 prefixEnd_6152073 := by exact prefixLift 6152073
  have htrace : WordTrace (prefixWord ++ tailWord_6152073) baseStart_6152073 baseEnd_6152073 := by
    simpa [prefixWord, tailWord_6152073, baseEnd_6152073] using wordTrace_append hprefix tailTrace_6152073
  have hstable : (prefixWord ++ tailWord_6152073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6152073).length < 2 ^ (prefixWord ++ tailWord_6152073).sum := by decide
  have hdescent : baseEnd_6152073 < baseStart_6152073 := by decide
  rcases family_descends (prefixWord ++ tailWord_6152073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6152084 : List Nat := [2, 4, 2, 1, 1, 3, 3, 2, 5]
def baseStart_6152084 : Nat := 118140960795 + 6152084 * 2 ^ 59
def prefixEnd_6152084 : Nat := 4983230072969 + 3 ^ 40 * 6152084 * 2
def baseEnd_6152084 : Nat := 350997346537223686306343

theorem tailTrace_6152084 : CollatzResearch.WordTrace tailWord_6152084 prefixEnd_6152084 350997346537223686306343 := by
  unfold tailWord_6152084
  simp only [CollatzResearch.WordTrace]
  refine ⟨112192468722028917571211653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149589958296038556761615537 112192468722028917571211653)
  ·
    refine ⟨21036087885380422044602185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112192468722028917571211653 21036087885380422044602185)
    ·
      refine ⟨15777065914035316533451639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21036087885380422044602185 15777065914035316533451639)
      ·
        refine ⟨23665598871052974800177459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15777065914035316533451639 23665598871052974800177459)
        ·
          refine ⟨35498398306579462200266189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23665598871052974800177459 35498398306579462200266189)
          ·
            refine ⟨13311899364967298325099821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35498398306579462200266189 13311899364967298325099821)
            ·
              refine ⟨4991962261862736871912433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13311899364967298325099821 4991962261862736871912433)
              ·
                refine ⟨3743971696397052653934325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4991962261862736871912433 3743971696397052653934325)
                ·
                  refine ⟨350997346537223686306343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3743971696397052653934325 350997346537223686306343)
                  ·
                    rfl

theorem cell23_6152084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 3, 2, 5].length) (baseStart_6152084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6152084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6152084 prefixEnd_6152084 := by exact prefixLift 6152084
  have htrace : WordTrace (prefixWord ++ tailWord_6152084) baseStart_6152084 baseEnd_6152084 := by
    simpa [prefixWord, tailWord_6152084, baseEnd_6152084] using wordTrace_append hprefix tailTrace_6152084
  have hstable : (prefixWord ++ tailWord_6152084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6152084).length < 2 ^ (prefixWord ++ tailWord_6152084).sum := by decide
  have hdescent : baseEnd_6152084 < baseStart_6152084 := by decide
  rcases family_descends (prefixWord ++ tailWord_6152084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6152090 : List Nat := [3, 1, 1, 4, 2, 2, 1, 1, 1, 2, 5]
def baseStart_6152090 : Nat := 118140960795 + 6152090 * 2 ^ 59
def prefixEnd_6152090 : Nat := 4983230072969 + 3 ^ 40 * 6152090 * 2
def baseEnd_6152090 : Nat := 3158979199718940153282059

theorem tailTrace_6152090 : CollatzResearch.WordTrace tailWord_6152090 prefixEnd_6152090 3158979199718940153282059 := by
  unfold tailWord_6152090
  simp only [CollatzResearch.WordTrace]
  refine ⟨56096289070509024541785431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149590104188024065444761149 56096289070509024541785431)
  ·
    refine ⟨84144433605763536812678147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56096289070509024541785431 84144433605763536812678147)
    ·
      refine ⟨126216650408645305219017221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84144433605763536812678147 126216650408645305219017221)
      ·
        refine ⟨23665621951620994728565729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 126216650408645305219017221 23665621951620994728565729)
        ·
          refine ⟨17749216463715746046424297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23665621951620994728565729 17749216463715746046424297)
          ·
            refine ⟨13311912347786809534818223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17749216463715746046424297 13311912347786809534818223)
            ·
              refine ⟨19967868521680214302227335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13311912347786809534818223 19967868521680214302227335)
              ·
                refine ⟨29951802782520321453341003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19967868521680214302227335 29951802782520321453341003)
                ·
                  refine ⟨44927704173780482180011505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29951802782520321453341003 44927704173780482180011505)
                  ·
                    refine ⟨33695778130335361635008629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44927704173780482180011505 33695778130335361635008629)
                    ·
                      refine ⟨3158979199718940153282059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33695778130335361635008629 3158979199718940153282059)
                      ·
                        rfl

theorem cell23_6152090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_6152090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6152090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6152090 prefixEnd_6152090 := by exact prefixLift 6152090
  have htrace : WordTrace (prefixWord ++ tailWord_6152090) baseStart_6152090 baseEnd_6152090 := by
    simpa [prefixWord, tailWord_6152090, baseEnd_6152090] using wordTrace_append hprefix tailTrace_6152090
  have hstable : (prefixWord ++ tailWord_6152090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6152090).length < 2 ^ (prefixWord ++ tailWord_6152090).sum := by decide
  have hdescent : baseEnd_6152090 < baseStart_6152090 := by decide
  rcases family_descends (prefixWord ++ tailWord_6152090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6152117 : List Nat := [1, 3, 3, 2, 1, 3, 2, 1, 2, 1, 4]
def baseStart_6152117 : Nat := 118140960795 + 6152117 * 2 ^ 59
def prefixEnd_6152117 : Nat := 4983230072969 + 3 ^ 40 * 6152117 * 2
def baseEnd_6152117 : Nat := 3158993063696611547644435

theorem tailTrace_6152117 : CollatzResearch.WordTrace tailWord_6152117 prefixEnd_6152117 3158993063696611547644435 := by
  unfold tailWord_6152117
  simp only [CollatzResearch.WordTrace]
  refine ⟨224386141052938281778374605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149590760701958854518916403 224386141052938281778374605)
  ·
    refine ⟨84144802894851855666890477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 224386141052938281778374605 84144802894851855666890477)
    ·
      refine ⟨31554301085569445875083929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84144802894851855666890477 31554301085569445875083929)
      ·
        refine ⟨23665725814177084406312947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31554301085569445875083929 23665725814177084406312947)
        ·
          refine ⟨35498588721265626609469421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23665725814177084406312947 35498588721265626609469421)
          ·
            refine ⟨13311970770474609978551033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35498588721265626609469421 13311970770474609978551033)
            ·
              refine ⟨9983978077855957483913275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13311970770474609978551033 9983978077855957483913275)
              ·
                refine ⟨14975967116783936225869913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9983978077855957483913275 14975967116783936225869913)
                ·
                  refine ⟨11231975337587952169402435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14975967116783936225869913 11231975337587952169402435)
                  ·
                    refine ⟨16847963006381928254103653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11231975337587952169402435 16847963006381928254103653)
                    ·
                      refine ⟨3158993063696611547644435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16847963006381928254103653 3158993063696611547644435)
                      ·
                        rfl

theorem cell23_6152117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2, 1, 2, 1, 4].length) (baseStart_6152117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6152117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6152117 prefixEnd_6152117 := by exact prefixLift 6152117
  have htrace : WordTrace (prefixWord ++ tailWord_6152117) baseStart_6152117 baseEnd_6152117 := by
    simpa [prefixWord, tailWord_6152117, baseEnd_6152117] using wordTrace_append hprefix tailTrace_6152117
  have hstable : (prefixWord ++ tailWord_6152117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6152117).length < 2 ^ (prefixWord ++ tailWord_6152117).sum := by decide
  have hdescent : baseEnd_6152117 < baseStart_6152117 := by decide
  rcases family_descends (prefixWord ++ tailWord_6152117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6152127 : List Nat := [1, 1, 2, 2, 2, 1, 4, 5, 1, 4]
def baseStart_6152127 : Nat := 118140960795 + 6152127 * 2 ^ 59
def prefixEnd_6152127 : Nat := 4983230072969 + 3 ^ 40 * 6152127 * 2
def baseEnd_6152127 : Nat := 1052999399501052169506463

theorem tailTrace_6152127 : CollatzResearch.WordTrace tailWord_6152127 prefixEnd_6152127 1052999399501052169506463 := by
  unfold tailWord_6152127
  simp only [CollatzResearch.WordTrace]
  refine ⟨224386505782902053486238635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149591003855268035657492423 224386505782902053486238635)
  ·
    refine ⟨336579758674353080229357953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224386505782902053486238635 336579758674353080229357953)
    ·
      refine ⟨252434819005764810172018465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 336579758674353080229357953 252434819005764810172018465)
      ·
        refine ⟨189326114254323607629013849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 252434819005764810172018465 189326114254323607629013849)
        ·
          refine ⟨141994585690742705721760387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189326114254323607629013849 141994585690742705721760387)
          ·
            refine ⟨212991878536114058582640581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141994585690742705721760387 212991878536114058582640581)
            ·
              refine ⟨39935977225521385984245109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 212991878536114058582640581 39935977225521385984245109)
              ·
                refine ⟨3743997864892629936022979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39935977225521385984245109 3743997864892629936022979)
                ·
                  refine ⟨5615996797338944904034469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3743997864892629936022979 5615996797338944904034469)
                  ·
                    refine ⟨1052999399501052169506463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5615996797338944904034469 1052999399501052169506463)
                    ·
                      rfl

theorem cell23_6152127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 5, 1, 4].length) (baseStart_6152127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6152127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6152127 prefixEnd_6152127 := by exact prefixLift 6152127
  have htrace : WordTrace (prefixWord ++ tailWord_6152127) baseStart_6152127 baseEnd_6152127 := by
    simpa [prefixWord, tailWord_6152127, baseEnd_6152127] using wordTrace_append hprefix tailTrace_6152127
  have hstable : (prefixWord ++ tailWord_6152127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6152127).length < 2 ^ (prefixWord ++ tailWord_6152127).sum := by decide
  have hdescent : baseEnd_6152127 < baseStart_6152127 := by decide
  rcases family_descends (prefixWord ++ tailWord_6152127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6152140 : List Nat := [2, 2, 1, 4, 1, 2, 1, 4, 6]
def baseStart_6152140 : Nat := 118140960795 + 6152140 * 2 ^ 59
def prefixEnd_6152140 : Nat := 4983230072969 + 3 ^ 40 * 6152140 * 2
def baseEnd_6152140 : Nat := 351000541527962773072981

theorem tailTrace_6152140 : CollatzResearch.WordTrace tailWord_6152140 prefixEnd_6152140 351000541527962773072981 := by
  unfold tailWord_6152140
  simp only [CollatzResearch.WordTrace]
  refine ⟨112193489965927478353230937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149591319954569971137641249 112193489965927478353230937)
  ·
    refine ⟨84145117474445608764923203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112193489965927478353230937 84145117474445608764923203)
    ·
      refine ⟨126217676211668413147384805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84145117474445608764923203 126217676211668413147384805)
      ·
        refine ⟨23665814289687827465134651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 126217676211668413147384805 23665814289687827465134651)
        ·
          refine ⟨35498721434531741197701977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23665814289687827465134651 35498721434531741197701977)
          ·
            refine ⟨26624041075898805898276483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35498721434531741197701977 26624041075898805898276483)
            ·
              refine ⟨39936061613848208847414725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26624041075898805898276483 39936061613848208847414725)
              ·
                refine ⟨7488011552596539158890261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39936061613848208847414725 7488011552596539158890261)
                ·
                  refine ⟨351000541527962773072981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7488011552596539158890261 351000541527962773072981)
                  ·
                    rfl

theorem cell23_6152140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 4, 6].length) (baseStart_6152140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6152140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6152140 prefixEnd_6152140 := by exact prefixLift 6152140
  have htrace : WordTrace (prefixWord ++ tailWord_6152140) baseStart_6152140 baseEnd_6152140 := by
    simpa [prefixWord, tailWord_6152140, baseEnd_6152140] using wordTrace_append hprefix tailTrace_6152140
  have hstable : (prefixWord ++ tailWord_6152140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6152140).length < 2 ^ (prefixWord ++ tailWord_6152140).sum := by decide
  have hdescent : baseEnd_6152140 < baseStart_6152140 := by decide
  rcases family_descends (prefixWord ++ tailWord_6152140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6152143 : List Nat := [1, 1, 2, 1, 1, 5, 2, 1, 1, 2, 6]
def baseStart_6152143 : Nat := 118140960795 + 6152143 * 2 ^ 59
def prefixEnd_6152143 : Nat := 4983230072969 + 3 ^ 40 * 6152143 * 2
def baseEnd_6152143 : Nat := 3159006414193628445919315

theorem tailTrace_6152143 : CollatzResearch.WordTrace tailWord_6152143 prefixEnd_6152143 3159006414193628445919315 := by
  unfold tailWord_6152143
  simp only [CollatzResearch.WordTrace]
  refine ⟨224387089350844088218821083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149591392900562725479214055 224387089350844088218821083)
  ·
    refine ⟨336580634026266132328231625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224387089350844088218821083 336580634026266132328231625)
    ·
      refine ⟨252435475519699599246173719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 336580634026266132328231625 252435475519699599246173719)
      ·
        refine ⟨378653213279549398869260579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252435475519699599246173719 378653213279549398869260579)
        ·
          refine ⟨567979819919324098303890869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 378653213279549398869260579 567979819919324098303890869)
          ·
            refine ⟨53248108117436634215989769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 567979819919324098303890869 53248108117436634215989769)
            ·
              refine ⟨39936081088077475661992327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53248108117436634215989769 39936081088077475661992327)
              ·
                refine ⟨59904121632116213492988491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39936081088077475661992327 59904121632116213492988491)
                ·
                  refine ⟨89856182448174320239482737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59904121632116213492988491 89856182448174320239482737)
                  ·
                    refine ⟨67392136836130740179612053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 89856182448174320239482737 67392136836130740179612053)
                    ·
                      refine ⟨3159006414193628445919315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67392136836130740179612053 3159006414193628445919315)
                      ·
                        rfl

theorem cell23_6152143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 1, 1, 2, 6].length) (baseStart_6152143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6152143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6152143 prefixEnd_6152143 := by exact prefixLift 6152143
  have htrace : WordTrace (prefixWord ++ tailWord_6152143) baseStart_6152143 baseEnd_6152143 := by
    simpa [prefixWord, tailWord_6152143, baseEnd_6152143] using wordTrace_append hprefix tailTrace_6152143
  have hstable : (prefixWord ++ tailWord_6152143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6152143).length < 2 ^ (prefixWord ++ tailWord_6152143).sum := by decide
  have hdescent : baseEnd_6152143 < baseStart_6152143 := by decide
  rcases family_descends (prefixWord ++ tailWord_6152143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6152144 : List Nat := [2, 1, 1, 1, 1, 2, 8, 2, 1, 4]
def baseStart_6152144 : Nat := 118140960795 + 6152144 * 2 ^ 59
def prefixEnd_6152144 : Nat := 4983230072969 + 3 ^ 40 * 6152144 * 2
def baseEnd_6152144 : Nat := 1053002309224760980668937

theorem tailTrace_6152144 : CollatzResearch.WordTrace tailWord_6152144 prefixEnd_6152144 1053002309224760980668937 := by
  unfold tailWord_6152144
  simp only [CollatzResearch.WordTrace]
  refine ⟨112193562911920232694803743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149591417215893643593071657 112193562911920232694803743)
  ·
    refine ⟨168290344367880349042205615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112193562911920232694803743 168290344367880349042205615)
    ·
      refine ⟨252435516551820523563308423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168290344367880349042205615 252435516551820523563308423)
      ·
        refine ⟨378653274827730785344962635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252435516551820523563308423 378653274827730785344962635)
        ·
          refine ⟨567979912241596178017443953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 378653274827730785344962635 567979912241596178017443953)
          ·
            refine ⟨425984934181197133513082965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 567979912241596178017443953 425984934181197133513082965)
            ·
              refine ⟨4992010947435903908356441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 425984934181197133513082965 4992010947435903908356441)
              ·
                refine ⟨3744008210576927931267331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4992010947435903908356441 3744008210576927931267331)
                ·
                  refine ⟨5616012315865391896900997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3744008210576927931267331 5616012315865391896900997)
                  ·
                    refine ⟨1053002309224760980668937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5616012315865391896900997 1053002309224760980668937)
                    ·
                      rfl

theorem cell23_6152144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 8, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 8, 2, 1, 4].length) (baseStart_6152144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6152144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6152144 prefixEnd_6152144 := by exact prefixLift 6152144
  have htrace : WordTrace (prefixWord ++ tailWord_6152144) baseStart_6152144 baseEnd_6152144 := by
    simpa [prefixWord, tailWord_6152144, baseEnd_6152144] using wordTrace_append hprefix tailTrace_6152144
  have hstable : (prefixWord ++ tailWord_6152144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6152144).length < 2 ^ (prefixWord ++ tailWord_6152144).sum := by decide
  have hdescent : baseEnd_6152144 < baseStart_6152144 := by decide
  rcases family_descends (prefixWord ++ tailWord_6152144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6152170 : List Nat := [3, 1, 3, 1, 2, 1, 1, 3, 3, 5]
def baseStart_6152170 : Nat := 118140960795 + 6152170 * 2 ^ 59
def prefixEnd_6152170 : Nat := 4983230072969 + 3 ^ 40 * 6152170 * 2
def baseEnd_6152170 : Nat := 1053006759390433280093897

theorem tailTrace_6152170 : CollatzResearch.WordTrace tailWord_6152170 prefixEnd_6152170 1053006759390433280093897 := by
  unfold tailWord_6152170
  simp only [CollatzResearch.WordTrace]
  refine ⟨56097018530436567957513491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149592049414497514553369309 56097018530436567957513491)
  ·
    refine ⟨84145527795654851936270237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56097018530436567957513491 84145527795654851936270237)
    ·
      refine ⟨31554572923370569476101339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84145527795654851936270237 31554572923370569476101339)
      ·
        refine ⟨47331859385055854214152009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31554572923370569476101339 47331859385055854214152009)
        ·
          refine ⟨35498894538791890660614007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47331859385055854214152009 35498894538791890660614007)
          ·
            refine ⟨53248341808187835990921011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35498894538791890660614007 53248341808187835990921011)
            ·
              refine ⟨79872512712281753986381517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53248341808187835990921011 79872512712281753986381517)
              ·
                refine ⟨29952192267105657744893069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79872512712281753986381517 29952192267105657744893069)
                ·
                  refine ⟨11232072100164621654334901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29952192267105657744893069 11232072100164621654334901)
                  ·
                    refine ⟨1053006759390433280093897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11232072100164621654334901 1053006759390433280093897)
                    ·
                      rfl

theorem cell23_6152170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 3, 3, 5].length) (baseStart_6152170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6152170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6152170 prefixEnd_6152170 := by exact prefixLift 6152170
  have htrace : WordTrace (prefixWord ++ tailWord_6152170) baseStart_6152170 baseEnd_6152170 := by
    simpa [prefixWord, tailWord_6152170, baseEnd_6152170] using wordTrace_append hprefix tailTrace_6152170
  have hstable : (prefixWord ++ tailWord_6152170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6152170).length < 2 ^ (prefixWord ++ tailWord_6152170).sum := by decide
  have hdescent : baseEnd_6152170 < baseStart_6152170 := by decide
  rcases family_descends (prefixWord ++ tailWord_6152170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6152184 : List Nat := [2, 1, 2, 1, 1, 3, 3, 5, 1, 1, 3]
def baseStart_6152184 : Nat := 118140960795 + 6152184 * 2 ^ 59
def prefixEnd_6152184 : Nat := 4983230072969 + 3 ^ 40 * 6152184 * 2
def baseEnd_6152184 : Nat := 3159027466900462785506627

theorem tailTrace_6152184 : CollatzResearch.WordTrace tailWord_6152184 prefixEnd_6152184 3159027466900462785506627 := by
  unfold tailWord_6152184
  simp only [CollatzResearch.WordTrace]
  refine ⟨112194292371847776110531803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149592389829130368147375737 112194292371847776110531803)
  ·
    refine ⟨168291438557771664165797705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112194292371847776110531803 168291438557771664165797705)
    ·
      refine ⟨126218578918328748124348279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168291438557771664165797705 126218578918328748124348279)
      ·
        refine ⟨189327868377493122186522419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126218578918328748124348279 189327868377493122186522419)
        ·
          refine ⟨283991802566239683279783629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189327868377493122186522419 283991802566239683279783629)
          ·
            refine ⟨106496925962339881229918861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 283991802566239683279783629 106496925962339881229918861)
            ·
              refine ⟨39936347235877455461219573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106496925962339881229918861 39936347235877455461219573)
              ·
                refine ⟨3744032553363511449489335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39936347235877455461219573 3744032553363511449489335)
                ·
                  refine ⟨5616048830045267174234003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3744032553363511449489335 5616048830045267174234003)
                  ·
                    refine ⟨8424073245067900761351005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5616048830045267174234003 8424073245067900761351005)
                    ·
                      refine ⟨3159027466900462785506627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8424073245067900761351005 3159027466900462785506627)
                      ·
                        rfl

theorem cell23_6152184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 5, 1, 1, 3].length) (baseStart_6152184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6152184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6152184 prefixEnd_6152184 := by exact prefixLift 6152184
  have htrace : WordTrace (prefixWord ++ tailWord_6152184) baseStart_6152184 baseEnd_6152184 := by
    simpa [prefixWord, tailWord_6152184, baseEnd_6152184] using wordTrace_append hprefix tailTrace_6152184
  have hstable : (prefixWord ++ tailWord_6152184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6152184).length < 2 ^ (prefixWord ++ tailWord_6152184).sum := by decide
  have hdescent : baseEnd_6152184 < baseStart_6152184 := by decide
  rcases family_descends (prefixWord ++ tailWord_6152184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6152187 : List Nat := [1, 1, 1, 1, 1, 3, 8, 1, 1, 5]
def baseStart_6152187 : Nat := 118140960795 + 6152187 * 2 ^ 59
def prefixEnd_6152187 : Nat := 4983230072969 + 3 ^ 40 * 6152187 * 2
def baseEnd_6152187 : Nat := 1053009669114142091256371

theorem tailTrace_6152187 : CollatzResearch.WordTrace tailWord_6152187 prefixEnd_6152187 1053009669114142091256371 := by
  unfold tailWord_6152187
  simp only [CollatzResearch.WordTrace]
  refine ⟨224388694162684683733422815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149592462775123122488948543 224388694162684683733422815)
  ·
    refine ⟨336583041244027025600134223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224388694162684683733422815 336583041244027025600134223)
    ·
      refine ⟨504874561866040538400201335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 336583041244027025600134223 504874561866040538400201335)
      ·
        refine ⟨757311842799060807600302003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 504874561866040538400201335 757311842799060807600302003)
        ·
          refine ⟨1135967764198591211400453005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 757311842799060807600302003 1135967764198591211400453005)
          ·
            refine ⟨425987911574471704275169877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1135967764198591211400453005 425987911574471704275169877)
            ·
              refine ⟨4992045838763340284474647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 425987911574471704275169877 4992045838763340284474647)
              ·
                refine ⟨7488068758145010426711971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4992045838763340284474647 7488068758145010426711971)
                ·
                  refine ⟨11232103137217515640067957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7488068758145010426711971 11232103137217515640067957)
                  ·
                    refine ⟨1053009669114142091256371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11232103137217515640067957 1053009669114142091256371)
                    ·
                      rfl

theorem cell23_6152187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 8, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 8, 1, 1, 5].length) (baseStart_6152187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6152187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6152187 prefixEnd_6152187 := by exact prefixLift 6152187
  have htrace : WordTrace (prefixWord ++ tailWord_6152187) baseStart_6152187 baseEnd_6152187 := by
    simpa [prefixWord, tailWord_6152187, baseEnd_6152187] using wordTrace_append hprefix tailTrace_6152187
  have hstable : (prefixWord ++ tailWord_6152187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6152187).length < 2 ^ (prefixWord ++ tailWord_6152187).sum := by decide
  have hdescent : baseEnd_6152187 < baseStart_6152187 := by decide
  rcases family_descends (prefixWord ++ tailWord_6152187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6152267 : List Nat := [1, 1, 1, 1, 3, 1, 2, 3, 5, 3, 2]
def baseStart_6152267 : Nat := 118140960795 + 6152267 * 2 ^ 59
def prefixEnd_6152267 : Nat := 4983230072969 + 3 ^ 40 * 6152267 * 2
def baseEnd_6152267 : Nat := 3159070085794785960768745

theorem tailTrace_6152267 : CollatzResearch.WordTrace tailWord_6152267 prefixEnd_6152267 3159070085794785960768745 := by
  unfold tailWord_6152267
  simp only [CollatzResearch.WordTrace]
  refine ⟨224391612002394857396335055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149594408001596571597556703 224391612002394857396335055)
  ·
    refine ⟨336587418003592286094502583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224391612002394857396335055 336587418003592286094502583)
    ·
      refine ⟨504881127005388429141753875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 336587418003592286094502583 504881127005388429141753875)
      ·
        refine ⟨757321690508082643712630813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 504881127005388429141753875 757321690508082643712630813)
        ·
          refine ⟨283995633940530991392236555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 757321690508082643712630813 283995633940530991392236555)
          ·
            refine ⟨425993450910796487088354833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 283995633940530991392236555 425993450910796487088354833)
            ·
              refine ⟨319495088183097365316266125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 425993450910796487088354833 319495088183097365316266125)
              ·
                refine ⟨119810658068661511993599797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 319495088183097365316266125 119810658068661511993599797)
                ·
                  refine ⟨11232249193937016749399981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 119810658068661511993599797 11232249193937016749399981)
                  ·
                    refine ⟨4212093447726381281024993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11232249193937016749399981 4212093447726381281024993)
                    ·
                      refine ⟨3159070085794785960768745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4212093447726381281024993 3159070085794785960768745)
                      ·
                        rfl

theorem cell23_6152267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 5, 3, 2].length) (baseStart_6152267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6152267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6152267 prefixEnd_6152267 := by exact prefixLift 6152267
  have htrace : WordTrace (prefixWord ++ tailWord_6152267) baseStart_6152267 baseEnd_6152267 := by
    simpa [prefixWord, tailWord_6152267, baseEnd_6152267] using wordTrace_append hprefix tailTrace_6152267
  have hstable : (prefixWord ++ tailWord_6152267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6152267).length < 2 ^ (prefixWord ++ tailWord_6152267).sum := by decide
  have hdescent : baseEnd_6152267 < baseStart_6152267 := by decide
  rcases family_descends (prefixWord ++ tailWord_6152267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6152278 : List Nat := [5, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3]
def baseStart_6152278 : Nat := 118140960795 + 6152278 * 2 ^ 59
def prefixEnd_6152278 : Nat := 4983230072969 + 3 ^ 40 * 6152278 * 2
def baseEnd_6152278 : Nat := 3159075734081985417731195

theorem tailTrace_6152278 : CollatzResearch.WordTrace tailWord_6152278 prefixEnd_6152278 3159075734081985417731195 := by
  unfold tailWord_6152278
  simp only [CollatzResearch.WordTrace]
  refine ⟨14024500825334687892186593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 149594675470236670849990325 14024500825334687892186593)
  ·
    refine ⟨10518375619001015919139945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14024500825334687892186593 10518375619001015919139945)
    ·
      refine ⟨7888781714250761939354959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10518375619001015919139945 7888781714250761939354959)
      ·
        refine ⟨11833172571376142909032439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7888781714250761939354959 11833172571376142909032439)
        ·
          refine ⟨17749758857064214363548659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11833172571376142909032439 17749758857064214363548659)
          ·
            refine ⟨26624638285596321545322989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17749758857064214363548659 26624638285596321545322989)
            ·
              refine ⟨9984239357098620579496121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26624638285596321545322989 9984239357098620579496121)
              ·
                refine ⟨7488179517823965434622091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9984239357098620579496121 7488179517823965434622091)
                ·
                  refine ⟨11232269276735948151933137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7488179517823965434622091 11232269276735948151933137)
                  ·
                    refine ⟨8424201957551961113949853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11232269276735948151933137 8424201957551961113949853)
                    ·
                      refine ⟨3159075734081985417731195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8424201957551961113949853 3159075734081985417731195)
                      ·
                        rfl

theorem cell23_6152278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_6152278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6152278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6152278 prefixEnd_6152278 := by exact prefixLift 6152278
  have htrace : WordTrace (prefixWord ++ tailWord_6152278) baseStart_6152278 baseEnd_6152278 := by
    simpa [prefixWord, tailWord_6152278, baseEnd_6152278] using wordTrace_append hprefix tailTrace_6152278
  have hstable : (prefixWord ++ tailWord_6152278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6152278).length < 2 ^ (prefixWord ++ tailWord_6152278).sum := by decide
  have hdescent : baseEnd_6152278 < baseStart_6152278 := by decide
  rcases family_descends (prefixWord ++ tailWord_6152278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6152317 : List Nat := [1, 4, 1, 1, 3, 2, 1, 1, 2, 4, 3]
def baseStart_6152317 : Nat := 118140960795 + 6152317 * 2 ^ 59
def prefixEnd_6152317 : Nat := 4983230072969 + 3 ^ 40 * 6152317 * 2
def baseEnd_6152317 : Nat := 3159095759827510765143515

theorem tailTrace_6152317 : CollatzResearch.WordTrace tailWord_6152317 prefixEnd_6152317 3159095759827510765143515 := by
  unfold tailWord_6152317
  simp only [CollatzResearch.WordTrace]
  refine ⟨224393435652213715935655205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149595623768142477290436803 224393435652213715935655205)
  ·
    refine ⟨42073769184790071737935351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 224393435652213715935655205 42073769184790071737935351)
    ·
      refine ⟨63110653777185107606903027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42073769184790071737935351 63110653777185107606903027)
      ·
        refine ⟨94665980665777661410354541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63110653777185107606903027 94665980665777661410354541)
        ·
          refine ⟨35499742749666623028882953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94665980665777661410354541 35499742749666623028882953)
          ·
            refine ⟨26624807062249967271662215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35499742749666623028882953 26624807062249967271662215)
            ·
              refine ⟨39937210593374950907493323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26624807062249967271662215 39937210593374950907493323)
              ·
                refine ⟨59905815890062426361239985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39937210593374950907493323 59905815890062426361239985)
                ·
                  refine ⟨44929361917546819770929989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59905815890062426361239985 44929361917546819770929989)
                  ·
                    refine ⟨8424255359540028707049373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44929361917546819770929989 8424255359540028707049373)
                    ·
                      refine ⟨3159095759827510765143515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8424255359540028707049373 3159095759827510765143515)
                      ·
                        rfl

theorem cell23_6152317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 1, 2, 4, 3].length) (baseStart_6152317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6152317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6152317 prefixEnd_6152317 := by exact prefixLift 6152317
  have htrace : WordTrace (prefixWord ++ tailWord_6152317) baseStart_6152317 baseEnd_6152317 := by
    simpa [prefixWord, tailWord_6152317, baseEnd_6152317] using wordTrace_append hprefix tailTrace_6152317
  have hstable : (prefixWord ++ tailWord_6152317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6152317).length < 2 ^ (prefixWord ++ tailWord_6152317).sum := by decide
  have hdescent : baseEnd_6152317 < baseStart_6152317 := by decide
  rcases family_descends (prefixWord ++ tailWord_6152317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6152320 : List Nat := [2, 1, 1, 2, 1, 3, 1, 5, 7]
def baseStart_6152320 : Nat := 118140960795 + 6152320 * 2 ^ 59
def prefixEnd_6152320 : Nat := 4983230072969 + 3 ^ 40 * 6152320 * 2
def baseEnd_6152320 : Nat := 351010811141052694822889

theorem tailTrace_6152320 : CollatzResearch.WordTrace tailWord_6152320 prefixEnd_6152320 351010811141052694822889 := by
  unfold tailWord_6152320
  simp only [CollatzResearch.WordTrace]
  refine ⟨112196772535601423724007207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149595696714135231632009609 112196772535601423724007207)
  ·
    refine ⟨168295158803402135586010811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112196772535601423724007207 168295158803402135586010811)
    ·
      refine ⟨252442738205103203379016217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168295158803402135586010811 252442738205103203379016217)
      ·
        refine ⟨189332053653827402534262163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 252442738205103203379016217 189332053653827402534262163)
        ·
          refine ⟨283998080480741103801393245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189332053653827402534262163 283998080480741103801393245)
          ·
            refine ⟨106499280180277913925522467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 283998080480741103801393245 106499280180277913925522467)
            ·
              refine ⟨159748920270416870888283701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106499280180277913925522467 159748920270416870888283701)
              ·
                refine ⟨14976461275351581645776597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 159748920270416870888283701 14976461275351581645776597)
                ·
                  refine ⟨351010811141052694822889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14976461275351581645776597 351010811141052694822889)
                  ·
                    rfl

theorem cell23_6152320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 5, 7].length) (baseStart_6152320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6152320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6152320 prefixEnd_6152320 := by exact prefixLift 6152320
  have htrace : WordTrace (prefixWord ++ tailWord_6152320) baseStart_6152320 baseEnd_6152320 := by
    simpa [prefixWord, tailWord_6152320, baseEnd_6152320] using wordTrace_append hprefix tailTrace_6152320
  have hstable : (prefixWord ++ tailWord_6152320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6152320).length < 2 ^ (prefixWord ++ tailWord_6152320).sum := by decide
  have hdescent : baseEnd_6152320 < baseStart_6152320 := by decide
  rcases family_descends (prefixWord ++ tailWord_6152320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6152365 : List Nat := [1, 5, 2, 1, 2, 3, 1, 2, 2, 2, 2]
def baseStart_6152365 : Nat := 118140960795 + 6152365 * 2 ^ 59
def prefixEnd_6152365 : Nat := 4983230072969 + 3 ^ 40 * 6152365 * 2
def baseEnd_6152365 : Nat := 3159120406898926577343295

theorem tailTrace_6152365 : CollatzResearch.WordTrace tailWord_6152365 prefixEnd_6152365 3159120406898926577343295 := by
  unfold tailWord_6152365
  simp only [CollatzResearch.WordTrace]
  refine ⟨224395186356039820133402549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149596790904026546755601699 224395186356039820133402549)
  ·
    refine ⟨21037048720878733137506489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 224395186356039820133402549 21037048720878733137506489)
    ·
      refine ⟨15777786540659049853129867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21037048720878733137506489 15777786540659049853129867)
      ·
        refine ⟨23666679810988574779694801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15777786540659049853129867 23666679810988574779694801)
        ·
          refine ⟨17750009858241431084771101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23666679810988574779694801 17750009858241431084771101)
          ·
            refine ⟨6656253696840536656789163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17750009858241431084771101 6656253696840536656789163)
            ·
              refine ⟨9984380545260804985183745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6656253696840536656789163 9984380545260804985183745)
              ·
                refine ⟨7488285408945603738887809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9984380545260804985183745 7488285408945603738887809)
                ·
                  refine ⟨5616214056709202804165857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7488285408945603738887809 5616214056709202804165857)
                  ·
                    refine ⟨4212160542531902103124393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5616214056709202804165857 4212160542531902103124393)
                    ·
                      refine ⟨3159120406898926577343295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4212160542531902103124393 3159120406898926577343295)
                      ·
                        rfl

theorem cell23_6152365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 1, 2, 2, 2, 2].length) (baseStart_6152365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6152365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6152365 prefixEnd_6152365 := by exact prefixLift 6152365
  have htrace : WordTrace (prefixWord ++ tailWord_6152365) baseStart_6152365 baseEnd_6152365 := by
    simpa [prefixWord, tailWord_6152365, baseEnd_6152365] using wordTrace_append hprefix tailTrace_6152365
  have hstable : (prefixWord ++ tailWord_6152365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6152365).length < 2 ^ (prefixWord ++ tailWord_6152365).sum := by decide
  have hdescent : baseEnd_6152365 < baseStart_6152365 := by decide
  rcases family_descends (prefixWord ++ tailWord_6152365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6152424 : List Nat := [2, 1, 4, 1, 2, 2, 1, 1, 4, 2, 3]
def baseStart_6152424 : Nat := 118140960795 + 6152424 * 2 ^ 59
def prefixEnd_6152424 : Nat := 4983230072969 + 3 ^ 40 * 6152424 * 2
def baseEnd_6152424 : Nat := 3159150702257541846505523

theorem tailTrace_6152424 : CollatzResearch.WordTrace tailWord_6152424 prefixEnd_6152424 3159150702257541846505523 := by
  unfold tailWord_6152424
  simp only [CollatzResearch.WordTrace]
  refine ⟨112198669131413036604900163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149598225508550715473200217 112198669131413036604900163)
  ·
    refine ⟨168298003697119554907350245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112198669131413036604900163 168298003697119554907350245)
    ·
      refine ⟨31555875693209916545128171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 168298003697119554907350245 31555875693209916545128171)
      ·
        refine ⟨47333813539814874817692257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31555875693209916545128171 47333813539814874817692257)
        ·
          refine ⟨35500360154861156113269193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47333813539814874817692257 35500360154861156113269193)
          ·
            refine ⟨26625270116145867084951895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35500360154861156113269193 26625270116145867084951895)
            ·
              refine ⟨39937905174218800627427843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26625270116145867084951895 39937905174218800627427843)
              ·
                refine ⟨59906857761328200941141765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39937905174218800627427843 59906857761328200941141765)
                ·
                  refine ⟨11232535830249037676464081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59906857761328200941141765 11232535830249037676464081)
                  ·
                    refine ⟨8424401872686778257348061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11232535830249037676464081 8424401872686778257348061)
                    ·
                      refine ⟨3159150702257541846505523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8424401872686778257348061 3159150702257541846505523)
                      ·
                        rfl

theorem cell23_6152424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 1, 4, 2, 3].length) (baseStart_6152424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6152424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6152424 prefixEnd_6152424 := by exact prefixLift 6152424
  have htrace : WordTrace (prefixWord ++ tailWord_6152424) baseStart_6152424 baseEnd_6152424 := by
    simpa [prefixWord, tailWord_6152424, baseEnd_6152424] using wordTrace_append hprefix tailTrace_6152424
  have hstable : (prefixWord ++ tailWord_6152424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6152424).length < 2 ^ (prefixWord ++ tailWord_6152424).sum := by decide
  have hdescent : baseEnd_6152424 < baseStart_6152424 := by decide
  rcases family_descends (prefixWord ++ tailWord_6152424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6152427 : List Nat := [1, 1, 1, 1, 2, 5, 2, 4, 6]
def baseStart_6152427 : Nat := 118140960795 + 6152427 * 2 ^ 59
def prefixEnd_6152427 : Nat := 4983230072969 + 3 ^ 40 * 6152427 * 2
def baseEnd_6152427 : Nat := 351016915855500592752001

theorem tailTrace_6152427 : CollatzResearch.WordTrace tailWord_6152427 prefixEnd_6152427 351016915855500592752001 := by
  unfold tailWord_6152427
  simp only [CollatzResearch.WordTrace]
  refine ⟨224397447681815204722159535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149598298454543469814773023 224397447681815204722159535)
  ·
    refine ⟨336596171522722807083239303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224397447681815204722159535 336596171522722807083239303)
    ·
      refine ⟨504894257284084210624858955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 336596171522722807083239303 504894257284084210624858955)
      ·
        refine ⟨757341385926126315937288433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 504894257284084210624858955 757341385926126315937288433)
        ·
          refine ⟨568006039444594736952966325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 757341385926126315937288433 568006039444594736952966325)
          ·
            refine ⟨53250566197930756589340593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 568006039444594736952966325 53250566197930756589340593)
            ·
              refine ⟨39937924648448067442005445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53250566197930756589340593 39937924648448067442005445)
              ·
                refine ⟨7488360871584012645376021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39937924648448067442005445 7488360871584012645376021)
                ·
                  refine ⟨351016915855500592752001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7488360871584012645376021 351016915855500592752001)
                  ·
                    rfl

theorem cell23_6152427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 4, 6].length) (baseStart_6152427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6152427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6152427 prefixEnd_6152427 := by exact prefixLift 6152427
  have htrace : WordTrace (prefixWord ++ tailWord_6152427) baseStart_6152427 baseEnd_6152427 := by
    simpa [prefixWord, tailWord_6152427, baseEnd_6152427] using wordTrace_append hprefix tailTrace_6152427
  have hstable : (prefixWord ++ tailWord_6152427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6152427).length < 2 ^ (prefixWord ++ tailWord_6152427).sum := by decide
  have hdescent : baseEnd_6152427 < baseStart_6152427 := by decide
  rcases family_descends (prefixWord ++ tailWord_6152427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6152431 : List Nat := [1, 1, 2, 1, 6, 3, 1, 1, 3, 4]
def baseStart_6152431 : Nat := 118140960795 + 6152431 * 2 ^ 59
def prefixEnd_6152431 : Nat := 4983230072969 + 3 ^ 40 * 6152431 * 2
def baseEnd_6152431 : Nat := 1053051432207374439705997

theorem tailTrace_6152431 : CollatzResearch.WordTrace tailWord_6152431 prefixEnd_6152431 1053051432207374439705997 := by
  unfold tailWord_6152431
  simp only [CollatzResearch.WordTrace]
  refine ⟨224397593573800713405305147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149598395715867142270203431 224397593573800713405305147)
  ·
    refine ⟨336596390360701070107957721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224397593573800713405305147 336596390360701070107957721)
    ·
      refine ⟨252447292770525802580968291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 336596390360701070107957721 252447292770525802580968291)
      ·
        refine ⟨378670939155788703871452437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252447292770525802580968291 378670939155788703871452437)
        ·
          refine ⟨17750200272927595493974333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 378670939155788703871452437 17750200272927595493974333)
          ·
            refine ⟨6656325102347848310240375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17750200272927595493974333 6656325102347848310240375)
            ·
              refine ⟨9984487653521772465360563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6656325102347848310240375 9984487653521772465360563)
              ·
                refine ⟨14976731480282658698040845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9984487653521772465360563 14976731480282658698040845)
                ·
                  refine ⟨5616274305105997011765317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14976731480282658698040845 5616274305105997011765317)
                  ·
                    refine ⟨1053051432207374439705997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5616274305105997011765317 1053051432207374439705997)
                    ·
                      rfl

theorem cell23_6152431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 1, 1, 3, 4].length) (baseStart_6152431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6152431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6152431 prefixEnd_6152431 := by exact prefixLift 6152431
  have htrace : WordTrace (prefixWord ++ tailWord_6152431) baseStart_6152431 baseEnd_6152431 := by
    simpa [prefixWord, tailWord_6152431, baseEnd_6152431] using wordTrace_append hprefix tailTrace_6152431
  have hstable : (prefixWord ++ tailWord_6152431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6152431).length < 2 ^ (prefixWord ++ tailWord_6152431).sum := by decide
  have hdescent : baseEnd_6152431 < baseStart_6152431 := by decide
  rcases family_descends (prefixWord ++ tailWord_6152431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6152444 : List Nat := [2, 2, 2, 1, 4, 2, 1, 3, 6]
def baseStart_6152444 : Nat := 118140960795 + 6152444 * 2 ^ 59
def prefixEnd_6152444 : Nat := 4983230072969 + 3 ^ 40 * 6152444 * 2
def baseEnd_6152444 : Nat := 351017885763403529806159

theorem tailTrace_6152444 : CollatzResearch.WordTrace tailWord_6152444 prefixEnd_6152444 351017885763403529806159 := by
  unfold tailWord_6152444
  simp only [CollatzResearch.WordTrace]
  refine ⟨112199033861376808312764193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149598711815169077750352257 112199033861376808312764193)
  ·
    refine ⟨84149275396032606234573145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112199033861376808312764193 84149275396032606234573145)
    ·
      refine ⟨63111956547024454675929859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84149275396032606234573145 63111956547024454675929859)
      ·
        refine ⟨94667934820536682013894789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63111956547024454675929859 94667934820536682013894789)
        ·
          refine ⟨17750237778850627877605273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94667934820536682013894789 17750237778850627877605273)
          ·
            refine ⟨13312678334137970908203955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17750237778850627877605273 13312678334137970908203955)
            ·
              refine ⟨19969017501206956362305933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13312678334137970908203955 19969017501206956362305933)
              ·
                refine ⟨7488381562952608635864725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19969017501206956362305933 7488381562952608635864725)
                ·
                  refine ⟨351017885763403529806159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7488381562952608635864725 351017885763403529806159)
                  ·
                    rfl

theorem cell23_6152444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 3, 6].length) (baseStart_6152444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6152444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6152444 prefixEnd_6152444 := by exact prefixLift 6152444
  have htrace : WordTrace (prefixWord ++ tailWord_6152444) baseStart_6152444 baseEnd_6152444 := by
    simpa [prefixWord, tailWord_6152444, baseEnd_6152444] using wordTrace_append hprefix tailTrace_6152444
  have hstable : (prefixWord ++ tailWord_6152444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6152444).length < 2 ^ (prefixWord ++ tailWord_6152444).sum := by decide
  have hdescent : baseEnd_6152444 < baseStart_6152444 := by decide
  rcases family_descends (prefixWord ++ tailWord_6152444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6152478 : List Nat := [4, 3, 2, 1, 1, 2, 2, 2, 6]
def baseStart_6152478 : Nat := 118140960795 + 6152478 * 2 ^ 59
def prefixEnd_6152478 : Nat := 4983230072969 + 3 ^ 40 * 6152478 * 2
def baseEnd_6152478 : Nat := 351019825579209403914475

theorem tailTrace_6152478 : CollatzResearch.WordTrace tailWord_6152478 prefixEnd_6152478 351019825579209403914475 := by
  unfold tailWord_6152478
  simp only [CollatzResearch.WordTrace]
  refine ⟨28049913475578805054033261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149599538536420293621510725 28049913475578805054033261)
  ·
    refine ⟨10518717553342051895262473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28049913475578805054033261 10518717553342051895262473)
    ·
      refine ⟨7889038165006538921446855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10518717553342051895262473 7889038165006538921446855)
      ·
        refine ⟨11833557247509808382170283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7889038165006538921446855 11833557247509808382170283)
        ·
          refine ⟨17750335871264712573255425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11833557247509808382170283 17750335871264712573255425)
          ·
            refine ⟨13312751903448534429941569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17750335871264712573255425 13312751903448534429941569)
            ·
              refine ⟨9984563927586400822456177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13312751903448534429941569 9984563927586400822456177)
              ·
                refine ⟨7488422945689800616842133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9984563927586400822456177 7488422945689800616842133)
                ·
                  refine ⟨351019825579209403914475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7488422945689800616842133 351019825579209403914475)
                  ·
                    rfl

theorem cell23_6152478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 2, 2, 6].length) (baseStart_6152478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6152478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6152478 prefixEnd_6152478 := by exact prefixLift 6152478
  have htrace : WordTrace (prefixWord ++ tailWord_6152478) baseStart_6152478 baseEnd_6152478 := by
    simpa [prefixWord, tailWord_6152478, baseEnd_6152478] using wordTrace_append hprefix tailTrace_6152478
  have hstable : (prefixWord ++ tailWord_6152478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6152478).length < 2 ^ (prefixWord ++ tailWord_6152478).sum := by decide
  have hdescent : baseEnd_6152478 < baseStart_6152478 := by decide
  rcases family_descends (prefixWord ++ tailWord_6152478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6152481 : List Nat := [1, 2, 3, 2, 1, 1, 4, 2, 2, 3, 2]
def baseStart_6152481 : Nat := 118140960795 + 6152481 * 2 ^ 59
def prefixEnd_6152481 : Nat := 4983230072969 + 3 ^ 40 * 6152481 * 2
def baseEnd_6152481 : Nat := 3159179970654848123492761

theorem tailTrace_6152481 : CollatzResearch.WordTrace tailWord_6152481 prefixEnd_6152481 3159179970654848123492761 := by
  unfold tailWord_6152481
  simp only [CollatzResearch.WordTrace]
  refine ⟨224399417223619571944625297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149599611482413047963083531 224399417223619571944625297)
  ·
    refine ⟨168299562917714678958468973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224399417223619571944625297 168299562917714678958468973)
    ·
      refine ⟨63112336094143004609425865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168299562917714678958468973 63112336094143004609425865)
      ·
        refine ⟨47334252070607253457069399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63112336094143004609425865 47334252070607253457069399)
        ·
          refine ⟨71001378105910880185604099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47334252070607253457069399 71001378105910880185604099)
          ·
            refine ⟨106502067158866320278406149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71001378105910880185604099 106502067158866320278406149)
            ·
              refine ⟨19969137592287435052201153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 106502067158866320278406149 19969137592287435052201153)
              ·
                refine ⟨14976853194215576289150865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19969137592287435052201153 14976853194215576289150865)
                ·
                  refine ⟨11232639895661682216863149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14976853194215576289150865 11232639895661682216863149)
                  ·
                    refine ⟨4212239960873130831323681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11232639895661682216863149 4212239960873130831323681)
                    ·
                      refine ⟨3159179970654848123492761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4212239960873130831323681 3159179970654848123492761)
                      ·
                        rfl

theorem cell23_6152481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 2, 2, 3, 2].length) (baseStart_6152481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6152481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6152481 prefixEnd_6152481 := by exact prefixLift 6152481
  have htrace : WordTrace (prefixWord ++ tailWord_6152481) baseStart_6152481 baseEnd_6152481 := by
    simpa [prefixWord, tailWord_6152481, baseEnd_6152481] using wordTrace_append hprefix tailTrace_6152481
  have hstable : (prefixWord ++ tailWord_6152481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6152481).length < 2 ^ (prefixWord ++ tailWord_6152481).sum := by decide
  have hdescent : baseEnd_6152481 < baseStart_6152481 := by decide
  rcases family_descends (prefixWord ++ tailWord_6152481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6152524 : List Nat := [2, 2, 1, 3, 2, 1, 1, 4, 1, 2, 4]
def baseStart_6152524 : Nat := 118140960795 + 6152524 * 2 ^ 59
def prefixEnd_6152524 : Nat := 4983230072969 + 3 ^ 40 * 6152524 * 2
def baseEnd_6152524 : Nat := 3159202050322991455255063

theorem tailTrace_6152524 : CollatzResearch.WordTrace tailWord_6152524 prefixEnd_6152524 3159202050322991455255063 := by
  unfold tailWord_6152524
  simp only [CollatzResearch.WordTrace]
  refine ⟨112200492781231895144220313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149600657041642526858960417 112200492781231895144220313)
  ·
    refine ⟨84150369585923921358165235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112200492781231895144220313 84150369585923921358165235)
    ·
      refine ⟨126225554378885882037247853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84150369585923921358165235 126225554378885882037247853)
      ·
        refine ⟨47334582892082205763967945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126225554378885882037247853 47334582892082205763967945)
        ·
          refine ⟨35500937169061654322975959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47334582892082205763967945 35500937169061654322975959)
          ·
            refine ⟨53251405753592481484463939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35500937169061654322975959 53251405753592481484463939)
            ·
              refine ⟨79877108630388722226695909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53251405753592481484463939 79877108630388722226695909)
              ·
                refine ⟨14976957868197885417505483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 79877108630388722226695909 14976957868197885417505483)
                ·
                  refine ⟨22465436802296828126258225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14976957868197885417505483 22465436802296828126258225)
                  ·
                    refine ⟨16849077601722621094693669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22465436802296828126258225 16849077601722621094693669)
                    ·
                      refine ⟨3159202050322991455255063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16849077601722621094693669 3159202050322991455255063)
                      ·
                        rfl

theorem cell23_6152524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 4, 1, 2, 4].length) (baseStart_6152524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6152524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6152524 prefixEnd_6152524 := by exact prefixLift 6152524
  have htrace : WordTrace (prefixWord ++ tailWord_6152524) baseStart_6152524 baseEnd_6152524 := by
    simpa [prefixWord, tailWord_6152524, baseEnd_6152524] using wordTrace_append hprefix tailTrace_6152524
  have hstable : (prefixWord ++ tailWord_6152524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6152524).length < 2 ^ (prefixWord ++ tailWord_6152524).sum := by decide
  have hdescent : baseEnd_6152524 < baseStart_6152524 := by decide
  rcases family_descends (prefixWord ++ tailWord_6152524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6152528 : List Nat := [2, 1, 1, 1, 1, 8, 2, 1, 1, 1, 4]
def baseStart_6152528 : Nat := 118140960795 + 6152528 * 2 ^ 59
def prefixEnd_6152528 : Nat := 4983230072969 + 3 ^ 40 * 6152528 * 2
def baseEnd_6152528 : Nat := 3159204104245609439605045

theorem tailTrace_6152528 : CollatzResearch.WordTrace tailWord_6152528 prefixEnd_6152528 3159204104245609439605045 := by
  unfold tailWord_6152528
  simp only [CollatzResearch.WordTrace]
  refine ⟨112200565727224649485793119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149600754302966199314390825 112200565727224649485793119)
  ·
    refine ⟨168300848590836974228689679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112200565727224649485793119 168300848590836974228689679)
    ·
      refine ⟨252451272886255461343034519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168300848590836974228689679 252451272886255461343034519)
      ·
        refine ⟨378676909329383192014551779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252451272886255461343034519 378676909329383192014551779)
        ·
          refine ⟨568015363994074788021827669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 378676909329383192014551779 568015363994074788021827669)
          ·
            refine ⟨6656430046805563922130793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 568015363994074788021827669 6656430046805563922130793)
            ·
              refine ⟨4992322535104172941598095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6656430046805563922130793 4992322535104172941598095)
              ·
                refine ⟨7488483802656259412397143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4992322535104172941598095 7488483802656259412397143)
                ·
                  refine ⟨11232725703984389118595715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7488483802656259412397143 11232725703984389118595715)
                  ·
                    refine ⟨16849088555976583677893573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11232725703984389118595715 16849088555976583677893573)
                    ·
                      refine ⟨3159204104245609439605045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16849088555976583677893573 3159204104245609439605045)
                      ·
                        rfl

theorem cell23_6152528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 2, 1, 1, 1, 4].length) (baseStart_6152528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6152528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6152528 prefixEnd_6152528 := by exact prefixLift 6152528
  have htrace : WordTrace (prefixWord ++ tailWord_6152528) baseStart_6152528 baseEnd_6152528 := by
    simpa [prefixWord, tailWord_6152528, baseEnd_6152528] using wordTrace_append hprefix tailTrace_6152528
  have hstable : (prefixWord ++ tailWord_6152528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6152528).length < 2 ^ (prefixWord ++ tailWord_6152528).sum := by decide
  have hdescent : baseEnd_6152528 < baseStart_6152528 := by decide
  rcases family_descends (prefixWord ++ tailWord_6152528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6152537 : List Nat := [1, 2, 1, 2, 2, 2, 1, 2, 2, 2, 6]
def baseStart_6152537 : Nat := 118140960795 + 6152537 * 2 ^ 59
def prefixEnd_6152537 : Nat := 4983230072969 + 3 ^ 40 * 6152537 * 2
def baseEnd_6152537 : Nat := 3159208725571499904392503

theorem tailTrace_6152537 : CollatzResearch.WordTrace tailWord_6152537 prefixEnd_6152537 3159208725571499904392503 := by
  unfold tailWord_6152537
  simp only [CollatzResearch.WordTrace]
  refine ⟨224401459711416693508663865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149600973140944462339109243 224401459711416693508663865)
  ·
    refine ⟨168301094783562520131497899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224401459711416693508663865 168301094783562520131497899)
    ·
      refine ⟨252451642175343780197246849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168301094783562520131497899 252451642175343780197246849)
      ·
        refine ⟨189338731631507835147935137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 252451642175343780197246849 189338731631507835147935137)
        ·
          refine ⟨142004048723630876360951353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189338731631507835147935137 142004048723630876360951353)
          ·
            refine ⟨106503036542723157270713515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142004048723630876360951353 106503036542723157270713515)
            ·
              refine ⟨159754554814084735906070273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106503036542723157270713515 159754554814084735906070273)
              ·
                refine ⟨119815916110563551929552705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 159754554814084735906070273 119815916110563551929552705)
                ·
                  refine ⟨89861937082922663947164529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 119815916110563551929552705 89861937082922663947164529)
                  ·
                    refine ⟨67396452812191997960373397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 89861937082922663947164529 67396452812191997960373397)
                    ·
                      refine ⟨3159208725571499904392503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67396452812191997960373397 3159208725571499904392503)
                      ·
                        rfl

theorem cell23_6152537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 2, 6].length) (baseStart_6152537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6152537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6152537 prefixEnd_6152537 := by exact prefixLift 6152537
  have htrace : WordTrace (prefixWord ++ tailWord_6152537) baseStart_6152537 baseEnd_6152537 := by
    simpa [prefixWord, tailWord_6152537, baseEnd_6152537] using wordTrace_append hprefix tailTrace_6152537
  have hstable : (prefixWord ++ tailWord_6152537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6152537).length < 2 ^ (prefixWord ++ tailWord_6152537).sum := by decide
  have hdescent : baseEnd_6152537 < baseStart_6152537 := by decide
  rcases family_descends (prefixWord ++ tailWord_6152537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6152567 : List Nat := [1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 8]
def baseStart_6152567 : Nat := 118140960795 + 6152567 * 2 ^ 59
def prefixEnd_6152567 : Nat := 4983230072969 + 3 ^ 40 * 6152567 * 2
def baseEnd_6152567 : Nat := 3159224129991134787017365

theorem tailTrace_6152567 : CollatzResearch.WordTrace tailWord_6152567 prefixEnd_6152567 3159224129991134787017365 := by
  unfold tailWord_6152567
  simp only [CollatzResearch.WordTrace]
  refine ⟨224402553901308008632255955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149601702600872005754837303 224402553901308008632255955)
  ·
    refine ⟨336603830851962012948383933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224402553901308008632255955 336603830851962012948383933)
    ·
      refine ⟨126226436569485754855643975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 336603830851962012948383933 126226436569485754855643975)
      ·
        refine ⟨189339654854228632283465963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126226436569485754855643975 189339654854228632283465963)
        ·
          refine ⟨284009482281342948425198945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189339654854228632283465963 284009482281342948425198945)
          ·
            refine ⟨213007111711007211318899209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 284009482281342948425198945 213007111711007211318899209)
            ·
              refine ⟨159755333783255408489174407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 213007111711007211318899209 159755333783255408489174407)
              ·
                refine ⟨239633000674883112733761611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 159755333783255408489174407 239633000674883112733761611)
                ·
                  refine ⟨359449501012324669100642417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 239633000674883112733761611 359449501012324669100642417)
                  ·
                    refine ⟨269587125759243501825481813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 359449501012324669100642417 269587125759243501825481813)
                    ·
                      refine ⟨3159224129991134787017365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 269587125759243501825481813 3159224129991134787017365)
                      ·
                        rfl

theorem cell23_6152567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 8].length) (baseStart_6152567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6152567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6152567 prefixEnd_6152567 := by exact prefixLift 6152567
  have htrace : WordTrace (prefixWord ++ tailWord_6152567) baseStart_6152567 baseEnd_6152567 := by
    simpa [prefixWord, tailWord_6152567, baseEnd_6152567] using wordTrace_append hprefix tailTrace_6152567
  have hstable : (prefixWord ++ tailWord_6152567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6152567).length < 2 ^ (prefixWord ++ tailWord_6152567).sum := by decide
  have hdescent : baseEnd_6152567 < baseStart_6152567 := by decide
  rcases family_descends (prefixWord ++ tailWord_6152567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6152579 : List Nat := [1, 1, 1, 3, 7, 1, 1, 3, 1, 2, 2]
def baseStart_6152579 : Nat := 118140960795 + 6152579 * 2 ^ 59
def prefixEnd_6152579 : Nat := 4983230072969 + 3 ^ 40 * 6152579 * 2
def baseEnd_6152579 : Nat := 3159230291758988740067311

theorem tailTrace_6152579 : CollatzResearch.WordTrace tailWord_6152579 prefixEnd_6152579 3159230291758988740067311 := by
  unfold tailWord_6152579
  simp only [CollatzResearch.WordTrace]
  refine ⟨224402991577264534681692791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149601994384843023121128527 224402991577264534681692791)
  ·
    refine ⟨336604487365896802022539187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224402991577264534681692791 336604487365896802022539187)
    ·
      refine ⟨504906731048845203033808781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 336604487365896802022539187 504906731048845203033808781)
      ·
        refine ⟨189340024143316951137678293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 504906731048845203033808781 189340024143316951137678293)
        ·
          refine ⟨4437656815858991042289335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 189340024143316951137678293 4437656815858991042289335)
          ·
            refine ⟨6656485223788486563434003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4437656815858991042289335 6656485223788486563434003)
            ·
              refine ⟨9984727835682729845151005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6656485223788486563434003 9984727835682729845151005)
              ·
                refine ⟨3744272938381023691931627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9984727835682729845151005 3744272938381023691931627)
                ·
                  refine ⟨5616409407571535537897441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3744272938381023691931627 5616409407571535537897441)
                  ·
                    refine ⟨4212307055678651653423081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5616409407571535537897441 4212307055678651653423081)
                    ·
                      refine ⟨3159230291758988740067311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4212307055678651653423081 3159230291758988740067311)
                      ·
                        rfl

theorem cell23_6152579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 1, 3, 1, 2, 2].length) (baseStart_6152579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6152579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6152579 prefixEnd_6152579 := by exact prefixLift 6152579
  have htrace : WordTrace (prefixWord ++ tailWord_6152579) baseStart_6152579 baseEnd_6152579 := by
    simpa [prefixWord, tailWord_6152579, baseEnd_6152579] using wordTrace_append hprefix tailTrace_6152579
  have hstable : (prefixWord ++ tailWord_6152579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6152579).length < 2 ^ (prefixWord ++ tailWord_6152579).sum := by decide
  have hdescent : baseEnd_6152579 < baseStart_6152579 := by decide
  rcases family_descends (prefixWord ++ tailWord_6152579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6152588 : List Nat := [2, 2, 1, 2, 1, 4, 2, 3, 1, 3, 2]
def baseStart_6152588 : Nat := 118140960795 + 6152588 * 2 ^ 59
def prefixEnd_6152588 : Nat := 4983230072969 + 3 ^ 40 * 6152588 * 2
def baseEnd_6152588 : Nat := 3159234913084879204854769

theorem tailTrace_6152588 : CollatzResearch.WordTrace tailWord_6152588 prefixEnd_6152588 3159234913084879204854769 := by
  unfold tailWord_6152588
  simp only [CollatzResearch.WordTrace]
  refine ⟨112201659917115964609385209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149602213222821286145846945 112201659917115964609385209)
  ·
    refine ⟨84151244937836973457038907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112201659917115964609385209 84151244937836973457038907)
    ·
      refine ⟨126226867406755460185558361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84151244937836973457038907 126226867406755460185558361)
      ·
        refine ⟨94670150555066595139168771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126226867406755460185558361 94670150555066595139168771)
        ·
          refine ⟨142005225832599892708753157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94670150555066595139168771 142005225832599892708753157)
          ·
            refine ⟨26625979843612479882891217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 142005225832599892708753157 26625979843612479882891217)
            ·
              refine ⟨19969484882709359912168413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26625979843612479882891217 19969484882709359912168413)
              ·
                refine ⟨7488556831016009967063155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19969484882709359912168413 7488556831016009967063155)
                ·
                  refine ⟨11232835246524014950594733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7488556831016009967063155 11232835246524014950594733)
                  ·
                    refine ⟨4212313217446505606473025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11232835246524014950594733 4212313217446505606473025)
                    ·
                      refine ⟨3159234913084879204854769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4212313217446505606473025 3159234913084879204854769)
                      ·
                        rfl

theorem cell23_6152588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 3, 1, 3, 2].length) (baseStart_6152588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6152588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6152588 prefixEnd_6152588 := by exact prefixLift 6152588
  have htrace : WordTrace (prefixWord ++ tailWord_6152588) baseStart_6152588 baseEnd_6152588 := by
    simpa [prefixWord, tailWord_6152588, baseEnd_6152588] using wordTrace_append hprefix tailTrace_6152588
  have hstable : (prefixWord ++ tailWord_6152588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6152588).length < 2 ^ (prefixWord ++ tailWord_6152588).sum := by decide
  have hdescent : baseEnd_6152588 < baseStart_6152588 := by decide
  rcases family_descends (prefixWord ++ tailWord_6152588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6152652 : List Nat := [2, 2, 1, 4, 3, 1, 2, 2, 2, 2, 2]
def baseStart_6152652 : Nat := 118140960795 + 6152652 * 2 ^ 59
def prefixEnd_6152652 : Nat := 4983230072969 + 3 ^ 40 * 6152652 * 2
def baseEnd_6152652 : Nat := 3159267775846766954454475

theorem tailTrace_6152652 : CollatzResearch.WordTrace tailWord_6152652 prefixEnd_6152652 3159267775846766954454475 := by
  unfold tailWord_6152652
  simp only [CollatzResearch.WordTrace]
  refine ⟨112202827053000034074550105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149603769404000045432733473 112202827053000034074550105)
  ·
    refine ⟨84152120289750025555912579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112202827053000034074550105 84152120289750025555912579)
    ·
      refine ⟨126228180434625038333868869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84152120289750025555912579 126228180434625038333868869)
      ·
        refine ⟨23667783831492194687600413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 126228180434625038333868869 23667783831492194687600413)
        ·
          refine ⟨8875418936809573007850155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23667783831492194687600413 8875418936809573007850155)
          ·
            refine ⟨13313128405214359511775233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8875418936809573007850155 13313128405214359511775233)
            ·
              refine ⟨9984846303910769633831425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13313128405214359511775233 9984846303910769633831425)
              ·
                refine ⟨7488634727933077225373569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9984846303910769633831425 7488634727933077225373569)
                ·
                  refine ⟨5616476045949807919030177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7488634727933077225373569 5616476045949807919030177)
                  ·
                    refine ⟨4212357034462355939272633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5616476045949807919030177 4212357034462355939272633)
                    ·
                      refine ⟨3159267775846766954454475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4212357034462355939272633 3159267775846766954454475)
                      ·
                        rfl

theorem cell23_6152652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 2, 2, 2, 2, 2].length) (baseStart_6152652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6152652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6152652 prefixEnd_6152652 := by exact prefixLift 6152652
  have htrace : WordTrace (prefixWord ++ tailWord_6152652) baseStart_6152652 baseEnd_6152652 := by
    simpa [prefixWord, tailWord_6152652, baseEnd_6152652] using wordTrace_append hprefix tailTrace_6152652
  have hstable : (prefixWord ++ tailWord_6152652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6152652).length < 2 ^ (prefixWord ++ tailWord_6152652).sum := by decide
  have hdescent : baseEnd_6152652 < baseStart_6152652 := by decide
  rcases family_descends (prefixWord ++ tailWord_6152652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6152654 : List Nat := [4, 1, 1, 1, 2, 1, 1, 2, 3, 7]
def baseStart_6152654 : Nat := 118140960795 + 6152654 * 2 ^ 59
def prefixEnd_6152654 : Nat := 4983230072969 + 3 ^ 40 * 6152654 * 2
def baseEnd_6152654 : Nat := 1053089600936025315543155

theorem tailTrace_6152654 : CollatzResearch.WordTrace tailWord_6152654 prefixEnd_6152654 1053089600936025315543155 := by
  unfold tailWord_6152654
  simp only [CollatzResearch.WordTrace]
  refine ⟨28050715881499102811334127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149603818034661881660448677 28050715881499102811334127)
  ·
    refine ⟨42076073822248654217001191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28050715881499102811334127 42076073822248654217001191)
    ·
      refine ⟨63114110733372981325501787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42076073822248654217001191 63114110733372981325501787)
      ·
        refine ⟨94671166100059471988252681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63114110733372981325501787 94671166100059471988252681)
        ·
          refine ⟨71003374575044603991189511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94671166100059471988252681 71003374575044603991189511)
          ·
            refine ⟨106505061862566905986784267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71003374575044603991189511 106505061862566905986784267)
            ·
              refine ⟨159757592793850358980176401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106505061862566905986784267 159757592793850358980176401)
              ·
                refine ⟨119818194595387769235132301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 159757592793850358980176401 119818194595387769235132301)
                ·
                  refine ⟨44931822973270413463174613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 119818194595387769235132301 44931822973270413463174613)
                  ·
                    refine ⟨1053089600936025315543155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44931822973270413463174613 1053089600936025315543155)
                    ·
                      rfl

theorem cell23_6152654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 3, 7].length) (baseStart_6152654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6152654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6152654 prefixEnd_6152654 := by exact prefixLift 6152654
  have htrace : WordTrace (prefixWord ++ tailWord_6152654) baseStart_6152654 baseEnd_6152654 := by
    simpa [prefixWord, tailWord_6152654, baseEnd_6152654] using wordTrace_append hprefix tailTrace_6152654
  have hstable : (prefixWord ++ tailWord_6152654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6152654).length < 2 ^ (prefixWord ++ tailWord_6152654).sum := by decide
  have hdescent : baseEnd_6152654 < baseStart_6152654 := by decide
  rcases family_descends (prefixWord ++ tailWord_6152654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6152691 : List Nat := [1, 1, 1, 2, 2, 2, 3, 2, 1, 6, 2]
def baseStart_6152691 : Nat := 118140960795 + 6152691 * 2 ^ 59
def prefixEnd_6152691 : Nat := 4983230072969 + 3 ^ 40 * 6152691 * 2
def baseEnd_6152691 : Nat := 3159287801592292301866795

theorem tailTrace_6152691 : CollatzResearch.WordTrace tailWord_6152691 prefixEnd_6152691 3159287801592292301866795 := by
  unfold tailWord_6152691
  simp only [CollatzResearch.WordTrace]
  refine ⟨224407076552858777809769927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149604717701905851873179951 224407076552858777809769927)
  ·
    refine ⟨336610614829288166714654891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224407076552858777809769927 336610614829288166714654891)
    ·
      refine ⟨504915922243932250071982337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 336610614829288166714654891 504915922243932250071982337)
      ·
        refine ⟨378686941682949187553986753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 504915922243932250071982337 378686941682949187553986753)
        ·
          refine ⟨284015206262211890665490065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 378686941682949187553986753 284015206262211890665490065)
          ·
            refine ⟨213011404696658917999117549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 284015206262211890665490065 213011404696658917999117549)
            ·
              refine ⟨79879276761247094249669081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 213011404696658917999117549 79879276761247094249669081)
              ·
                refine ⟨59909457570935320687251811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79879276761247094249669081 59909457570935320687251811)
                ·
                  refine ⟨89864186356402981030877717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59909457570935320687251811 89864186356402981030877717)
                  ·
                    refine ⟨4212383735456389735822393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 89864186356402981030877717 4212383735456389735822393)
                    ·
                      refine ⟨3159287801592292301866795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4212383735456389735822393 3159287801592292301866795)
                      ·
                        rfl

theorem cell23_6152691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 2, 1, 6, 2].length) (baseStart_6152691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6152691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6152691 prefixEnd_6152691 := by exact prefixLift 6152691
  have htrace : WordTrace (prefixWord ++ tailWord_6152691) baseStart_6152691 baseEnd_6152691 := by
    simpa [prefixWord, tailWord_6152691, baseEnd_6152691] using wordTrace_append hprefix tailTrace_6152691
  have hstable : (prefixWord ++ tailWord_6152691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6152691).length < 2 ^ (prefixWord ++ tailWord_6152691).sum := by decide
  have hdescent : baseEnd_6152691 < baseStart_6152691 := by decide
  rcases family_descends (prefixWord ++ tailWord_6152691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6152701 : List Nat := [1, 4, 1, 1, 1, 3, 1, 2, 5, 4]
def baseStart_6152701 : Nat := 118140960795 + 6152701 * 2 ^ 59
def prefixEnd_6152701 : Nat := 4983230072969 + 3 ^ 40 * 6152701 * 2
def baseEnd_6152701 : Nat := 1053097645466279087580583

theorem tailTrace_6152701 : CollatzResearch.WordTrace tailWord_6152701 prefixEnd_6152701 1053097645466279087580583 := by
  unfold tailWord_6152701
  simp only [CollatzResearch.WordTrace]
  refine ⟨224407441282822549517633957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149604960855215033011755971 224407441282822549517633957)
  ·
    refine ⟨42076395240529228034556367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 224407441282822549517633957 42076395240529228034556367)
    ·
      refine ⟨63114592860793842051834551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42076395240529228034556367 63114592860793842051834551)
      ·
        refine ⟨94671889291190763077751827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63114592860793842051834551 94671889291190763077751827)
        ·
          refine ⟨142007833936786144616627741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94671889291190763077751827 142007833936786144616627741)
          ·
            refine ⟨53252937726294804231235403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 142007833936786144616627741 53252937726294804231235403)
            ·
              refine ⟨79879406589442206346853105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53252937726294804231235403 79879406589442206346853105)
              ·
                refine ⟨59909554942081654760139829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79879406589442206346853105 59909554942081654760139829)
                ·
                  refine ⟨5616520775820155133763109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59909554942081654760139829 5616520775820155133763109)
                  ·
                    refine ⟨1053097645466279087580583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5616520775820155133763109 1053097645466279087580583)
                    ·
                      rfl

theorem cell23_6152701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 2, 5, 4].length) (baseStart_6152701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6152701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6152701 prefixEnd_6152701 := by exact prefixLift 6152701
  have htrace : WordTrace (prefixWord ++ tailWord_6152701) baseStart_6152701 baseEnd_6152701 := by
    simpa [prefixWord, tailWord_6152701, baseEnd_6152701] using wordTrace_append hprefix tailTrace_6152701
  have hstable : (prefixWord ++ tailWord_6152701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6152701).length < 2 ^ (prefixWord ++ tailWord_6152701).sum := by decide
  have hdescent : baseEnd_6152701 < baseStart_6152701 := by decide
  rcases family_descends (prefixWord ++ tailWord_6152701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6152704 : List Nat := [2, 1, 1, 2, 1, 1, 1, 1, 3, 6, 4]
def baseStart_6152704 : Nat := 118140960795 + 6152704 * 2 ^ 59
def prefixEnd_6152704 : Nat := 4983230072969 + 3 ^ 40 * 6152704 * 2
def baseEnd_6152704 : Nat := 3159294476840800751004235

theorem tailTrace_6152704 : CollatzResearch.WordTrace tailWord_6152704 prefixEnd_6152704 3159294476840800751004235 := by
  unfold tailWord_6152704
  simp only [CollatzResearch.WordTrace]
  refine ⟨112203775350905840514996583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149605033801207787353328777 112203775350905840514996583)
  ·
    refine ⟨168305663026358760772494875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112203775350905840514996583 168305663026358760772494875)
    ·
      refine ⟨252458494539538141158742313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168305663026358760772494875 252458494539538141158742313)
      ·
        refine ⟨189343870904653605869056735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 252458494539538141158742313 189343870904653605869056735)
        ·
          refine ⟨284015806356980408803585103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189343870904653605869056735 284015806356980408803585103)
          ·
            refine ⟨426023709535470613205377655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 284015806356980408803585103 426023709535470613205377655)
            ·
              refine ⟨639035564303205919808066483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 426023709535470613205377655 639035564303205919808066483)
              ·
                refine ⟨958553346454808879712099725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 639035564303205919808066483 958553346454808879712099725)
                ·
                  refine ⟨359457504920553329892037397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 958553346454808879712099725 359457504920553329892037397)
                  ·
                    refine ⟨16849570543150937338689253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 359457504920553329892037397 16849570543150937338689253)
                    ·
                      refine ⟨3159294476840800751004235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16849570543150937338689253 3159294476840800751004235)
                      ·
                        rfl

theorem cell23_6152704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6, 4].length) (baseStart_6152704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6152704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6152704 prefixEnd_6152704 := by exact prefixLift 6152704
  have htrace : WordTrace (prefixWord ++ tailWord_6152704) baseStart_6152704 baseEnd_6152704 := by
    simpa [prefixWord, tailWord_6152704, baseEnd_6152704] using wordTrace_append hprefix tailTrace_6152704
  have hstable : (prefixWord ++ tailWord_6152704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6152704).length < 2 ^ (prefixWord ++ tailWord_6152704).sum := by decide
  have hdescent : baseEnd_6152704 < baseStart_6152704 := by decide
  rcases family_descends (prefixWord ++ tailWord_6152704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6152718 : List Nat := [4, 1, 1, 2, 3, 1, 1, 3, 3, 4]
def baseStart_6152718 : Nat := 118140960795 + 6152718 * 2 ^ 59
def prefixEnd_6152718 : Nat := 4983230072969 + 3 ^ 40 * 6152718 * 2
def baseEnd_6152718 : Nat := 1053100555189987898743057

theorem tailTrace_6152718 : CollatzResearch.WordTrace tailWord_6152718 prefixEnd_6152718 1053100555189987898743057 := by
  unfold tailWord_6152718
  simp only [CollatzResearch.WordTrace]
  refine ⟨28051007665470120177625351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149605374215840640947335205 28051007665470120177625351)
  ·
    refine ⟨42076511498205180266438027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28051007665470120177625351 42076511498205180266438027)
    ·
      refine ⟨63114767247307770399657041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42076511498205180266438027 63114767247307770399657041)
      ·
        refine ⟨47336075435480827799742781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63114767247307770399657041 47336075435480827799742781)
        ·
          refine ⟨17751028288305310424903543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47336075435480827799742781 17751028288305310424903543)
          ·
            refine ⟨26626542432457965637355315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17751028288305310424903543 26626542432457965637355315)
            ·
              refine ⟨39939813648686948456032973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26626542432457965637355315 39939813648686948456032973)
              ·
                refine ⟨14977430118257605671012365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39939813648686948456032973 14977430118257605671012365)
                ·
                  refine ⟨5616536294346602126629637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14977430118257605671012365 5616536294346602126629637)
                  ·
                    refine ⟨1053100555189987898743057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5616536294346602126629637 1053100555189987898743057)
                    ·
                      rfl

theorem cell23_6152718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 3, 3, 4].length) (baseStart_6152718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6152718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6152718 prefixEnd_6152718 := by exact prefixLift 6152718
  have htrace : WordTrace (prefixWord ++ tailWord_6152718) baseStart_6152718 baseEnd_6152718 := by
    simpa [prefixWord, tailWord_6152718, baseEnd_6152718] using wordTrace_append hprefix tailTrace_6152718
  have hstable : (prefixWord ++ tailWord_6152718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6152718).length < 2 ^ (prefixWord ++ tailWord_6152718).sum := by decide
  have hdescent : baseEnd_6152718 < baseStart_6152718 := by decide
  rcases family_descends (prefixWord ++ tailWord_6152718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6152768 : List Nat := [2, 1, 1, 2, 2, 2, 3, 1, 4, 3, 2]
def baseStart_6152768 : Nat := 118140960795 + 6152768 * 2 ^ 59
def prefixEnd_6152768 : Nat := 4983230072969 + 3 ^ 40 * 6152768 * 2
def baseEnd_6152768 : Nat := 3159327339602688500603941

theorem tailTrace_6152768 : CollatzResearch.WordTrace tailWord_6152768 prefixEnd_6152768 3159327339602688500603941 := by
  unfold tailWord_6152768
  simp only [CollatzResearch.WordTrace]
  refine ⟨112204942486789909980161479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149606589982386546640215305 112204942486789909980161479)
  ·
    refine ⟨168307413730184864970242219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112204942486789909980161479 168307413730184864970242219)
    ·
      refine ⟨252461120595277297455363329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168307413730184864970242219 252461120595277297455363329)
      ·
        refine ⟨189345840446457973091522497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 252461120595277297455363329 189345840446457973091522497)
        ·
          refine ⟨142009380334843479818641873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189345840446457973091522497 142009380334843479818641873)
          ·
            refine ⟨106507035251132609863981405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142009380334843479818641873 106507035251132609863981405)
            ·
              refine ⟨39940138219174728698993027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106507035251132609863981405 39940138219174728698993027)
              ·
                refine ⟨59910207328762093048489541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39940138219174728698993027 59910207328762093048489541)
                ·
                  refine ⟨11233163874142892446591789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59910207328762093048489541 11233163874142892446591789)
                  ·
                    refine ⟨4212436452803584667471921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11233163874142892446591789 4212436452803584667471921)
                    ·
                      refine ⟨3159327339602688500603941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4212436452803584667471921 3159327339602688500603941)
                      ·
                        rfl

theorem cell23_6152768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 1, 4, 3, 2].length) (baseStart_6152768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6152768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6152768 prefixEnd_6152768 := by exact prefixLift 6152768
  have htrace : WordTrace (prefixWord ++ tailWord_6152768) baseStart_6152768 baseEnd_6152768 := by
    simpa [prefixWord, tailWord_6152768, baseEnd_6152768] using wordTrace_append hprefix tailTrace_6152768
  have hstable : (prefixWord ++ tailWord_6152768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6152768).length < 2 ^ (prefixWord ++ tailWord_6152768).sum := by decide
  have hdescent : baseEnd_6152768 < baseStart_6152768 := by decide
  rcases family_descends (prefixWord ++ tailWord_6152768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6152775 : List Nat := [1, 1, 4, 1, 4, 1, 3, 1, 3, 1, 3]
def baseStart_6152775 : Nat := 118140960795 + 6152775 * 2 ^ 59
def prefixEnd_6152775 : Nat := 4983230072969 + 3 ^ 40 * 6152775 * 2
def baseEnd_6152775 : Nat := 3159330933967269973216409

theorem tailTrace_6152775 : CollatzResearch.WordTrace tailWord_6152775 prefixEnd_6152775 3159330933967269973216409 := by
  unfold tailWord_6152775
  simp only [CollatzResearch.WordTrace]
  refine ⟨224410140284554460155827779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149606760189702973437218519 224410140284554460155827779)
  ·
    refine ⟨336615210426831690233741669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224410140284554460155827779 336615210426831690233741669)
    ·
      refine ⟨63115351955030941918826563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 336615210426831690233741669 63115351955030941918826563)
      ·
        refine ⟨94673027932546412878239845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63115351955030941918826563 94673027932546412878239845)
        ·
          refine ⟨17751192737352452414669971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94673027932546412878239845 17751192737352452414669971)
          ·
            refine ⟨26626789106028678622004957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17751192737352452414669971 26626789106028678622004957)
            ·
              refine ⟨9985045914760754483251859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26626789106028678622004957 9985045914760754483251859)
              ·
                refine ⟨14977568872141131724877789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9985045914760754483251859 14977568872141131724877789)
                ·
                  refine ⟨5616588327052924396829171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14977568872141131724877789 5616588327052924396829171)
                  ·
                    refine ⟨8424882490579386595243757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5616588327052924396829171 8424882490579386595243757)
                    ·
                      refine ⟨3159330933967269973216409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8424882490579386595243757 3159330933967269973216409)
                      ·
                        rfl

theorem cell23_6152775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3, 1, 3, 1, 3].length) (baseStart_6152775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6152775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6152775 prefixEnd_6152775 := by exact prefixLift 6152775
  have htrace : WordTrace (prefixWord ++ tailWord_6152775) baseStart_6152775 baseEnd_6152775 := by
    simpa [prefixWord, tailWord_6152775, baseEnd_6152775] using wordTrace_append hprefix tailTrace_6152775
  have hstable : (prefixWord ++ tailWord_6152775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6152775).length < 2 ^ (prefixWord ++ tailWord_6152775).sum := by decide
  have hdescent : baseEnd_6152775 < baseStart_6152775 := by decide
  rcases family_descends (prefixWord ++ tailWord_6152775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6152791 : List Nat := [1, 1, 3, 2, 2, 2, 2, 3, 1, 6]
def baseStart_6152791 : Nat := 118140960795 + 6152791 * 2 ^ 59
def prefixEnd_6152791 : Nat := 4983230072969 + 3 ^ 40 * 6152791 * 2
def baseEnd_6152791 : Nat := 1053113049885913970205445

theorem tailTrace_6152791 : CollatzResearch.WordTrace tailWord_6152791 prefixEnd_6152791 1053113049885913970205445 := by
  unfold tailWord_6152791
  simp only [CollatzResearch.WordTrace]
  refine ⟨224410723852496494888410227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149607149234997663258940151 224410723852496494888410227)
  ·
    refine ⟨336616085778744742332615341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224410723852496494888410227 336616085778744742332615341)
    ·
      refine ⟨126231032167029278374730753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 336616085778744742332615341 126231032167029278374730753)
      ·
        refine ⟨94673274125271958781048065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126231032167029278374730753 94673274125271958781048065)
        ·
          refine ⟨71004955593953969085786049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94673274125271958781048065 71004955593953969085786049)
          ·
            refine ⟨53253716695465476814339537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71004955593953969085786049 53253716695465476814339537)
            ·
              refine ⟨39940287521599107610754653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53253716695465476814339537 39940287521599107610754653)
              ·
                refine ⟨14977607820599665354032995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39940287521599107610754653 14977607820599665354032995)
                ·
                  refine ⟨22466411730899498031049493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14977607820599665354032995 22466411730899498031049493)
                  ·
                    refine ⟨1053113049885913970205445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22466411730899498031049493 1053113049885913970205445)
                    ·
                      rfl

theorem cell23_6152791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 3, 1, 6].length) (baseStart_6152791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6152791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6152791 prefixEnd_6152791 := by exact prefixLift 6152791
  have htrace : WordTrace (prefixWord ++ tailWord_6152791) baseStart_6152791 baseEnd_6152791 := by
    simpa [prefixWord, tailWord_6152791, baseEnd_6152791] using wordTrace_append hprefix tailTrace_6152791
  have hstable : (prefixWord ++ tailWord_6152791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6152791).length < 2 ^ (prefixWord ++ tailWord_6152791).sum := by decide
  have hdescent : baseEnd_6152791 < baseStart_6152791 := by decide
  rcases family_descends (prefixWord ++ tailWord_6152791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6152821 : List Nat := [1, 3, 4, 2, 13]
def baseStart_6152821 : Nat := 118140960795 + 6152821 * 2 ^ 59
def prefixEnd_6152821 : Nat := 4983230072969 + 3 ^ 40 * 6152821 * 2
def baseEnd_6152821 : Nat := 4333819690092423584693

theorem tailTrace_6152821 : CollatzResearch.WordTrace tailWord_6152821 prefixEnd_6152821 4333819690092423584693 := by
  unfold tailWord_6152821
  simp only [CollatzResearch.WordTrace]
  refine ⟨224411818042387810012002317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149607878694925206674668211 224411818042387810012002317)
  ·
    refine ⟨84154431765895428754500869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 224411818042387810012002317 84154431765895428754500869)
    ·
      refine ⟨15778955956105392891468913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84154431765895428754500869 15778955956105392891468913)
      ·
        refine ⟨11834216967079044668601685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15778955956105392891468913 11834216967079044668601685)
        ·
          refine ⟨4333819690092423584693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 11834216967079044668601685 4333819690092423584693)
          ·
            rfl

theorem cell23_6152821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 13].length) (baseStart_6152821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6152821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6152821 prefixEnd_6152821 := by exact prefixLift 6152821
  have htrace : WordTrace (prefixWord ++ tailWord_6152821) baseStart_6152821 baseEnd_6152821 := by
    simpa [prefixWord, tailWord_6152821, baseEnd_6152821] using wordTrace_append hprefix tailTrace_6152821
  have hstable : (prefixWord ++ tailWord_6152821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6152821).length < 2 ^ (prefixWord ++ tailWord_6152821).sum := by decide
  have hdescent : baseEnd_6152821 < baseStart_6152821 := by decide
  rcases family_descends (prefixWord ++ tailWord_6152821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6152825 : List Nat := [1, 2, 1, 3, 3, 3, 2, 2, 2, 4]
def baseStart_6152825 : Nat := 118140960795 + 6152825 * 2 ^ 59
def prefixEnd_6152825 : Nat := 4983230072969 + 3 ^ 40 * 6152825 * 2
def baseEnd_6152825 : Nat := 1053118869333331592530393

theorem tailTrace_6152825 : CollatzResearch.WordTrace tailWord_6152825 prefixEnd_6152825 1053118869333331592530393 := by
  unfold tailWord_6152825
  simp only [CollatzResearch.WordTrace]
  refine ⟨224411963934373318695147929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149607975956248879130098619 224411963934373318695147929)
  ·
    refine ⟨168308972950779989021360947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224411963934373318695147929 168308972950779989021360947)
    ·
      refine ⟨252463459426169983532041421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168308972950779989021360947 252463459426169983532041421)
      ·
        refine ⟨94673797284813743824515533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 252463459426169983532041421 94673797284813743824515533)
        ·
          refine ⟨35502673981805153934193325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94673797284813743824515533 35502673981805153934193325)
          ·
            refine ⟨13313502743176932725322497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35502673981805153934193325 13313502743176932725322497)
            ·
              refine ⟨9985127057382699543991873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13313502743176932725322497 9985127057382699543991873)
              ·
                refine ⟨7488845293037024657993905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9985127057382699543991873 7488845293037024657993905)
                ·
                  refine ⟨5616633969777768493495429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7488845293037024657993905 5616633969777768493495429)
                  ·
                    refine ⟨1053118869333331592530393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5616633969777768493495429 1053118869333331592530393)
                    ·
                      rfl

theorem cell23_6152825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2, 2, 2, 4].length) (baseStart_6152825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6152825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6152825 prefixEnd_6152825 := by exact prefixLift 6152825
  have htrace : WordTrace (prefixWord ++ tailWord_6152825) baseStart_6152825 baseEnd_6152825 := by
    simpa [prefixWord, tailWord_6152825, baseEnd_6152825] using wordTrace_append hprefix tailTrace_6152825
  have hstable : (prefixWord ++ tailWord_6152825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6152825).length < 2 ^ (prefixWord ++ tailWord_6152825).sum := by decide
  have hdescent : baseEnd_6152825 < baseStart_6152825 := by decide
  rcases family_descends (prefixWord ++ tailWord_6152825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6152848 : List Nat := [2, 1, 1, 1, 1, 1, 3, 1, 8, 1, 3]
def baseStart_6152848 : Nat := 118140960795 + 6152848 * 2 ^ 59
def prefixEnd_6152848 : Nat := 4983230072969 + 3 ^ 40 * 6152848 * 2
def baseEnd_6152848 : Nat := 3159368418055048187603573

theorem tailTrace_6152848 : CollatzResearch.WordTrace tailWord_6152848 prefixEnd_6152848 3159368418055048187603573 := by
  unfold tailWord_6152848
  simp only [CollatzResearch.WordTrace]
  refine ⟨112206401406644996811617599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149608535208859995748823465 112206401406644996811617599)
  ·
    refine ⟨168309602109967495217426399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112206401406644996811617599 168309602109967495217426399)
    ·
      refine ⟨252464403164951242826139599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168309602109967495217426399 252464403164951242826139599)
      ·
        refine ⟨378696604747426864239209399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252464403164951242826139599 378696604747426864239209399)
        ·
          refine ⟨568044907121140296358814099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 378696604747426864239209399 568044907121140296358814099)
          ·
            refine ⟨852067360681710444538221149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 568044907121140296358814099 852067360681710444538221149)
            ·
              refine ⟨319525260255641416701832931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 852067360681710444538221149 319525260255641416701832931)
              ·
                refine ⟨479287890383462125052749397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 319525260255641416701832931 479287890383462125052749397)
                ·
                  refine ⟨5616654965431196777961907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 479287890383462125052749397 5616654965431196777961907)
                  ·
                    refine ⟨8424982448146795166942861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5616654965431196777961907 8424982448146795166942861)
                    ·
                      refine ⟨3159368418055048187603573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8424982448146795166942861 3159368418055048187603573)
                      ·
                        rfl

theorem cell23_6152848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 8, 1, 3].length) (baseStart_6152848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6152848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6152848 prefixEnd_6152848 := by exact prefixLift 6152848
  have htrace : WordTrace (prefixWord ++ tailWord_6152848) baseStart_6152848 baseEnd_6152848 := by
    simpa [prefixWord, tailWord_6152848, baseEnd_6152848] using wordTrace_append hprefix tailTrace_6152848
  have hstable : (prefixWord ++ tailWord_6152848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6152848).length < 2 ^ (prefixWord ++ tailWord_6152848).sum := by decide
  have hdescent : baseEnd_6152848 < baseStart_6152848 := by decide
  rcases family_descends (prefixWord ++ tailWord_6152848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6152888 : List Nat := [2, 1, 2, 1, 2, 1, 1, 1, 2, 8, 2]
def baseStart_6152888 : Nat := 118140960795 + 6152888 * 2 ^ 59
def prefixEnd_6152888 : Nat := 4983230072969 + 3 ^ 40 * 6152888 * 2
def baseEnd_6152888 : Nat := 3159388957281228031103389

theorem tailTrace_6152888 : CollatzResearch.WordTrace tailWord_6152888 prefixEnd_6152888 3159388957281228031103389 := by
  unfold tailWord_6152888
  simp only [CollatzResearch.WordTrace]
  refine ⟨112207130866572540227345659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149609507822096720303127545 112207130866572540227345659)
  ·
    refine ⟨168310696299858810341018489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112207130866572540227345659 168310696299858810341018489)
    ·
      refine ⟨126233022224894107755763867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168310696299858810341018489 126233022224894107755763867)
      ·
        refine ⟨189349533337341161633645801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126233022224894107755763867 189349533337341161633645801)
        ·
          refine ⟨142012150003005871225234351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189349533337341161633645801 142012150003005871225234351)
          ·
            refine ⟨213018225004508806837851527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142012150003005871225234351 213018225004508806837851527)
            ·
              refine ⟨319527337506763210256777291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 213018225004508806837851527 319527337506763210256777291)
              ·
                refine ⟨479291006260144815385165937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 319527337506763210256777291 479291006260144815385165937)
                ·
                  refine ⟨359468254695108611538874453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 479291006260144815385165937 359468254695108611538874453)
                  ·
                    refine ⟨4212518609708304041471185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 359468254695108611538874453 4212518609708304041471185)
                    ·
                      refine ⟨3159388957281228031103389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4212518609708304041471185 3159388957281228031103389)
                      ·
                        rfl

theorem cell23_6152888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 2, 8, 2].length) (baseStart_6152888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6152888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6152888 prefixEnd_6152888 := by exact prefixLift 6152888
  have htrace : WordTrace (prefixWord ++ tailWord_6152888) baseStart_6152888 baseEnd_6152888 := by
    simpa [prefixWord, tailWord_6152888, baseEnd_6152888] using wordTrace_append hprefix tailTrace_6152888
  have hstable : (prefixWord ++ tailWord_6152888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6152888).length < 2 ^ (prefixWord ++ tailWord_6152888).sum := by decide
  have hdescent : baseEnd_6152888 < baseStart_6152888 := by decide
  rcases family_descends (prefixWord ++ tailWord_6152888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6152891 : List Nat := [1, 1, 1, 1, 1, 2, 3, 1, 6, 1, 5]
def baseStart_6152891 : Nat := 118140960795 + 6152891 * 2 ^ 59
def prefixEnd_6152891 : Nat := 4983230072969 + 3 ^ 40 * 6152891 * 2
def baseEnd_6152891 : Nat := 3159390497723191519365875

theorem tailTrace_6152891 : CollatzResearch.WordTrace tailWord_6152891 prefixEnd_6152891 3159390497723191519365875 := by
  unfold tailWord_6152891
  simp only [CollatzResearch.WordTrace]
  refine ⟨224414371152134211967050527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149609580768089474644700351 224414371152134211967050527)
  ·
    refine ⟨336621556728201317950575791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224414371152134211967050527 336621556728201317950575791)
    ·
      refine ⟨504932335092301976925863687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 336621556728201317950575791 504932335092301976925863687)
      ·
        refine ⟨757398502638452965388795531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 504932335092301976925863687 757398502638452965388795531)
        ·
          refine ⟨1136097753957679448083193297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 757398502638452965388795531 1136097753957679448083193297)
          ·
            refine ⟨852073315468259586062394973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1136097753957679448083193297 852073315468259586062394973)
            ·
              refine ⟨319527493300597344773398115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 852073315468259586062394973 319527493300597344773398115)
              ·
                refine ⟨479291239950896017160097173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 319527493300597344773398115 479291239950896017160097173)
                ·
                  refine ⟨22466776872698250804379555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 479291239950896017160097173 22466776872698250804379555)
                  ·
                    refine ⟨33700165309047376206569333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22466776872698250804379555 33700165309047376206569333)
                    ·
                      refine ⟨3159390497723191519365875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33700165309047376206569333 3159390497723191519365875)
                      ·
                        rfl

theorem cell23_6152891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 6, 1, 5].length) (baseStart_6152891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6152891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6152891 prefixEnd_6152891 := by exact prefixLift 6152891
  have htrace : WordTrace (prefixWord ++ tailWord_6152891) baseStart_6152891 baseEnd_6152891 := by
    simpa [prefixWord, tailWord_6152891, baseEnd_6152891] using wordTrace_append hprefix tailTrace_6152891
  have hstable : (prefixWord ++ tailWord_6152891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6152891).length < 2 ^ (prefixWord ++ tailWord_6152891).sum := by decide
  have hdescent : baseEnd_6152891 < baseStart_6152891 := by decide
  rcases family_descends (prefixWord ++ tailWord_6152891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6152956 : List Nat := [2, 2, 2, 1, 3, 4, 2, 1, 2, 2, 2]
def baseStart_6152956 : Nat := 118140960795 + 6152956 * 2 ^ 59
def prefixEnd_6152956 : Nat := 4983230072969 + 3 ^ 40 * 6152956 * 2
def baseEnd_6152956 : Nat := 3159423873965733765053077

theorem tailTrace_6152956 : CollatzResearch.WordTrace tailWord_6152956 prefixEnd_6152956 3159423873965733765053077 := by
  unfold tailWord_6152956
  simp only [CollatzResearch.WordTrace]
  refine ⟨112208370948449364034083361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149611161264599152045444481 112208370948449364034083361)
  ·
    refine ⟨84156278211337023025562521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112208370948449364034083361 84156278211337023025562521)
    ·
      refine ⟨63117208658502767269171891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84156278211337023025562521 63117208658502767269171891)
      ·
        refine ⟨94675812987754150903757837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63117208658502767269171891 94675812987754150903757837)
        ·
          refine ⟨35503429870407806588909189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94675812987754150903757837 35503429870407806588909189)
          ·
            refine ⟨6656893100701463735420473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35503429870407806588909189 6656893100701463735420473)
            ·
              refine ⟨4992669825526097801565355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6656893100701463735420473 4992669825526097801565355)
              ·
                refine ⟨7489004738289146702348033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4992669825526097801565355 7489004738289146702348033)
                ·
                  refine ⟨5616753553716860026761025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7489004738289146702348033 5616753553716860026761025)
                  ·
                    refine ⟨4212565165287645020070769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5616753553716860026761025 4212565165287645020070769)
                    ·
                      refine ⟨3159423873965733765053077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4212565165287645020070769 3159423873965733765053077)
                      ·
                        rfl

theorem cell23_6152956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 2, 1, 2, 2, 2].length) (baseStart_6152956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6152956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6152956 prefixEnd_6152956 := by exact prefixLift 6152956
  have htrace : WordTrace (prefixWord ++ tailWord_6152956) baseStart_6152956 baseEnd_6152956 := by
    simpa [prefixWord, tailWord_6152956, baseEnd_6152956] using wordTrace_append hprefix tailTrace_6152956
  have hstable : (prefixWord ++ tailWord_6152956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6152956).length < 2 ^ (prefixWord ++ tailWord_6152956).sum := by decide
  have hdescent : baseEnd_6152956 < baseStart_6152956 := by decide
  rcases family_descends (prefixWord ++ tailWord_6152956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6152995 : List Nat := [1, 1, 1, 4, 2, 1, 1, 4, 2, 4, 2]
def baseStart_6152995 : Nat := 118140960795 + 6152995 * 2 ^ 59
def prefixEnd_6152995 : Nat := 4983230072969 + 3 ^ 40 * 6152995 * 2
def baseEnd_6152995 : Nat := 3159443899711259112465397

theorem tailTrace_6152995 : CollatzResearch.WordTrace tailWord_6152995 prefixEnd_6152995 3159443899711259112465397 := by
  unfold tailWord_6152995
  simp only [CollatzResearch.WordTrace]
  refine ⟨224418164343757437728836439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149612109562504958485890959 224418164343757437728836439)
  ·
    refine ⟨336627246515636156593254659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224418164343757437728836439 336627246515636156593254659)
    ·
      refine ⟨504940869773454234889881989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 336627246515636156593254659 504940869773454234889881989)
      ·
        refine ⟨94676413082522669041852873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 504940869773454234889881989 94676413082522669041852873)
        ·
          refine ⟨71007309811892001781389655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94676413082522669041852873 71007309811892001781389655)
          ·
            refine ⟨106510964717838002672084483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71007309811892001781389655 106510964717838002672084483)
            ·
              refine ⟨159766447076757004008126725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106510964717838002672084483 159766447076757004008126725)
              ·
                refine ⟨29956208826891938251523761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 159766447076757004008126725 29956208826891938251523761)
                ·
                  refine ⟨22467156620168953688642821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29956208826891938251523761 22467156620168953688642821)
                  ·
                    refine ⟨4212591866281678816620529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22467156620168953688642821 4212591866281678816620529)
                    ·
                      refine ⟨3159443899711259112465397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4212591866281678816620529 3159443899711259112465397)
                      ·
                        rfl

theorem cell23_6152995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 4, 2, 4, 2].length) (baseStart_6152995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6152995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6152995 prefixEnd_6152995 := by exact prefixLift 6152995
  have htrace : WordTrace (prefixWord ++ tailWord_6152995) baseStart_6152995 baseEnd_6152995 := by
    simpa [prefixWord, tailWord_6152995, baseEnd_6152995] using wordTrace_append hprefix tailTrace_6152995
  have hstable : (prefixWord ++ tailWord_6152995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6152995).length < 2 ^ (prefixWord ++ tailWord_6152995).sum := by decide
  have hdescent : baseEnd_6152995 < baseStart_6152995 := by decide
  rcases family_descends (prefixWord ++ tailWord_6152995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6152996 : List Nat := [2, 3, 1, 3, 4, 1, 2, 2, 5]
def baseStart_6152996 : Nat := 118140960795 + 6152996 * 2 ^ 59
def prefixEnd_6152996 : Nat := 4983230072969 + 3 ^ 40 * 6152996 * 2
def baseEnd_6152996 : Nat := 351049379243545956505877

theorem tailTrace_6152996 : CollatzResearch.WordTrace tailWord_6152996 prefixEnd_6152996 351049379243545956505877 := by
  unfold tailWord_6152996
  simp only [CollatzResearch.WordTrace]
  refine ⟨112209100408376907449811421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149612133877835876599748561 112209100408376907449811421)
  ·
    refine ⟨42078412653141340293679283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112209100408376907449811421 42078412653141340293679283)
    ·
      refine ⟨63117618979712010440518925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42078412653141340293679283 63117618979712010440518925)
      ·
        refine ⟨23669107117392003915194597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63117618979712010440518925 23669107117392003915194597)
        ·
          refine ⟨4437957584511000734098987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23669107117392003915194597 4437957584511000734098987)
          ·
            refine ⟨6656936376766501101148481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4437957584511000734098987 6656936376766501101148481)
            ·
              refine ⟨4992702282574875825861361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6656936376766501101148481 4992702282574875825861361)
              ·
                refine ⟨3744526711931156869396021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4992702282574875825861361 3744526711931156869396021)
                ·
                  refine ⟨351049379243545956505877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3744526711931156869396021 351049379243545956505877)
                  ·
                    rfl

theorem cell23_6152996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 2, 2, 5].length) (baseStart_6152996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6152996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6152996 prefixEnd_6152996 := by exact prefixLift 6152996
  have htrace : WordTrace (prefixWord ++ tailWord_6152996) baseStart_6152996 baseEnd_6152996 := by
    simpa [prefixWord, tailWord_6152996, baseEnd_6152996] using wordTrace_append hprefix tailTrace_6152996
  have hstable : (prefixWord ++ tailWord_6152996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6152996).length < 2 ^ (prefixWord ++ tailWord_6152996).sum := by decide
  have hdescent : baseEnd_6152996 < baseStart_6152996 := by decide
  rcases family_descends (prefixWord ++ tailWord_6152996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6153038 : List Nat := [4, 1, 1, 1, 1, 1, 1, 2, 3, 2, 6]
def baseStart_6153038 : Nat := 118140960795 + 6153038 * 2 ^ 59
def prefixEnd_6153038 : Nat := 4983230072969 + 3 ^ 40 * 6153038 * 2
def baseEnd_6153038 : Nat := 3159465979379402444227699

theorem tailTrace_6153038 : CollatzResearch.WordTrace tailWord_6153038 prefixEnd_6153038 3159465979379402444227699 := by
  unfold tailWord_6153038
  simp only [CollatzResearch.WordTrace]
  refine ⟨28052466585325207009081471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149613155121734437381767845 28052466585325207009081471)
  ·
    refine ⟨42078699877987810513622207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28052466585325207009081471 42078699877987810513622207)
    ·
      refine ⟨63118049816981715770433311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42078699877987810513622207 63118049816981715770433311)
      ·
        refine ⟨94677074725472573655649967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63118049816981715770433311 94677074725472573655649967)
        ·
          refine ⟨142015612088208860483474951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94677074725472573655649967 142015612088208860483474951)
          ·
            refine ⟨213023418132313290725212427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142015612088208860483474951 213023418132313290725212427)
            ·
              refine ⟨319535127198469936087818641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 213023418132313290725212427 319535127198469936087818641)
              ·
                refine ⟨239651345398852452065863981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 319535127198469936087818641 239651345398852452065863981)
                ·
                  refine ⟨89869254524569669524698993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 239651345398852452065863981 89869254524569669524698993)
                  ·
                    refine ⟨67401940893427252143524245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 89869254524569669524698993 67401940893427252143524245)
                    ·
                      refine ⟨3159465979379402444227699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67401940893427252143524245 3159465979379402444227699)
                      ·
                        rfl

theorem cell23_6153038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 3, 2, 6].length) (baseStart_6153038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6153038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6153038 prefixEnd_6153038 := by exact prefixLift 6153038
  have htrace : WordTrace (prefixWord ++ tailWord_6153038) baseStart_6153038 baseEnd_6153038 := by
    simpa [prefixWord, tailWord_6153038, baseEnd_6153038] using wordTrace_append hprefix tailTrace_6153038
  have hstable : (prefixWord ++ tailWord_6153038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6153038).length < 2 ^ (prefixWord ++ tailWord_6153038).sum := by decide
  have hdescent : baseEnd_6153038 < baseStart_6153038 := by decide
  rcases family_descends (prefixWord ++ tailWord_6153038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6153052 : List Nat := [2, 2, 4, 2, 1, 1, 3, 2, 6]
def baseStart_6153052 : Nat := 118140960795 + 6153052 * 2 ^ 59
def prefixEnd_6153052 : Nat := 4983230072969 + 3 ^ 40 * 6153052 * 2
def baseEnd_6153052 : Nat := 351052574234285043272515

theorem tailTrace_6153052 : CollatzResearch.WordTrace tailWord_6153052 prefixEnd_6153052 351052574234285043272515 := by
  unfold tailWord_6153052
  simp only [CollatzResearch.WordTrace]
  refine ⟨112210121652275468231830705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149613495536367290975774273 112210121652275468231830705)
  ·
    refine ⟨84157591239206601173873029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112210121652275468231830705 84157591239206601173873029)
    ·
      refine ⟨15779548357351237720101193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84157591239206601173873029 15779548357351237720101193)
      ·
        refine ⟨11834661268013428290075895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15779548357351237720101193 11834661268013428290075895)
        ·
          refine ⟨17751991902020142435113843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11834661268013428290075895 17751991902020142435113843)
          ·
            refine ⟨26627987853030213652670765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17751991902020142435113843 26627987853030213652670765)
            ·
              refine ⟨9985495444886330119751537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26627987853030213652670765 9985495444886330119751537)
              ·
                refine ⟨7489121583664747589813653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9985495444886330119751537 7489121583664747589813653)
                ·
                  refine ⟨351052574234285043272515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7489121583664747589813653 351052574234285043272515)
                  ·
                    rfl

theorem cell23_6153052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3, 2, 6].length) (baseStart_6153052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6153052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6153052 prefixEnd_6153052 := by exact prefixLift 6153052
  have htrace : WordTrace (prefixWord ++ tailWord_6153052) baseStart_6153052 baseEnd_6153052 := by
    simpa [prefixWord, tailWord_6153052, baseEnd_6153052] using wordTrace_append hprefix tailTrace_6153052
  have hstable : (prefixWord ++ tailWord_6153052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6153052).length < 2 ^ (prefixWord ++ tailWord_6153052).sum := by decide
  have hdescent : baseEnd_6153052 < baseStart_6153052 := by decide
  rcases family_descends (prefixWord ++ tailWord_6153052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6153085 : List Nat := [1, 4, 1, 1, 2, 1, 2, 3, 3, 1, 4]
def baseStart_6153085 : Nat := 118140960795 + 6153085 * 2 ^ 59
def prefixEnd_6153085 : Nat := 4983230072969 + 3 ^ 40 * 6153085 * 2
def baseEnd_6153085 : Nat := 3159490112970163760339983

theorem tailTrace_6153085 : CollatzResearch.WordTrace tailWord_6153085 prefixEnd_6153085 3159490112970163760339983 := by
  unfold tailWord_6153085
  simp only [CollatzResearch.WordTrace]
  refine ⟨224421446913431383099612709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149614297942287588733075139 224421446913431383099612709)
  ·
    refine ⟨42079021296268384331177383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 224421446913431383099612709 42079021296268384331177383)
    ·
      refine ⟨63118531944402576496766075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42079021296268384331177383 63118531944402576496766075)
      ·
        refine ⟨94677797916603864745149113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63118531944402576496766075 94677797916603864745149113)
        ·
          refine ⟨71008348437452898558861835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94677797916603864745149113 71008348437452898558861835)
          ·
            refine ⟨106512522656179347838292753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71008348437452898558861835 106512522656179347838292753)
            ·
              refine ⟨79884391992134510878719565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106512522656179347838292753 79884391992134510878719565)
              ·
                refine ⟨29956646997050441579519837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79884391992134510878719565 29956646997050441579519837)
                ·
                  refine ⟨11233742623893915592319939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29956646997050441579519837 11233742623893915592319939)
                  ·
                    refine ⟨16850613935840873388479909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11233742623893915592319939 16850613935840873388479909)
                    ·
                      refine ⟨3159490112970163760339983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16850613935840873388479909 3159490112970163760339983)
                      ·
                        rfl

theorem cell23_6153085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 3, 3, 1, 4].length) (baseStart_6153085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6153085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6153085 prefixEnd_6153085 := by exact prefixLift 6153085
  have htrace : WordTrace (prefixWord ++ tailWord_6153085) baseStart_6153085 baseEnd_6153085 := by
    simpa [prefixWord, tailWord_6153085, baseEnd_6153085] using wordTrace_append hprefix tailTrace_6153085
  have hstable : (prefixWord ++ tailWord_6153085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6153085).length < 2 ^ (prefixWord ++ tailWord_6153085).sum := by decide
  have hdescent : baseEnd_6153085 < baseStart_6153085 := by decide
  rcases family_descends (prefixWord ++ tailWord_6153085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6153090 : List Nat := [3, 4, 2, 2, 1, 2, 1, 3, 1, 4]
def baseStart_6153090 : Nat := 118140960795 + 6153090 * 2 ^ 59
def prefixEnd_6153090 : Nat := 4983230072969 + 3 ^ 40 * 6153090 * 2
def baseEnd_6153090 : Nat := 1053164226791145413592487

theorem tailTrace_6153090 : CollatzResearch.WordTrace tailWord_6153090 prefixEnd_6153090 1053164226791145413592487 := by
  unfold tailWord_6153090
  simp only [CollatzResearch.WordTrace]
  refine ⟨56105407319603317238386181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149614419518942179302363149 56105407319603317238386181)
  ·
    refine ⟨10519763872425621982197409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56105407319603317238386181 10519763872425621982197409)
    ·
      refine ⟨7889822904319216486648057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10519763872425621982197409 7889822904319216486648057)
      ·
        refine ⟨5917367178239412364986043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7889822904319216486648057 5917367178239412364986043)
        ·
          refine ⟨8876050767359118547479065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5917367178239412364986043 8876050767359118547479065)
          ·
            refine ⟨6657038075519338910609299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8876050767359118547479065 6657038075519338910609299)
            ·
              refine ⟨9985557113279008365913949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6657038075519338910609299 9985557113279008365913949)
              ·
                refine ⟨3744583917479628137217731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9985557113279008365913949 3744583917479628137217731)
                ·
                  refine ⟨5616875876219442205826597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3744583917479628137217731 5616875876219442205826597)
                  ·
                    refine ⟨1053164226791145413592487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5616875876219442205826597 1053164226791145413592487)
                    ·
                      rfl

theorem cell23_6153090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_6153090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6153090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6153090 prefixEnd_6153090 := by exact prefixLift 6153090
  have htrace : WordTrace (prefixWord ++ tailWord_6153090) baseStart_6153090 baseEnd_6153090 := by
    simpa [prefixWord, tailWord_6153090, baseEnd_6153090] using wordTrace_append hprefix tailTrace_6153090
  have hstable : (prefixWord ++ tailWord_6153090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6153090).length < 2 ^ (prefixWord ++ tailWord_6153090).sum := by decide
  have hdescent : baseEnd_6153090 < baseStart_6153090 := by decide
  rcases family_descends (prefixWord ++ tailWord_6153090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6153096 : List Nat := [2, 1, 3, 3, 2, 1, 3, 3, 1, 1, 3]
def baseStart_6153096 : Nat := 118140960795 + 6153096 * 2 ^ 59
def prefixEnd_6153096 : Nat := 4983230072969 + 3 ^ 40 * 6153096 * 2
def baseEnd_6153096 : Nat := 3159495761257363217302433

theorem tailTrace_6153096 : CollatzResearch.WordTrace tailWord_6153096 prefixEnd_6153096 3159495761257363217302433 := by
  unfold tailWord_6153096
  simp only [CollatzResearch.WordTrace]
  refine ⟨112210924058195765989131571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149614565410927687985508761 112210924058195765989131571)
  ·
    refine ⟨168316386087293648983697357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112210924058195765989131571 168316386087293648983697357)
    ·
      refine ⟨63118644782735118368886509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168316386087293648983697357 63118644782735118368886509)
      ·
        refine ⟨23669491793525669388332441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63118644782735118368886509 23669491793525669388332441)
        ·
          refine ⟨17752118845144252041249331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23669491793525669388332441 17752118845144252041249331)
          ·
            refine ⟨26628178267716378061873997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17752118845144252041249331 26628178267716378061873997)
            ·
              refine ⟨9985566850393641773202749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26628178267716378061873997 9985566850393641773202749)
              ·
                refine ⟨3744587568897615664951031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9985566850393641773202749 3744587568897615664951031)
                ·
                  refine ⟨5616881353346423497426547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3744587568897615664951031 5616881353346423497426547)
                  ·
                    refine ⟨8425322030019635246139821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5616881353346423497426547 8425322030019635246139821)
                    ·
                      refine ⟨3159495761257363217302433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8425322030019635246139821 3159495761257363217302433)
                      ·
                        rfl

theorem cell23_6153096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3, 3, 1, 1, 3].length) (baseStart_6153096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6153096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6153096 prefixEnd_6153096 := by exact prefixLift 6153096
  have htrace : WordTrace (prefixWord ++ tailWord_6153096) baseStart_6153096 baseEnd_6153096 := by
    simpa [prefixWord, tailWord_6153096, baseEnd_6153096] using wordTrace_append hprefix tailTrace_6153096
  have hstable : (prefixWord ++ tailWord_6153096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6153096).length < 2 ^ (prefixWord ++ tailWord_6153096).sum := by decide
  have hdescent : baseEnd_6153096 < baseStart_6153096 := by decide
  rcases family_descends (prefixWord ++ tailWord_6153096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6153105 : List Nat := [1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 3]
def baseStart_6153105 : Nat := 118140960795 + 6153105 * 2 ^ 59
def prefixEnd_6153105 : Nat := 4983230072969 + 3 ^ 40 * 6153105 * 2
def baseEnd_6153105 : Nat := 3159500382583253682089891

theorem tailTrace_6153105 : CollatzResearch.WordTrace tailWord_6153105 prefixEnd_6153105 3159500382583253682089891 := by
  unfold tailWord_6153105
  simp only [CollatzResearch.WordTrace]
  refine ⟨224422176373358926515340769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149614784248905951010227179 224422176373358926515340769)
  ·
    refine ⟨168316632280019194886505577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224422176373358926515340769 168316632280019194886505577)
    ·
      refine ⟨126237474210014396164879183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168316632280019194886505577 126237474210014396164879183)
      ·
        refine ⟨189356211315021594247318775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126237474210014396164879183 189356211315021594247318775)
        ·
          refine ⟨284034316972532391370978163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189356211315021594247318775 284034316972532391370978163)
          ·
            refine ⟨426051475458798587056467245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 284034316972532391370978163 426051475458798587056467245)
            ·
              refine ⟨159769303297049470146175217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 426051475458798587056467245 159769303297049470146175217)
              ·
                refine ⟨119826977472787102609631413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 159769303297049470146175217 119826977472787102609631413)
                ·
                  refine ⟨11233779138073790869652945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 119826977472787102609631413 11233779138073790869652945)
                  ·
                    refine ⟨8425334353555343152239709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11233779138073790869652945 8425334353555343152239709)
                    ·
                      refine ⟨3159500382583253682089891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8425334353555343152239709 3159500382583253682089891)
                      ·
                        rfl

theorem cell23_6153105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 3].length) (baseStart_6153105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6153105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6153105 prefixEnd_6153105 := by exact prefixLift 6153105
  have htrace : WordTrace (prefixWord ++ tailWord_6153105) baseStart_6153105 baseEnd_6153105 := by
    simpa [prefixWord, tailWord_6153105, baseEnd_6153105] using wordTrace_append hprefix tailTrace_6153105
  have hstable : (prefixWord ++ tailWord_6153105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6153105).length < 2 ^ (prefixWord ++ tailWord_6153105).sum := by decide
  have hdescent : baseEnd_6153105 < baseStart_6153105 := by decide
  rcases family_descends (prefixWord ++ tailWord_6153105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6153106 : List Nat := [3, 2, 3, 2, 2, 1, 1, 2, 2, 3, 2]
def baseStart_6153106 : Nat := 118140960795 + 6153106 * 2 ^ 59
def prefixEnd_6153106 : Nat := 4983230072969 + 3 ^ 40 * 6153106 * 2
def baseEnd_6153106 : Nat := 3159500896063908178177387

theorem tailTrace_6153106 : CollatzResearch.WordTrace tailWord_6153106 prefixEnd_6153106 3159500896063908178177387 := by
  unfold tailWord_6153106
  simp only [CollatzResearch.WordTrace]
  refine ⟨56105553211588825921531793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149614808564236869124084781 56105553211588825921531793)
  ·
    refine ⟨42079164908691619441148845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56105553211588825921531793 42079164908691619441148845)
    ·
      refine ⟨15779686840759357290430817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42079164908691619441148845 15779686840759357290430817)
      ·
        refine ⟨11834765130569517967823113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15779686840759357290430817 11834765130569517967823113)
        ·
          refine ⟨8876073847927138475867335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11834765130569517967823113 8876073847927138475867335)
          ·
            refine ⟨13314110771890707713801003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8876073847927138475867335 13314110771890707713801003)
            ·
              refine ⟨19971166157836061570701505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13314110771890707713801003 19971166157836061570701505)
              ·
                refine ⟨14978374618377046178026129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19971166157836061570701505 14978374618377046178026129)
                ·
                  refine ⟨11233780963782784633519597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14978374618377046178026129 11233780963782784633519597)
                  ·
                    refine ⟨4212667861418544237569849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11233780963782784633519597 4212667861418544237569849)
                    ·
                      refine ⟨3159500896063908178177387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4212667861418544237569849 3159500896063908178177387)
                      ·
                        rfl

theorem cell23_6153106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 2, 2, 3, 2].length) (baseStart_6153106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6153106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6153106 prefixEnd_6153106 := by exact prefixLift 6153106
  have htrace : WordTrace (prefixWord ++ tailWord_6153106) baseStart_6153106 baseEnd_6153106 := by
    simpa [prefixWord, tailWord_6153106, baseEnd_6153106] using wordTrace_append hprefix tailTrace_6153106
  have hstable : (prefixWord ++ tailWord_6153106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6153106).length < 2 ^ (prefixWord ++ tailWord_6153106).sum := by decide
  have hdescent : baseEnd_6153106 < baseStart_6153106 := by decide
  rcases family_descends (prefixWord ++ tailWord_6153106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6153122 : List Nat := [3, 3, 1, 2, 2, 1, 2, 2, 1, 1, 5]
def baseStart_6153122 : Nat := 118140960795 + 6153122 * 2 ^ 59
def prefixEnd_6153122 : Nat := 4983230072969 + 3 ^ 40 * 6153122 * 2
def baseEnd_6153122 : Nat := 3159509111754380115577313

theorem tailTrace_6153122 : CollatzResearch.WordTrace tailWord_6153122 prefixEnd_6153122 3159509111754380115577313 := by
  unfold tailWord_6153122
  simp only [CollatzResearch.WordTrace]
  refine ⟨56105699103574334604677405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149615197609531558945806413 56105699103574334604677405)
  ·
    refine ⟨21039637163840375476754027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56105699103574334604677405 21039637163840375476754027)
    ·
      refine ⟨31559455745760563215131041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21039637163840375476754027 31559455745760563215131041)
      ·
        refine ⟨23669591809320422411348281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31559455745760563215131041 23669591809320422411348281)
        ·
          refine ⟨17752193856990316808511211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23669591809320422411348281 17752193856990316808511211)
          ·
            refine ⟨26628290785485475212766817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17752193856990316808511211 26628290785485475212766817)
            ·
              refine ⟨19971218089114106409575113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26628290785485475212766817 19971218089114106409575113)
              ·
                refine ⟨14978413566835579807181335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19971218089114106409575113 14978413566835579807181335)
                ·
                  refine ⟨22467620350253369710772003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14978413566835579807181335 22467620350253369710772003)
                  ·
                    refine ⟨33701430525380054566158005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22467620350253369710772003 33701430525380054566158005)
                    ·
                      refine ⟨3159509111754380115577313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33701430525380054566158005 3159509111754380115577313)
                      ·
                        rfl

theorem cell23_6153122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_6153122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6153122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6153122 prefixEnd_6153122 := by exact prefixLift 6153122
  have htrace : WordTrace (prefixWord ++ tailWord_6153122) baseStart_6153122 baseEnd_6153122 := by
    simpa [prefixWord, tailWord_6153122, baseEnd_6153122] using wordTrace_append hprefix tailTrace_6153122
  have hstable : (prefixWord ++ tailWord_6153122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6153122).length < 2 ^ (prefixWord ++ tailWord_6153122).sum := by decide
  have hdescent : baseEnd_6153122 < baseStart_6153122 := by decide
  rcases family_descends (prefixWord ++ tailWord_6153122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6153133 : List Nat := [1, 5, 2, 3, 2, 1, 1, 2, 1, 5]
def baseStart_6153133 : Nat := 118140960795 + 6153133 * 2 ^ 59
def prefixEnd_6153133 : Nat := 4983230072969 + 3 ^ 40 * 6153133 * 2
def baseEnd_6153133 : Nat := 1053171586680526524179921

theorem tailTrace_6153133 : CollatzResearch.WordTrace tailWord_6153133 prefixEnd_6153133 1053171586680526524179921 := by
  unfold tailWord_6153133
  simp only [CollatzResearch.WordTrace]
  refine ⟨224423197617257487297360053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149615465078171658198240035 224423197617257487297360053)
  ·
    refine ⟨21039674776617889434127505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 224423197617257487297360053 21039674776617889434127505)
    ·
      refine ⟨15779756082463417075595629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21039674776617889434127505 15779756082463417075595629)
      ·
        refine ⟨5917408530923781403348361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15779756082463417075595629 5917408530923781403348361)
        ·
          refine ⟨4438056398192836052511271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5917408530923781403348361 4438056398192836052511271)
          ·
            refine ⟨6657084597289254078766907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4438056398192836052511271 6657084597289254078766907)
            ·
              refine ⟨9985626895933881118150361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6657084597289254078766907 9985626895933881118150361)
              ·
                refine ⟨7489220171950410838612771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9985626895933881118150361 7489220171950410838612771)
                ·
                  refine ⟨11233830257925616257919157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7489220171950410838612771 11233830257925616257919157)
                  ·
                    refine ⟨1053171586680526524179921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11233830257925616257919157 1053171586680526524179921)
                    ·
                      rfl

theorem cell23_6153133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 1, 2, 1, 5].length) (baseStart_6153133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6153133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6153133 prefixEnd_6153133 := by exact prefixLift 6153133
  have htrace : WordTrace (prefixWord ++ tailWord_6153133) baseStart_6153133 baseEnd_6153133 := by
    simpa [prefixWord, tailWord_6153133, baseEnd_6153133] using wordTrace_append hprefix tailTrace_6153133
  have hstable : (prefixWord ++ tailWord_6153133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6153133).length < 2 ^ (prefixWord ++ tailWord_6153133).sum := by decide
  have hdescent : baseEnd_6153133 < baseStart_6153133 := by decide
  rcases family_descends (prefixWord ++ tailWord_6153133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6153152 : List Nat := [2, 1, 1, 2, 3, 4, 1, 2, 1, 3, 3]
def baseStart_6153152 : Nat := 118140960795 + 6153152 * 2 ^ 59
def prefixEnd_6153152 : Nat := 4983230072969 + 3 ^ 40 * 6153152 * 2
def baseEnd_6153152 : Nat := 3159524516174014998202175

theorem tailTrace_6153152 : CollatzResearch.WordTrace tailWord_6153152 prefixEnd_6153152 3159524516174014998202175 := by
  unfold tailWord_6153152
  simp only [CollatzResearch.WordTrace]
  refine ⟨112211945302094326771150855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149615927069459102361534473 112211945302094326771150855)
  ·
    refine ⟨168317917953141490156726283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112211945302094326771150855 168317917953141490156726283)
    ·
      refine ⟨252476876929712235235089425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168317917953141490156726283 252476876929712235235089425)
      ·
        refine ⟨189357657697284176426317069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 252476876929712235235089425 189357657697284176426317069)
        ·
          refine ⟨71009121636481566159868901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 189357657697284176426317069 71009121636481566159868901)
          ·
            refine ⟨13314210306840293654975419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71009121636481566159868901 13314210306840293654975419)
            ·
              refine ⟨19971315460260440482463129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13314210306840293654975419 19971315460260440482463129)
              ·
                refine ⟨14978486595195330361847347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19971315460260440482463129 14978486595195330361847347)
                ·
                  refine ⟨22467729892792995542771021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14978486595195330361847347 22467729892792995542771021)
                  ·
                    refine ⟨8425398709797373328539133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22467729892792995542771021 8425398709797373328539133)
                    ·
                      refine ⟨3159524516174014998202175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8425398709797373328539133 3159524516174014998202175)
                      ·
                        rfl

theorem cell23_6153152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 2, 1, 3, 3].length) (baseStart_6153152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6153152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6153152 prefixEnd_6153152 := by exact prefixLift 6153152
  have htrace : WordTrace (prefixWord ++ tailWord_6153152) baseStart_6153152 baseEnd_6153152 := by
    simpa [prefixWord, tailWord_6153152, baseEnd_6153152] using wordTrace_append hprefix tailTrace_6153152
  have hstable : (prefixWord ++ tailWord_6153152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6153152).length < 2 ^ (prefixWord ++ tailWord_6153152).sum := by decide
  have hdescent : baseEnd_6153152 < baseStart_6153152 := by decide
  rcases family_descends (prefixWord ++ tailWord_6153152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6153156 : List Nat := [2, 3, 3, 3, 1, 2, 1, 1, 1, 1, 5]
def baseStart_6153156 : Nat := 118140960795 + 6153156 * 2 ^ 59
def prefixEnd_6153156 : Nat := 4983230072969 + 3 ^ 40 * 6153156 * 2
def baseEnd_6153156 : Nat := 3159526570096632982552157

theorem tailTrace_6153156 : CollatzResearch.WordTrace tailWord_6153156 prefixEnd_6153156 3159526570096632982552157 := by
  unfold tailWord_6153156
  simp only [CollatzResearch.WordTrace]
  refine ⟨112212018248087081112723661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149616024330782774816964881 112212018248087081112723661)
  ·
    refine ⟨42079506843032655417271373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112212018248087081112723661 42079506843032655417271373)
    ·
      refine ⟨15779815066137245781476765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42079506843032655417271373 15779815066137245781476765)
      ·
        refine ⟨5917430649801467168053787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15779815066137245781476765 5917430649801467168053787)
        ·
          refine ⟨8876145974702200752080681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5917430649801467168053787 8876145974702200752080681)
          ·
            refine ⟨6657109481026650564060511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8876145974702200752080681 6657109481026650564060511)
            ·
              refine ⟨9985664221539975846090767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6657109481026650564060511 9985664221539975846090767)
              ·
                refine ⟨14978496332309963769136151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9985664221539975846090767 14978496332309963769136151)
                ·
                  refine ⟨22467744498464945653704227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14978496332309963769136151 22467744498464945653704227)
                  ·
                    refine ⟨33701616747697418480556341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22467744498464945653704227 33701616747697418480556341)
                    ·
                      refine ⟨3159526570096632982552157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33701616747697418480556341 3159526570096632982552157)
                      ·
                        rfl

theorem cell23_6153156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_6153156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6153156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6153156 prefixEnd_6153156 := by exact prefixLift 6153156
  have htrace : WordTrace (prefixWord ++ tailWord_6153156) baseStart_6153156 baseEnd_6153156 := by
    simpa [prefixWord, tailWord_6153156, baseEnd_6153156] using wordTrace_append hprefix tailTrace_6153156
  have hstable : (prefixWord ++ tailWord_6153156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6153156).length < 2 ^ (prefixWord ++ tailWord_6153156).sum := by decide
  have hdescent : baseEnd_6153156 < baseStart_6153156 := by decide
  rcases family_descends (prefixWord ++ tailWord_6153156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6153169 : List Nat := [1, 2, 2, 1, 2, 1, 6, 2, 2, 1, 3]
def baseStart_6153169 : Nat := 118140960795 + 6153169 * 2 ^ 59
def prefixEnd_6153169 : Nat := 4983230072969 + 3 ^ 40 * 6153169 * 2
def baseEnd_6153169 : Nat := 3159533245345141431689597

theorem tailTrace_6153169 : CollatzResearch.WordTrace tailWord_6153169 prefixEnd_6153169 3159533245345141431689597 := by
  unfold tailWord_6153169
  simp only [CollatzResearch.WordTrace]
  refine ⟨224424510645127065445670561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149616340430084710297113707 224424510645127065445670561)
  ·
    refine ⟨168318382983845299084252921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224424510645127065445670561 168318382983845299084252921)
    ·
      refine ⟨126238787237883974313189691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168318382983845299084252921 126238787237883974313189691)
      ·
        refine ⟨189358180856825961469784537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126238787237883974313189691 189358180856825961469784537)
        ·
          refine ⟨142018635642619471102338403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189358180856825961469784537 142018635642619471102338403)
          ·
            refine ⟨213027953463929206653507605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142018635642619471102338403 213027953463929206653507605)
            ·
              refine ⟨9985685318621681561883169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 213027953463929206653507605 9985685318621681561883169)
              ·
                refine ⟨7489263988966261171412377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9985685318621681561883169 7489263988966261171412377)
                ·
                  refine ⟨5616947991724695878559283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7489263988966261171412377 5616947991724695878559283)
                  ·
                    refine ⟨8425421987587043817838925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5616947991724695878559283 8425421987587043817838925)
                    ·
                      refine ⟨3159533245345141431689597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8425421987587043817838925 3159533245345141431689597)
                      ·
                        rfl

theorem cell23_6153169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6, 2, 2, 1, 3].length) (baseStart_6153169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6153169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6153169 prefixEnd_6153169 := by exact prefixLift 6153169
  have htrace : WordTrace (prefixWord ++ tailWord_6153169) baseStart_6153169 baseEnd_6153169 := by
    simpa [prefixWord, tailWord_6153169, baseEnd_6153169] using wordTrace_append hprefix tailTrace_6153169
  have hstable : (prefixWord ++ tailWord_6153169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6153169).length < 2 ^ (prefixWord ++ tailWord_6153169).sum := by decide
  have hdescent : baseEnd_6153169 < baseStart_6153169 := by decide
  rcases family_descends (prefixWord ++ tailWord_6153169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6153170 : List Nat := [3, 2, 2, 3, 1, 1, 4, 2, 1, 2, 2]
def baseStart_6153170 : Nat := 118140960795 + 6153170 * 2 ^ 59
def prefixEnd_6153170 : Nat := 4983230072969 + 3 ^ 40 * 6153170 * 2
def baseEnd_6153170 : Nat := 3159533758825795927777093

theorem tailTrace_6153170 : CollatzResearch.WordTrace tailWord_6153170 prefixEnd_6153170 3159533758825795927777093 := by
  unfold tailWord_6153170
  simp only [CollatzResearch.WordTrace]
  refine ⟨56106136779530860654114241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149616364745415628410971309 56106136779530860654114241)
  ·
    refine ⟨42079602584648145490585681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56106136779530860654114241 42079602584648145490585681)
    ·
      refine ⟨31559701938486109117939261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42079602584648145490585681 31559701938486109117939261)
      ·
        refine ⟨11834888226932290919227223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31559701938486109117939261 11834888226932290919227223)
        ·
          refine ⟨17752332340398436378840835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11834888226932290919227223 17752332340398436378840835)
          ·
            refine ⟨26628498510597654568261253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17752332340398436378840835 26628498510597654568261253)
            ·
              refine ⟨4992843470737060231548985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26628498510597654568261253 4992843470737060231548985)
              ·
                refine ⟨3744632603052795173661739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4992843470737060231548985 3744632603052795173661739)
                ·
                  refine ⟨5616948904579192760492609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3744632603052795173661739 5616948904579192760492609)
                  ·
                    refine ⟨4212711678434394570369457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5616948904579192760492609 4212711678434394570369457)
                    ·
                      refine ⟨3159533758825795927777093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4212711678434394570369457 3159533758825795927777093)
                      ·
                        rfl

theorem cell23_6153170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 4, 2, 1, 2, 2].length) (baseStart_6153170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6153170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6153170 prefixEnd_6153170 := by exact prefixLift 6153170
  have htrace : WordTrace (prefixWord ++ tailWord_6153170) baseStart_6153170 baseEnd_6153170 := by
    simpa [prefixWord, tailWord_6153170, baseEnd_6153170] using wordTrace_append hprefix tailTrace_6153170
  have hstable : (prefixWord ++ tailWord_6153170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6153170).length < 2 ^ (prefixWord ++ tailWord_6153170).sum := by decide
  have hdescent : baseEnd_6153170 < baseStart_6153170 := by decide
  rcases family_descends (prefixWord ++ tailWord_6153170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6153186 : List Nat := [3, 3, 3, 1, 1, 2, 2, 1, 1, 3, 3]
def baseStart_6153186 : Nat := 118140960795 + 6153186 * 2 ^ 59
def prefixEnd_6153186 : Nat := 4983230072969 + 3 ^ 40 * 6153186 * 2
def baseEnd_6153186 : Nat := 3159541974516267865177019

theorem tailTrace_6153186 : CollatzResearch.WordTrace tailWord_6153186 prefixEnd_6153186 3159541974516267865177019 := by
  unfold tailWord_6153186
  simp only [CollatzResearch.WordTrace]
  refine ⟨56106282671516369337259853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149616753790710318232692941 56106282671516369337259853)
  ·
    refine ⟨21039856001818638501472445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56106282671516369337259853 21039856001818638501472445)
    ·
      refine ⟨7889946000681989438052167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21039856001818638501472445 7889946000681989438052167)
      ·
        refine ⟨11834919001022984157078251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7889946000681989438052167 11834919001022984157078251)
        ·
          refine ⟨17752378501534476235617377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11834919001022984157078251 17752378501534476235617377)
          ·
            refine ⟨13314283876150857176713033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17752378501534476235617377 13314283876150857176713033)
            ·
              refine ⟨9985712907113142882534775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13314283876150857176713033 9985712907113142882534775)
              ·
                refine ⟨14978569360669714323802163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9985712907113142882534775 14978569360669714323802163)
                ·
                  refine ⟨22467854041004571485703245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14978569360669714323802163 22467854041004571485703245)
                  ·
                    refine ⟨8425445265376714307138717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22467854041004571485703245 8425445265376714307138717)
                    ·
                      refine ⟨3159541974516267865177019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8425445265376714307138717 3159541974516267865177019)
                      ·
                        rfl

theorem cell23_6153186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_6153186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6153186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6153186 prefixEnd_6153186 := by exact prefixLift 6153186
  have htrace : WordTrace (prefixWord ++ tailWord_6153186) baseStart_6153186 baseEnd_6153186 := by
    simpa [prefixWord, tailWord_6153186, baseEnd_6153186] using wordTrace_append hprefix tailTrace_6153186
  have hstable : (prefixWord ++ tailWord_6153186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6153186).length < 2 ^ (prefixWord ++ tailWord_6153186).sum := by decide
  have hdescent : baseEnd_6153186 < baseStart_6153186 := by decide
  rcases family_descends (prefixWord ++ tailWord_6153186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6153204 : List Nat := [2, 6, 2, 1, 2, 1, 2, 1, 1, 1, 4]
def baseStart_6153204 : Nat := 118140960795 + 6153204 * 2 ^ 59
def prefixEnd_6153204 : Nat := 4983230072969 + 3 ^ 40 * 6153204 * 2
def baseEnd_6153204 : Nat := 3159551217168048794751937

theorem tailTrace_6153204 : CollatzResearch.WordTrace tailWord_6153204 prefixEnd_6153204 3159551217168048794751937 := by
  unfold tailWord_6153204
  simp only [CollatzResearch.WordTrace]
  refine ⟨112212893600000133211597333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149617191466666844282129777 112212893600000133211597333)
  ·
    refine ⟨5259979387500006244293625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 112212893600000133211597333 5259979387500006244293625)
    ·
      refine ⟨3944984540625004683220219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5259979387500006244293625 3944984540625004683220219)
      ·
        refine ⟨5917476810937507024830329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3944984540625004683220219 5917476810937507024830329)
        ·
          refine ⟨4438107608203130268622747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5917476810937507024830329 4438107608203130268622747)
          ·
            refine ⟨6657161412304695402934121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4438107608203130268622747 6657161412304695402934121)
            ·
              refine ⟨4992871059228521552200591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6657161412304695402934121 4992871059228521552200591)
              ·
                refine ⟨7489306588842782328300887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4992871059228521552200591 7489306588842782328300887)
                ·
                  refine ⟨11233959883264173492451331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7489306588842782328300887 11233959883264173492451331)
                  ·
                    refine ⟨16850939824896260238676997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11233959883264173492451331 16850939824896260238676997)
                    ·
                      refine ⟨3159551217168048794751937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16850939824896260238676997 3159551217168048794751937)
                      ·
                        rfl

theorem cell23_6153204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_6153204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6153204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6153204 prefixEnd_6153204 := by exact prefixLift 6153204
  have htrace : WordTrace (prefixWord ++ tailWord_6153204) baseStart_6153204 baseEnd_6153204 := by
    simpa [prefixWord, tailWord_6153204, baseEnd_6153204] using wordTrace_append hprefix tailTrace_6153204
  have hstable : (prefixWord ++ tailWord_6153204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6153204).length < 2 ^ (prefixWord ++ tailWord_6153204).sum := by decide
  have hdescent : baseEnd_6153204 < baseStart_6153204 := by decide
  rcases family_descends (prefixWord ++ tailWord_6153204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6153209 : List Nat := [1, 2, 1, 3, 1, 3, 2, 2, 4, 2, 2]
def baseStart_6153209 : Nat := 118140960795 + 6153209 * 2 ^ 59
def prefixEnd_6153209 : Nat := 4983230072969 + 3 ^ 40 * 6153209 * 2
def baseEnd_6153209 : Nat := 3159553784571321275189413

theorem tailTrace_6153209 : CollatzResearch.WordTrace tailWord_6153209 prefixEnd_6153209 3159553784571321275189413 := by
  unfold tailWord_6153209
  simp only [CollatzResearch.WordTrace]
  refine ⟨224425969564982152277126681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149617313043321434851417787 224425969564982152277126681)
  ·
    refine ⟨168319477173736614207845011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224425969564982152277126681 168319477173736614207845011)
    ·
      refine ⟨252479215760604921311767517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168319477173736614207845011 252479215760604921311767517)
      ·
        refine ⟨94679705910226845491912819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 252479215760604921311767517 94679705910226845491912819)
        ·
          refine ⟨142019558865340268237869229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94679705910226845491912819 142019558865340268237869229)
          ·
            refine ⟨53257334574502600589200961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 142019558865340268237869229 53257334574502600589200961)
            ·
              refine ⟨39943000930876950441900721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53257334574502600589200961 39943000930876950441900721)
              ·
                refine ⟨29957250698157712831425541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39943000930876950441900721 29957250698157712831425541)
                ·
                  refine ⟨5616984505904571155892289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29957250698157712831425541 5616984505904571155892289)
                  ·
                    refine ⟨4212738379428428366919217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5616984505904571155892289 4212738379428428366919217)
                    ·
                      refine ⟨3159553784571321275189413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4212738379428428366919217 3159553784571321275189413)
                      ·
                        rfl

theorem cell23_6153209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 2, 4, 2, 2].length) (baseStart_6153209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6153209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6153209 prefixEnd_6153209 := by exact prefixLift 6153209
  have htrace : WordTrace (prefixWord ++ tailWord_6153209) baseStart_6153209 baseEnd_6153209 := by
    simpa [prefixWord, tailWord_6153209, baseEnd_6153209] using wordTrace_append hprefix tailTrace_6153209
  have hstable : (prefixWord ++ tailWord_6153209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6153209).length < 2 ^ (prefixWord ++ tailWord_6153209).sum := by decide
  have hdescent : baseEnd_6153209 < baseStart_6153209 := by decide
  rcases family_descends (prefixWord ++ tailWord_6153209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6153226 : List Nat := [3, 1, 2, 2, 3, 2, 1, 1, 4, 2, 2]
def baseStart_6153226 : Nat := 118140960795 + 6153226 * 2 ^ 59
def prefixEnd_6153226 : Nat := 4983230072969 + 3 ^ 40 * 6153226 * 2
def baseEnd_6153226 : Nat := 3159562513742447708676835

theorem tailTrace_6153226 : CollatzResearch.WordTrace tailWord_6153226 prefixEnd_6153226 3159562513742447708676835 := by
  unfold tailWord_6153226
  simp only [CollatzResearch.WordTrace]
  refine ⟨56106647401480141045123883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149617726403947042786997021 56106647401480141045123883)
  ·
    refine ⟨84159971102220211567685825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56106647401480141045123883 84159971102220211567685825)
    ·
      refine ⟨63119978326665158675764369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84159971102220211567685825 63119978326665158675764369)
      ·
        refine ⟨47339983744998869006823277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63119978326665158675764369 47339983744998869006823277)
        ·
          refine ⟨17752493904374575877558729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47339983744998869006823277 17752493904374575877558729)
          ·
            refine ⟨13314370428280931908169047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17752493904374575877558729 13314370428280931908169047)
            ·
              refine ⟨19971555642421397862253571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13314370428280931908169047 19971555642421397862253571)
              ·
                refine ⟨29957333463632096793380357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19971555642421397862253571 29957333463632096793380357)
                ·
                  refine ⟨5617000024431018148758817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29957333463632096793380357 5617000024431018148758817)
                  ·
                    refine ⟨4212750018323263611569113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5617000024431018148758817 4212750018323263611569113)
                    ·
                      refine ⟨3159562513742447708676835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4212750018323263611569113 3159562513742447708676835)
                      ·
                        rfl

theorem cell23_6153226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 1, 4, 2, 2].length) (baseStart_6153226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6153226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6153226 prefixEnd_6153226 := by exact prefixLift 6153226
  have htrace : WordTrace (prefixWord ++ tailWord_6153226) baseStart_6153226 baseEnd_6153226 := by
    simpa [prefixWord, tailWord_6153226, baseEnd_6153226] using wordTrace_append hprefix tailTrace_6153226
  have hstable : (prefixWord ++ tailWord_6153226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6153226).length < 2 ^ (prefixWord ++ tailWord_6153226).sum := by decide
  have hdescent : baseEnd_6153226 < baseStart_6153226 := by decide
  rcases family_descends (prefixWord ++ tailWord_6153226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6153242 : List Nat := [3, 1, 1, 3, 1, 2, 1, 3, 2, 3, 3]
def baseStart_6153242 : Nat := 118140960795 + 6153242 * 2 ^ 59
def prefixEnd_6153242 : Nat := 4983230072969 + 3 ^ 40 * 6153242 * 2
def baseEnd_6153242 : Nat := 3159570729432919646076761

theorem tailTrace_6153242 : CollatzResearch.WordTrace tailWord_6153242 prefixEnd_6153242 3159570729432919646076761 := by
  unfold tailWord_6153242
  simp only [CollatzResearch.WordTrace]
  refine ⟨56106793293465649728269495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149618115449241732608718653 56106793293465649728269495)
  ·
    refine ⟨84160189940198474592404243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56106793293465649728269495 84160189940198474592404243)
    ·
      refine ⟨126240284910297711888606365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84160189940198474592404243 126240284910297711888606365)
      ·
        refine ⟨47340106841361641958227387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126240284910297711888606365 47340106841361641958227387)
        ·
          refine ⟨71010160262042462937341081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47340106841361641958227387 71010160262042462937341081)
          ·
            refine ⟨53257620196531847203005811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71010160262042462937341081 53257620196531847203005811)
            ·
              refine ⟨79886430294797770804508717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53257620196531847203005811 79886430294797770804508717)
              ·
                refine ⟨29957411360549164051690769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79886430294797770804508717 29957411360549164051690769)
                ·
                  refine ⟨22468058520411873038768077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29957411360549164051690769 22468058520411873038768077)
                  ·
                    refine ⟨8425521945154452389538029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22468058520411873038768077 8425521945154452389538029)
                    ·
                      refine ⟨3159570729432919646076761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8425521945154452389538029 3159570729432919646076761)
                      ·
                        rfl

theorem cell23_6153242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 3, 2, 3, 3].length) (baseStart_6153242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6153242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6153242 prefixEnd_6153242 := by exact prefixLift 6153242
  have htrace : WordTrace (prefixWord ++ tailWord_6153242) baseStart_6153242 baseEnd_6153242 := by
    simpa [prefixWord, tailWord_6153242, baseEnd_6153242] using wordTrace_append hprefix tailTrace_6153242
  have hstable : (prefixWord ++ tailWord_6153242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6153242).length < 2 ^ (prefixWord ++ tailWord_6153242).sum := by decide
  have hdescent : baseEnd_6153242 < baseStart_6153242 := by decide
  rcases family_descends (prefixWord ++ tailWord_6153242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6153262 : List Nat := [4, 1, 3, 1, 1, 1, 1, 3, 1, 7]
def baseStart_6153262 : Nat := 118140960795 + 6153262 * 2 ^ 59
def prefixEnd_6153262 : Nat := 4983230072969 + 3 ^ 40 * 6153262 * 2
def baseEnd_6153262 : Nat := 1053193666348669855942223

theorem tailTrace_6153262 : CollatzResearch.WordTrace tailWord_6153262 prefixEnd_6153262 1053193666348669855942223 := by
  unfold tailWord_6153262
  simp only [CollatzResearch.WordTrace]
  refine ⟨28053487829223767791100755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149618601755860094885870693 28053487829223767791100755)
  ·
    refine ⟨42080231743835651686651133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28053487829223767791100755 42080231743835651686651133)
    ·
      refine ⟨15780086903938369382494175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42080231743835651686651133 15780086903938369382494175)
      ·
        refine ⟨23670130355907554073741263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15780086903938369382494175 23670130355907554073741263)
        ·
          refine ⟨35505195533861331110611895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23670130355907554073741263 35505195533861331110611895)
          ·
            refine ⟨53257793300791996665917843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35505195533861331110611895 53257793300791996665917843)
            ·
              refine ⟨79886689951187994998876765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53257793300791996665917843 79886689951187994998876765)
              ·
                refine ⟨29957508731695498124578787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79886689951187994998876765 29957508731695498124578787)
                ·
                  refine ⟨44936263097543247186868181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29957508731695498124578787 44936263097543247186868181)
                  ·
                    refine ⟨1053193666348669855942223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44936263097543247186868181 1053193666348669855942223)
                    ·
                      rfl

theorem cell23_6153262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_6153262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6153262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6153262 prefixEnd_6153262 := by exact prefixLift 6153262
  have htrace : WordTrace (prefixWord ++ tailWord_6153262) baseStart_6153262 baseEnd_6153262 := by
    simpa [prefixWord, tailWord_6153262, baseEnd_6153262] using wordTrace_append hprefix tailTrace_6153262
  have hstable : (prefixWord ++ tailWord_6153262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6153262).length < 2 ^ (prefixWord ++ tailWord_6153262).sum := by decide
  have hdescent : baseEnd_6153262 < baseStart_6153262 := by decide
  rcases family_descends (prefixWord ++ tailWord_6153262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6153305 : List Nat := [1, 2, 1, 2, 2, 1, 2, 2, 10]
def baseStart_6153305 : Nat := 118140960795 + 6153305 * 2 ^ 59
def prefixEnd_6153305 : Nat := 4983230072969 + 3 ^ 40 * 6153305 * 2
def baseEnd_6153305 : Nat := 351067008746016988843219

theorem tailTrace_6153305 : CollatzResearch.WordTrace tailWord_6153305 prefixEnd_6153305 351067008746016988843219 := by
  unfold tailWord_6153305
  simp only [CollatzResearch.WordTrace]
  refine ⟨224429470972634360672621369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149619647315089573781747579 224429470972634360672621369)
  ·
    refine ⟨168322103229475770504466027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224429470972634360672621369 168322103229475770504466027)
    ·
      refine ⟨252483154844213655756699041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168322103229475770504466027 252483154844213655756699041)
      ·
        refine ⟨189362366133160241817524281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 252483154844213655756699041 189362366133160241817524281)
        ·
          refine ⟨142021774599870181363143211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189362366133160241817524281 142021774599870181363143211)
          ·
            refine ⟨213032661899805272044714817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142021774599870181363143211 213032661899805272044714817)
            ·
              refine ⟨159774496424853954033536113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 213032661899805272044714817 159774496424853954033536113)
              ·
                refine ⟨119830872318640465525152085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 159774496424853954033536113 119830872318640465525152085)
                ·
                  refine ⟨351067008746016988843219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 119830872318640465525152085 351067008746016988843219)
                  ·
                    rfl

theorem cell23_6153305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 10].length) (baseStart_6153305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6153305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6153305 prefixEnd_6153305 := by exact prefixLift 6153305
  have htrace : WordTrace (prefixWord ++ tailWord_6153305) baseStart_6153305 baseEnd_6153305 := by
    simpa [prefixWord, tailWord_6153305, baseEnd_6153305] using wordTrace_append hprefix tailTrace_6153305
  have hstable : (prefixWord ++ tailWord_6153305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6153305).length < 2 ^ (prefixWord ++ tailWord_6153305).sum := by decide
  have hdescent : baseEnd_6153305 < baseStart_6153305 := by decide
  rcases family_descends (prefixWord ++ tailWord_6153305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6153319 : List Nat := [1, 1, 5, 1, 1, 3, 1, 3, 2, 2, 3]
def baseStart_6153319 : Nat := 118140960795 + 6153319 * 2 ^ 59
def prefixEnd_6153319 : Nat := 4983230072969 + 3 ^ 40 * 6153319 * 2
def baseEnd_6153319 : Nat := 3159610267443315844813907

theorem tailTrace_6153319 : CollatzResearch.WordTrace tailWord_6153319 prefixEnd_6153319 3159610267443315844813907 := by
  unfold tailWord_6153319
  simp only [CollatzResearch.WordTrace]
  refine ⟨224429981594583641063631011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149619987729722427375754007 224429981594583641063631011)
  ·
    refine ⟨336644972391875461595446517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224429981594583641063631011 336644972391875461595446517)
    ·
      refine ⟨31560466161738324524573111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 336644972391875461595446517 31560466161738324524573111)
      ·
        refine ⟨47340699242607486786859667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31560466161738324524573111 47340699242607486786859667)
        ·
          refine ⟨71011048863911230180289501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47340699242607486786859667 71011048863911230180289501)
          ·
            refine ⟨26629143323966711317608563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71011048863911230180289501 26629143323966711317608563)
            ·
              refine ⟨39943714985950066976412845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26629143323966711317608563 39943714985950066976412845)
              ·
                refine ⟨14978893119731275116154817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39943714985950066976412845 14978893119731275116154817)
                ·
                  refine ⟨11234169839798456337116113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14978893119731275116154817 11234169839798456337116113)
                  ·
                    refine ⟨8425627379848842252837085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11234169839798456337116113 8425627379848842252837085)
                    ·
                      refine ⟨3159610267443315844813907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8425627379848842252837085 3159610267443315844813907)
                      ·
                        rfl

theorem cell23_6153319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 3, 2, 2, 3].length) (baseStart_6153319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6153319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6153319 prefixEnd_6153319 := by exact prefixLift 6153319
  have htrace : WordTrace (prefixWord ++ tailWord_6153319) baseStart_6153319 baseEnd_6153319 := by
    simpa [prefixWord, tailWord_6153319, baseEnd_6153319] using wordTrace_append hprefix tailTrace_6153319
  have hstable : (prefixWord ++ tailWord_6153319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6153319).length < 2 ^ (prefixWord ++ tailWord_6153319).sum := by decide
  have hdescent : baseEnd_6153319 < baseStart_6153319 := by decide
  rcases family_descends (prefixWord ++ tailWord_6153319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6153399 : List Nat := [1, 1, 3, 1, 4, 1, 3, 1, 4, 4]
def baseStart_6153399 : Nat := 118140960795 + 6153399 * 2 ^ 59
def prefixEnd_6153399 : Nat := 4983230072969 + 3 ^ 40 * 6153399 * 2
def baseEnd_6153399 : Nat := 1053217115298558510604513

theorem tailTrace_6153399 : CollatzResearch.WordTrace tailWord_6153399 prefixEnd_6153399 1053217115298558510604513 := by
  unfold tailWord_6153399
  simp only [CollatzResearch.WordTrace]
  refine ⟨224432899434293814726543251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149621932956195876484362167 224432899434293814726543251)
  ·
    refine ⟨336649349151440722089814877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224432899434293814726543251 336649349151440722089814877)
    ·
      refine ⟨126243505931790270783680579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 336649349151440722089814877 126243505931790270783680579)
      ·
        refine ⟨189365258897685406175520869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126243505931790270783680579 189365258897685406175520869)
        ·
          refine ⟨35505986043316013657910163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 189365258897685406175520869 35505986043316013657910163)
          ·
            refine ⟨53258979064974020486865245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35505986043316013657910163 53258979064974020486865245)
            ·
              refine ⟨19972117149365257682574467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53258979064974020486865245 19972117149365257682574467)
              ·
                refine ⟨29958175724047886523861701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19972117149365257682574467 29958175724047886523861701)
                ·
                  refine ⟨5617157948258978723224069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29958175724047886523861701 5617157948258978723224069)
                  ·
                    refine ⟨1053217115298558510604513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5617157948258978723224069 1053217115298558510604513)
                    ·
                      rfl

theorem cell23_6153399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 1, 4, 4].length) (baseStart_6153399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6153399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6153399 prefixEnd_6153399 := by exact prefixLift 6153399
  have htrace : WordTrace (prefixWord ++ tailWord_6153399) baseStart_6153399 baseEnd_6153399 := by
    simpa [prefixWord, tailWord_6153399, baseEnd_6153399] using wordTrace_append hprefix tailTrace_6153399
  have hstable : (prefixWord ++ tailWord_6153399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6153399).length < 2 ^ (prefixWord ++ tailWord_6153399).sum := by decide
  have hdescent : baseEnd_6153399 < baseStart_6153399 := by decide
  rcases family_descends (prefixWord ++ tailWord_6153399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6153402 : List Nat := [3, 1, 1, 1, 2, 2, 1, 4, 1, 1, 6]
def baseStart_6153402 : Nat := 118140960795 + 6153402 * 2 ^ 59
def prefixEnd_6153402 : Nat := 4983230072969 + 3 ^ 40 * 6153402 * 2
def baseEnd_6153402 : Nat := 3159652886337639020076025

theorem tailTrace_6153402 : CollatzResearch.WordTrace tailWord_6153402 prefixEnd_6153402 3159652886337639020076025 := by
  unfold tailWord_6153402
  simp only [CollatzResearch.WordTrace]
  refine ⟨56108252213320736559725615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149622005902188630825934973 56108252213320736559725615)
  ·
    refine ⟨84162378319981104839588423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56108252213320736559725615 84162378319981104839588423)
    ·
      refine ⟨126243567479971657259382635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84162378319981104839588423 126243567479971657259382635)
      ·
        refine ⟨189365351219957485889073953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126243567479971657259382635 189365351219957485889073953)
        ·
          refine ⟨142024013414968114416805465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189365351219957485889073953 142024013414968114416805465)
          ·
            refine ⟨106518010061226085812604099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142024013414968114416805465 106518010061226085812604099)
            ·
              refine ⟨159777015091839128718906149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106518010061226085812604099 159777015091839128718906149)
              ·
                refine ⟨29958190329719836634794903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 159777015091839128718906149 29958190329719836634794903)
                ·
                  refine ⟨44937285494579754952192355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29958190329719836634794903 44937285494579754952192355)
                  ·
                    refine ⟨67405928241869632428288533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44937285494579754952192355 67405928241869632428288533)
                    ·
                      refine ⟨3159652886337639020076025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67405928241869632428288533 3159652886337639020076025)
                      ·
                        rfl

theorem cell23_6153402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 4, 1, 1, 6].length) (baseStart_6153402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6153402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6153402 prefixEnd_6153402 := by exact prefixLift 6153402
  have htrace : WordTrace (prefixWord ++ tailWord_6153402) baseStart_6153402 baseEnd_6153402 := by
    simpa [prefixWord, tailWord_6153402, baseEnd_6153402] using wordTrace_append hprefix tailTrace_6153402
  have hstable : (prefixWord ++ tailWord_6153402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6153402).length < 2 ^ (prefixWord ++ tailWord_6153402).sum := by decide
  have hdescent : baseEnd_6153402 < baseStart_6153402 := by decide
  rcases family_descends (prefixWord ++ tailWord_6153402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6153429 : List Nat := [1, 3, 2, 4, 1, 2, 1, 9]
def baseStart_6153429 : Nat := 118140960795 + 6153429 * 2 ^ 59
def prefixEnd_6153429 : Nat := 4983230072969 + 3 ^ 40 * 6153429 * 2
def baseEnd_6153429 : Nat := 117024694456122607942163

theorem tailTrace_6153429 : CollatzResearch.WordTrace tailWord_6153429 prefixEnd_6153429 117024694456122607942163 := by
  unfold tailWord_6153429
  simp only [CollatzResearch.WordTrace]
  refine ⟨224433993624185129850135341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149622662416123419900090227 224433993624185129850135341)
  ·
    refine ⟨84162747609069423693800753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 224433993624185129850135341 84162747609069423693800753)
    ·
      refine ⟨63122060706802067770350565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84162747609069423693800753 63122060706802067770350565)
      ·
        refine ⟨11835386382525387706940731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63122060706802067770350565 11835386382525387706940731)
        ·
          refine ⟨17753079573788081560411097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11835386382525387706940731 17753079573788081560411097)
          ·
            refine ⟨13314809680341061170308323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17753079573788081560411097 13314809680341061170308323)
            ·
              refine ⟨19972214520511591755462485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13314809680341061170308323 19972214520511591755462485)
              ·
                refine ⟨117024694456122607942163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19972214520511591755462485 117024694456122607942163)
                ·
                  rfl

theorem cell23_6153429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 9].length) (baseStart_6153429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6153429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6153429 prefixEnd_6153429 := by exact prefixLift 6153429
  have htrace : WordTrace (prefixWord ++ tailWord_6153429) baseStart_6153429 baseEnd_6153429 := by
    simpa [prefixWord, tailWord_6153429, baseEnd_6153429] using wordTrace_append hprefix tailTrace_6153429
  have hstable : (prefixWord ++ tailWord_6153429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6153429).length < 2 ^ (prefixWord ++ tailWord_6153429).sum := by decide
  have hdescent : baseEnd_6153429 < baseStart_6153429 := by decide
  rcases family_descends (prefixWord ++ tailWord_6153429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6153439 : List Nat := [1, 1, 2, 3, 2, 1, 2, 4, 1, 3, 3]
def baseStart_6153439 : Nat := 118140960795 + 6153439 * 2 ^ 59
def prefixEnd_6153439 : Nat := 4983230072969 + 3 ^ 40 * 6153439 * 2
def baseEnd_6153439 : Nat := 3159671885121855375313355

theorem tailTrace_6153439 : CollatzResearch.WordTrace tailWord_6153439 prefixEnd_6153439 3159671885121855375313355 := by
  unfold tailWord_6153439
  simp only [CollatzResearch.WordTrace]
  refine ⟨224434358354148901557999371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149622905569432601038666247 224434358354148901557999371)
  ·
    refine ⟨336651537531223352336999057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224434358354148901557999371 336651537531223352336999057)
    ·
      refine ⟨252488653148417514252749293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 336651537531223352336999057 252488653148417514252749293)
      ·
        refine ⟨94683244930656567844780985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 252488653148417514252749293 94683244930656567844780985)
        ·
          refine ⟨71012433697992425883585739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94683244930656567844780985 71012433697992425883585739)
          ·
            refine ⟨106518650546988638825378609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71012433697992425883585739 106518650546988638825378609)
            ·
              refine ⟨79888987910241479119033957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106518650546988638825378609 79888987910241479119033957)
              ·
                refine ⟨14979185233170277334818867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 79888987910241479119033957 14979185233170277334818867)
                ·
                  refine ⟨22468777849755416002228301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14979185233170277334818867 22468777849755416002228301)
                  ·
                    refine ⟨8425791693658281000835613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22468777849755416002228301 8425791693658281000835613)
                    ·
                      refine ⟨3159671885121855375313355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8425791693658281000835613 3159671885121855375313355)
                      ·
                        rfl

theorem cell23_6153439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 4, 1, 3, 3].length) (baseStart_6153439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6153439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6153439 prefixEnd_6153439 := by exact prefixLift 6153439
  have htrace : WordTrace (prefixWord ++ tailWord_6153439) baseStart_6153439 baseEnd_6153439 := by
    simpa [prefixWord, tailWord_6153439, baseEnd_6153439] using wordTrace_append hprefix tailTrace_6153439
  have hstable : (prefixWord ++ tailWord_6153439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6153439).length < 2 ^ (prefixWord ++ tailWord_6153439).sum := by decide
  have hdescent : baseEnd_6153439 < baseStart_6153439 := by decide
  rcases family_descends (prefixWord ++ tailWord_6153439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6153440 : List Nat := [2, 1, 1, 3, 1, 4, 3, 3, 1, 2, 2]
def baseStart_6153440 : Nat := 118140960795 + 6153440 * 2 ^ 59
def prefixEnd_6153440 : Nat := 4983230072969 + 3 ^ 40 * 6153440 * 2
def baseEnd_6153440 : Nat := 3159672398602509871400851

theorem tailTrace_6153440 : CollatzResearch.WordTrace tailWord_6153440 prefixEnd_6153440 3159672398602509871400851 := by
  unfold tailWord_6153440
  simp only [CollatzResearch.WordTrace]
  refine ⟨112217197413572639364392887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149622929884763519152523849 112217197413572639364392887)
  ·
    refine ⟨168325796120358959046589331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112217197413572639364392887 168325796120358959046589331)
    ·
      refine ⟨252488694180538438569883997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168325796120358959046589331 252488694180538438569883997)
      ·
        refine ⟨94683260317701914463706499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 252488694180538438569883997 94683260317701914463706499)
        ·
          refine ⟨142024890476552871695559749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94683260317701914463706499 142024890476552871695559749)
          ·
            refine ⟨26629666964353663442917453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 142024890476552871695559749 26629666964353663442917453)
            ·
              refine ⟨9986125111632623791094045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26629666964353663442917453 9986125111632623791094045)
              ·
                refine ⟨3744796916862233921660267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9986125111632623791094045 3744796916862233921660267)
                ·
                  refine ⟨5617195375293350882490401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3744796916862233921660267 5617195375293350882490401)
                  ·
                    refine ⟨4212896531470013161867801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5617195375293350882490401 4212896531470013161867801)
                    ·
                      refine ⟨3159672398602509871400851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4212896531470013161867801 3159672398602509871400851)
                      ·
                        rfl

theorem cell23_6153440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3, 3, 1, 2, 2].length) (baseStart_6153440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6153440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6153440 prefixEnd_6153440 := by exact prefixLift 6153440
  have htrace : WordTrace (prefixWord ++ tailWord_6153440) baseStart_6153440 baseEnd_6153440 := by
    simpa [prefixWord, tailWord_6153440, baseEnd_6153440] using wordTrace_append hprefix tailTrace_6153440
  have hstable : (prefixWord ++ tailWord_6153440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6153440).length < 2 ^ (prefixWord ++ tailWord_6153440).sum := by decide
  have hdescent : baseEnd_6153440 < baseStart_6153440 := by decide
  rcases family_descends (prefixWord ++ tailWord_6153440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6153466 : List Nat := [3, 1, 1, 1, 1, 4, 2, 2, 3, 3, 2]
def baseStart_6153466 : Nat := 118140960795 + 6153466 * 2 ^ 59
def prefixEnd_6153466 : Nat := 4983230072969 + 3 ^ 40 * 6153466 * 2
def baseEnd_6153466 : Nat := 3159685749099526769675731

theorem tailTrace_6153466 : CollatzResearch.WordTrace tailWord_6153466 prefixEnd_6153466 3159685749099526769675731 := by
  unfold tailWord_6153466
  simp only [CollatzResearch.WordTrace]
  refine ⟨56108835781262771292308063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149623562083367390112821501 56108835781262771292308063)
  ·
    refine ⟨84163253671894156938462095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56108835781262771292308063 84163253671894156938462095)
    ·
      refine ⟨126244880507841235407693143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84163253671894156938462095 126244880507841235407693143)
      ·
        refine ⟨189367320761761853111539715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126244880507841235407693143 189367320761761853111539715)
        ·
          refine ⟨284050981142642779667309573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189367320761761853111539715 284050981142642779667309573)
          ·
            refine ⟨53259558964245521187620545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 284050981142642779667309573 53259558964245521187620545)
            ·
              refine ⟨39944669223184140890715409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53259558964245521187620545 39944669223184140890715409)
              ·
                refine ⟨29958501917388105668036557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39944669223184140890715409 29958501917388105668036557)
                ·
                  refine ⟨11234438219020539625513709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29958501917388105668036557 11234438219020539625513709)
                  ·
                    refine ⟨4212914332132702359567641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11234438219020539625513709 4212914332132702359567641)
                    ·
                      refine ⟨3159685749099526769675731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4212914332132702359567641 3159685749099526769675731)
                      ·
                        rfl

theorem cell23_6153466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 2, 3, 3, 2].length) (baseStart_6153466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6153466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6153466 prefixEnd_6153466 := by exact prefixLift 6153466
  have htrace : WordTrace (prefixWord ++ tailWord_6153466) baseStart_6153466 baseEnd_6153466 := by
    simpa [prefixWord, tailWord_6153466, baseEnd_6153466] using wordTrace_append hprefix tailTrace_6153466
  have hstable : (prefixWord ++ tailWord_6153466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6153466).length < 2 ^ (prefixWord ++ tailWord_6153466).sum := by decide
  have hdescent : baseEnd_6153466 < baseStart_6153466 := by decide
  rcases family_descends (prefixWord ++ tailWord_6153466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6153472 : List Nat := [2, 1, 1, 2, 1, 1, 3, 3, 1, 8]
def baseStart_6153472 : Nat := 118140960795 + 6153472 * 2 ^ 59
def prefixEnd_6153472 : Nat := 4983230072969 + 3 ^ 40 * 6153472 * 2
def baseEnd_6153472 : Nat := 1053229609994484582066901

theorem tailTrace_6153472 : CollatzResearch.WordTrace tailWord_6153472 prefixEnd_6153472 1053229609994484582066901 := by
  unfold tailWord_6153472
  simp only [CollatzResearch.WordTrace]
  refine ⟨112217780981514674096975335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149623707975352898795967113 112217780981514674096975335)
  ·
    refine ⟨168326671472272011145463003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112217780981514674096975335 168326671472272011145463003)
    ·
      refine ⟨252490007208408016718194505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168326671472272011145463003 252490007208408016718194505)
      ·
        refine ⟨189367505406306012538645879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 252490007208408016718194505 189367505406306012538645879)
        ·
          refine ⟨284051258109459018807968819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189367505406306012538645879 284051258109459018807968819)
          ·
            refine ⟨426076887164188528211953229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 284051258109459018807968819 426076887164188528211953229)
            ·
              refine ⟨159778832686570698079482461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 426076887164188528211953229 159778832686570698079482461)
              ·
                refine ⟨59917062257464011779805923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 159778832686570698079482461 59917062257464011779805923)
                ·
                  refine ⟨89875593386196017669708885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59917062257464011779805923 89875593386196017669708885)
                  ·
                    refine ⟨1053229609994484582066901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 89875593386196017669708885 1053229609994484582066901)
                    ·
                      rfl

theorem cell23_6153472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 3, 1, 8].length) (baseStart_6153472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6153472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6153472 prefixEnd_6153472 := by exact prefixLift 6153472
  have htrace : WordTrace (prefixWord ++ tailWord_6153472) baseStart_6153472 baseEnd_6153472 := by
    simpa [prefixWord, tailWord_6153472, baseEnd_6153472] using wordTrace_append hprefix tailTrace_6153472
  have hstable : (prefixWord ++ tailWord_6153472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6153472).length < 2 ^ (prefixWord ++ tailWord_6153472).sum := by decide
  have hdescent : baseEnd_6153472 < baseStart_6153472 := by decide
  rcases family_descends (prefixWord ++ tailWord_6153472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6153473 : List Nat := [1, 2, 4, 1, 1, 4, 1, 3, 2, 1, 3]
def baseStart_6153473 : Nat := 118140960795 + 6153473 * 2 ^ 59
def prefixEnd_6153473 : Nat := 4983230072969 + 3 ^ 40 * 6153473 * 2
def baseEnd_6153473 : Nat := 3159689343464108242288199

theorem tailTrace_6153473 : CollatzResearch.WordTrace tailWord_6153473 prefixEnd_6153473 3159689343464108242288199 := by
  unfold tailWord_6153473
  simp only [CollatzResearch.WordTrace]
  refine ⟨224435598436025725364737073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149623732290683816909824715 224435598436025725364737073)
  ·
    refine ⟨168326698827019294023552805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224435598436025725364737073 168326698827019294023552805)
    ·
      refine ⟨31561256030066117629416151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 168326698827019294023552805 31561256030066117629416151)
      ·
        refine ⟨47341884045099176444124227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31561256030066117629416151 47341884045099176444124227)
        ·
          refine ⟨71012826067648764666186341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47341884045099176444124227 71012826067648764666186341)
          ·
            refine ⟨13314904887684143374909939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71012826067648764666186341 13314904887684143374909939)
            ·
              refine ⟨19972357331526215062364909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13314904887684143374909939 19972357331526215062364909)
              ·
                refine ⟨7489633999322330648386841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19972357331526215062364909 7489633999322330648386841)
                ·
                  refine ⟨5617225499491747986290131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7489633999322330648386841 5617225499491747986290131)
                  ·
                    refine ⟨8425838249237621979435197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5617225499491747986290131 8425838249237621979435197)
                    ·
                      refine ⟨3159689343464108242288199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8425838249237621979435197 3159689343464108242288199)
                      ·
                        rfl

theorem cell23_6153473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 3, 2, 1, 3].length) (baseStart_6153473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6153473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6153473 prefixEnd_6153473 := by exact prefixLift 6153473
  have htrace : WordTrace (prefixWord ++ tailWord_6153473) baseStart_6153473 baseEnd_6153473 := by
    simpa [prefixWord, tailWord_6153473, baseEnd_6153473] using wordTrace_append hprefix tailTrace_6153473
  have hstable : (prefixWord ++ tailWord_6153473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6153473).length < 2 ^ (prefixWord ++ tailWord_6153473).sum := by decide
  have hdescent : baseEnd_6153473 < baseStart_6153473 := by decide
  rcases family_descends (prefixWord ++ tailWord_6153473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6153483 : List Nat := [1, 1, 1, 1, 5, 3, 3, 2, 1, 3, 2]
def baseStart_6153483 : Nat := 118140960795 + 6153483 * 2 ^ 59
def prefixEnd_6153483 : Nat := 4983230072969 + 3 ^ 40 * 6153483 * 2
def baseEnd_6153483 : Nat := 3159694478270653203163153

theorem tailTrace_6153483 : CollatzResearch.WordTrace tailWord_6153483 prefixEnd_6153483 3159694478270653203163153 := by
  unfold tailWord_6153483
  simp only [CollatzResearch.WordTrace]
  refine ⟨224435963165989497072601103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149623975443992998048400735 224435963165989497072601103)
  ·
    refine ⟨336653944748984245608901655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224435963165989497072601103 336653944748984245608901655)
    ·
      refine ⟨504980917123476368413352483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 336653944748984245608901655 504980917123476368413352483)
      ·
        refine ⟨757471375685214552620028725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 504980917123476368413352483 757471375685214552620028725)
        ·
          refine ⟨71012941470488864308127693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 757471375685214552620028725 71012941470488864308127693)
          ·
            refine ⟨26629853051433324115547885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71012941470488864308127693 26629853051433324115547885)
            ·
              refine ⟨9986194894287496543330457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26629853051433324115547885 9986194894287496543330457)
              ·
                refine ⟨7489646170715622407497843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9986194894287496543330457 7489646170715622407497843)
                ·
                  refine ⟨11234469256073433611246765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7489646170715622407497843 11234469256073433611246765)
                  ·
                    refine ⟨4212925971027537604217537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11234469256073433611246765 4212925971027537604217537)
                    ·
                      refine ⟨3159694478270653203163153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4212925971027537604217537 3159694478270653203163153)
                      ·
                        rfl

theorem cell23_6153483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3, 2, 1, 3, 2].length) (baseStart_6153483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6153483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6153483 prefixEnd_6153483 := by exact prefixLift 6153483
  have htrace : WordTrace (prefixWord ++ tailWord_6153483) baseStart_6153483 baseEnd_6153483 := by
    simpa [prefixWord, tailWord_6153483, baseEnd_6153483] using wordTrace_append hprefix tailTrace_6153483
  have hstable : (prefixWord ++ tailWord_6153483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6153483).length < 2 ^ (prefixWord ++ tailWord_6153483).sum := by decide
  have hdescent : baseEnd_6153483 < baseStart_6153483 := by decide
  rcases family_descends (prefixWord ++ tailWord_6153483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6153490 : List Nat := [3, 2, 4, 2, 1, 1, 1, 2, 1, 3, 3]
def baseStart_6153490 : Nat := 118140960795 + 6153490 * 2 ^ 59
def prefixEnd_6153490 : Nat := 4983230072969 + 3 ^ 40 * 6153490 * 2
def baseEnd_6153490 : Nat := 3159698072635234675775621

theorem tailTrace_6153490 : CollatzResearch.WordTrace tailWord_6153490 prefixEnd_6153490 3159698072635234675775621 := by
  unfold tailWord_6153490
  simp only [CollatzResearch.WordTrace]
  refine ⟨56109054619241034317026481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149624145651309424845403949 56109054619241034317026481)
  ·
    refine ⟨42081790964430775737769861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56109054619241034317026481 42081790964430775737769861)
    ·
      refine ⟨7890335805830770450831849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42081790964430775737769861 7890335805830770450831849)
      ·
        refine ⟨5917751854373077838123887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7890335805830770450831849 5917751854373077838123887)
        ·
          refine ⟨8876627781559616757185831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5917751854373077838123887 8876627781559616757185831)
          ·
            refine ⟨13314941672339425135778747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8876627781559616757185831 13314941672339425135778747)
            ·
              refine ⟨19972412508509137703668121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13314941672339425135778747 19972412508509137703668121)
              ·
                refine ⟨14979309381381853277751091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19972412508509137703668121 14979309381381853277751091)
                ·
                  refine ⟨22468964072072779916626637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14979309381381853277751091 22468964072072779916626637)
                  ·
                    refine ⟨8425861527027292468734989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22468964072072779916626637 8425861527027292468734989)
                    ·
                      refine ⟨3159698072635234675775621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8425861527027292468734989 3159698072635234675775621)
                      ·
                        rfl

theorem cell23_6153490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_6153490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6153490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6153490 prefixEnd_6153490 := by exact prefixLift 6153490
  have htrace : WordTrace (prefixWord ++ tailWord_6153490) baseStart_6153490 baseEnd_6153490 := by
    simpa [prefixWord, tailWord_6153490, baseEnd_6153490] using wordTrace_append hprefix tailTrace_6153490
  have hstable : (prefixWord ++ tailWord_6153490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6153490).length < 2 ^ (prefixWord ++ tailWord_6153490).sum := by decide
  have hdescent : baseEnd_6153490 < baseStart_6153490 := by decide
  rcases family_descends (prefixWord ++ tailWord_6153490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6153496 : List Nat := [2, 1, 2, 3, 1, 3, 1, 1, 3, 4, 2]
def baseStart_6153496 : Nat := 118140960795 + 6153496 * 2 ^ 59
def prefixEnd_6153496 : Nat := 4983230072969 + 3 ^ 40 * 6153496 * 2
def baseEnd_6153496 : Nat := 3159701153519161652300593

theorem tailTrace_6153496 : CollatzResearch.WordTrace tailWord_6153496 prefixEnd_6153496 3159701153519161652300593 := by
  unfold tailWord_6153496
  simp only [CollatzResearch.WordTrace]
  refine ⟨112218218657471200146412171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149624291543294933528549561 112218218657471200146412171)
  ·
    refine ⟨168327327986206800219618257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112218218657471200146412171 168327327986206800219618257)
    ·
      refine ⟨126245495989655100164713693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168327327986206800219618257 126245495989655100164713693)
      ·
        refine ⟨47342060996120662561767635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126245495989655100164713693 47342060996120662561767635)
        ·
          refine ⟨71013091494180993842651453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47342060996120662561767635 71013091494180993842651453)
          ·
            refine ⟨26629909310317872690994295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71013091494180993842651453 26629909310317872690994295)
            ·
              refine ⟨39944863965476809036491443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26629909310317872690994295 39944863965476809036491443)
              ·
                refine ⟨59917295948215213554737165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39944863965476809036491443 59917295948215213554737165)
                ·
                  refine ⟨22468985980580705083026437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59917295948215213554737165 22468985980580705083026437)
                  ·
                    refine ⟨4212934871358882203067457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22468985980580705083026437 4212934871358882203067457)
                    ·
                      refine ⟨3159701153519161652300593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4212934871358882203067457 3159701153519161652300593)
                      ·
                        rfl

theorem cell23_6153496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 1, 3, 4, 2].length) (baseStart_6153496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6153496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6153496 prefixEnd_6153496 := by exact prefixLift 6153496
  have htrace : WordTrace (prefixWord ++ tailWord_6153496) baseStart_6153496 baseEnd_6153496 := by
    simpa [prefixWord, tailWord_6153496, baseEnd_6153496] using wordTrace_append hprefix tailTrace_6153496
  have hstable : (prefixWord ++ tailWord_6153496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6153496).length < 2 ^ (prefixWord ++ tailWord_6153496).sum := by decide
  have hdescent : baseEnd_6153496 < baseStart_6153496 := by decide
  rcases family_descends (prefixWord ++ tailWord_6153496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6153558 : List Nat := [5, 2, 3, 1, 2, 1, 1, 2, 2, 1, 3]
def baseStart_6153558 : Nat := 118140960795 + 6153558 * 2 ^ 59
def prefixEnd_6153558 : Nat := 4983230072969 + 3 ^ 40 * 6153558 * 2
def baseEnd_6153558 : Nat := 3159732989319740409725309

theorem tailTrace_6153558 : CollatzResearch.WordTrace tailWord_6153558 prefixEnd_6153558 3159732989319740409725309 := by
  unfold tailWord_6153558
  simp only [CollatzResearch.WordTrace]
  refine ⟨14027418665044861555098833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 149625799093811856587720885 14027418665044861555098833)
  ·
    refine ⟨10520563998783646166324125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14027418665044861555098833 10520563998783646166324125)
    ·
      refine ⟨3945211499543867312371547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10520563998783646166324125 3945211499543867312371547)
      ·
        refine ⟨5917817249315800968557321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3945211499543867312371547 5917817249315800968557321)
        ·
          refine ⟨4438362936986850726417991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5917817249315800968557321 4438362936986850726417991)
          ·
            refine ⟨6657544405480276089626987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4438362936986850726417991 6657544405480276089626987)
            ·
              refine ⟨9986316608220414134440481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6657544405480276089626987 9986316608220414134440481)
              ·
                refine ⟨7489737456165310600830361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9986316608220414134440481 7489737456165310600830361)
                ·
                  refine ⟨5617303092123982950622771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7489737456165310600830361 5617303092123982950622771)
                  ·
                    refine ⟨8425954638185974425934157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5617303092123982950622771 8425954638185974425934157)
                    ·
                      refine ⟨3159732989319740409725309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8425954638185974425934157 3159732989319740409725309)
                      ·
                        rfl

theorem cell23_6153558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_6153558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6153558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6153558 prefixEnd_6153558 := by exact prefixLift 6153558
  have htrace : WordTrace (prefixWord ++ tailWord_6153558) baseStart_6153558 baseEnd_6153558 := by
    simpa [prefixWord, tailWord_6153558, baseEnd_6153558] using wordTrace_append hprefix tailTrace_6153558
  have hstable : (prefixWord ++ tailWord_6153558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6153558).length < 2 ^ (prefixWord ++ tailWord_6153558).sum := by decide
  have hdescent : baseEnd_6153558 < baseStart_6153558 := by decide
  rcases family_descends (prefixWord ++ tailWord_6153558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6153596 : List Nat := [2, 2, 2, 1, 1, 1, 3, 4, 3, 4]
def baseStart_6153596 : Nat := 118140960795 + 6153596 * 2 ^ 59
def prefixEnd_6153596 : Nat := 4983230072969 + 3 ^ 40 * 6153596 * 2
def baseEnd_6153596 : Nat := 1053250833861537087016711

theorem tailTrace_6153596 : CollatzResearch.WordTrace tailWord_6153596 prefixEnd_6153596 1053250833861537087016711 := by
  unfold tailWord_6153596
  simp only [CollatzResearch.WordTrace]
  refine ⟨112220042307290058685732321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149626723076386744914309761 112220042307290058685732321)
  ·
    refine ⟨84165031730467544014299241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112220042307290058685732321 84165031730467544014299241)
    ·
      refine ⟨63123773797850658010724431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84165031730467544014299241 63123773797850658010724431)
      ·
        refine ⟨94685660696775987016086647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63123773797850658010724431 94685660696775987016086647)
        ·
          refine ⟨142028491045163980524129971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94685660696775987016086647 142028491045163980524129971)
          ·
            refine ⟨213042736567745970786194957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142028491045163980524129971 213042736567745970786194957)
            ·
              refine ⟨79891026212904739044823109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 213042736567745970786194957 79891026212904739044823109)
              ·
                refine ⟨14979567414919638570904333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 79891026212904739044823109 14979567414919638570904333)
                ·
                  refine ⟨5617337780594864464089125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14979567414919638570904333 5617337780594864464089125)
                  ·
                    refine ⟨1053250833861537087016711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5617337780594864464089125 1053250833861537087016711)
                    ·
                      rfl

theorem cell23_6153596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 4, 3, 4].length) (baseStart_6153596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6153596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6153596 prefixEnd_6153596 := by exact prefixLift 6153596
  have htrace : WordTrace (prefixWord ++ tailWord_6153596) baseStart_6153596 baseEnd_6153596 := by
    simpa [prefixWord, tailWord_6153596, baseEnd_6153596] using wordTrace_append hprefix tailTrace_6153596
  have hstable : (prefixWord ++ tailWord_6153596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6153596).length < 2 ^ (prefixWord ++ tailWord_6153596).sum := by decide
  have hdescent : baseEnd_6153596 < baseStart_6153596 := by decide
  rcases family_descends (prefixWord ++ tailWord_6153596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6153626 : List Nat := [3, 1, 1, 4, 1, 1, 2, 4, 6]
def baseStart_6153626 : Nat := 118140960795 + 6153626 * 2 ^ 59
def prefixEnd_6153626 : Nat := 4983230072969 + 3 ^ 40 * 6153626 * 2
def baseEnd_6153626 : Nat := 351085322889360682630555

theorem tailTrace_6153626 : CollatzResearch.WordTrace tailWord_6153626 prefixEnd_6153626 351085322889360682630555 := by
  unfold tailWord_6153626
  simp only [CollatzResearch.WordTrace]
  refine ⟨56110294701117858123764183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149627452536314288330037821 56110294701117858123764183)
  ·
    refine ⟨84165442051676787185646275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56110294701117858123764183 84165442051676787185646275)
    ·
      refine ⟨126248163077515180778469413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84165442051676787185646275 126248163077515180778469413)
      ·
        refine ⟨23671530577034096395963015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 126248163077515180778469413 23671530577034096395963015)
        ·
          refine ⟨35507295865551144593944523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23671530577034096395963015 35507295865551144593944523)
          ·
            refine ⟨53260943798326716890916785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35507295865551144593944523 53260943798326716890916785)
            ·
              refine ⟨39945707848745037668187589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53260943798326716890916785 39945707848745037668187589)
              ·
                refine ⟨7489820221639694562785173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39945707848745037668187589 7489820221639694562785173)
                ·
                  refine ⟨351085322889360682630555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7489820221639694562785173 351085322889360682630555)
                  ·
                    rfl

theorem cell23_6153626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 4, 6].length) (baseStart_6153626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6153626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6153626 prefixEnd_6153626 := by exact prefixLift 6153626
  have htrace : WordTrace (prefixWord ++ tailWord_6153626) baseStart_6153626 baseEnd_6153626 := by
    simpa [prefixWord, tailWord_6153626, baseEnd_6153626] using wordTrace_append hprefix tailTrace_6153626
  have hstable : (prefixWord ++ tailWord_6153626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6153626).length < 2 ^ (prefixWord ++ tailWord_6153626).sum := by decide
  have hdescent : baseEnd_6153626 < baseStart_6153626 := by decide
  rcases family_descends (prefixWord ++ tailWord_6153626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6153693 : List Nat := [1, 4, 3, 1, 1, 2, 1, 2, 3, 1, 4]
def baseStart_6153693 : Nat := 118140960795 + 6153693 * 2 ^ 59
def prefixEnd_6153693 : Nat := 4983230072969 + 3 ^ 40 * 6153693 * 2
def baseEnd_6153693 : Nat := 3159802309208097381537187

theorem tailTrace_6153693 : CollatzResearch.WordTrace tailWord_6153693 prefixEnd_6153693 3159802309208097381537187 := by
  unfold tailWord_6153693
  simp only [CollatzResearch.WordTrace]
  refine ⟨224443622495228702937745733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149629081663485801958497155 224443622495228702937745733)
  ·
    refine ⟨42083179217855381800827325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 224443622495228702937745733 42083179217855381800827325)
    ·
      refine ⟨15781192206695768175310247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42083179217855381800827325 15781192206695768175310247)
      ·
        refine ⟨23671788310043652262965371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15781192206695768175310247 23671788310043652262965371)
        ·
          refine ⟨35507682465065478394448057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23671788310043652262965371 35507682465065478394448057)
          ·
            refine ⟨26630761848799108795836043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35507682465065478394448057 26630761848799108795836043)
            ·
              refine ⟨39946142773198663193754065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26630761848799108795836043 39946142773198663193754065)
              ·
                refine ⟨29959607079898997395315549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39946142773198663193754065 29959607079898997395315549)
                ·
                  refine ⟨11234852654962124023243331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29959607079898997395315549 11234852654962124023243331)
                  ·
                    refine ⟨16852278982443186034864997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11234852654962124023243331 16852278982443186034864997)
                    ·
                      refine ⟨3159802309208097381537187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16852278982443186034864997 3159802309208097381537187)
                      ·
                        rfl

theorem cell23_6153693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_6153693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6153693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6153693 prefixEnd_6153693 := by exact prefixLift 6153693
  have htrace : WordTrace (prefixWord ++ tailWord_6153693) baseStart_6153693 baseEnd_6153693 := by
    simpa [prefixWord, tailWord_6153693, baseEnd_6153693] using wordTrace_append hprefix tailTrace_6153693
  have hstable : (prefixWord ++ tailWord_6153693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6153693).length < 2 ^ (prefixWord ++ tailWord_6153693).sum := by decide
  have hdescent : baseEnd_6153693 < baseStart_6153693 := by decide
  rcases family_descends (prefixWord ++ tailWord_6153693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6153703 : List Nat := [1, 1, 5, 2, 1, 3, 2, 1, 1, 6]
def baseStart_6153703 : Nat := 118140960795 + 6153703 * 2 ^ 59
def prefixEnd_6153703 : Nat := 4983230072969 + 3 ^ 40 * 6153703 * 2
def baseEnd_6153703 : Nat := 1053269148004880780804047

theorem tailTrace_6153703 : CollatzResearch.WordTrace tailWord_6153703 prefixEnd_6153703 1053269148004880780804047 := by
  unfold tailWord_6153703
  simp only [CollatzResearch.WordTrace]
  refine ⟨224443987225192474645609763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149629324816794983097073175 224443987225192474645609763)
  ·
    refine ⟨336665980837788711968414645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224443987225192474645609763 336665980837788711968414645)
    ·
      refine ⟨31562435703542691747038873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 336665980837788711968414645 31562435703542691747038873)
      ·
        refine ⟨23671826777657018810279155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31562435703542691747038873 23671826777657018810279155)
        ·
          refine ⟨35507740166485528215418733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23671826777657018810279155 35507740166485528215418733)
          ·
            refine ⟨13315402562432073080782025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35507740166485528215418733 13315402562432073080782025)
            ·
              refine ⟨9986551921824054810586519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13315402562432073080782025 9986551921824054810586519)
              ·
                refine ⟨14979827882736082215879779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9986551921824054810586519 14979827882736082215879779)
                ·
                  refine ⟨22469741824104123323819669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14979827882736082215879779 22469741824104123323819669)
                  ·
                    refine ⟨1053269148004880780804047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22469741824104123323819669 1053269148004880780804047)
                    ·
                      rfl

theorem cell23_6153703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2, 1, 1, 6].length) (baseStart_6153703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6153703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6153703 prefixEnd_6153703 := by exact prefixLift 6153703
  have htrace : WordTrace (prefixWord ++ tailWord_6153703) baseStart_6153703 baseEnd_6153703 := by
    simpa [prefixWord, tailWord_6153703, baseEnd_6153703] using wordTrace_append hprefix tailTrace_6153703
  have hstable : (prefixWord ++ tailWord_6153703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6153703).length < 2 ^ (prefixWord ++ tailWord_6153703).sum := by decide
  have hdescent : baseEnd_6153703 < baseStart_6153703 := by decide
  rcases family_descends (prefixWord ++ tailWord_6153703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6153713 : List Nat := [1, 2, 2, 2, 3, 2, 2, 1, 3, 2, 3]
def baseStart_6153713 : Nat := 118140960795 + 6153713 * 2 ^ 59
def prefixEnd_6153713 : Nat := 4983230072969 + 3 ^ 40 * 6153713 * 2
def baseEnd_6153713 : Nat := 3159812578821187303287095

theorem tailTrace_6153713 : CollatzResearch.WordTrace tailWord_6153713 prefixEnd_6153713 3159812578821187303287095 := by
  unfold tailWord_6153713
  simp only [CollatzResearch.WordTrace]
  refine ⟨224444351955156246353473793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149629567970104164235649195 224444351955156246353473793)
  ·
    refine ⟨168333263966367184765105345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224444351955156246353473793 168333263966367184765105345)
    ·
      refine ⟨126249947974775388573829009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168333263966367184765105345 126249947974775388573829009)
      ·
        refine ⟨94687460981081541430371757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126249947974775388573829009 94687460981081541430371757)
        ·
          refine ⟨35507797867905578036389409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94687460981081541430371757 35507797867905578036389409)
          ·
            refine ⟨26630848400929183527292057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35507797867905578036389409 26630848400929183527292057)
            ·
              refine ⟨19973136300696887645469043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26630848400929183527292057 19973136300696887645469043)
              ·
                refine ⟨29959704451045331468203565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19973136300696887645469043 29959704451045331468203565)
                ·
                  refine ⟨11234889169141999300576337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29959704451045331468203565 11234889169141999300576337)
                  ·
                    refine ⟨8426166876856499475432253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11234889169141999300576337 8426166876856499475432253)
                    ·
                      refine ⟨3159812578821187303287095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8426166876856499475432253 3159812578821187303287095)
                      ·
                        rfl

theorem cell23_6153713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 1, 3, 2, 3].length) (baseStart_6153713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6153713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6153713 prefixEnd_6153713 := by exact prefixLift 6153713
  have htrace : WordTrace (prefixWord ++ tailWord_6153713) baseStart_6153713 baseEnd_6153713 := by
    simpa [prefixWord, tailWord_6153713, baseEnd_6153713] using wordTrace_append hprefix tailTrace_6153713
  have hstable : (prefixWord ++ tailWord_6153713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6153713).length < 2 ^ (prefixWord ++ tailWord_6153713).sum := by decide
  have hdescent : baseEnd_6153713 < baseStart_6153713 := by decide
  rcases family_descends (prefixWord ++ tailWord_6153713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6153760 : List Nat := [2, 1, 1, 6, 1, 1, 3, 1, 1, 3, 3]
def baseStart_6153760 : Nat := 118140960795 + 6153760 * 2 ^ 59
def prefixEnd_6153760 : Nat := 4983230072969 + 3 ^ 40 * 6153760 * 2
def baseEnd_6153760 : Nat := 3159836712411948619399379

theorem tailTrace_6153760 : CollatzResearch.WordTrace tailWord_6153760 prefixEnd_6153760 3159836712411948619399379 := by
  unfold tailWord_6153760
  simp only [CollatzResearch.WordTrace]
  refine ⟨112223033092992986690217367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149630710790657315586956489 112223033092992986690217367)
  ·
    refine ⟨168334549639489480035326051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112223033092992986690217367 168334549639489480035326051)
    ·
      refine ⟨252501824459234220052989077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168334549639489480035326051 252501824459234220052989077)
      ·
        refine ⟨11836023021526604064983863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 252501824459234220052989077 11836023021526604064983863)
        ·
          refine ⟨17754034532289906097475795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11836023021526604064983863 17754034532289906097475795)
          ·
            refine ⟨26631051798434859146213693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17754034532289906097475795 26631051798434859146213693)
            ·
              refine ⟨9986644424413072179830135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26631051798434859146213693 9986644424413072179830135)
              ·
                refine ⟨14979966636619608269745203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9986644424413072179830135 14979966636619608269745203)
                ·
                  refine ⟨22469949954929412404617805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14979966636619608269745203 22469949954929412404617805)
                  ·
                    refine ⟨8426231233098529651731677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22469949954929412404617805 8426231233098529651731677)
                    ·
                      refine ⟨3159836712411948619399379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8426231233098529651731677 3159836712411948619399379)
                      ·
                        rfl

theorem cell23_6153760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_6153760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6153760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6153760 prefixEnd_6153760 := by exact prefixLift 6153760
  have htrace : WordTrace (prefixWord ++ tailWord_6153760) baseStart_6153760 baseEnd_6153760 := by
    simpa [prefixWord, tailWord_6153760, baseEnd_6153760] using wordTrace_append hprefix tailTrace_6153760
  have hstable : (prefixWord ++ tailWord_6153760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6153760).length < 2 ^ (prefixWord ++ tailWord_6153760).sum := by decide
  have hdescent : baseEnd_6153760 < baseStart_6153760 := by decide
  rcases family_descends (prefixWord ++ tailWord_6153760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6153857 : List Nat := [1, 2, 4, 2, 1, 2, 4, 2, 5]
def baseStart_6153857 : Nat := 118140960795 + 6153857 * 2 ^ 59
def prefixEnd_6153857 : Nat := 4983230072969 + 3 ^ 40 * 6153857 * 2
def baseEnd_6153857 : Nat := 351098502226159415542937

theorem tailTrace_6153857 : CollatzResearch.WordTrace tailWord_6153857 prefixEnd_6153857 351098502226159415542937 := by
  unfold tailWord_6153857
  simp only [CollatzResearch.WordTrace]
  refine ⟨224449604066634558946715825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149633069377756372631143883 224449604066634558946715825)
  ·
    refine ⟨168337203049975919210036869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224449604066634558946715825 168337203049975919210036869)
    ·
      refine ⟨31563225571870484851881913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 168337203049975919210036869 31563225571870484851881913)
      ·
        refine ⟨23672419178902863638911435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31563225571870484851881913 23672419178902863638911435)
        ·
          refine ⟨35508628768354295458367153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23672419178902863638911435 35508628768354295458367153)
          ·
            refine ⟨26631471576265721593775365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35508628768354295458367153 26631471576265721593775365)
            ·
              refine ⟨4993400920549822798832881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26631471576265721593775365 4993400920549822798832881)
              ·
                refine ⟨3745050690412367099124661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4993400920549822798832881 3745050690412367099124661)
                ·
                  refine ⟨351098502226159415542937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3745050690412367099124661 351098502226159415542937)
                  ·
                    rfl

theorem cell23_6153857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 4, 2, 5].length) (baseStart_6153857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6153857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6153857 prefixEnd_6153857 := by exact prefixLift 6153857
  have htrace : WordTrace (prefixWord ++ tailWord_6153857) baseStart_6153857 baseEnd_6153857 := by
    simpa [prefixWord, tailWord_6153857, baseEnd_6153857] using wordTrace_append hprefix tailTrace_6153857
  have hstable : (prefixWord ++ tailWord_6153857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6153857).length < 2 ^ (prefixWord ++ tailWord_6153857).sum := by decide
  have hdescent : baseEnd_6153857 < baseStart_6153857 := by decide
  rcases family_descends (prefixWord ++ tailWord_6153857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6153863 : List Nat := [1, 1, 4, 2, 1, 3, 2, 1, 1, 2, 5]
def baseStart_6153863 : Nat := 118140960795 + 6153863 * 2 ^ 59
def prefixEnd_6153863 : Nat := 4983230072969 + 3 ^ 40 * 6153863 * 2
def baseEnd_6153863 : Nat := 3159889600919361716411405

theorem tailTrace_6153863 : CollatzResearch.WordTrace tailWord_6153863 prefixEnd_6153863 3159889600919361716411405 := by
  unfold tailWord_6153863
  simp only [CollatzResearch.WordTrace]
  refine ⟨224449822904612821971434243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149633215269741881314289495 224449822904612821971434243)
  ·
    refine ⟨336674734356919232957151365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224449822904612821971434243 336674734356919232957151365)
    ·
      refine ⟨63126512691922356179465881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 336674734356919232957151365 63126512691922356179465881)
      ·
        refine ⟨47344884518941767134599411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63126512691922356179465881 47344884518941767134599411)
        ·
          refine ⟨71017326778412650701899117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47344884518941767134599411 71017326778412650701899117)
          ·
            refine ⟨26631497541904744013212169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71017326778412650701899117 26631497541904744013212169)
            ·
              refine ⟨19973623156428558009909127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26631497541904744013212169 19973623156428558009909127)
              ·
                refine ⟨29960434734642837014863691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19973623156428558009909127 29960434734642837014863691)
                ·
                  refine ⟨44940652101964255522295537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29960434734642837014863691 44940652101964255522295537)
                  ·
                    refine ⟨33705489076473191641721653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44940652101964255522295537 33705489076473191641721653)
                    ·
                      refine ⟨3159889600919361716411405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33705489076473191641721653 3159889600919361716411405)
                      ·
                        rfl

theorem cell23_6153863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 1, 1, 2, 5].length) (baseStart_6153863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6153863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6153863 prefixEnd_6153863 := by exact prefixLift 6153863
  have htrace : WordTrace (prefixWord ++ tailWord_6153863) baseStart_6153863 baseEnd_6153863 := by
    simpa [prefixWord, tailWord_6153863, baseEnd_6153863] using wordTrace_append hprefix tailTrace_6153863
  have hstable : (prefixWord ++ tailWord_6153863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6153863).length < 2 ^ (prefixWord ++ tailWord_6153863).sum := by decide
  have hdescent : baseEnd_6153863 < baseStart_6153863 := by decide
  rcases family_descends (prefixWord ++ tailWord_6153863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6153917 : List Nat := [1, 4, 1, 2, 1, 2, 1, 6, 1, 4]
def baseStart_6153917 : Nat := 118140960795 + 6153917 * 2 ^ 59
def prefixEnd_6153917 : Nat := 4983230072969 + 3 ^ 40 * 6153917 * 2
def baseEnd_6153917 : Nat := 1053305776291568168378719

theorem tailTrace_6153917 : CollatzResearch.WordTrace tailWord_6153917 prefixEnd_6153917 1053305776291568168378719 := by
  unfold tailWord_6153917
  simp only [CollatzResearch.WordTrace]
  refine ⟨224451792446417189193900005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149634528297611459462600003 224451792446417189193900005)
  ·
    refine ⟨42084711083703222973856251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 224451792446417189193900005 42084711083703222973856251)
    ·
      refine ⟨63127066625554834460784377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42084711083703222973856251 63127066625554834460784377)
      ·
        refine ⟨47345299969166125845588283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63127066625554834460784377 47345299969166125845588283)
        ·
          refine ⟨71017949953749188768382425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47345299969166125845588283 71017949953749188768382425)
          ·
            refine ⟨53263462465311891576286819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71017949953749188768382425 53263462465311891576286819)
            ·
              refine ⟨79895193697967837364430229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53263462465311891576286819 79895193697967837364430229)
              ·
                refine ⟨3745087204592242376457667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 79895193697967837364430229 3745087204592242376457667)
                ·
                  refine ⟨5617630806888363564686501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3745087204592242376457667 5617630806888363564686501)
                  ·
                    refine ⟨1053305776291568168378719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5617630806888363564686501 1053305776291568168378719)
                    ·
                      rfl

theorem cell23_6153917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 6, 1, 4].length) (baseStart_6153917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6153917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6153917 prefixEnd_6153917 := by exact prefixLift 6153917
  have htrace : WordTrace (prefixWord ++ tailWord_6153917) baseStart_6153917 baseEnd_6153917 := by
    simpa [prefixWord, tailWord_6153917, baseEnd_6153917] using wordTrace_append hprefix tailTrace_6153917
  have hstable : (prefixWord ++ tailWord_6153917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6153917).length < 2 ^ (prefixWord ++ tailWord_6153917).sum := by decide
  have hdescent : baseEnd_6153917 < baseStart_6153917 := by decide
  rcases family_descends (prefixWord ++ tailWord_6153917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6153967 : List Nat := [1, 1, 2, 1, 5, 1, 3, 2, 2, 3, 2]
def baseStart_6153967 : Nat := 118140960795 + 6153967 * 2 ^ 59
def prefixEnd_6153967 : Nat := 4983230072969 + 3 ^ 40 * 6153967 * 2
def baseEnd_6153967 : Nat := 3159943002907429309510927

theorem tailTrace_6153967 : CollatzResearch.WordTrace tailWord_6153967 prefixEnd_6153967 3159943002907429309510927 := by
  unfold tailWord_6153967
  simp only [CollatzResearch.WordTrace]
  refine ⟨224453616096236047733220155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149635744064157365155480103 224453616096236047733220155)
  ·
    refine ⟨336680424144354071599830233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224453616096236047733220155 336680424144354071599830233)
    ·
      refine ⟨252510318108265553699872675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 336680424144354071599830233 252510318108265553699872675)
      ·
        refine ⟨378765477162398330549809013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252510318108265553699872675 378765477162398330549809013)
        ·
          refine ⟨35509263483974843489044595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 378765477162398330549809013 35509263483974843489044595)
          ·
            refine ⟨53263895225962265233566893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35509263483974843489044595 53263895225962265233566893)
            ·
              refine ⟨19973960709735849462587585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53263895225962265233566893 19973960709735849462587585)
              ·
                refine ⟨14980470532301887096940689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19973960709735849462587585 14980470532301887096940689)
                ·
                  refine ⟨11235352899226415322705517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14980470532301887096940689 11235352899226415322705517)
                  ·
                    refine ⟨4213257337209905746014569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11235352899226415322705517 4213257337209905746014569)
                    ·
                      refine ⟨3159943002907429309510927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4213257337209905746014569 3159943002907429309510927)
                      ·
                        rfl

theorem cell23_6153967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 2, 2, 3, 2].length) (baseStart_6153967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6153967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6153967 prefixEnd_6153967 := by exact prefixLift 6153967
  have htrace : WordTrace (prefixWord ++ tailWord_6153967) baseStart_6153967 baseEnd_6153967 := by
    simpa [prefixWord, tailWord_6153967, baseEnd_6153967] using wordTrace_append hprefix tailTrace_6153967
  have hstable : (prefixWord ++ tailWord_6153967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6153967).length < 2 ^ (prefixWord ++ tailWord_6153967).sum := by decide
  have hdescent : baseEnd_6153967 < baseStart_6153967 := by decide
  rcases family_descends (prefixWord ++ tailWord_6153967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6153974 : List Nat := [5, 1, 1, 1, 1, 3, 3, 1, 3, 1, 3]
def baseStart_6153974 : Nat := 118140960795 + 6153974 * 2 ^ 59
def prefixEnd_6153974 : Nat := 4983230072969 + 3 ^ 40 * 6153974 * 2
def baseEnd_6153974 : Nat := 3159946597272010782123395

theorem tailTrace_6153974 : CollatzResearch.WordTrace tailWord_6153974 prefixEnd_6153974 3159946597272010782123395 := by
  unfold tailWord_6153974
  simp only [CollatzResearch.WordTrace]
  refine ⟨14028366962950667995545311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 149635914271473791952483317 14028366962950667995545311)
  ·
    refine ⟨21042550444426001993317967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14028366962950667995545311 21042550444426001993317967)
    ·
      refine ⟨31563825666639002989976951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21042550444426001993317967 31563825666639002989976951)
      ·
        refine ⟨47345738499958504484965427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31563825666639002989976951 47345738499958504484965427)
        ·
          refine ⟨71018607749937756727448141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47345738499958504484965427 71018607749937756727448141)
          ·
            refine ⟨26631977906226658772793053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71018607749937756727448141 26631977906226658772793053)
            ·
              refine ⟨9986991714834997039797395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26631977906226658772793053 9986991714834997039797395)
              ·
                refine ⟨14980487572252495559696093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9986991714834997039797395 14980487572252495559696093)
                ·
                  refine ⟨5617682839594685834886035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14980487572252495559696093 5617682839594685834886035)
                  ·
                    refine ⟨8426524259392028752329053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5617682839594685834886035 8426524259392028752329053)
                    ·
                      refine ⟨3159946597272010782123395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8426524259392028752329053 3159946597272010782123395)
                      ·
                        rfl

theorem cell23_6153974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3, 1, 3, 1, 3].length) (baseStart_6153974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6153974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6153974 prefixEnd_6153974 := by exact prefixLift 6153974
  have htrace : WordTrace (prefixWord ++ tailWord_6153974) baseStart_6153974 baseEnd_6153974 := by
    simpa [prefixWord, tailWord_6153974, baseEnd_6153974] using wordTrace_append hprefix tailTrace_6153974
  have hstable : (prefixWord ++ tailWord_6153974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6153974).length < 2 ^ (prefixWord ++ tailWord_6153974).sum := by decide
  have hdescent : baseEnd_6153974 < baseStart_6153974 := by decide
  rcases family_descends (prefixWord ++ tailWord_6153974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6153980 : List Nat := [2, 2, 2, 1, 3, 1, 2, 2, 3, 1, 4]
def baseStart_6153980 : Nat := 118140960795 + 6153980 * 2 ^ 59
def prefixEnd_6153980 : Nat := 4983230072969 + 3 ^ 40 * 6153980 * 2
def baseEnd_6153980 : Nat := 3159949678155937758648367

theorem tailTrace_6153980 : CollatzResearch.WordTrace tailWord_6153980 prefixEnd_6153980 3159949678155937758648367 := by
  unfold tailWord_6153980
  simp only [CollatzResearch.WordTrace]
  refine ⟨112227045122594475476721697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149636060163459300635628929 112227045122594475476721697)
  ·
    refine ⟨84170283841945856607541273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112227045122594475476721697 84170283841945856607541273)
    ·
      refine ⟨63127712881459392455655955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84170283841945856607541273 63127712881459392455655955)
      ·
        refine ⟨94691569322189088683483933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63127712881459392455655955 94691569322189088683483933)
        ·
          refine ⟨35509338495820908256306475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94691569322189088683483933 35509338495820908256306475)
          ·
            refine ⟨53264007743731362384459713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35509338495820908256306475 53264007743731362384459713)
            ·
              refine ⟨39948005807798521788344785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53264007743731362384459713 39948005807798521788344785)
              ·
                refine ⟨29961004355848891341258589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39948005807798521788344785 29961004355848891341258589)
                ·
                  refine ⟨11235376633443334252971971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29961004355848891341258589 11235376633443334252971971)
                  ·
                    refine ⟨16853064950165001379457957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11235376633443334252971971 16853064950165001379457957)
                    ·
                      refine ⟨3159949678155937758648367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16853064950165001379457957 3159949678155937758648367)
                      ·
                        rfl

theorem cell23_6153980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 2, 3, 1, 4].length) (baseStart_6153980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6153980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6153980 prefixEnd_6153980 := by exact prefixLift 6153980
  have htrace : WordTrace (prefixWord ++ tailWord_6153980) baseStart_6153980 baseEnd_6153980 := by
    simpa [prefixWord, tailWord_6153980, baseEnd_6153980] using wordTrace_append hprefix tailTrace_6153980
  have hstable : (prefixWord ++ tailWord_6153980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6153980).length < 2 ^ (prefixWord ++ tailWord_6153980).sum := by decide
  have hdescent : baseEnd_6153980 < baseStart_6153980 := by decide
  rcases family_descends (prefixWord ++ tailWord_6153980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6154010 : List Nat := [3, 1, 1, 3, 2, 2, 1, 1, 3, 2, 4]
def baseStart_6154010 : Nat := 118140960795 + 6154010 * 2 ^ 59
def prefixEnd_6154010 : Nat := 4983230072969 + 3 ^ 40 * 6154010 * 2
def baseEnd_6154010 : Nat := 3159965082575572641273229

theorem tailTrace_6154010 : CollatzResearch.WordTrace tailWord_6154010 prefixEnd_6154010 3159965082575572641273229 := by
  unfold tailWord_6154010
  simp only [CollatzResearch.WordTrace]
  refine ⟨56113796108770066519258871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149636789623386844051356989 56113796108770066519258871)
  ·
    refine ⟨84170694163155099778888307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56113796108770066519258871 84170694163155099778888307)
    ·
      refine ⟨126256041244732649668332461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84170694163155099778888307 126256041244732649668332461)
      ·
        refine ⟨47346015466774743625624673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126256041244732649668332461 47346015466774743625624673)
        ·
          refine ⟨35509511600081057719218505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47346015466774743625624673 35509511600081057719218505)
          ·
            refine ⟨26632133700060793289413879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35509511600081057719218505 26632133700060793289413879)
            ·
              refine ⟨39948200550091189934120819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26632133700060793289413879 39948200550091189934120819)
              ·
                refine ⟨59922300825136784901181229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39948200550091189934120819 59922300825136784901181229)
                ·
                  refine ⟨22470862809426294337942961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59922300825136784901181229 22470862809426294337942961)
                  ·
                    refine ⟨16853147107069720753457221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22470862809426294337942961 16853147107069720753457221)
                    ·
                      refine ⟨3159965082575572641273229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16853147107069720753457221 3159965082575572641273229)
                      ·
                        rfl

theorem cell23_6154010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 1, 3, 2, 4].length) (baseStart_6154010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6154010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6154010 prefixEnd_6154010 := by exact prefixLift 6154010
  have htrace : WordTrace (prefixWord ++ tailWord_6154010) baseStart_6154010 baseEnd_6154010 := by
    simpa [prefixWord, tailWord_6154010, baseEnd_6154010] using wordTrace_append hprefix tailTrace_6154010
  have hstable : (prefixWord ++ tailWord_6154010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6154010).length < 2 ^ (prefixWord ++ tailWord_6154010).sum := by decide
  have hdescent : baseEnd_6154010 < baseStart_6154010 := by decide
  rcases family_descends (prefixWord ++ tailWord_6154010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6154017 : List Nat := [1, 2, 3, 2, 1, 5, 1, 1, 1, 1, 5]
def baseStart_6154017 : Nat := 118140960795 + 6154017 * 2 ^ 59
def prefixEnd_6154017 : Nat := 4983230072969 + 3 ^ 40 * 6154017 * 2
def baseEnd_6154017 : Nat := 3159968676940154113885697

theorem tailTrace_6154017 : CollatzResearch.WordTrace tailWord_6154017 prefixEnd_6154017 3159968676940154113885697 := by
  unfold tailWord_6154017
  simp only [CollatzResearch.WordTrace]
  refine ⟨224455439746054906272540305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149636959830703270848360203 224455439746054906272540305)
  ·
    refine ⟨168341579809541179704405229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224455439746054906272540305 168341579809541179704405229)
    ·
      refine ⟨63128092428577942389151961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168341579809541179704405229 63128092428577942389151961)
      ·
        refine ⟨47346069321433456791863971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63128092428577942389151961 47346069321433456791863971)
        ·
          refine ⟨71019103982150185187795957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47346069321433456791863971 71019103982150185187795957)
          ·
            refine ⟨6658040998326579861355871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 71019103982150185187795957 6658040998326579861355871)
            ·
              refine ⟨9987061497489869792033807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6658040998326579861355871 9987061497489869792033807)
              ·
                refine ⟨14980592246234804688050711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9987061497489869792033807 14980592246234804688050711)
                ·
                  refine ⟨22470888369352207032076067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14980592246234804688050711 22470888369352207032076067)
                  ·
                    refine ⟨33706332554028310548114101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22470888369352207032076067 33706332554028310548114101)
                    ·
                      refine ⟨3159968676940154113885697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33706332554028310548114101 3159968676940154113885697)
                      ·
                        rfl

theorem cell23_6154017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 1, 1, 1, 1, 5].length) (baseStart_6154017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6154017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6154017 prefixEnd_6154017 := by exact prefixLift 6154017
  have htrace : WordTrace (prefixWord ++ tailWord_6154017) baseStart_6154017 baseEnd_6154017 := by
    simpa [prefixWord, tailWord_6154017, baseEnd_6154017] using wordTrace_append hprefix tailTrace_6154017
  have hstable : (prefixWord ++ tailWord_6154017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6154017).length < 2 ^ (prefixWord ++ tailWord_6154017).sum := by decide
  have hdescent : baseEnd_6154017 < baseStart_6154017 := by decide
  rcases family_descends (prefixWord ++ tailWord_6154017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6154024 : List Nat := [2, 1, 5, 1, 1, 3, 2, 2, 2, 4]
def baseStart_6154024 : Nat := 118140960795 + 6154024 * 2 ^ 59
def prefixEnd_6154024 : Nat := 4983230072969 + 3 ^ 40 * 6154024 * 2
def baseEnd_6154024 : Nat := 1053324090434911862166055

theorem tailTrace_6154024 : CollatzResearch.WordTrace tailWord_6154024 prefixEnd_6154024 1053324090434911862166055 := by
  unfold tailWord_6154024
  simp only [CollatzResearch.WordTrace]
  refine ⟨112227847528514773234022563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149637130038019697645363417 112227847528514773234022563)
  ·
    refine ⟨168341771292772159851033845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112227847528514773234022563 168341771292772159851033845)
    ·
      refine ⟨15782041058697389986034423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 168341771292772159851033845 15782041058697389986034423)
      ·
        refine ⟨23673061588046084979051635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15782041058697389986034423 23673061588046084979051635)
        ·
          refine ⟨35509592382069127468577453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23673061588046084979051635 35509592382069127468577453)
          ·
            refine ⟨13316097143275922800716545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35509592382069127468577453 13316097143275922800716545)
            ·
              refine ⟨9987072857456942100537409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13316097143275922800716545 9987072857456942100537409)
              ·
                refine ⟨7490304643092706575403057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9987072857456942100537409 7490304643092706575403057)
                ·
                  refine ⟨5617728482319529931552293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7490304643092706575403057 5617728482319529931552293)
                  ·
                    refine ⟨1053324090434911862166055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5617728482319529931552293 1053324090434911862166055)
                    ·
                      rfl

theorem cell23_6154024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2, 2, 2, 4].length) (baseStart_6154024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6154024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6154024 prefixEnd_6154024 := by exact prefixLift 6154024
  have htrace : WordTrace (prefixWord ++ tailWord_6154024) baseStart_6154024 baseEnd_6154024 := by
    simpa [prefixWord, tailWord_6154024, baseEnd_6154024] using wordTrace_append hprefix tailTrace_6154024
  have hstable : (prefixWord ++ tailWord_6154024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6154024).length < 2 ^ (prefixWord ++ tailWord_6154024).sum := by decide
  have hdescent : baseEnd_6154024 < baseStart_6154024 := by decide
  rcases family_descends (prefixWord ++ tailWord_6154024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6154037 : List Nat := [1, 3, 3, 1, 4, 2, 1, 8]
def baseStart_6154037 : Nat := 118140960795 + 6154037 * 2 ^ 59
def prefixEnd_6154037 : Nat := 4983230072969 + 3 ^ 40 * 6154037 * 2
def baseEnd_6154037 : Nat := 117036257279749779097615

theorem tailTrace_6154037 : CollatzResearch.WordTrace tailWord_6154037 prefixEnd_6154037 117036257279749779097615 := by
  unfold tailWord_6154037
  simp only [CollatzResearch.WordTrace]
  refine ⟨224456169205982449688268365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149637446137321633125512243 224456169205982449688268365)
  ·
    refine ⟨84171063452243418633100637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 224456169205982449688268365 84171063452243418633100637)
    ·
      refine ⟨31564148794591281987412739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84171063452243418633100637 31564148794591281987412739)
      ·
        refine ⟨47346223191886922981119109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31564148794591281987412739 47346223191886922981119109)
        ·
          refine ⟨8877416848478798058959833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47346223191886922981119109 8877416848478798058959833)
          ·
            refine ⟨6658062636359098544219875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8877416848478798058959833 6658062636359098544219875)
            ·
              refine ⟨9987093954538647816329813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6658062636359098544219875 9987093954538647816329813)
              ·
                refine ⟨117036257279749779097615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9987093954538647816329813 117036257279749779097615)
                ·
                  rfl

theorem cell23_6154037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 1, 8].length) (baseStart_6154037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6154037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6154037 prefixEnd_6154037 := by exact prefixLift 6154037
  have htrace : WordTrace (prefixWord ++ tailWord_6154037) baseStart_6154037 baseEnd_6154037 := by
    simpa [prefixWord, tailWord_6154037, baseEnd_6154037] using wordTrace_append hprefix tailTrace_6154037
  have hstable : (prefixWord ++ tailWord_6154037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6154037).length < 2 ^ (prefixWord ++ tailWord_6154037).sum := by decide
  have hdescent : baseEnd_6154037 < baseStart_6154037 := by decide
  rcases family_descends (prefixWord ++ tailWord_6154037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6154057 : List Nat := [1, 2, 1, 1, 2, 4, 1, 3, 3, 3, 2]
def baseStart_6154057 : Nat := 118140960795 + 6154057 * 2 ^ 59
def prefixEnd_6154057 : Nat := 4983230072969 + 3 ^ 40 * 6154057 * 2
def baseEnd_6154057 : Nat := 3159989216166333957385513

theorem tailTrace_6154057 : CollatzResearch.WordTrace tailWord_6154057 prefixEnd_6154057 3159989216166333957385513 := by
  unfold tailWord_6154057
  simp only [CollatzResearch.WordTrace]
  refine ⟨224456898665909993103996425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149637932443939995402664283 224456898665909993103996425)
  ·
    refine ⟨168342673999432494827997319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224456898665909993103996425 168342673999432494827997319)
    ·
      refine ⟨252514010999148742241995979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168342673999432494827997319 252514010999148742241995979)
      ·
        refine ⟨378771016498723113362993969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252514010999148742241995979 378771016498723113362993969)
        ·
          refine ⟨284078262374042335022245477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 378771016498723113362993969 284078262374042335022245477)
          ·
            refine ⟨53264674195132937816671027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 284078262374042335022245477 53264674195132937816671027)
            ·
              refine ⟨79897011292699406725006541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53264674195132937816671027 79897011292699406725006541)
              ·
                refine ⟨29961379234762277521877453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79897011292699406725006541 29961379234762277521877453)
                ·
                  refine ⟨11235517213035854070704045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29961379234762277521877453 11235517213035854070704045)
                  ·
                    refine ⟨4213318954888445276514017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11235517213035854070704045 4213318954888445276514017)
                    ·
                      refine ⟨3159989216166333957385513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4213318954888445276514017 3159989216166333957385513)
                      ·
                        rfl

theorem cell23_6154057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 3, 3, 3, 2].length) (baseStart_6154057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6154057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6154057 prefixEnd_6154057 := by exact prefixLift 6154057
  have htrace : WordTrace (prefixWord ++ tailWord_6154057) baseStart_6154057 baseEnd_6154057 := by
    simpa [prefixWord, tailWord_6154057, baseEnd_6154057] using wordTrace_append hprefix tailTrace_6154057
  have hstable : (prefixWord ++ tailWord_6154057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6154057).length < 2 ^ (prefixWord ++ tailWord_6154057).sum := by decide
  have hdescent : baseEnd_6154057 < baseStart_6154057 := by decide
  rcases family_descends (prefixWord ++ tailWord_6154057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6154074 : List Nat := [3, 1, 1, 2, 1, 3, 3, 3, 1, 3, 2]
def baseStart_6154074 : Nat := 118140960795 + 6154074 * 2 ^ 59
def prefixEnd_6154074 : Nat := 4983230072969 + 3 ^ 40 * 6154074 * 2
def baseEnd_6154074 : Nat := 3159997945337460390872935

theorem tailTrace_6154074 : CollatzResearch.WordTrace tailWord_6154074 prefixEnd_6154074 3159997945337460390872935 := by
  unfold tailWord_6154074
  simp only [CollatzResearch.WordTrace]
  refine ⟨56114379676712101251841319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149638345804565603338243517 56114379676712101251841319)
  ·
    refine ⟨84171569515068151877761979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56114379676712101251841319 84171569515068151877761979)
    ·
      refine ⟨126257354272602227816642969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84171569515068151877761979 126257354272602227816642969)
      ·
        refine ⟨94693015704451670862482227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126257354272602227816642969 94693015704451670862482227)
        ·
          refine ⟨142039523556677506293723341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94693015704451670862482227 142039523556677506293723341)
          ·
            refine ⟨53264821333754064860146253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 142039523556677506293723341 53264821333754064860146253)
            ·
              refine ⟨19974308000157774322554845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53264821333754064860146253 19974308000157774322554845)
              ·
                refine ⟨7490365500059165370958067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19974308000157774322554845 7490365500059165370958067)
                ·
                  refine ⟨11235548250088748056437101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7490365500059165370958067 11235548250088748056437101)
                  ·
                    refine ⟨4213330593783280521163913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11235548250088748056437101 4213330593783280521163913)
                    ·
                      refine ⟨3159997945337460390872935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4213330593783280521163913 3159997945337460390872935)
                      ·
                        rfl

theorem cell23_6154074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 3, 1, 3, 2].length) (baseStart_6154074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6154074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6154074 prefixEnd_6154074 := by exact prefixLift 6154074
  have htrace : WordTrace (prefixWord ++ tailWord_6154074) baseStart_6154074 baseEnd_6154074 := by
    simpa [prefixWord, tailWord_6154074, baseEnd_6154074] using wordTrace_append hprefix tailTrace_6154074
  have hstable : (prefixWord ++ tailWord_6154074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6154074).length < 2 ^ (prefixWord ++ tailWord_6154074).sum := by decide
  have hdescent : baseEnd_6154074 < baseStart_6154074 := by decide
  rcases family_descends (prefixWord ++ tailWord_6154074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6154080 : List Nat := [2, 1, 1, 3, 3, 2, 1, 2, 2, 6]
def baseStart_6154080 : Nat := 118140960795 + 6154080 * 2 ^ 59
def prefixEnd_6154080 : Nat := 4983230072969 + 3 ^ 40 * 6154080 * 2
def baseEnd_6154080 : Nat := 1053333675407129122465969

theorem tailTrace_6154080 : CollatzResearch.WordTrace tailWord_6154080 prefixEnd_6154080 1053333675407129122465969 := by
  unfold tailWord_6154080
  simp only [CollatzResearch.WordTrace]
  refine ⟨112228868772413334016041847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149638491696551112021389129 112228868772413334016041847)
  ·
    refine ⟨168343303158620001024062771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112228868772413334016041847 168343303158620001024062771)
    ·
      refine ⟨252514954737930001536094157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168343303158620001024062771 252514954737930001536094157)
      ·
        refine ⟨94693108026723750576035309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 252514954737930001536094157 94693108026723750576035309)
        ·
          refine ⟨35509915510021406466013241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94693108026723750576035309 35509915510021406466013241)
          ·
            refine ⟨26632436632516054849509931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35509915510021406466013241 26632436632516054849509931)
            ·
              refine ⟨39948654948774082274264897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26632436632516054849509931 39948654948774082274264897)
              ·
                refine ⟨29961491211580561705698673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39948654948774082274264897 29961491211580561705698673)
                ·
                  refine ⟨22471118408685421279274005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29961491211580561705698673 22471118408685421279274005)
                  ·
                    refine ⟨1053333675407129122465969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22471118408685421279274005 1053333675407129122465969)
                    ·
                      rfl

theorem cell23_6154080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 2, 2, 6].length) (baseStart_6154080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6154080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6154080 prefixEnd_6154080 := by exact prefixLift 6154080
  have htrace : WordTrace (prefixWord ++ tailWord_6154080) baseStart_6154080 baseEnd_6154080 := by
    simpa [prefixWord, tailWord_6154080, baseEnd_6154080] using wordTrace_append hprefix tailTrace_6154080
  have hstable : (prefixWord ++ tailWord_6154080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6154080).length < 2 ^ (prefixWord ++ tailWord_6154080).sum := by decide
  have hdescent : baseEnd_6154080 < baseStart_6154080 := by decide
  rcases family_descends (prefixWord ++ tailWord_6154080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6154147 : List Nat := [1, 1, 1, 4, 1, 2, 1, 3, 2, 5, 2]
def baseStart_6154147 : Nat := 118140960795 + 6154147 * 2 ^ 59
def prefixEnd_6154147 : Nat := 4983230072969 + 3 ^ 40 * 6154147 * 2
def baseEnd_6154147 : Nat := 3160035429425238605260099

theorem tailTrace_6154147 : CollatzResearch.WordTrace tailWord_6154147 prefixEnd_6154147 3160035429425238605260099 := by
  unfold tailWord_6154147
  simp only [CollatzResearch.WordTrace]
  refine ⟨224460181235583938474772695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149640120823722625649848463 224460181235583938474772695)
  ·
    refine ⟨336690271853375907712159043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224460181235583938474772695 336690271853375907712159043)
    ·
      refine ⟨505035407780063861568238565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 336690271853375907712159043 505035407780063861568238565)
      ·
        refine ⟨94694138958761974044044731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 505035407780063861568238565 94694138958761974044044731)
        ·
          refine ⟨142041208438142961066067097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94694138958761974044044731 142041208438142961066067097)
          ·
            refine ⟨106530906328607220799550323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142041208438142961066067097 106530906328607220799550323)
            ·
              refine ⟨159796359492910831199325485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106530906328607220799550323 159796359492910831199325485)
              ·
                refine ⟨59923634809841561699747057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 159796359492910831199325485 59923634809841561699747057)
                ·
                  refine ⟨44942726107381171274810293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59923634809841561699747057 44942726107381171274810293)
                  ·
                    refine ⟨4213380572566984807013465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44942726107381171274810293 4213380572566984807013465)
                    ·
                      refine ⟨3160035429425238605260099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4213380572566984807013465 3160035429425238605260099)
                      ·
                        rfl

theorem cell23_6154147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 3, 2, 5, 2].length) (baseStart_6154147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6154147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6154147 prefixEnd_6154147 := by exact prefixLift 6154147
  have htrace : WordTrace (prefixWord ++ tailWord_6154147) baseStart_6154147 baseEnd_6154147 := by
    simpa [prefixWord, tailWord_6154147, baseEnd_6154147] using wordTrace_append hprefix tailTrace_6154147
  have hstable : (prefixWord ++ tailWord_6154147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6154147).length < 2 ^ (prefixWord ++ tailWord_6154147).sum := by decide
  have hdescent : baseEnd_6154147 < baseStart_6154147 := by decide
  rcases family_descends (prefixWord ++ tailWord_6154147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6154174 : List Nat := [4, 2, 1, 1, 1, 4, 2, 1, 2, 5]
def baseStart_6154174 : Nat := 118140960795 + 6154174 * 2 ^ 59
def prefixEnd_6154174 : Nat := 4983230072969 + 3 ^ 40 * 6154174 * 2
def baseEnd_6154174 : Nat := 1053349764467636666540825

theorem tailTrace_6154174 : CollatzResearch.WordTrace tailWord_6154174 prefixEnd_6154174 1053349764467636666540825 := by
  unfold tailWord_6154174
  simp only [CollatzResearch.WordTrace]
  refine ⟨28057645750810765260750697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149640777337657414724003717 28057645750810765260750697)
  ·
    refine ⟨21043234313108073945563023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28057645750810765260750697 21043234313108073945563023)
    ·
      refine ⟨31564851469662110918344535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21043234313108073945563023 31564851469662110918344535)
      ·
        refine ⟨47347277204493166377516803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31564851469662110918344535 47347277204493166377516803)
        ·
          refine ⟨71020915806739749566275205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47347277204493166377516803 71020915806739749566275205)
          ·
            refine ⟨13316421713763703043676601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71020915806739749566275205 13316421713763703043676601)
            ·
              refine ⟨9987316285322777282757451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13316421713763703043676601 9987316285322777282757451)
              ·
                refine ⟨14980974427984165924136177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9987316285322777282757451 14980974427984165924136177)
                ·
                  refine ⟨11235730820988124443102133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14980974427984165924136177 11235730820988124443102133)
                  ·
                    refine ⟨1053349764467636666540825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11235730820988124443102133 1053349764467636666540825)
                    ·
                      rfl

theorem cell23_6154174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2, 1, 2, 5].length) (baseStart_6154174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6154174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6154174 prefixEnd_6154174 := by exact prefixLift 6154174
  have htrace : WordTrace (prefixWord ++ tailWord_6154174) baseStart_6154174 baseEnd_6154174 := by
    simpa [prefixWord, tailWord_6154174, baseEnd_6154174] using wordTrace_append hprefix tailTrace_6154174
  have hstable : (prefixWord ++ tailWord_6154174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6154174).length < 2 ^ (prefixWord ++ tailWord_6154174).sum := by decide
  have hdescent : baseEnd_6154174 < baseStart_6154174 := by decide
  rcases family_descends (prefixWord ++ tailWord_6154174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6154238 : List Nat := [4, 2, 2, 2, 1, 1, 1, 5, 1, 4]
def baseStart_6154238 : Nat := 118140960795 + 6154238 * 2 ^ 59
def prefixEnd_6154238 : Nat := 4983230072969 + 3 ^ 40 * 6154238 * 2
def baseEnd_6154238 : Nat := 1053360718721599249740727

theorem tailTrace_6154238 : CollatzResearch.WordTrace tailWord_6154238 prefixEnd_6154238 1053360718721599249740727 := by
  unfold tailWord_6154238
  simp only [CollatzResearch.WordTrace]
  refine ⟨28057937534781782627041921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149642333518836174010890245 28057937534781782627041921)
  ·
    refine ⟨21043453151086336970281441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28057937534781782627041921 21043453151086336970281441)
    ·
      refine ⟨15782589863314752727711081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21043453151086336970281441 15782589863314752727711081)
      ·
        refine ⟨11836942397486064545783311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15782589863314752727711081 11836942397486064545783311)
        ·
          refine ⟨17755413596229096818674967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11836942397486064545783311 17755413596229096818674967)
          ·
            refine ⟨26633120394343645228012451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17755413596229096818674967 26633120394343645228012451)
            ·
              refine ⟨39949680591515467842018677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26633120394343645228012451 39949680591515467842018677)
              ·
                refine ⟨3745282555454575110189251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39949680591515467842018677 3745282555454575110189251)
                ·
                  refine ⟨5617923833181862665283877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3745282555454575110189251 5617923833181862665283877)
                  ·
                    refine ⟨1053360718721599249740727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5617923833181862665283877 1053360718721599249740727)
                    ·
                      rfl

theorem cell23_6154238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 5, 1, 4].length) (baseStart_6154238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6154238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6154238 prefixEnd_6154238 := by exact prefixLift 6154238
  have htrace : WordTrace (prefixWord ++ tailWord_6154238) baseStart_6154238 baseEnd_6154238 := by
    simpa [prefixWord, tailWord_6154238, baseEnd_6154238] using wordTrace_append hprefix tailTrace_6154238
  have hstable : (prefixWord ++ tailWord_6154238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6154238).length < 2 ^ (prefixWord ++ tailWord_6154238).sum := by decide
  have hdescent : baseEnd_6154238 < baseStart_6154238 := by decide
  rcases family_descends (prefixWord ++ tailWord_6154238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6154267 : List Nat := [1, 1, 1, 1, 1, 1, 3, 6, 3, 1, 4]
def baseStart_6154267 : Nat := 118140960795 + 6154267 * 2 ^ 59
def prefixEnd_6154267 : Nat := 4983230072969 + 3 ^ 40 * 6154267 * 2
def baseEnd_6154267 : Nat := 3160097047103778135759547

theorem tailTrace_6154267 : CollatzResearch.WordTrace tailWord_6154267 prefixEnd_6154267 3160097047103778135759547 := by
  unfold tailWord_6154267
  simp only [CollatzResearch.WordTrace]
  refine ⟨224464557995149198969141055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149643038663432799312760703 224464557995149198969141055)
  ·
    refine ⟨336696836992723798453711583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224464557995149198969141055 336696836992723798453711583)
    ·
      refine ⟨505045255489085697680567375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 336696836992723798453711583 505045255489085697680567375)
      ·
        refine ⟨757567883233628546520851063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 505045255489085697680567375 757567883233628546520851063)
        ·
          refine ⟨1136351824850442819781276595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 757567883233628546520851063 1136351824850442819781276595)
          ·
            refine ⟨1704527737275664229671914893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1136351824850442819781276595 1704527737275664229671914893)
            ·
              refine ⟨639197901478374086126968085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1704527737275664229671914893 639197901478374086126968085)
              ·
                refine ⟨29962401631798785287201629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 639197901478374086126968085 29962401631798785287201629)
                ·
                  refine ⟨11235900611924544482700611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29962401631798785287201629 11235900611924544482700611)
                  ·
                    refine ⟨16853850917886816724050917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11235900611924544482700611 16853850917886816724050917)
                    ·
                      refine ⟨3160097047103778135759547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16853850917886816724050917 3160097047103778135759547)
                      ·
                        rfl

theorem cell23_6154267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 6, 3, 1, 4].length) (baseStart_6154267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6154267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6154267 prefixEnd_6154267 := by exact prefixLift 6154267
  have htrace : WordTrace (prefixWord ++ tailWord_6154267) baseStart_6154267 baseEnd_6154267 := by
    simpa [prefixWord, tailWord_6154267, baseEnd_6154267] using wordTrace_append hprefix tailTrace_6154267
  have hstable : (prefixWord ++ tailWord_6154267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6154267).length < 2 ^ (prefixWord ++ tailWord_6154267).sum := by decide
  have hdescent : baseEnd_6154267 < baseStart_6154267 := by decide
  rcases family_descends (prefixWord ++ tailWord_6154267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6154294 : List Nat := [5, 1, 2, 1, 1, 1, 2, 1, 3, 6]
def baseStart_6154294 : Nat := 118140960795 + 6154294 * 2 ^ 59
def prefixEnd_6154294 : Nat := 4983230072969 + 3 ^ 40 * 6154294 * 2
def baseEnd_6154294 : Nat := 1053370303693816510040641

theorem tailTrace_6154294 : CollatzResearch.WordTrace tailWord_6154294 prefixEnd_6154294 1053370303693816510040641 := by
  unfold tailWord_6154294
  simp only [CollatzResearch.WordTrace]
  refine ⟨14029096422878211411273371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 149643695177367588386915957 14029096422878211411273371)
  ·
    refine ⟨21043644634317317116910057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14029096422878211411273371 21043644634317317116910057)
    ·
      refine ⟨15782733475737987837682543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21043644634317317116910057 15782733475737987837682543)
      ·
        refine ⟨23674100213606981756523815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15782733475737987837682543 23674100213606981756523815)
        ·
          refine ⟨35511150320410472634785723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23674100213606981756523815 35511150320410472634785723)
          ·
            refine ⟨53266725480615708952178585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35511150320410472634785723 53266725480615708952178585)
            ·
              refine ⟨39950044110461781714133939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53266725480615708952178585 39950044110461781714133939)
              ·
                refine ⟨59925066165692672571200909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39950044110461781714133939 59925066165692672571200909)
                ·
                  refine ⟨22471899812134752214200341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59925066165692672571200909 22471899812134752214200341)
                  ·
                    refine ⟨1053370303693816510040641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22471899812134752214200341 1053370303693816510040641)
                    ·
                      rfl

theorem cell23_6154294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_6154294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6154294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6154294 prefixEnd_6154294 := by exact prefixLift 6154294
  have htrace : WordTrace (prefixWord ++ tailWord_6154294) baseStart_6154294 baseEnd_6154294 := by
    simpa [prefixWord, tailWord_6154294, baseEnd_6154294] using wordTrace_append hprefix tailTrace_6154294
  have hstable : (prefixWord ++ tailWord_6154294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6154294).length < 2 ^ (prefixWord ++ tailWord_6154294).sum := by decide
  have hdescent : baseEnd_6154294 < baseStart_6154294 := by decide
  rcases family_descends (prefixWord ++ tailWord_6154294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6154304 : List Nat := [2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 5]
def baseStart_6154304 : Nat := 118140960795 + 6154304 * 2 ^ 59
def prefixEnd_6154304 : Nat := 4983230072969 + 3 ^ 40 * 6154304 * 2
def baseEnd_6154304 : Nat := 3160116045887994490996877

theorem tailTrace_6154304 : CollatzResearch.WordTrace tailWord_6154304 prefixEnd_6154304 3160116045887994490996877 := by
  unfold tailWord_6154304
  simp only [CollatzResearch.WordTrace]
  refine ⟨112232953748007577144118983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149643938330676769525491977 112232953748007577144118983)
  ·
    refine ⟨168349430622011365716178475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112232953748007577144118983 168349430622011365716178475)
    ·
      refine ⟨252524145933017048574267713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168349430622011365716178475 252524145933017048574267713)
      ·
        refine ⟨189393109449762786430700785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 252524145933017048574267713 189393109449762786430700785)
        ·
          refine ⟨142044832087322089823025589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189393109449762786430700785 142044832087322089823025589)
          ·
            refine ⟨13316703008186445920908649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 142044832087322089823025589 13316703008186445920908649)
            ·
              refine ⟨9987527256139834440681487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13316703008186445920908649 9987527256139834440681487)
              ·
                refine ⟨14981290884209751661022231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9987527256139834440681487 14981290884209751661022231)
                ·
                  refine ⟨22471936326314627491533347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14981290884209751661022231 22471936326314627491533347)
                  ·
                    refine ⟨33707904489471941237300021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22471936326314627491533347 33707904489471941237300021)
                    ·
                      refine ⟨3160116045887994490996877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33707904489471941237300021 3160116045887994490996877)
                      ·
                        rfl

theorem cell23_6154304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 5].length) (baseStart_6154304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6154304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6154304 prefixEnd_6154304 := by exact prefixLift 6154304
  have htrace : WordTrace (prefixWord ++ tailWord_6154304) baseStart_6154304 baseEnd_6154304 := by
    simpa [prefixWord, tailWord_6154304, baseEnd_6154304] using wordTrace_append hprefix tailTrace_6154304
  have hstable : (prefixWord ++ tailWord_6154304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6154304).length < 2 ^ (prefixWord ++ tailWord_6154304).sum := by decide
  have hdescent : baseEnd_6154304 < baseStart_6154304 := by decide
  rcases family_descends (prefixWord ++ tailWord_6154304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6154318 : List Nat := [4, 1, 1, 1, 1, 4, 3, 1, 3, 2, 2]
def baseStart_6154318 : Nat := 118140960795 + 6154318 * 2 ^ 59
def prefixEnd_6154318 : Nat := 4983230072969 + 3 ^ 40 * 6154318 * 2
def baseEnd_6154318 : Nat := 3160123234617157436221813

theorem tailTrace_6154318 : CollatzResearch.WordTrace tailWord_6154318 prefixEnd_6154318 3160123234617157436221813 := by
  unfold tailWord_6154318
  simp only [CollatzResearch.WordTrace]
  refine ⟨28058302264745554334905951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149644278745309623119498405 28058302264745554334905951)
  ·
    refine ⟨42087453397118331502358927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28058302264745554334905951 42087453397118331502358927)
    ·
      refine ⟨63131180095677497253538391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42087453397118331502358927 63131180095677497253538391)
      ·
        refine ⟨94696770143516245880307587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63131180095677497253538391 94696770143516245880307587)
        ·
          refine ⟨142045155215274368820461381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94696770143516245880307587 142045155215274368820461381)
          ·
            refine ⟨26633466602863944153836509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 142045155215274368820461381 26633466602863944153836509)
            ·
              refine ⟨9987549976073979057688691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26633466602863944153836509 9987549976073979057688691)
              ·
                refine ⟨14981324964110968586533037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9987549976073979057688691 14981324964110968586533037)
                ·
                  refine ⟨5617996861541613219949889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14981324964110968586533037 5617996861541613219949889)
                  ·
                    refine ⟨4213497646156209914962417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5617996861541613219949889 4213497646156209914962417)
                    ·
                      refine ⟨3160123234617157436221813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4213497646156209914962417 3160123234617157436221813)
                      ·
                        rfl

theorem cell23_6154318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3, 1, 3, 2, 2].length) (baseStart_6154318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6154318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6154318 prefixEnd_6154318 := by exact prefixLift 6154318
  have htrace : WordTrace (prefixWord ++ tailWord_6154318) baseStart_6154318 baseEnd_6154318 := by
    simpa [prefixWord, tailWord_6154318, baseEnd_6154318] using wordTrace_append hprefix tailTrace_6154318
  have hstable : (prefixWord ++ tailWord_6154318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6154318).length < 2 ^ (prefixWord ++ tailWord_6154318).sum := by decide
  have hdescent : baseEnd_6154318 < baseStart_6154318 := by decide
  rcases family_descends (prefixWord ++ tailWord_6154318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6154328 : List Nat := [2, 1, 2, 2, 1, 6, 2, 1, 2, 4]
def baseStart_6154328 : Nat := 118140960795 + 6154328 * 2 ^ 59
def prefixEnd_6154328 : Nat := 4983230072969 + 3 ^ 40 * 6154328 * 2
def baseEnd_6154328 : Nat := 1053376123141234132365589

theorem tailTrace_6154328 : CollatzResearch.WordTrace tailWord_6154328 prefixEnd_6154328 1053376123141234132365589 := by
  unfold tailWord_6154328
  simp only [CollatzResearch.WordTrace]
  refine ⟨112233391423964103193555819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149644521898618804258074425 112233391423964103193555819)
  ·
    refine ⟨168350087135946154790333729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112233391423964103193555819 168350087135946154790333729)
    ·
      refine ⟨126262565351959616092750297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168350087135946154790333729 126262565351959616092750297)
      ·
        refine ⟨94696924013969712069562723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126262565351959616092750297 94696924013969712069562723)
        ·
          refine ⟨142045386020954568104344085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94696924013969712069562723 142045386020954568104344085)
          ·
            refine ⟨6658377469732245379891129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 142045386020954568104344085 6658377469732245379891129)
            ·
              refine ⟨4993783102299184034918347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6658377469732245379891129 4993783102299184034918347)
              ·
                refine ⟨7490674653448776052377521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4993783102299184034918347 7490674653448776052377521)
                ·
                  refine ⟨5618005990086582039283141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7490674653448776052377521 5618005990086582039283141)
                  ·
                    refine ⟨1053376123141234132365589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5618005990086582039283141 1053376123141234132365589)
                    ·
                      rfl

theorem cell23_6154328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 2, 1, 2, 4].length) (baseStart_6154328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6154328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6154328 prefixEnd_6154328 := by exact prefixLift 6154328
  have htrace : WordTrace (prefixWord ++ tailWord_6154328) baseStart_6154328 baseEnd_6154328 := by
    simpa [prefixWord, tailWord_6154328, baseEnd_6154328] using wordTrace_append hprefix tailTrace_6154328
  have hstable : (prefixWord ++ tailWord_6154328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6154328).length < 2 ^ (prefixWord ++ tailWord_6154328).sum := by decide
  have hdescent : baseEnd_6154328 < baseStart_6154328 := by decide
  rcases family_descends (prefixWord ++ tailWord_6154328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6154338 : List Nat := [3, 3, 2, 2, 2, 1, 1, 1, 3, 2, 3]
def baseStart_6154338 : Nat := 118140960795 + 6154338 * 2 ^ 59
def prefixEnd_6154338 : Nat := 4983230072969 + 3 ^ 40 * 6154338 * 2
def baseEnd_6154338 : Nat := 3160133504230247357971721

theorem tailTrace_6154338 : CollatzResearch.WordTrace tailWord_6154338 prefixEnd_6154338 3160133504230247357971721 := by
  unfold tailWord_6154338
  simp only [CollatzResearch.WordTrace]
  refine ⟨56116786894472994523743917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149644765051927985396650445 56116786894472994523743917)
  ·
    refine ⟨21043795085427372946403969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56116786894472994523743917 21043795085427372946403969)
    ·
      refine ⟨15782846314070529709802977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21043795085427372946403969 15782846314070529709802977)
      ·
        refine ⟨11837134735552897282352233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15782846314070529709802977 11837134735552897282352233)
        ·
          refine ⟨8877851051664672961764175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11837134735552897282352233 8877851051664672961764175)
          ·
            refine ⟨13316776577497009442646263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8877851051664672961764175 13316776577497009442646263)
            ·
              refine ⟨19975164866245514163969395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13316776577497009442646263 19975164866245514163969395)
              ·
                refine ⟨29962747299368271245954093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19975164866245514163969395 29962747299368271245954093)
                ·
                  refine ⟨11236030237263101717232785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29962747299368271245954093 11236030237263101717232785)
                  ·
                    refine ⟨8427022677947326287924589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11236030237263101717232785 8427022677947326287924589)
                    ·
                      refine ⟨3160133504230247357971721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8427022677947326287924589 3160133504230247357971721)
                      ·
                        rfl

theorem cell23_6154338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_6154338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6154338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6154338 prefixEnd_6154338 := by exact prefixLift 6154338
  have htrace : WordTrace (prefixWord ++ tailWord_6154338) baseStart_6154338 baseEnd_6154338 := by
    simpa [prefixWord, tailWord_6154338, baseEnd_6154338] using wordTrace_append hprefix tailTrace_6154338
  have hstable : (prefixWord ++ tailWord_6154338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6154338).length < 2 ^ (prefixWord ++ tailWord_6154338).sum := by decide
  have hdescent : baseEnd_6154338 < baseStart_6154338 := by decide
  rcases family_descends (prefixWord ++ tailWord_6154338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6154369 : List Nat := [1, 2, 4, 2, 3, 2, 2, 2, 1, 2, 2]
def baseStart_6154369 : Nat := 118140960795 + 6154369 * 2 ^ 59
def prefixEnd_6154369 : Nat := 4983230072969 + 3 ^ 40 * 6154369 * 2
def baseEnd_6154369 : Nat := 3160149422130536736684079

theorem tailTrace_6154369 : CollatzResearch.WordTrace tailWord_6154369 prefixEnd_6154369 3160149422130536736684079 := by
  unfold tailWord_6154369
  simp only [CollatzResearch.WordTrace]
  refine ⟨224468278240779670389354161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149645518827186446926236107 224468278240779670389354161)
  ·
    refine ⟨168351208680584752792015621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224468278240779670389354161 168351208680584752792015621)
    ·
      refine ⟨31565851627609641148502929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 168351208680584752792015621 31565851627609641148502929)
      ·
        refine ⟨23674388720707230861377197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31565851627609641148502929 23674388720707230861377197)
        ·
          refine ⟨8877895770265211573016449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23674388720707230861377197 8877895770265211573016449)
          ·
            refine ⟨6658421827698908679762337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8877895770265211573016449 6658421827698908679762337)
            ·
              refine ⟨4993816370774181509821753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6658421827698908679762337 4993816370774181509821753)
              ·
                refine ⟨3745362278080636132366315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4993816370774181509821753 3745362278080636132366315)
                ·
                  refine ⟨5618043417120954198549473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3745362278080636132366315 5618043417120954198549473)
                  ·
                    refine ⟨4213532562840715648912105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5618043417120954198549473 4213532562840715648912105)
                    ·
                      refine ⟨3160149422130536736684079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4213532562840715648912105 3160149422130536736684079)
                      ·
                        rfl

theorem cell23_6154369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 2, 2, 1, 2, 2].length) (baseStart_6154369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6154369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6154369 prefixEnd_6154369 := by exact prefixLift 6154369
  have htrace : WordTrace (prefixWord ++ tailWord_6154369) baseStart_6154369 baseEnd_6154369 := by
    simpa [prefixWord, tailWord_6154369, baseEnd_6154369] using wordTrace_append hprefix tailTrace_6154369
  have hstable : (prefixWord ++ tailWord_6154369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6154369).length < 2 ^ (prefixWord ++ tailWord_6154369).sum := by decide
  have hdescent : baseEnd_6154369 < baseStart_6154369 := by decide
  rcases family_descends (prefixWord ++ tailWord_6154369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6154424 : List Nat := [2, 1, 2, 1, 2, 1, 3, 1, 4, 3, 3]
def baseStart_6154424 : Nat := 118140960795 + 6154424 * 2 ^ 59
def prefixEnd_6154424 : Nat := 4983230072969 + 3 ^ 40 * 6154424 * 2
def baseEnd_6154424 : Nat := 3160177663566534021496325

theorem tailTrace_6154424 : CollatzResearch.WordTrace tailWord_6154424 prefixEnd_6154424 3160177663566534021496325 := by
  unfold tailWord_6154424
  simp only [CollatzResearch.WordTrace]
  refine ⟨112235142127790207391303163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149646856170386943188404217 112235142127790207391303163)
  ·
    refine ⟨168352713191685311086954745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112235142127790207391303163 168352713191685311086954745)
    ·
      refine ⟨126264534893763983315216059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168352713191685311086954745 126264534893763983315216059)
      ·
        refine ⟨189396802340645974972824089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126264534893763983315216059 189396802340645974972824089)
        ·
          refine ⟨142047601755484481229618067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189396802340645974972824089 142047601755484481229618067)
          ·
            refine ⟨213071402633226721844427101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142047601755484481229618067 213071402633226721844427101)
            ·
              refine ⟨79901775987460020691660163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 213071402633226721844427101 79901775987460020691660163)
              ·
                refine ⟨119852663981190031037490245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79901775987460020691660163 119852663981190031037490245)
                ·
                  refine ⟨22472374496473130819529421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 119852663981190031037490245 22472374496473130819529421)
                  ·
                    refine ⟨8427140436177424057323533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22472374496473130819529421 8427140436177424057323533)
                    ·
                      refine ⟨3160177663566534021496325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8427140436177424057323533 3160177663566534021496325)
                      ·
                        rfl

theorem cell23_6154424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 4, 3, 3].length) (baseStart_6154424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6154424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6154424 prefixEnd_6154424 := by exact prefixLift 6154424
  have htrace : WordTrace (prefixWord ++ tailWord_6154424) baseStart_6154424 baseEnd_6154424 := by
    simpa [prefixWord, tailWord_6154424, baseEnd_6154424] using wordTrace_append hprefix tailTrace_6154424
  have hstable : (prefixWord ++ tailWord_6154424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6154424).length < 2 ^ (prefixWord ++ tailWord_6154424).sum := by decide
  have hdescent : baseEnd_6154424 < baseStart_6154424 := by decide
  rcases family_descends (prefixWord ++ tailWord_6154424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6154461 : List Nat := [1, 4, 3, 2, 1, 1, 2, 1, 1, 7]
def baseStart_6154461 : Nat := 118140960795 + 6154461 * 2 ^ 59
def prefixEnd_6154461 : Nat := 4983230072969 + 3 ^ 40 * 6154461 * 2
def baseEnd_6154461 : Nat := 1053398887450250125577885

theorem tailTrace_6154461 : CollatzResearch.WordTrace tailWord_6154461 prefixEnd_6154461 1053398887450250125577885 := by
  unfold tailWord_6154461
  simp only [CollatzResearch.WordTrace]
  refine ⟨224471633756446370101703237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149647755837630913401135491 224471633756446370101703237)
  ·
    refine ⟨42088431329333694394069357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 224471633756446370101703237 42088431329333694394069357)
    ·
      refine ⟨15783161748500135397776009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42088431329333694394069357 15783161748500135397776009)
      ·
        refine ⟨11837371311375101548332007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15783161748500135397776009 11837371311375101548332007)
        ·
          refine ⟨17756056967062652322498011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11837371311375101548332007 17756056967062652322498011)
          ·
            refine ⟨26634085450593978483747017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17756056967062652322498011 26634085450593978483747017)
            ·
              refine ⟨19975564087945483862810263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26634085450593978483747017 19975564087945483862810263)
              ·
                refine ⟨29963346131918225794215395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19975564087945483862810263 29963346131918225794215395)
                ·
                  refine ⟨44945019197877338691323093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29963346131918225794215395 44945019197877338691323093)
                  ·
                    refine ⟨1053398887450250125577885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44945019197877338691323093 1053398887450250125577885)
                    ·
                      rfl

theorem cell23_6154461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_6154461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6154461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6154461 prefixEnd_6154461 := by exact prefixLift 6154461
  have htrace : WordTrace (prefixWord ++ tailWord_6154461) baseStart_6154461 baseEnd_6154461 := by
    simpa [prefixWord, tailWord_6154461, baseEnd_6154461] using wordTrace_append hprefix tailTrace_6154461
  have hstable : (prefixWord ++ tailWord_6154461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6154461).length < 2 ^ (prefixWord ++ tailWord_6154461).sum := by decide
  have hdescent : baseEnd_6154461 < baseStart_6154461 := by decide
  rcases family_descends (prefixWord ++ tailWord_6154461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6154464 : List Nat := [2, 1, 1, 3, 1, 3, 1, 3, 1, 3, 4]
def baseStart_6154464 : Nat := 118140960795 + 6154464 * 2 ^ 59
def prefixEnd_6154464 : Nat := 4983230072969 + 3 ^ 40 * 6154464 * 2
def baseEnd_6154464 : Nat := 3160198202792713864996141

theorem tailTrace_6154464 : CollatzResearch.WordTrace tailWord_6154464 prefixEnd_6154464 3160198202792713864996141 := by
  unfold tailWord_6154464
  simp only [CollatzResearch.WordTrace]
  refine ⟨112235871587717750807031223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149647828783623667742708297 112235871587717750807031223)
  ·
    refine ⟨168353807381576626210546835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112235871587717750807031223 168353807381576626210546835)
    ·
      refine ⟨252530711072364939315820253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168353807381576626210546835 252530711072364939315820253)
      ·
        refine ⟨94699016652136852243432595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 252530711072364939315820253 94699016652136852243432595)
        ·
          refine ⟨142048524978205278365148893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94699016652136852243432595 142048524978205278365148893)
          ·
            refine ⟨53268196866826979386930835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 142048524978205278365148893 53268196866826979386930835)
            ·
              refine ⟨79902295300240469080396253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53268196866826979386930835 79902295300240469080396253)
              ·
                refine ⟨29963360737590175905148595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79902295300240469080396253 29963360737590175905148595)
                ·
                  refine ⟨44945041106385263857722893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29963360737590175905148595 44945041106385263857722893)
                  ·
                    refine ⟨16854390414894473946646085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44945041106385263857722893 16854390414894473946646085)
                    ·
                      refine ⟨3160198202792713864996141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16854390414894473946646085 3160198202792713864996141)
                      ·
                        rfl

theorem cell23_6154464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3, 4].length) (baseStart_6154464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6154464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6154464 prefixEnd_6154464 := by exact prefixLift 6154464
  have htrace : WordTrace (prefixWord ++ tailWord_6154464) baseStart_6154464 baseEnd_6154464 := by
    simpa [prefixWord, tailWord_6154464, baseEnd_6154464] using wordTrace_append hprefix tailTrace_6154464
  have hstable : (prefixWord ++ tailWord_6154464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6154464).length < 2 ^ (prefixWord ++ tailWord_6154464).sum := by decide
  have hdescent : baseEnd_6154464 < baseStart_6154464 := by decide
  rcases family_descends (prefixWord ++ tailWord_6154464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6154481 : List Nat := [1, 2, 2, 2, 2, 1, 2, 1, 4, 4, 2]
def baseStart_6154481 : Nat := 118140960795 + 6154481 * 2 ^ 59
def prefixEnd_6154481 : Nat := 4983230072969 + 3 ^ 40 * 6154481 * 2
def baseEnd_6154481 : Nat := 3160206931963840298483563

theorem tailTrace_6154481 : CollatzResearch.WordTrace tailWord_6154481 prefixEnd_6154481 3160206931963840298483563 := by
  unfold tailWord_6154481
  simp only [CollatzResearch.WordTrace]
  refine ⟨224472363216373913517431297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149648242144249275678287531 224472363216373913517431297)
  ·
    refine ⟨168354272412280435138073473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224472363216373913517431297 168354272412280435138073473)
    ·
      refine ⟨126265704309210326353555105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168354272412280435138073473 126265704309210326353555105)
      ·
        refine ⟨94699278231907744765166329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126265704309210326353555105 94699278231907744765166329)
        ·
          refine ⟨71024458673930808573874747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94699278231907744765166329 71024458673930808573874747)
          ·
            refine ⟨106536688010896212860812121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71024458673930808573874747 106536688010896212860812121)
            ·
              refine ⟨79902516008172159645609091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106536688010896212860812121 79902516008172159645609091)
              ·
                refine ⟨119853774012258239468413637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79902516008172159645609091 119853774012258239468413637)
                ·
                  refine ⟨22472582627298419900327557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 119853774012258239468413637 22472582627298419900327557)
                  ·
                    refine ⟨4213609242618453731311417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22472582627298419900327557 4213609242618453731311417)
                    ·
                      refine ⟨3160206931963840298483563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4213609242618453731311417 3160206931963840298483563)
                      ·
                        rfl

theorem cell23_6154481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 4, 4, 2].length) (baseStart_6154481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6154481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6154481 prefixEnd_6154481 := by exact prefixLift 6154481
  have htrace : WordTrace (prefixWord ++ tailWord_6154481) baseStart_6154481 baseEnd_6154481 := by
    simpa [prefixWord, tailWord_6154481, baseEnd_6154481] using wordTrace_append hprefix tailTrace_6154481
  have hstable : (prefixWord ++ tailWord_6154481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6154481).length < 2 ^ (prefixWord ++ tailWord_6154481).sum := by decide
  have hdescent : baseEnd_6154481 < baseStart_6154481 := by decide
  rcases family_descends (prefixWord ++ tailWord_6154481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6154524 : List Nat := [2, 2, 3, 1, 1, 1, 1, 2, 1, 1, 8]
def baseStart_6154524 : Nat := 118140960795 + 6154524 * 2 ^ 59
def prefixEnd_6154524 : Nat := 4983230072969 + 3 ^ 40 * 6154524 * 2
def baseEnd_6154524 : Nat := 3160229011631983630245865

theorem tailTrace_6154524 : CollatzResearch.WordTrace tailWord_6154524 prefixEnd_6154524 3160229011631983630245865 := by
  unfold tailWord_6154524
  simp only [CollatzResearch.WordTrace]
  refine ⟨112236965777609065930623313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149649287703478754574164417 112236965777609065930623313)
  ·
    refine ⟨84177724333206799447967485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112236965777609065930623313 84177724333206799447967485)
    ·
      refine ⟨31566646624952549792987807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84177724333206799447967485 31566646624952549792987807)
      ·
        refine ⟨47349969937428824689481711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31566646624952549792987807 47349969937428824689481711)
        ·
          refine ⟨71024954906143237034222567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47349969937428824689481711 71024954906143237034222567)
          ·
            refine ⟨106537432359214855551333851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71024954906143237034222567 106537432359214855551333851)
            ·
              refine ⟨159806148538822283327000777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106537432359214855551333851 159806148538822283327000777)
              ·
                refine ⟨119854611404116712495250583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 159806148538822283327000777 119854611404116712495250583)
                ·
                  refine ⟨179781917106175068742875875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 119854611404116712495250583 179781917106175068742875875)
                  ·
                    refine ⟨269672875659262603114313813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 179781917106175068742875875 269672875659262603114313813)
                    ·
                      refine ⟨3160229011631983630245865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 269672875659262603114313813 3160229011631983630245865)
                      ·
                        rfl

theorem cell23_6154524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_6154524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6154524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6154524 prefixEnd_6154524 := by exact prefixLift 6154524
  have htrace : WordTrace (prefixWord ++ tailWord_6154524) baseStart_6154524 baseEnd_6154524 := by
    simpa [prefixWord, tailWord_6154524, baseEnd_6154524] using wordTrace_append hprefix tailTrace_6154524
  have hstable : (prefixWord ++ tailWord_6154524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6154524).length < 2 ^ (prefixWord ++ tailWord_6154524).sum := by decide
  have hdescent : baseEnd_6154524 < baseStart_6154524 := by decide
  rcases family_descends (prefixWord ++ tailWord_6154524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6154571 : List Nat := [1, 1, 1, 1, 3, 1, 1, 3, 1, 8, 2]
def baseStart_6154571 : Nat := 118140960795 + 6154571 * 2 ^ 59
def prefixEnd_6154571 : Nat := 4983230072969 + 3 ^ 40 * 6154571 * 2
def baseEnd_6154571 : Nat := 3160253145222744946358149

theorem tailTrace_6154571 : CollatzResearch.WordTrace tailWord_6154571 prefixEnd_6154571 3160253145222744946358149 := by
  unfold tailWord_6154571
  simp only [CollatzResearch.WordTrace]
  refine ⟨224475645786047858888207567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149650430524031905925471711 224475645786047858888207567)
  ·
    refine ⟨336713468679071788332311351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224475645786047858888207567 336713468679071788332311351)
    ·
      refine ⟨505070203018607682498467027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 336713468679071788332311351 505070203018607682498467027)
      ·
        refine ⟨757605304527911523747700541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 505070203018607682498467027 757605304527911523747700541)
        ·
          refine ⟨284101989197966821405387703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 757605304527911523747700541 284101989197966821405387703)
          ·
            refine ⟨426152983796950232108081555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 284101989197966821405387703 426152983796950232108081555)
            ·
              refine ⟨639229475695425348162122333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 426152983796950232108081555 639229475695425348162122333)
              ·
                refine ⟨239711053385784505560795875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 639229475695425348162122333 239711053385784505560795875)
                ·
                  refine ⟨359566580078676758341193813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 239711053385784505560795875 359566580078676758341193813)
                  ·
                    refine ⟨4213670860296993261810865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 359566580078676758341193813 4213670860296993261810865)
                    ·
                      refine ⟨3160253145222744946358149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4213670860296993261810865 3160253145222744946358149)
                      ·
                        rfl

theorem cell23_6154571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 8, 2].length) (baseStart_6154571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6154571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6154571 prefixEnd_6154571 := by exact prefixLift 6154571
  have htrace : WordTrace (prefixWord ++ tailWord_6154571) baseStart_6154571 baseEnd_6154571 := by
    simpa [prefixWord, tailWord_6154571, baseEnd_6154571] using wordTrace_append hprefix tailTrace_6154571
  have hstable : (prefixWord ++ tailWord_6154571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6154571).length < 2 ^ (prefixWord ++ tailWord_6154571).sum := by decide
  have hdescent : baseEnd_6154571 < baseStart_6154571 := by decide
  rcases family_descends (prefixWord ++ tailWord_6154571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6154625 : List Nat := [1, 2, 4, 3, 1, 1, 1, 4, 1, 2, 3]
def baseStart_6154625 : Nat := 118140960795 + 6154625 * 2 ^ 59
def prefixEnd_6154625 : Nat := 4983230072969 + 3 ^ 40 * 6154625 * 2
def baseEnd_6154625 : Nat := 3160280873178087735082901

theorem tailTrace_6154625 : CollatzResearch.WordTrace tailWord_6154625 prefixEnd_6154625 3160280873178087735082901 := by
  unfold tailWord_6154625
  simp only [CollatzResearch.WordTrace]
  refine ⟨224477615327852226110673329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149651743551901484073782219 224477615327852226110673329)
  ·
    refine ⟨168358211495889169583004997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224477615327852226110673329 168358211495889169583004997)
    ·
      refine ⟨31567164655479219296813437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 168358211495889169583004997 31567164655479219296813437)
      ·
        refine ⟨11837686745804707236305039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31567164655479219296813437 11837686745804707236305039)
        ·
          refine ⟨17756530118707060854457559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11837686745804707236305039 17756530118707060854457559)
          ·
            refine ⟨26634795178060591281686339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17756530118707060854457559 26634795178060591281686339)
            ·
              refine ⟨39952192767090886922529509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26634795178060591281686339 39952192767090886922529509)
              ·
                refine ⟨7491036143829541297974283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39952192767090886922529509 7491036143829541297974283)
                ·
                  refine ⟨11236554215744311946961425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7491036143829541297974283 11236554215744311946961425)
                  ·
                    refine ⟨8427415661808233960221069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11236554215744311946961425 8427415661808233960221069)
                    ·
                      refine ⟨3160280873178087735082901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8427415661808233960221069 3160280873178087735082901)
                      ·
                        rfl

theorem cell23_6154625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_6154625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6154625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6154625 prefixEnd_6154625 := by exact prefixLift 6154625
  have htrace : WordTrace (prefixWord ++ tailWord_6154625) baseStart_6154625 baseEnd_6154625 := by
    simpa [prefixWord, tailWord_6154625, baseEnd_6154625] using wordTrace_append hprefix tailTrace_6154625
  have hstable : (prefixWord ++ tailWord_6154625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6154625).length < 2 ^ (prefixWord ++ tailWord_6154625).sum := by decide
  have hdescent : baseEnd_6154625 < baseStart_6154625 := by decide
  rcases family_descends (prefixWord ++ tailWord_6154625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6154655 : List Nat := [1, 1, 2, 5, 1, 1, 2, 4, 2, 1, 3]
def baseStart_6154655 : Nat := 118140960795 + 6154655 * 2 ^ 59
def prefixEnd_6154655 : Nat := 4983230072969 + 3 ^ 40 * 6154655 * 2
def baseEnd_6154655 : Nat := 3160296277597722617707763

theorem tailTrace_6154655 : CollatzResearch.WordTrace tailWord_6154655 prefixEnd_6154655 3160296277597722617707763 := by
  unfold tailWord_6154655
  simp only [CollatzResearch.WordTrace]
  refine ⟨224478709517743541234265419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149652473011829027489510279 224478709517743541234265419)
  ·
    refine ⟨336718064276615311851398129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224478709517743541234265419 336718064276615311851398129)
    ·
      refine ⟨252538548207461483888548597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 336718064276615311851398129 252538548207461483888548597)
      ·
        refine ⟨23675488894449514114551431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 252538548207461483888548597 23675488894449514114551431)
        ·
          refine ⟨35513233341674271171827147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23675488894449514114551431 35513233341674271171827147)
          ·
            refine ⟨53269850012511406757740721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35513233341674271171827147 53269850012511406757740721)
            ·
              refine ⟨39952387509383555068305541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53269850012511406757740721 39952387509383555068305541)
              ·
                refine ⟨7491072658009416575307289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39952387509383555068305541 7491072658009416575307289)
                ·
                  refine ⟨5618304493507062431480467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7491072658009416575307289 5618304493507062431480467)
                  ·
                    refine ⟨8427456740260593647220701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5618304493507062431480467 8427456740260593647220701)
                    ·
                      refine ⟨3160296277597722617707763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8427456740260593647220701 3160296277597722617707763)
                      ·
                        rfl

theorem cell23_6154655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 4, 2, 1, 3].length) (baseStart_6154655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6154655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6154655 prefixEnd_6154655 := by exact prefixLift 6154655
  have htrace : WordTrace (prefixWord ++ tailWord_6154655) baseStart_6154655 baseEnd_6154655 := by
    simpa [prefixWord, tailWord_6154655, baseEnd_6154655] using wordTrace_append hprefix tailTrace_6154655
  have hstable : (prefixWord ++ tailWord_6154655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6154655).length < 2 ^ (prefixWord ++ tailWord_6154655).sum := by decide
  have hdescent : baseEnd_6154655 < baseStart_6154655 := by decide
  rcases family_descends (prefixWord ++ tailWord_6154655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6154661 : List Nat := [1, 3, 1, 2, 1, 1, 4, 1, 2, 3, 4]
def baseStart_6154661 : Nat := 118140960795 + 6154661 * 2 ^ 59
def prefixEnd_6154661 : Nat := 4983230072969 + 3 ^ 40 * 6154661 * 2
def baseEnd_6154661 : Nat := 3160299358481649594232735

theorem tailTrace_6154661 : CollatzResearch.WordTrace tailWord_6154661 prefixEnd_6154661 3160299358481649594232735 := by
  unfold tailWord_6154661
  simp only [CollatzResearch.WordTrace]
  refine ⟨224478928355721804258983837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149652618903814536172655891 224478928355721804258983837)
  ·
    refine ⟨84179598133395676597118939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 224478928355721804258983837 84179598133395676597118939)
    ·
      refine ⟨126269397200093514895678409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84179598133395676597118939 126269397200093514895678409)
      ·
        refine ⟨94702047900070136171758807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126269397200093514895678409 94702047900070136171758807)
        ·
          refine ⟨142053071850105204257638211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94702047900070136171758807 142053071850105204257638211)
          ·
            refine ⟨213079607775157806386457317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142053071850105204257638211 213079607775157806386457317)
            ·
              refine ⟨39952426457842088697460747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 213079607775157806386457317 39952426457842088697460747)
              ·
                refine ⟨59928639686763133046191121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39952426457842088697460747 59928639686763133046191121)
                ·
                  refine ⟨44946479765072349784643341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59928639686763133046191121 44946479765072349784643341)
                  ·
                    refine ⟨16854929911902131169241253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44946479765072349784643341 16854929911902131169241253)
                    ·
                      refine ⟨3160299358481649594232735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16854929911902131169241253 3160299358481649594232735)
                      ·
                        rfl

theorem cell23_6154661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 1, 2, 3, 4].length) (baseStart_6154661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6154661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6154661 prefixEnd_6154661 := by exact prefixLift 6154661
  have htrace : WordTrace (prefixWord ++ tailWord_6154661) baseStart_6154661 baseEnd_6154661 := by
    simpa [prefixWord, tailWord_6154661, baseEnd_6154661] using wordTrace_append hprefix tailTrace_6154661
  have hstable : (prefixWord ++ tailWord_6154661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6154661).length < 2 ^ (prefixWord ++ tailWord_6154661).sum := by decide
  have hdescent : baseEnd_6154661 < baseStart_6154661 := by decide
  rcases family_descends (prefixWord ++ tailWord_6154661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6154676 : List Nat := [2, 5, 2, 2, 1, 2, 1, 2, 1, 2, 3]
def baseStart_6154676 : Nat := 118140960795 + 6154676 * 2 ^ 59
def prefixEnd_6154676 : Nat := 4983230072969 + 3 ^ 40 * 6154676 * 2
def baseEnd_6154676 : Nat := 3160307060691467035545167

theorem tailTrace_6154676 : CollatzResearch.WordTrace tailWord_6154676 prefixEnd_6154676 3160307060691467035545167 := by
  unfold tailWord_6154676
  simp only [CollatzResearch.WordTrace]
  refine ⟨112239737725333730910389941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149652983633778307880519921 112239737725333730910389941)
  ·
    refine ⟨10522475411750037272849057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 112239737725333730910389941 10522475411750037272849057)
    ·
      refine ⟨7891856558812527954636793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10522475411750037272849057 7891856558812527954636793)
      ·
        refine ⟨5918892419109395965977595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7891856558812527954636793 5918892419109395965977595)
        ·
          refine ⟨8878338628664093948966393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5918892419109395965977595 8878338628664093948966393)
          ·
            refine ⟨6658753971498070461724795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8878338628664093948966393 6658753971498070461724795)
            ·
              refine ⟨9988130957247105692587193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6658753971498070461724795 9988130957247105692587193)
              ·
                refine ⟨7491098217935329269440395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9988130957247105692587193 7491098217935329269440395)
                ·
                  refine ⟨11236647326902993904160593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7491098217935329269440395 11236647326902993904160593)
                  ·
                    refine ⟨8427485495177245428120445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11236647326902993904160593 8427485495177245428120445)
                    ·
                      refine ⟨3160307060691467035545167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8427485495177245428120445 3160307060691467035545167)
                      ·
                        rfl

theorem cell23_6154676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_6154676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6154676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6154676 prefixEnd_6154676 := by exact prefixLift 6154676
  have htrace : WordTrace (prefixWord ++ tailWord_6154676) baseStart_6154676 baseEnd_6154676 := by
    simpa [prefixWord, tailWord_6154676, baseEnd_6154676] using wordTrace_append hprefix tailTrace_6154676
  have hstable : (prefixWord ++ tailWord_6154676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6154676).length < 2 ^ (prefixWord ++ tailWord_6154676).sum := by decide
  have hdescent : baseEnd_6154676 < baseStart_6154676 := by decide
  rcases family_descends (prefixWord ++ tailWord_6154676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6154689 : List Nat := [1, 2, 7, 1, 1, 1, 1, 2, 1, 3, 3]
def baseStart_6154689 : Nat := 118140960795 + 6154689 * 2 ^ 59
def prefixEnd_6154689 : Nat := 4983230072969 + 3 ^ 40 * 6154689 * 2
def baseEnd_6154689 : Nat := 3160313735939975484682607

theorem tailTrace_6154689 : CollatzResearch.WordTrace tailWord_6154689 prefixEnd_6154689 3160313735939975484682607 := by
  unfold tailWord_6154689
  simp only [CollatzResearch.WordTrace]
  refine ⟨224479949599620365041003121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149653299733080243360668747 224479949599620365041003121)
  ·
    refine ⟨168359962199715273780752341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224479949599620365041003121 168359962199715273780752341)
    ·
      refine ⟨3945936614055826729236383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 168359962199715273780752341 3945936614055826729236383)
      ·
        refine ⟨5918904921083740093854575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3945936614055826729236383 5918904921083740093854575)
        ·
          refine ⟨8878357381625610140781863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5918904921083740093854575 8878357381625610140781863)
          ·
            refine ⟨13317536072438415211172795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8878357381625610140781863 13317536072438415211172795)
            ·
              refine ⟨19976304108657622816759193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13317536072438415211172795 19976304108657622816759193)
              ·
                refine ⟨14982228081493217112569395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19976304108657622816759193 14982228081493217112569395)
                ·
                  refine ⟨22473342122239825668854093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14982228081493217112569395 22473342122239825668854093)
                  ·
                    refine ⟨8427503295839934625820285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22473342122239825668854093 8427503295839934625820285)
                    ·
                      refine ⟨3160313735939975484682607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8427503295839934625820285 3160313735939975484682607)
                      ·
                        rfl

theorem cell23_6154689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_6154689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6154689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6154689 prefixEnd_6154689 := by exact prefixLift 6154689
  have htrace : WordTrace (prefixWord ++ tailWord_6154689) baseStart_6154689 baseEnd_6154689 := by
    simpa [prefixWord, tailWord_6154689, baseEnd_6154689] using wordTrace_append hprefix tailTrace_6154689
  have hstable : (prefixWord ++ tailWord_6154689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6154689).length < 2 ^ (prefixWord ++ tailWord_6154689).sum := by decide
  have hdescent : baseEnd_6154689 < baseStart_6154689 := by decide
  rcases family_descends (prefixWord ++ tailWord_6154689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6154691 : List Nat := [1, 1, 1, 3, 1, 1, 3, 2, 4, 2, 4]
def baseStart_6154691 : Nat := 118140960795 + 6154691 * 2 ^ 59
def prefixEnd_6154691 : Nat := 4983230072969 + 3 ^ 40 * 6154691 * 2
def baseEnd_6154691 : Nat := 3160314762901284476857597

theorem tailTrace_6154691 : CollatzResearch.WordTrace tailWord_6154691 prefixEnd_6154691 3160314762901284476857597 := by
  unfold tailWord_6154691
  simp only [CollatzResearch.WordTrace]
  refine ⟨224480022545613119382575927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149653348363742079588383951 224480022545613119382575927)
  ·
    refine ⟨336720033818419679073863891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224480022545613119382575927 336720033818419679073863891)
    ·
      refine ⟨505080050727629518610795837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 336720033818419679073863891 505080050727629518610795837)
      ·
        refine ⟨189405019022861069479048439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 505080050727629518610795837 189405019022861069479048439)
        ·
          refine ⟨284107528534291604218572659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189405019022861069479048439 284107528534291604218572659)
          ·
            refine ⟨426161292801437406327858989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 284107528534291604218572659 426161292801437406327858989)
            ·
              refine ⟨159810484800539027372947121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 426161292801437406327858989 159810484800539027372947121)
              ·
                refine ⟨119857863600404270529710341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 159810484800539027372947121 119857863600404270529710341)
                ·
                  refine ⟨22473349425075800724320689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 119857863600404270529710341 22473349425075800724320689)
                  ·
                    refine ⟨16855012068806850543240517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22473349425075800724320689 16855012068806850543240517)
                    ·
                      refine ⟨3160314762901284476857597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16855012068806850543240517 3160314762901284476857597)
                      ·
                        rfl

theorem cell23_6154691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 4, 2, 4].length) (baseStart_6154691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6154691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6154691 prefixEnd_6154691 := by exact prefixLift 6154691
  have htrace : WordTrace (prefixWord ++ tailWord_6154691) baseStart_6154691 baseEnd_6154691 := by
    simpa [prefixWord, tailWord_6154691, baseEnd_6154691] using wordTrace_append hprefix tailTrace_6154691
  have hstable : (prefixWord ++ tailWord_6154691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6154691).length < 2 ^ (prefixWord ++ tailWord_6154691).sum := by decide
  have hdescent : baseEnd_6154691 < baseStart_6154691 := by decide
  rcases family_descends (prefixWord ++ tailWord_6154691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6154695 : List Nat := [1, 1, 4, 1, 1, 5, 1, 2, 1, 4, 2]
def baseStart_6154695 : Nat := 118140960795 + 6154695 * 2 ^ 59
def prefixEnd_6154695 : Nat := 4983230072969 + 3 ^ 40 * 6154695 * 2
def baseEnd_6154695 : Nat := 3160316816823902461207579

theorem tailTrace_6154695 : CollatzResearch.WordTrace tailWord_6154695 prefixEnd_6154695 3160316816823902461207579 := by
  unfold tailWord_6154695
  simp only [CollatzResearch.WordTrace]
  refine ⟨224480168437598628065721539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149653445625065752043814359 224480168437598628065721539)
  ·
    refine ⟨336720252656397942098582309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224480168437598628065721539 336720252656397942098582309)
    ·
      refine ⟨63135047373074614143484183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 336720252656397942098582309 63135047373074614143484183)
      ·
        refine ⟨94702571059611921215226275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63135047373074614143484183 94702571059611921215226275)
        ·
          refine ⟨142053856589417881822839413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94702571059611921215226275 142053856589417881822839413)
          ·
            refine ⟨13317549055257926420891195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 142053856589417881822839413 13317549055257926420891195)
            ·
              refine ⟨19976323582886889631336793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13317549055257926420891195 19976323582886889631336793)
              ·
                refine ⟨14982242687165167223502595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19976323582886889631336793 14982242687165167223502595)
                ·
                  refine ⟨22473364030747750835253893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14982242687165167223502595 22473364030747750835253893)
                  ·
                    refine ⟨4213755755765203281610105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22473364030747750835253893 4213755755765203281610105)
                    ·
                      refine ⟨3160316816823902461207579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4213755755765203281610105 3160316816823902461207579)
                      ·
                        rfl

theorem cell23_6154695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 2, 1, 4, 2].length) (baseStart_6154695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6154695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6154695 prefixEnd_6154695 := by exact prefixLift 6154695
  have htrace : WordTrace (prefixWord ++ tailWord_6154695) baseStart_6154695 baseEnd_6154695 := by
    simpa [prefixWord, tailWord_6154695, baseEnd_6154695] using wordTrace_append hprefix tailTrace_6154695
  have hstable : (prefixWord ++ tailWord_6154695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6154695).length < 2 ^ (prefixWord ++ tailWord_6154695).sum := by decide
  have hdescent : baseEnd_6154695 < baseStart_6154695 := by decide
  rcases family_descends (prefixWord ++ tailWord_6154695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6154722 : List Nat := [3, 3, 3, 2, 1, 1, 1, 1, 2, 6]
def baseStart_6154722 : Nat := 118140960795 + 6154722 * 2 ^ 59
def prefixEnd_6154722 : Nat := 4983230072969 + 3 ^ 40 * 6154722 * 2
def baseEnd_6154722 : Nat := 1053443560267191285189985

theorem tailTrace_6154722 : CollatzResearch.WordTrace tailWord_6154722 prefixEnd_6154722 1053443560267191285189985 := by
  unfold tailWord_6154722
  simp only [CollatzResearch.WordTrace]
  refine ⟨56120288302125202919238605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149654102139000541117969613 56120288302125202919238605)
  ·
    refine ⟨21045108113296951094714477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56120288302125202919238605 21045108113296951094714477)
    ·
      refine ⟨7891915542486356660517929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21045108113296951094714477 7891915542486356660517929)
      ·
        refine ⟨5918936656864767495388447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7891915542486356660517929 5918936656864767495388447)
        ·
          refine ⟨8878404985297151243082671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5918936656864767495388447 8878404985297151243082671)
          ·
            refine ⟨13317607477945726864624007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8878404985297151243082671 13317607477945726864624007)
            ·
              refine ⟨19976411216918590296936011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13317607477945726864624007 19976411216918590296936011)
              ·
                refine ⟨29964616825377885445404017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19976411216918590296936011 29964616825377885445404017)
                ·
                  refine ⟨22473462619033414084053013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29964616825377885445404017 22473462619033414084053013)
                  ·
                    refine ⟨1053443560267191285189985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22473462619033414084053013 1053443560267191285189985)
                    ·
                      rfl

theorem cell23_6154722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_6154722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6154722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6154722 prefixEnd_6154722 := by exact prefixLift 6154722
  have htrace : WordTrace (prefixWord ++ tailWord_6154722) baseStart_6154722 baseEnd_6154722 := by
    simpa [prefixWord, tailWord_6154722, baseEnd_6154722] using wordTrace_append hprefix tailTrace_6154722
  have hstable : (prefixWord ++ tailWord_6154722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6154722).length < 2 ^ (prefixWord ++ tailWord_6154722).sum := by decide
  have hdescent : baseEnd_6154722 < baseStart_6154722 := by decide
  rcases family_descends (prefixWord ++ tailWord_6154722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6154725 : List Nat := [1, 3, 1, 5, 2, 1, 1, 1, 2, 2, 4]
def baseStart_6154725 : Nat := 118140960795 + 6154725 * 2 ^ 59
def prefixEnd_6154725 : Nat := 4983230072969 + 3 ^ 40 * 6154725 * 2
def baseEnd_6154725 : Nat := 3160332221243537343832441

theorem tailTrace_6154725 : CollatzResearch.WordTrace tailWord_6154725 prefixEnd_6154725 3160332221243537343832441 := by
  unfold tailWord_6154725
  simp only [CollatzResearch.WordTrace]
  refine ⟨224481262627489943189313629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149654175084993295459542419 224481262627489943189313629)
  ·
    refine ⟨84180473485308728695992611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 224481262627489943189313629 84180473485308728695992611)
    ·
      refine ⟨126270710227963093043988917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84180473485308728695992611 126270710227963093043988917)
      ·
        refine ⟨11837879083871539972873961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 126270710227963093043988917 11837879083871539972873961)
        ·
          refine ⟨8878409312903654979655471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11837879083871539972873961 8878409312903654979655471)
          ·
            refine ⟨13317613969355482469483207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8878409312903654979655471 13317613969355482469483207)
            ·
              refine ⟨19976420954033223704224811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13317613969355482469483207 19976420954033223704224811)
              ·
                refine ⟨29964631431049835556337217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19976420954033223704224811 29964631431049835556337217)
                ·
                  refine ⟨22473473573287376667252913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29964631431049835556337217 22473473573287376667252913)
                  ·
                    refine ⟨16855105179965532500439685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22473473573287376667252913 16855105179965532500439685)
                    ·
                      refine ⟨3160332221243537343832441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16855105179965532500439685 3160332221243537343832441)
                      ·
                        rfl

theorem cell23_6154725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_6154725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6154725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6154725 prefixEnd_6154725 := by exact prefixLift 6154725
  have htrace : WordTrace (prefixWord ++ tailWord_6154725) baseStart_6154725 baseEnd_6154725 := by
    simpa [prefixWord, tailWord_6154725, baseEnd_6154725] using wordTrace_append hprefix tailTrace_6154725
  have hstable : (prefixWord ++ tailWord_6154725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6154725).length < 2 ^ (prefixWord ++ tailWord_6154725).sum := by decide
  have hdescent : baseEnd_6154725 < baseStart_6154725 := by decide
  rcases family_descends (prefixWord ++ tailWord_6154725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6154728 : List Nat := [2, 1, 4, 1, 1, 3, 1, 1, 1, 5, 3]
def baseStart_6154728 : Nat := 118140960795 + 6154728 * 2 ^ 59
def prefixEnd_6154728 : Nat := 4983230072969 + 3 ^ 40 * 6154728 * 2
def baseEnd_6154728 : Nat := 3160333761685500832094927

theorem tailTrace_6154728 : CollatzResearch.WordTrace tailWord_6154728 prefixEnd_6154728 3160333761685500832094927 := by
  unfold tailWord_6154728
  simp only [CollatzResearch.WordTrace]
  refine ⟨112240686023239537350836419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149654248030986049801115225 112240686023239537350836419)
  ·
    refine ⟨168361029034859306026254629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112240686023239537350836419 168361029034859306026254629)
    ·
      refine ⟨31567692944036119879922743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 168361029034859306026254629 31567692944036119879922743)
      ·
        refine ⟨47351539416054179819884115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31567692944036119879922743 47351539416054179819884115)
        ·
          refine ⟨71027309124081269729826173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47351539416054179819884115 71027309124081269729826173)
          ·
            refine ⟨26635240921530476148684815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71027309124081269729826173 26635240921530476148684815)
            ·
              refine ⟨39952861382295714223027223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26635240921530476148684815 39952861382295714223027223)
              ·
                refine ⟨59929292073443571334540835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39952861382295714223027223 59929292073443571334540835)
                ·
                  refine ⟨89893938110165357001811253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59929292073443571334540835 89893938110165357001811253)
                  ·
                    refine ⟨8427556697828002218919805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 89893938110165357001811253 8427556697828002218919805)
                    ·
                      refine ⟨3160333761685500832094927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8427556697828002218919805 3160333761685500832094927)
                      ·
                        rfl

theorem cell23_6154728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 1, 1, 5, 3].length) (baseStart_6154728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6154728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6154728 prefixEnd_6154728 := by exact prefixLift 6154728
  have htrace : WordTrace (prefixWord ++ tailWord_6154728) baseStart_6154728 baseEnd_6154728 := by
    simpa [prefixWord, tailWord_6154728, baseEnd_6154728] using wordTrace_append hprefix tailTrace_6154728
  have hstable : (prefixWord ++ tailWord_6154728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6154728).length < 2 ^ (prefixWord ++ tailWord_6154728).sum := by decide
  have hdescent : baseEnd_6154728 < baseStart_6154728 := by decide
  rcases family_descends (prefixWord ++ tailWord_6154728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6154731 : List Nat := [1, 1, 1, 1, 2, 3, 4, 2, 1, 7]
def baseStart_6154731 : Nat := 118140960795 + 6154731 * 2 ^ 59
def prefixEnd_6154731 : Nat := 4983230072969 + 3 ^ 40 * 6154731 * 2
def baseEnd_6154731 : Nat := 1053445100709154773452471

theorem tailTrace_6154731 : CollatzResearch.WordTrace tailWord_6154731 prefixEnd_6154731 1053445100709154773452471 := by
  unfold tailWord_6154731
  simp only [CollatzResearch.WordTrace]
  refine ⟨224481481465468206214032047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149654320976978804142688031 224481481465468206214032047)
  ·
    refine ⟨336722222198202309321048071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224481481465468206214032047 336722222198202309321048071)
    ·
      refine ⟨505083333297303463981572107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 336722222198202309321048071 505083333297303463981572107)
      ·
        refine ⟨757624999945955195972358161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 505083333297303463981572107 757624999945955195972358161)
        ·
          refine ⟨568218749959466396979268621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 757624999945955195972358161 568218749959466396979268621)
          ·
            refine ⟨213082031234799898867225733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 568218749959466396979268621 213082031234799898867225733)
            ·
              refine ⟨39952880856524981037604825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 213082031234799898867225733 39952880856524981037604825)
              ·
                refine ⟨29964660642393735778203619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39952880856524981037604825 29964660642393735778203619)
                ·
                  refine ⟨44946990963590603667305429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29964660642393735778203619 44946990963590603667305429)
                  ·
                    refine ⟨1053445100709154773452471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44946990963590603667305429 1053445100709154773452471)
                    ·
                      rfl

theorem cell23_6154731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 2, 1, 7].length) (baseStart_6154731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6154731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6154731 prefixEnd_6154731 := by exact prefixLift 6154731
  have htrace : WordTrace (prefixWord ++ tailWord_6154731) baseStart_6154731 baseEnd_6154731 := by
    simpa [prefixWord, tailWord_6154731, baseEnd_6154731] using wordTrace_append hprefix tailTrace_6154731
  have hstable : (prefixWord ++ tailWord_6154731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6154731).length < 2 ^ (prefixWord ++ tailWord_6154731).sum := by decide
  have hdescent : baseEnd_6154731 < baseStart_6154731 := by decide
  rcases family_descends (prefixWord ++ tailWord_6154731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6154785 : List Nat := [1, 2, 3, 2, 2, 1, 1, 3, 2, 4, 2]
def baseStart_6154785 : Nat := 118140960795 + 6154785 * 2 ^ 59
def prefixEnd_6154785 : Nat := 4983230072969 + 3 ^ 40 * 6154785 * 2
def baseEnd_6154785 : Nat := 3160363030082807109082165

theorem tailTrace_6154785 : CollatzResearch.WordTrace tailWord_6154785 prefixEnd_6154785 3160363030082807109082165 := by
  unfold tailWord_6154785
  simp only [CollatzResearch.WordTrace]
  refine ⟨224483451007272573436497809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149655634004848382290998539 224483451007272573436497809)
  ·
    refine ⟨168362588255454430077373357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224483451007272573436497809 168362588255454430077373357)
    ·
      refine ⟨63135970595795411279015009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168362588255454430077373357 63135970595795411279015009)
      ·
        refine ⟨47351977946846558459261257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63135970595795411279015009 47351977946846558459261257)
        ·
          refine ⟨35513983460134918844445943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47351977946846558459261257 35513983460134918844445943)
          ·
            refine ⟨53270975190202378266668915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35513983460134918844445943 53270975190202378266668915)
            ·
              refine ⟨79906462785303567400003373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53270975190202378266668915 79906462785303567400003373)
              ·
                refine ⟨29964923544488837775001265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79906462785303567400003373 29964923544488837775001265)
                ·
                  refine ⟨22473692658366628331250949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29964923544488837775001265 22473692658366628331250949)
                  ·
                    refine ⟨4213817373443742812109553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22473692658366628331250949 4213817373443742812109553)
                    ·
                      refine ⟨3160363030082807109082165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4213817373443742812109553 3160363030082807109082165)
                      ·
                        rfl

theorem cell23_6154785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 3, 2, 4, 2].length) (baseStart_6154785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6154785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6154785 prefixEnd_6154785 := by exact prefixLift 6154785
  have htrace : WordTrace (prefixWord ++ tailWord_6154785) baseStart_6154785 baseEnd_6154785 := by
    simpa [prefixWord, tailWord_6154785, baseEnd_6154785] using wordTrace_append hprefix tailTrace_6154785
  have hstable : (prefixWord ++ tailWord_6154785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6154785).length < 2 ^ (prefixWord ++ tailWord_6154785).sum := by decide
  have hdescent : baseEnd_6154785 < baseStart_6154785 := by decide
  rcases family_descends (prefixWord ++ tailWord_6154785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6154805 : List Nat := [1, 3, 3, 1, 1, 2, 2, 3, 2, 2, 3]
def baseStart_6154805 : Nat := 118140960795 + 6154805 * 2 ^ 59
def prefixEnd_6154805 : Nat := 4983230072969 + 3 ^ 40 * 6154805 * 2
def baseEnd_6154805 : Nat := 3160373299695897030832073

theorem tailTrace_6154805 : CollatzResearch.WordTrace tailWord_6154805 prefixEnd_6154805 3160373299695897030832073 := by
  unfold tailWord_6154805
  simp only [CollatzResearch.WordTrace]
  refine ⟨224484180467200116852225869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149656120311466744568150579 224484180467200116852225869)
  ·
    refine ⟨84181567675200043819584701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 224484180467200116852225869 84181567675200043819584701)
    ·
      refine ⟨31568087878200016432344263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84181567675200043819584701 31568087878200016432344263)
      ·
        refine ⟨47352131817300024648516395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31568087878200016432344263 47352131817300024648516395)
        ·
          refine ⟨71028197725950036972774593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47352131817300024648516395 71028197725950036972774593)
          ·
            refine ⟨53271148294462527729580945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71028197725950036972774593 53271148294462527729580945)
            ·
              refine ⟨39953361220846895797185709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53271148294462527729580945 39953361220846895797185709)
              ·
                refine ⟨14982510457817585923944641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39953361220846895797185709 14982510457817585923944641)
                ·
                  refine ⟨11236882843363189442958481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14982510457817585923944641 11236882843363189442958481)
                  ·
                    refine ⟨8427662132522392082218861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11236882843363189442958481 8427662132522392082218861)
                    ·
                      refine ⟨3160373299695897030832073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8427662132522392082218861 3160373299695897030832073)
                      ·
                        rfl

theorem cell23_6154805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 3, 2, 2, 3].length) (baseStart_6154805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6154805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6154805 prefixEnd_6154805 := by exact prefixLift 6154805
  have htrace : WordTrace (prefixWord ++ tailWord_6154805) baseStart_6154805 baseEnd_6154805 := by
    simpa [prefixWord, tailWord_6154805, baseEnd_6154805] using wordTrace_append hprefix tailTrace_6154805
  have hstable : (prefixWord ++ tailWord_6154805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6154805).length < 2 ^ (prefixWord ++ tailWord_6154805).sum := by decide
  have hdescent : baseEnd_6154805 < baseStart_6154805 := by decide
  rcases family_descends (prefixWord ++ tailWord_6154805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6154829 : List Nat := [1, 6, 1, 1, 2, 3, 1, 1, 3, 4]
def baseStart_6154829 : Nat := 118140960795 + 6154829 * 2 ^ 59
def prefixEnd_6154829 : Nat := 4983230072969 + 3 ^ 40 * 6154829 * 2
def baseEnd_6154829 : Nat := 1053461874410534978977321

theorem tailTrace_6154829 : CollatzResearch.WordTrace tailWord_6154829 prefixEnd_6154829 1053461874410534978977321 := by
  unfold tailWord_6154829
  simp only [CollatzResearch.WordTrace]
  refine ⟨224485055819113168951099541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149656703879408779300733027 224485055819113168951099541)
  ·
    refine ⟨10522736991520929794582791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 224485055819113168951099541 10522736991520929794582791)
    ·
      refine ⟨15784105487281394691874187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10522736991520929794582791 15784105487281394691874187)
      ·
        refine ⟨23676158230922092037811281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15784105487281394691874187 23676158230922092037811281)
        ·
          refine ⟨17757118673191569028358461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23676158230922092037811281 17757118673191569028358461)
          ·
            refine ⟨6658919502446838385634423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17757118673191569028358461 6658919502446838385634423)
            ·
              refine ⟨9988379253670257578451635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6658919502446838385634423 9988379253670257578451635)
              ·
                refine ⟨14982568880505386367677453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9988379253670257578451635 14982568880505386367677453)
                ·
                  refine ⟨5618463330189519887879045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14982568880505386367677453 5618463330189519887879045)
                  ·
                    refine ⟨1053461874410534978977321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5618463330189519887879045 1053461874410534978977321)
                    ·
                      rfl

theorem cell23_6154829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 1, 1, 3, 4].length) (baseStart_6154829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6154829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6154829 prefixEnd_6154829 := by exact prefixLift 6154829
  have htrace : WordTrace (prefixWord ++ tailWord_6154829) baseStart_6154829 baseEnd_6154829 := by
    simpa [prefixWord, tailWord_6154829, baseEnd_6154829] using wordTrace_append hprefix tailTrace_6154829
  have hstable : (prefixWord ++ tailWord_6154829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6154829).length < 2 ^ (prefixWord ++ tailWord_6154829).sum := by decide
  have hdescent : baseEnd_6154829 < baseStart_6154829 := by decide
  rcases family_descends (prefixWord ++ tailWord_6154829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6154905 : List Nat := [1, 2, 1, 2, 1, 2, 6, 1, 1, 2, 4]
def baseStart_6154905 : Nat := 118140960795 + 6154905 * 2 ^ 59
def prefixEnd_6154905 : Nat := 4983230072969 + 3 ^ 40 * 6154905 * 2
def baseEnd_6154905 : Nat := 3160424647761346639581613

theorem tailTrace_6154905 : CollatzResearch.WordTrace tailWord_6154905 prefixEnd_6154905 3160424647761346639581613 := by
  unfold tailWord_6154905
  simp only [CollatzResearch.WordTrace]
  refine ⟨224487827766837833930866169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149658551844558555953910779 224487827766837833930866169)
  ·
    refine ⟨168365870825128375448149627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224487827766837833930866169 168365870825128375448149627)
    ·
      refine ⟨252548806237692563172224441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168365870825128375448149627 252548806237692563172224441)
      ·
        refine ⟨189411604678269422379168331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 252548806237692563172224441 189411604678269422379168331)
        ·
          refine ⟨284117407017404133568752497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189411604678269422379168331 284117407017404133568752497)
          ·
            refine ⟨213088055263053100176564373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 284117407017404133568752497 213088055263053100176564373)
            ·
              refine ⟨9988502590455614070776455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 213088055263053100176564373 9988502590455614070776455)
              ·
                refine ⟨14982753885683421106164683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9988502590455614070776455 14982753885683421106164683)
                ·
                  refine ⟨22474130828525131659247025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14982753885683421106164683 22474130828525131659247025)
                  ·
                    refine ⟨16855598121393848744435269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22474130828525131659247025 16855598121393848744435269)
                    ·
                      refine ⟨3160424647761346639581613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16855598121393848744435269 3160424647761346639581613)
                      ·
                        rfl

theorem cell23_6154905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6, 1, 1, 2, 4].length) (baseStart_6154905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6154905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6154905 prefixEnd_6154905 := by exact prefixLift 6154905
  have htrace : WordTrace (prefixWord ++ tailWord_6154905) baseStart_6154905 baseEnd_6154905 := by
    simpa [prefixWord, tailWord_6154905, baseEnd_6154905] using wordTrace_append hprefix tailTrace_6154905
  have hstable : (prefixWord ++ tailWord_6154905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6154905).length < 2 ^ (prefixWord ++ tailWord_6154905).sum := by decide
  have hdescent : baseEnd_6154905 < baseStart_6154905 := by decide
  rcases family_descends (prefixWord ++ tailWord_6154905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6154926 : List Nat := [4, 1, 4, 1, 1, 1, 4, 1, 1, 1, 4]
def baseStart_6154926 : Nat := 118140960795 + 6154926 * 2 ^ 59
def prefixEnd_6154926 : Nat := 4983230072969 + 3 ^ 40 * 6154926 * 2
def baseEnd_6154926 : Nat := 3160435430855091057419017

theorem tailTrace_6154926 : CollatzResearch.WordTrace tailWord_6154926 prefixEnd_6154926 3160435430855091057419017 := by
  unfold tailWord_6154926
  simp only [CollatzResearch.WordTrace]
  refine ⟨28061074212470219314672579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149659062466507836344920421 28061074212470219314672579)
  ·
    refine ⟨42091611318705328972008869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28061074212470219314672579 42091611318705328972008869)
    ·
      refine ⟨7892177122257249182251663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42091611318705328972008869 7892177122257249182251663)
      ·
        refine ⟨11838265683385873773377495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7892177122257249182251663 11838265683385873773377495)
        ·
          refine ⟨17757398525078810660066243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11838265683385873773377495 17757398525078810660066243)
          ·
            refine ⟨26636097787618215990099365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17757398525078810660066243 26636097787618215990099365)
            ·
              refine ⟨4994268335178415498143631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26636097787618215990099365 4994268335178415498143631)
              ·
                refine ⟨7491402502767623247215447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4994268335178415498143631 7491402502767623247215447)
                ·
                  refine ⟨11237103754151434870823171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7491402502767623247215447 11237103754151434870823171)
                  ·
                    refine ⟨16855655631227152306234757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11237103754151434870823171 16855655631227152306234757)
                    ·
                      refine ⟨3160435430855091057419017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16855655631227152306234757 3160435430855091057419017)
                      ·
                        rfl

theorem cell23_6154926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 4, 1, 1, 1, 4].length) (baseStart_6154926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6154926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6154926 prefixEnd_6154926 := by exact prefixLift 6154926
  have htrace : WordTrace (prefixWord ++ tailWord_6154926) baseStart_6154926 baseEnd_6154926 := by
    simpa [prefixWord, tailWord_6154926, baseEnd_6154926] using wordTrace_append hprefix tailTrace_6154926
  have hstable : (prefixWord ++ tailWord_6154926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6154926).length < 2 ^ (prefixWord ++ tailWord_6154926).sum := by decide
  have hdescent : baseEnd_6154926 < baseStart_6154926 := by decide
  rcases family_descends (prefixWord ++ tailWord_6154926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6154969 : List Nat := [1, 2, 1, 2, 3, 2, 4, 2, 1, 3, 2]
def baseStart_6154969 : Nat := 118140960795 + 6154969 * 2 ^ 59
def prefixEnd_6154969 : Nat := 4983230072969 + 3 ^ 40 * 6154969 * 2
def baseEnd_6154969 : Nat := 3160457510523234389181319

theorem tailTrace_6154969 : CollatzResearch.WordTrace tailWord_6154969 prefixEnd_6154969 3160457510523234389181319 := by
  unfold tailWord_6154969
  simp only [CollatzResearch.WordTrace]
  refine ⟨224490162038605972861195961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149660108025737315240797307 224490162038605972861195961)
  ·
    refine ⟨168367621528954479645896971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224490162038605972861195961 168367621528954479645896971)
    ·
      refine ⟨252551432293431719468845457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168367621528954479645896971 252551432293431719468845457)
      ·
        refine ⟨189413574220073789601634093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 252551432293431719468845457 189413574220073789601634093)
        ·
          refine ⟨71030090332527671100612785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 189413574220073789601634093 71030090332527671100612785)
          ·
            refine ⟨53272567749395753325459589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71030090332527671100612785 53272567749395753325459589)
            ·
              refine ⟨9988606453011703748523673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53272567749395753325459589 9988606453011703748523673)
              ·
                refine ⟨7491454839758777811392755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9988606453011703748523673 7491454839758777811392755)
                ·
                  refine ⟨11237182259638166717089133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7491454839758777811392755 11237182259638166717089133)
                  ·
                    refine ⟨4213943347364312518908425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11237182259638166717089133 4213943347364312518908425)
                    ·
                      refine ⟨3160457510523234389181319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4213943347364312518908425 3160457510523234389181319)
                      ·
                        rfl

theorem cell23_6154969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4, 2, 1, 3, 2].length) (baseStart_6154969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6154969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6154969 prefixEnd_6154969 := by exact prefixLift 6154969
  have htrace : WordTrace (prefixWord ++ tailWord_6154969) baseStart_6154969 baseEnd_6154969 := by
    simpa [prefixWord, tailWord_6154969, baseEnd_6154969] using wordTrace_append hprefix tailTrace_6154969
  have hstable : (prefixWord ++ tailWord_6154969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6154969).length < 2 ^ (prefixWord ++ tailWord_6154969).sum := by decide
  have hdescent : baseEnd_6154969 < baseStart_6154969 := by decide
  rcases family_descends (prefixWord ++ tailWord_6154969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6154972 : List Nat := [2, 2, 5, 1, 1, 1, 1, 1, 2, 2, 5]
def baseStart_6154972 : Nat := 118140960795 + 6154972 * 2 ^ 59
def prefixEnd_6154972 : Nat := 4983230072969 + 3 ^ 40 * 6154972 * 2
def baseEnd_6154972 : Nat := 3160459050965197877443805

theorem tailTrace_6154972 : CollatzResearch.WordTrace tailWord_6154972 prefixEnd_6154972 3160459050965197877443805 := by
  unfold tailWord_6154972
  simp only [CollatzResearch.WordTrace]
  refine ⟨112245135728797552186777585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149660180971730069582370113 112245135728797552186777585)
  ·
    refine ⟨84183851796598164140083189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112245135728797552186777585 84183851796598164140083189)
    ·
      refine ⟨7892236105931077888132799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 84183851796598164140083189 7892236105931077888132799)
      ·
        refine ⟨11838354158896616832199199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7892236105931077888132799 11838354158896616832199199)
        ·
          refine ⟨17757531238344925248298799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11838354158896616832199199 17757531238344925248298799)
          ·
            refine ⟨26636296857517387872448199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17757531238344925248298799 26636296857517387872448199)
            ·
              refine ⟨39954445286276081808672299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26636296857517387872448199 39954445286276081808672299)
              ·
                refine ⟨59931667929414122713008449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39954445286276081808672299 59931667929414122713008449)
                ·
                  refine ⟨44948750947060592034756337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59931667929414122713008449 44948750947060592034756337)
                  ·
                    refine ⟨33711563210295444026067253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44948750947060592034756337 33711563210295444026067253)
                    ·
                      refine ⟨3160459050965197877443805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33711563210295444026067253 3160459050965197877443805)
                      ·
                        rfl

theorem cell23_6154972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_6154972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6154972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6154972 prefixEnd_6154972 := by exact prefixLift 6154972
  have htrace : WordTrace (prefixWord ++ tailWord_6154972) baseStart_6154972 baseEnd_6154972 := by
    simpa [prefixWord, tailWord_6154972, baseEnd_6154972] using wordTrace_append hprefix tailTrace_6154972
  have hstable : (prefixWord ++ tailWord_6154972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6154972).length < 2 ^ (prefixWord ++ tailWord_6154972).sum := by decide
  have hdescent : baseEnd_6154972 < baseStart_6154972 := by decide
  rcases family_descends (prefixWord ++ tailWord_6154972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6154999 : List Nat := [1, 1, 3, 1, 1, 1, 3, 6, 2, 2, 2]
def baseStart_6154999 : Nat := 118140960795 + 6154999 * 2 ^ 59
def prefixEnd_6154999 : Nat := 4983230072969 + 3 ^ 40 * 6154999 * 2
def baseEnd_6154999 : Nat := 3160472914942869271806181

theorem tailTrace_6154999 : CollatzResearch.WordTrace tailWord_6154999 prefixEnd_6154999 3160472914942869271806181 := by
  unfold tailWord_6154999
  simp only [CollatzResearch.WordTrace]
  refine ⟨224491256228497287984788051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149660837485664858656525367 224491256228497287984788051)
  ·
    refine ⟨336736884342745931977182077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224491256228497287984788051 336736884342745931977182077)
    ·
      refine ⟨126276331628529724491443279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 336736884342745931977182077 126276331628529724491443279)
      ·
        refine ⟨189414497442794586737164919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126276331628529724491443279 189414497442794586737164919)
        ·
          refine ⟨284121746164191880105747379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189414497442794586737164919 284121746164191880105747379)
          ·
            refine ⟨426182619246287820158621069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 284121746164191880105747379 426182619246287820158621069)
            ·
              refine ⟨159818482217357932559482901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 426182619246287820158621069 159818482217357932559482901)
              ·
                refine ⟨7491491353938653088725761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 159818482217357932559482901 7491491353938653088725761)
                ·
                  refine ⟨5618618515453989816544321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7491491353938653088725761 5618618515453989816544321)
                  ·
                    refine ⟨4213963886590492362408241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5618618515453989816544321 4213963886590492362408241)
                    ·
                      refine ⟨3160472914942869271806181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4213963886590492362408241 3160472914942869271806181)
                      ·
                        rfl

theorem cell23_6154999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 6, 2, 2, 2].length) (baseStart_6154999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6154999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6154999 prefixEnd_6154999 := by exact prefixLift 6154999
  have htrace : WordTrace (prefixWord ++ tailWord_6154999) baseStart_6154999 baseEnd_6154999 := by
    simpa [prefixWord, tailWord_6154999, baseEnd_6154999] using wordTrace_append hprefix tailTrace_6154999
  have hstable : (prefixWord ++ tailWord_6154999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6154999).length < 2 ^ (prefixWord ++ tailWord_6154999).sum := by decide
  have hdescent : baseEnd_6154999 < baseStart_6154999 := by decide
  rcases family_descends (prefixWord ++ tailWord_6154999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6155016 : List Nat := [2, 1, 3, 2, 2, 3, 1, 3, 2, 2, 2]
def baseStart_6155016 : Nat := 118140960795 + 6155016 * 2 ^ 59
def prefixEnd_6155016 : Nat := 4983230072969 + 3 ^ 40 * 6155016 * 2
def baseEnd_6155016 : Nat := 3160481644113995705293603

theorem tailTrace_6155016 : CollatzResearch.WordTrace tailWord_6155016 prefixEnd_6155016 3160481644113995705293603 := by
  unfold tailWord_6155016
  simp only [CollatzResearch.WordTrace]
  refine ⟨112245938134717849944078451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149661250846290466592104601 112245938134717849944078451)
  ·
    refine ⟨168368907202076774916117677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112245938134717849944078451 168368907202076774916117677)
    ·
      refine ⟨63138340200778790593544129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168368907202076774916117677 63138340200778790593544129)
      ·
        refine ⟨47353755150584092945158097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63138340200778790593544129 47353755150584092945158097)
        ·
          refine ⟨35515316362938069708868573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47353755150584092945158097 35515316362938069708868573)
          ·
            refine ⟨13318243636101776140825715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35515316362938069708868573 13318243636101776140825715)
            ·
              refine ⟨19977365454152664211238573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13318243636101776140825715 19977365454152664211238573)
              ·
                refine ⟨7491512045307249079214465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19977365454152664211238573 7491512045307249079214465)
                ·
                  refine ⟨5618634033980436809410849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7491512045307249079214465 5618634033980436809410849)
                  ·
                    refine ⟨4213975525485327607058137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5618634033980436809410849 4213975525485327607058137)
                    ·
                      refine ⟨3160481644113995705293603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4213975525485327607058137 3160481644113995705293603)
                      ·
                        rfl

theorem cell23_6155016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 3, 2, 2, 2].length) (baseStart_6155016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6155016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6155016 prefixEnd_6155016 := by exact prefixLift 6155016
  have htrace : WordTrace (prefixWord ++ tailWord_6155016) baseStart_6155016 baseEnd_6155016 := by
    simpa [prefixWord, tailWord_6155016, baseEnd_6155016] using wordTrace_append hprefix tailTrace_6155016
  have hstable : (prefixWord ++ tailWord_6155016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6155016).length < 2 ^ (prefixWord ++ tailWord_6155016).sum := by decide
  have hdescent : baseEnd_6155016 < baseStart_6155016 := by decide
  rcases family_descends (prefixWord ++ tailWord_6155016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6155045 : List Nat := [1, 3, 1, 2, 3, 1, 1, 1, 3, 2, 5]
def baseStart_6155045 : Nat := 118140960795 + 6155045 * 2 ^ 59
def prefixEnd_6155045 : Nat := 4983230072969 + 3 ^ 40 * 6155045 * 2
def baseEnd_6155045 : Nat := 3160496535052976091830969

theorem tailTrace_6155045 : CollatzResearch.WordTrace tailWord_6155045 prefixEnd_6155045 3160496535052976091830969 := by
  unfold tailWord_6155045
  simp only [CollatzResearch.WordTrace]
  refine ⟨224492933986330637840962589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149661955990887091893975059 224492933986330637840962589)
  ·
    refine ⟨84184850244873989190360971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 224492933986330637840962589 84184850244873989190360971)
    ·
      refine ⟨126277275367310983785541457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84184850244873989190360971 126277275367310983785541457)
      ·
        refine ⟨94707956525483237839156093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126277275367310983785541457 94707956525483237839156093)
        ·
          refine ⟨35515483697056214189683535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94707956525483237839156093 35515483697056214189683535)
          ·
            refine ⟨53273225545584321284525303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35515483697056214189683535 53273225545584321284525303)
            ·
              refine ⟨79909838318376481926787955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53273225545584321284525303 79909838318376481926787955)
              ·
                refine ⟨119864757477564722890181933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79909838318376481926787955 119864757477564722890181933)
                ·
                  refine ⟨44949284054086771083818225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 119864757477564722890181933 44949284054086771083818225)
                  ·
                    refine ⟨33711963040565078312863669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44949284054086771083818225 33711963040565078312863669)
                    ·
                      refine ⟨3160496535052976091830969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33711963040565078312863669 3160496535052976091830969)
                      ·
                        rfl

theorem cell23_6155045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 3, 2, 5].length) (baseStart_6155045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6155045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6155045 prefixEnd_6155045 := by exact prefixLift 6155045
  have htrace : WordTrace (prefixWord ++ tailWord_6155045) baseStart_6155045 baseEnd_6155045 := by
    simpa [prefixWord, tailWord_6155045, baseEnd_6155045] using wordTrace_append hprefix tailTrace_6155045
  have hstable : (prefixWord ++ tailWord_6155045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6155045).length < 2 ^ (prefixWord ++ tailWord_6155045).sum := by decide
  have hdescent : baseEnd_6155045 < baseStart_6155045 := by decide
  rcases family_descends (prefixWord ++ tailWord_6155045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6155050 : List Nat := [3, 1, 4, 3, 1, 1, 2, 2, 2, 2, 2]
def baseStart_6155050 : Nat := 118140960795 + 6155050 * 2 ^ 59
def prefixEnd_6155050 : Nat := 4983230072969 + 3 ^ 40 * 6155050 * 2
def baseEnd_6155050 : Nat := 3160499102456248572268447

theorem tailTrace_6155050 : CollatzResearch.WordTrace tailWord_6155050 prefixEnd_6155050 3160499102456248572268447 := by
  unfold tailWord_6155050
  simp only [CollatzResearch.WordTrace]
  refine ⟨56123279087828130923723651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149662077567541682463263069 56123279087828130923723651)
  ·
    refine ⟨84184918631742196385585477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56123279087828130923723651 84184918631742196385585477)
    ·
      refine ⟨15784672243451661822297277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84184918631742196385585477 15784672243451661822297277)
      ·
        refine ⟨5919252091294373183361479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15784672243451661822297277 5919252091294373183361479)
        ·
          refine ⟨8878878136941559775042219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5919252091294373183361479 8878878136941559775042219)
          ·
            refine ⟨13318317205412339662563329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8878878136941559775042219 13318317205412339662563329)
            ·
              refine ⟨9988737904059254746922497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13318317205412339662563329 9988737904059254746922497)
              ·
                refine ⟨7491553428044441060191873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9988737904059254746922497 7491553428044441060191873)
                ·
                  refine ⟨5618665071033330795143905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7491553428044441060191873 5618665071033330795143905)
                  ·
                    refine ⟨4213998803274998096357929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5618665071033330795143905 4213998803274998096357929)
                    ·
                      refine ⟨3160499102456248572268447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4213998803274998096357929 3160499102456248572268447)
                      ·
                        rfl

theorem cell23_6155050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_6155050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6155050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6155050 prefixEnd_6155050 := by exact prefixLift 6155050
  have htrace : WordTrace (prefixWord ++ tailWord_6155050) baseStart_6155050 baseEnd_6155050 := by
    simpa [prefixWord, tailWord_6155050, baseEnd_6155050] using wordTrace_append hprefix tailTrace_6155050
  have hstable : (prefixWord ++ tailWord_6155050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6155050).length < 2 ^ (prefixWord ++ tailWord_6155050).sum := by decide
  have hdescent : baseEnd_6155050 < baseStart_6155050 := by decide
  rcases family_descends (prefixWord ++ tailWord_6155050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6155112 : List Nat := [2, 1, 4, 2, 1, 3, 1, 1, 8]
def baseStart_6155112 : Nat := 118140960795 + 6155112 * 2 ^ 59
def prefixEnd_6155112 : Nat := 4983230072969 + 3 ^ 40 * 6155112 * 2
def baseEnd_6155112 : Nat := 351170104250758592188129

theorem tailTrace_6155112 : CollatzResearch.WordTrace tailWord_6155112 prefixEnd_6155112 351170104250758592188129 := by
  unfold tailWord_6155112
  simp only [CollatzResearch.WordTrace]
  refine ⟨112247688838543954141825795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149663585118058605522434393 112247688838543954141825795)
  ·
    refine ⟨168371533257815931212738693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112247688838543954141825795 168371533257815931212738693)
    ·
      refine ⟨31569662485840487102388505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 168371533257815931212738693 31569662485840487102388505)
      ·
        refine ⟨23677246864380365326791379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31569662485840487102388505 23677246864380365326791379)
        ·
          refine ⟨35515870296570547990187069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23677246864380365326791379 35515870296570547990187069)
          ·
            refine ⟨13318451361213955496320151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35515870296570547990187069 13318451361213955496320151)
            ·
              refine ⟨19977677041820933244480227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13318451361213955496320151 19977677041820933244480227)
              ·
                refine ⟨29966515562731399866720341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19977677041820933244480227 29966515562731399866720341)
                ·
                  refine ⟨351170104250758592188129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29966515562731399866720341 351170104250758592188129)
                  ·
                    rfl

theorem cell23_6155112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 1, 8].length) (baseStart_6155112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6155112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6155112 prefixEnd_6155112 := by exact prefixLift 6155112
  have htrace : WordTrace (prefixWord ++ tailWord_6155112) baseStart_6155112 baseEnd_6155112 := by
    simpa [prefixWord, tailWord_6155112, baseEnd_6155112] using wordTrace_append hprefix tailTrace_6155112
  have hstable : (prefixWord ++ tailWord_6155112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6155112).length < 2 ^ (prefixWord ++ tailWord_6155112).sum := by decide
  have hdescent : baseEnd_6155112 < baseStart_6155112 := by decide
  rcases family_descends (prefixWord ++ tailWord_6155112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6155115 : List Nat := [1, 1, 1, 1, 2, 2, 5, 1, 1, 2, 6]
def baseStart_6155115 : Nat := 118140960795 + 6155115 * 2 ^ 59
def prefixEnd_6155115 : Nat := 4983230072969 + 3 ^ 40 * 6155115 * 2
def baseEnd_6155115 : Nat := 3160532478698790817955647

theorem tailTrace_6155115 : CollatzResearch.WordTrace tailWord_6155115 prefixEnd_6155115 3160532478698790817955647 := by
  unfold tailWord_6155115
  simp only [CollatzResearch.WordTrace]
  refine ⟨224495487096077039796010799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149663658064051359864007199 224495487096077039796010799)
  ·
    refine ⟨336743230644115559694016199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224495487096077039796010799 336743230644115559694016199)
    ·
      refine ⟨505114845966173339541024299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 336743230644115559694016199 505114845966173339541024299)
      ·
        refine ⟨757672268949260009311536449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 505114845966173339541024299 757672268949260009311536449)
        ·
          refine ⟨568254201711945006983652337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 757672268949260009311536449 568254201711945006983652337)
          ·
            refine ⟨426190651283958755237739253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 568254201711945006983652337 426190651283958755237739253)
            ·
              refine ⟨39955373557871133303538055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 426190651283958755237739253 39955373557871133303538055)
              ·
                refine ⟨59933060336806699955307083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39955373557871133303538055 59933060336806699955307083)
                ·
                  refine ⟨89899590505210049932960625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59933060336806699955307083 89899590505210049932960625)
                  ·
                    refine ⟨67424692878907537449720469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 89899590505210049932960625 67424692878907537449720469)
                    ·
                      refine ⟨3160532478698790817955647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67424692878907537449720469 3160532478698790817955647)
                      ·
                        rfl

theorem cell23_6155115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 1, 1, 2, 6].length) (baseStart_6155115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6155115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6155115 prefixEnd_6155115 := by exact prefixLift 6155115
  have htrace : WordTrace (prefixWord ++ tailWord_6155115) baseStart_6155115 baseEnd_6155115 := by
    simpa [prefixWord, tailWord_6155115, baseEnd_6155115] using wordTrace_append hprefix tailTrace_6155115
  have hstable : (prefixWord ++ tailWord_6155115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6155115).length < 2 ^ (prefixWord ++ tailWord_6155115).sum := by decide
  have hdescent : baseEnd_6155115 < baseStart_6155115 := by decide
  rcases family_descends (prefixWord ++ tailWord_6155115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6155129 : List Nat := [1, 2, 1, 3, 2, 4, 3, 1, 6]
def baseStart_6155129 : Nat := 118140960795 + 6155129 * 2 ^ 59
def prefixEnd_6155129 : Nat := 4983230072969 + 3 ^ 40 * 6155129 * 2
def baseEnd_6155129 : Nat := 351171074158661529242287

theorem tailTrace_6155129 : CollatzResearch.WordTrace tailWord_6155129 prefixEnd_6155129 351171074158661529242287 := by
  unfold tailWord_6155129
  simp only [CollatzResearch.WordTrace]
  refine ⟨224495997718026320187020441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149663998478684213458013627 224495997718026320187020441)
  ·
    refine ⟨168371998288519740140265331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224495997718026320187020441 168371998288519740140265331)
    ·
      refine ⟨252557997432779610210397997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168371998288519740140265331 252557997432779610210397997)
      ·
        refine ⟨94709249037292353828899249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 252557997432779610210397997 94709249037292353828899249)
        ·
          refine ⟨71031936777969265371674437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94709249037292353828899249 71031936777969265371674437)
          ·
            refine ⟨13318488145869237257188957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71031936777969265371674437 13318488145869237257188957)
            ·
              refine ⟨4994433054700963971445859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13318488145869237257188957 4994433054700963971445859)
              ·
                refine ⟨7491649582051445957168789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4994433054700963971445859 7491649582051445957168789)
                ·
                  refine ⟨351171074158661529242287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7491649582051445957168789 351171074158661529242287)
                  ·
                    rfl

theorem cell23_6155129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 3, 1, 6].length) (baseStart_6155129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6155129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6155129 prefixEnd_6155129 := by exact prefixLift 6155129
  have htrace : WordTrace (prefixWord ++ tailWord_6155129) baseStart_6155129 baseEnd_6155129 := by
    simpa [prefixWord, tailWord_6155129, baseEnd_6155129] using wordTrace_append hprefix tailTrace_6155129
  have hstable : (prefixWord ++ tailWord_6155129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6155129).length < 2 ^ (prefixWord ++ tailWord_6155129).sum := by decide
  have hdescent : baseEnd_6155129 < baseStart_6155129 := by decide
  rcases family_descends (prefixWord ++ tailWord_6155129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6155135 : List Nat := [1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 7]
def baseStart_6155135 : Nat := 118140960795 + 6155135 * 2 ^ 59
def prefixEnd_6155135 : Nat := 4983230072969 + 3 ^ 40 * 6155135 * 2
def baseEnd_6155135 : Nat := 3160542748311880739705555

theorem tailTrace_6155135 : CollatzResearch.WordTrace tailWord_6155135 prefixEnd_6155135 3160542748311880739705555 := by
  unfold tailWord_6155135
  simp only [CollatzResearch.WordTrace]
  refine ⟨224496216556004583211738859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149664144370669722141159239 224496216556004583211738859)
  ·
    refine ⟨336744324834006874817608289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224496216556004583211738859 336744324834006874817608289)
    ·
      refine ⟨252558243625505156113206217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 336744324834006874817608289 252558243625505156113206217)
      ·
        refine ⟨189418682719128867084904663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 252558243625505156113206217 189418682719128867084904663)
        ·
          refine ⟨284128024078693300627356995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189418682719128867084904663 284128024078693300627356995)
          ·
            refine ⟨426192036118039950941035493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 284128024078693300627356995 426192036118039950941035493)
            ·
              refine ⟨79911006772132490801444155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 426192036118039950941035493 79911006772132490801444155)
              ·
                refine ⟨119866510158198736202166233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79911006772132490801444155 119866510158198736202166233)
                ·
                  refine ⟨89899882618649052151624675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 119866510158198736202166233 89899882618649052151624675)
                  ·
                    refine ⟨134849823927973578227437013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 89899882618649052151624675 134849823927973578227437013)
                    ·
                      refine ⟨3160542748311880739705555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 134849823927973578227437013 3160542748311880739705555)
                      ·
                        rfl

theorem cell23_6155135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 7].length) (baseStart_6155135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6155135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6155135 prefixEnd_6155135 := by exact prefixLift 6155135
  have htrace : WordTrace (prefixWord ++ tailWord_6155135) baseStart_6155135 baseEnd_6155135 := by
    simpa [prefixWord, tailWord_6155135, baseEnd_6155135] using wordTrace_append hprefix tailTrace_6155135
  have hstable : (prefixWord ++ tailWord_6155135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6155135).length < 2 ^ (prefixWord ++ tailWord_6155135).sum := by decide
  have hdescent : baseEnd_6155135 < baseStart_6155135 := by decide
  rcases family_descends (prefixWord ++ tailWord_6155135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6155139 : List Nat := [1, 1, 1, 3, 4, 1, 1, 4, 3, 1, 3]
def baseStart_6155139 : Nat := 118140960795 + 6155139 * 2 ^ 59
def prefixEnd_6155139 : Nat := 4983230072969 + 3 ^ 40 * 6155139 * 2
def baseEnd_6155139 : Nat := 3160544802234498724055537

theorem tailTrace_6155139 : CollatzResearch.WordTrace tailWord_6155139 prefixEnd_6155139 3160544802234498724055537 := by
  unfold tailWord_6155139
  simp only [CollatzResearch.WordTrace]
  refine ⟨224496362447990091894884471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149664241631993394596589647 224496362447990091894884471)
  ·
    refine ⟨336744543671985137842326707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224496362447990091894884471 336744543671985137842326707)
    ·
      refine ⟨505116815507977706763490061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 336744543671985137842326707 505116815507977706763490061)
      ·
        refine ⟨189418805815491640036308773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 505116815507977706763490061 189418805815491640036308773)
        ·
          refine ⟨35516026090404682506807895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 189418805815491640036308773 35516026090404682506807895)
          ·
            refine ⟨53274039135607023760211843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35516026090404682506807895 53274039135607023760211843)
            ·
              refine ⟨79911058703410535640317765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53274039135607023760211843 79911058703410535640317765)
              ·
                refine ⟨14983323506889475432559581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 79911058703410535640317765 14983323506889475432559581)
                ·
                  refine ⟨5618746315083553287209843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14983323506889475432559581 5618746315083553287209843)
                  ·
                    refine ⟨8428119472625329930814765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5618746315083553287209843 8428119472625329930814765)
                    ·
                      refine ⟨3160544802234498724055537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8428119472625329930814765 3160544802234498724055537)
                      ·
                        rfl

theorem cell23_6155139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 4, 3, 1, 3].length) (baseStart_6155139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6155139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6155139 prefixEnd_6155139 := by exact prefixLift 6155139
  have htrace : WordTrace (prefixWord ++ tailWord_6155139) baseStart_6155139 baseEnd_6155139 := by
    simpa [prefixWord, tailWord_6155139, baseEnd_6155139] using wordTrace_append hprefix tailTrace_6155139
  have hstable : (prefixWord ++ tailWord_6155139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6155139).length < 2 ^ (prefixWord ++ tailWord_6155139).sum := by decide
  have hdescent : baseEnd_6155139 < baseStart_6155139 := by decide
  rcases family_descends (prefixWord ++ tailWord_6155139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6155192 : List Nat := [2, 1, 2, 1, 2, 4, 2, 1, 1, 1, 6]
def baseStart_6155192 : Nat := 118140960795 + 6155192 * 2 ^ 59
def prefixEnd_6155192 : Nat := 4983230072969 + 3 ^ 40 * 6155192 * 2
def baseEnd_6155192 : Nat := 3160572016709187016692793

theorem tailTrace_6155192 : CollatzResearch.WordTrace tailWord_6155192 prefixEnd_6155192 3160572016709187016692793 := by
  unfold tailWord_6155192
  simp only [CollatzResearch.WordTrace]
  refine ⟨112249147758399040973281915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149665530344532054631042553 112249147758399040973281915)
  ·
    refine ⟨168373721637598561459922873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112249147758399040973281915 168373721637598561459922873)
    ·
      refine ⟨126280291228198921094942155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168373721637598561459922873 126280291228198921094942155)
      ·
        refine ⟨189420436842298381642413233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126280291228198921094942155 189420436842298381642413233)
        ·
          refine ⟨142065327631723786231809925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189420436842298381642413233 142065327631723786231809925)
          ·
            refine ⟨26637248930948209918464361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 142065327631723786231809925 26637248930948209918464361)
            ·
              refine ⟨19977936698211157438848271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26637248930948209918464361 19977936698211157438848271)
              ·
                refine ⟨29966905047316736158272407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19977936698211157438848271 29966905047316736158272407)
                ·
                  refine ⟨44950357570975104237408611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29966905047316736158272407 44950357570975104237408611)
                  ·
                    refine ⟨67425536356462656356112917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44950357570975104237408611 67425536356462656356112917)
                    ·
                      refine ⟨3160572016709187016692793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67425536356462656356112917 3160572016709187016692793)
                      ·
                        rfl

theorem cell23_6155192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 1, 1, 1, 6].length) (baseStart_6155192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6155192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6155192 prefixEnd_6155192 := by exact prefixLift 6155192
  have htrace : WordTrace (prefixWord ++ tailWord_6155192) baseStart_6155192 baseEnd_6155192 := by
    simpa [prefixWord, tailWord_6155192, baseEnd_6155192] using wordTrace_append hprefix tailTrace_6155192
  have hstable : (prefixWord ++ tailWord_6155192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6155192).length < 2 ^ (prefixWord ++ tailWord_6155192).sum := by decide
  have hdescent : baseEnd_6155192 < baseStart_6155192 := by decide
  rcases family_descends (prefixWord ++ tailWord_6155192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6155199 : List Nat := [1, 1, 2, 2, 2, 1, 2, 6, 1, 2, 3]
def baseStart_6155199 : Nat := 118140960795 + 6155199 * 2 ^ 59
def prefixEnd_6155199 : Nat := 4983230072969 + 3 ^ 40 * 6155199 * 2
def baseEnd_6155199 : Nat := 3160575611073768489305261

theorem tailTrace_6155199 : CollatzResearch.WordTrace tailWord_6155199 prefixEnd_6155199 3160575611073768489305261 := by
  unfold tailWord_6155199
  simp only [CollatzResearch.WordTrace]
  refine ⟨224498550827772722142068651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149665700551848481428045767 224498550827772722142068651)
  ·
    refine ⟨336747826241659083213102977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224498550827772722142068651 336747826241659083213102977)
    ·
      refine ⟨252560869681244312409827233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 336747826241659083213102977 252560869681244312409827233)
      ·
        refine ⟨189420652260933234307370425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 252560869681244312409827233 189420652260933234307370425)
        ·
          refine ⟨142065489195699925730527819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189420652260933234307370425 142065489195699925730527819)
          ·
            refine ⟨213098233793549888595791729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142065489195699925730527819 213098233793549888595791729)
            ·
              refine ⟨159823675345162416446843797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 213098233793549888595791729 159823675345162416446843797)
              ·
                refine ⟨7491734781804488270945803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 159823675345162416446843797 7491734781804488270945803)
                ·
                  refine ⟨11237602172706732406418705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7491734781804488270945803 11237602172706732406418705)
                  ·
                    refine ⟨8428201629530049304814029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11237602172706732406418705 8428201629530049304814029)
                    ·
                      refine ⟨3160575611073768489305261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8428201629530049304814029 3160575611073768489305261)
                      ·
                        rfl

theorem cell23_6155199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 6, 1, 2, 3].length) (baseStart_6155199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6155199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6155199 prefixEnd_6155199 := by exact prefixLift 6155199
  have htrace : WordTrace (prefixWord ++ tailWord_6155199) baseStart_6155199 baseEnd_6155199 := by
    simpa [prefixWord, tailWord_6155199, baseEnd_6155199] using wordTrace_append hprefix tailTrace_6155199
  have hstable : (prefixWord ++ tailWord_6155199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6155199).length < 2 ^ (prefixWord ++ tailWord_6155199).sum := by decide
  have hdescent : baseEnd_6155199 < baseStart_6155199 := by decide
  rcases family_descends (prefixWord ++ tailWord_6155199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6155253 : List Nat := [1, 3, 5, 2, 1, 1, 3, 7]
def baseStart_6155253 : Nat := 118140960795 + 6155253 * 2 ^ 59
def prefixEnd_6155253 : Nat := 4983230072969 + 3 ^ 40 * 6155253 * 2
def baseEnd_6155253 : Nat := 117059382927004121408519

theorem tailTrace_6155253 : CollatzResearch.WordTrace tailWord_6155253 prefixEnd_6155253 117059382927004121408519 := by
  unfold tailWord_6155253
  simp only [CollatzResearch.WordTrace]
  refine ⟨224500520369577089364534413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149667013579718059576356275 224500520369577089364534413)
  ·
    refine ⟨84187695138591408511700405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 224500520369577089364534413 84187695138591408511700405)
    ·
      refine ⟨7892596419242944547971913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 84187695138591408511700405 7892596419242944547971913)
      ·
        refine ⟨5919447314432208410978935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7892596419242944547971913 5919447314432208410978935)
        ·
          refine ⟨8879170971648312616468403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5919447314432208410978935 8879170971648312616468403)
          ·
            refine ⟨13318756457472468924702605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8879170971648312616468403 13318756457472468924702605)
            ·
              refine ⟨4994533671552175846763477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13318756457472468924702605 4994533671552175846763477)
              ·
                refine ⟨117059382927004121408519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4994533671552175846763477 117059382927004121408519)
                ·
                  rfl

theorem cell23_6155253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 3, 7].length) (baseStart_6155253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6155253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6155253 prefixEnd_6155253 := by exact prefixLift 6155253
  have htrace : WordTrace (prefixWord ++ tailWord_6155253) baseStart_6155253 baseEnd_6155253 := by
    simpa [prefixWord, tailWord_6155253, baseEnd_6155253] using wordTrace_append hprefix tailTrace_6155253
  have hstable : (prefixWord ++ tailWord_6155253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6155253).length < 2 ^ (prefixWord ++ tailWord_6155253).sum := by decide
  have hdescent : baseEnd_6155253 < baseStart_6155253 := by decide
  rcases family_descends (prefixWord ++ tailWord_6155253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6155256 : List Nat := [2, 1, 2, 1, 1, 3, 1, 6, 1, 3, 2]
def baseStart_6155256 : Nat := 118140960795 + 6155256 * 2 ^ 59
def prefixEnd_6155256 : Nat := 4983230072969 + 3 ^ 40 * 6155256 * 2
def baseEnd_6155256 : Nat := 3160604879471074766292499

theorem tailTrace_6155256 : CollatzResearch.WordTrace tailWord_6155256 prefixEnd_6155256 3160604879471074766292499 := by
  unfold tailWord_6155256
  simp only [CollatzResearch.WordTrace]
  refine ⟨112250314894283110438446811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149667086525710813917929081 112250314894283110438446811)
  ·
    refine ⟨168375472341424665657670217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112250314894283110438446811 168375472341424665657670217)
    ·
      refine ⟨126281604256068499243252663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168375472341424665657670217 126281604256068499243252663)
      ·
        refine ⟨189422406384102748864878995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126281604256068499243252663 189422406384102748864878995)
        ·
          refine ⟨284133609576154123297318493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189422406384102748864878995 284133609576154123297318493)
          ·
            refine ⟨106550103591057796236494435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 284133609576154123297318493 106550103591057796236494435)
            ·
              refine ⟨159825155386586694354741653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106550103591057796236494435 159825155386586694354741653)
              ·
                refine ⟨7491804158746251297878515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 159825155386586694354741653 7491804158746251297878515)
                ·
                  refine ⟨11237706238119376946817773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7491804158746251297878515 11237706238119376946817773)
                  ·
                    refine ⟨4214139839294766355056665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11237706238119376946817773 4214139839294766355056665)
                    ·
                      refine ⟨3160604879471074766292499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4214139839294766355056665 3160604879471074766292499)
                      ·
                        rfl

theorem cell23_6155256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 6, 1, 3, 2].length) (baseStart_6155256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6155256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6155256 prefixEnd_6155256 := by exact prefixLift 6155256
  have htrace : WordTrace (prefixWord ++ tailWord_6155256) baseStart_6155256 baseEnd_6155256 := by
    simpa [prefixWord, tailWord_6155256, baseEnd_6155256] using wordTrace_append hprefix tailTrace_6155256
  have hstable : (prefixWord ++ tailWord_6155256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6155256).length < 2 ^ (prefixWord ++ tailWord_6155256).sum := by decide
  have hdescent : baseEnd_6155256 < baseStart_6155256 := by decide
  rcases family_descends (prefixWord ++ tailWord_6155256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6155299 : List Nat := [1, 1, 1, 4, 3, 2, 2, 1, 2, 2, 4]
def baseStart_6155299 : Nat := 118140960795 + 6155299 * 2 ^ 59
def prefixEnd_6155299 : Nat := 4983230072969 + 3 ^ 40 * 6155299 * 2
def baseEnd_6155299 : Nat := 3160626959139218098054801

theorem tailTrace_6155299 : CollatzResearch.WordTrace tailWord_6155299 prefixEnd_6155299 3160626959139218098054801 := by
  unfold tailWord_6155299
  simp only [CollatzResearch.WordTrace]
  refine ⟨224502198127410439220708951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149668132084940292813805967 224502198127410439220708951)
  ·
    refine ⟨336753297191115658831063427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224502198127410439220708951 336753297191115658831063427)
    ·
      refine ⟨505129945786673488246595141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 336753297191115658831063427 505129945786673488246595141)
      ·
        refine ⟨94711864835001279046236589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 505129945786673488246595141 94711864835001279046236589)
        ·
          refine ⟨35516949313125479642338721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94711864835001279046236589 35516949313125479642338721)
          ·
            refine ⟨26637711984844109731754041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35516949313125479642338721 26637711984844109731754041)
            ·
              refine ⟨19978283988633082298815531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26637711984844109731754041 19978283988633082298815531)
              ·
                refine ⟨29967425982949623448223297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19978283988633082298815531 29967425982949623448223297)
                ·
                  refine ⟨22475569487212217586167473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29967425982949623448223297 22475569487212217586167473)
                  ·
                    refine ⟨16856677115409163189625605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22475569487212217586167473 16856677115409163189625605)
                    ·
                      refine ⟨3160626959139218098054801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16856677115409163189625605 3160626959139218098054801)
                      ·
                        rfl

theorem cell23_6155299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 1, 2, 2, 4].length) (baseStart_6155299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6155299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6155299 prefixEnd_6155299 := by exact prefixLift 6155299
  have htrace : WordTrace (prefixWord ++ tailWord_6155299) baseStart_6155299 baseEnd_6155299 := by
    simpa [prefixWord, tailWord_6155299, baseEnd_6155299] using wordTrace_append hprefix tailTrace_6155299
  have hstable : (prefixWord ++ tailWord_6155299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6155299).length < 2 ^ (prefixWord ++ tailWord_6155299).sum := by decide
  have hdescent : baseEnd_6155299 < baseStart_6155299 := by decide
  rcases family_descends (prefixWord ++ tailWord_6155299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6155349 : List Nat := [1, 3, 2, 2, 1, 2, 3, 1, 1, 2, 5]
def baseStart_6155349 : Nat := 118140960795 + 6155349 * 2 ^ 59
def prefixEnd_6155349 : Nat := 4983230072969 + 3 ^ 40 * 6155349 * 2
def baseEnd_6155349 : Nat := 3160652633171942902429571

theorem tailTrace_6155349 : CollatzResearch.WordTrace tailWord_6155349 prefixEnd_6155349 3160652633171942902429571 := by
  unfold tailWord_6155349
  simp only [CollatzResearch.WordTrace]
  refine ⟨224504021777229297760029101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149669347851486198506686067 224504021777229297760029101)
  ·
    refine ⟨84189008166460986660010913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 224504021777229297760029101 84189008166460986660010913)
    ·
      refine ⟨63141756124845739995008185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84189008166460986660010913 63141756124845739995008185)
      ·
        refine ⟨47356317093634304996256139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63141756124845739995008185 47356317093634304996256139)
        ·
          refine ⟨71034475640451457494384209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47356317093634304996256139 71034475640451457494384209)
          ·
            refine ⟨53275856730338593120788157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71034475640451457494384209 53275856730338593120788157)
            ·
              refine ⟨19978446273876972420295559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53275856730338593120788157 19978446273876972420295559)
              ·
                refine ⟨29967669410815458630443339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19978446273876972420295559 29967669410815458630443339)
                ·
                  refine ⟨44951504116223187945665009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29967669410815458630443339 44951504116223187945665009)
                  ·
                    refine ⟨33713628087167390959248757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44951504116223187945665009 33713628087167390959248757)
                    ·
                      refine ⟨3160652633171942902429571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33713628087167390959248757 3160652633171942902429571)
                      ·
                        rfl

theorem cell23_6155349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 1, 1, 2, 5].length) (baseStart_6155349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6155349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6155349 prefixEnd_6155349 := by exact prefixLift 6155349
  have htrace : WordTrace (prefixWord ++ tailWord_6155349) baseStart_6155349 baseEnd_6155349 := by
    simpa [prefixWord, tailWord_6155349, baseEnd_6155349] using wordTrace_append hprefix tailTrace_6155349
  have hstable : (prefixWord ++ tailWord_6155349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6155349).length < 2 ^ (prefixWord ++ tailWord_6155349).sum := by decide
  have hdescent : baseEnd_6155349 < baseStart_6155349 := by decide
  rcases family_descends (prefixWord ++ tailWord_6155349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6155359 : List Nat := [1, 1, 2, 3, 1, 1, 3, 2, 4, 1, 4]
def baseStart_6155359 : Nat := 118140960795 + 6155359 * 2 ^ 59
def prefixEnd_6155359 : Nat := 4983230072969 + 3 ^ 40 * 6155359 * 2
def baseEnd_6155359 : Nat := 3160657767978487863304525

theorem tailTrace_6155359 : CollatzResearch.WordTrace tailWord_6155359 prefixEnd_6155359 3160657767978487863304525 := by
  unfold tailWord_6155359
  simp only [CollatzResearch.WordTrace]
  refine ⟨224504386507193069467893131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149669591004795379645262087 224504386507193069467893131)
  ·
    refine ⟨336756579760789604201839697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224504386507193069467893131 336756579760789604201839697)
    ·
      refine ⟨252567434820592203151379773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 336756579760789604201839697 252567434820592203151379773)
      ·
        refine ⟨94712788057722076181767415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 252567434820592203151379773 94712788057722076181767415)
        ·
          refine ⟨142069182086583114272651123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94712788057722076181767415 142069182086583114272651123)
          ·
            refine ⟨213103773129874671408976685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142069182086583114272651123 213103773129874671408976685)
            ·
              refine ⟨79913914923703001778366257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 213103773129874671408976685 79913914923703001778366257)
              ·
                refine ⟨59935436192777251333774693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79913914923703001778366257 59935436192777251333774693)
                ·
                  refine ⟨11237894286145734625082755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59935436192777251333774693 11237894286145734625082755)
                  ·
                    refine ⟨16856841429218601937624133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11237894286145734625082755 16856841429218601937624133)
                    ·
                      refine ⟨3160657767978487863304525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16856841429218601937624133 3160657767978487863304525)
                      ·
                        rfl

theorem cell23_6155359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 2, 4, 1, 4].length) (baseStart_6155359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6155359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6155359 prefixEnd_6155359 := by exact prefixLift 6155359
  have htrace : WordTrace (prefixWord ++ tailWord_6155359) baseStart_6155359 baseEnd_6155359 := by
    simpa [prefixWord, tailWord_6155359, baseEnd_6155359] using wordTrace_append hprefix tailTrace_6155359
  have hstable : (prefixWord ++ tailWord_6155359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6155359).length < 2 ^ (prefixWord ++ tailWord_6155359).sum := by decide
  have hdescent : baseEnd_6155359 < baseStart_6155359 := by decide
  rcases family_descends (prefixWord ++ tailWord_6155359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6155376 : List Nat := [2, 1, 1, 1, 5, 1, 4, 1, 2, 1, 4]
def baseStart_6155376 : Nat := 118140960795 + 6155376 * 2 ^ 59
def prefixEnd_6155376 : Nat := 4983230072969 + 3 ^ 40 * 6155376 * 2
def baseEnd_6155376 : Nat := 3160666497149614296791947

theorem tailTrace_6155376 : CollatzResearch.WordTrace tailWord_6155376 prefixEnd_6155376 3160666497149614296791947 := by
  unfold tailWord_6155376
  simp only [CollatzResearch.WordTrace]
  refine ⟨112252503274065740685630991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149670004365420987580841321 112252503274065740685630991)
  ·
    refine ⟨168378754911098611028446487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112252503274065740685630991 168378754911098611028446487)
    ·
      refine ⟨252568132366647916542669731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168378754911098611028446487 252568132366647916542669731)
      ·
        refine ⟨378852198549971874814004597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252568132366647916542669731 378852198549971874814004597)
        ·
          refine ⟨35517393614059863263812931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 378852198549971874814004597 35517393614059863263812931)
          ·
            refine ⟨53276090421089794895719397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35517393614059863263812931 53276090421089794895719397)
            ·
              refine ⟨9989266953954336542947387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53276090421089794895719397 9989266953954336542947387)
              ·
                refine ⟨14983900430931504814421081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9989266953954336542947387 14983900430931504814421081)
                ·
                  refine ⟨11237925323198628610815811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14983900430931504814421081 11237925323198628610815811)
                  ·
                    refine ⟨16856887984797942916223717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11237925323198628610815811 16856887984797942916223717)
                    ·
                      refine ⟨3160666497149614296791947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16856887984797942916223717 3160666497149614296791947)
                      ·
                        rfl

theorem cell23_6155376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4, 1, 2, 1, 4].length) (baseStart_6155376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6155376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6155376 prefixEnd_6155376 := by exact prefixLift 6155376
  have htrace : WordTrace (prefixWord ++ tailWord_6155376) baseStart_6155376 baseEnd_6155376 := by
    simpa [prefixWord, tailWord_6155376, baseEnd_6155376] using wordTrace_append hprefix tailTrace_6155376
  have hstable : (prefixWord ++ tailWord_6155376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6155376).length < 2 ^ (prefixWord ++ tailWord_6155376).sum := by decide
  have hdescent : baseEnd_6155376 < baseStart_6155376 := by decide
  rcases family_descends (prefixWord ++ tailWord_6155376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6155389 : List Nat := [1, 4, 1, 1, 3, 1, 2, 1, 2, 1, 6]
def baseStart_6155389 : Nat := 118140960795 + 6155389 * 2 ^ 59
def prefixEnd_6155389 : Nat := 4983230072969 + 3 ^ 40 * 6155389 * 2
def baseEnd_6155389 : Nat := 3160673172398122745929387

theorem tailTrace_6155389 : CollatzResearch.WordTrace tailWord_6155389 prefixEnd_6155389 3160673172398122745929387 := by
  unfold tailWord_6155389
  simp only [CollatzResearch.WordTrace]
  refine ⟨224505480697084384591485221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149670320464722923060990147 224505480697084384591485221)
  ·
    refine ⟨42094777630703322110903479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 224505480697084384591485221 42094777630703322110903479)
    ·
      refine ⟨63142166446054983166355219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42094777630703322110903479 63142166446054983166355219)
      ·
        refine ⟨94713249669082474749532829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63142166446054983166355219 94713249669082474749532829)
        ·
          refine ⟨35517468625905928031074811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94713249669082474749532829 35517468625905928031074811)
          ·
            refine ⟨53276202938858892046612217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35517468625905928031074811 53276202938858892046612217)
            ·
              refine ⟨39957152204144169034959163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53276202938858892046612217 39957152204144169034959163)
              ·
                refine ⟨59935728306216253552438745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39957152204144169034959163 59935728306216253552438745)
                ·
                  refine ⟨44951796229662190164329059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59935728306216253552438745 44951796229662190164329059)
                  ·
                    refine ⟨67427694344493285246493589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44951796229662190164329059 67427694344493285246493589)
                    ·
                      refine ⟨3160673172398122745929387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67427694344493285246493589 3160673172398122745929387)
                      ·
                        rfl

theorem cell23_6155389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 1, 2, 1, 6].length) (baseStart_6155389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6155389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6155389 prefixEnd_6155389 := by exact prefixLift 6155389
  have htrace : WordTrace (prefixWord ++ tailWord_6155389) baseStart_6155389 baseEnd_6155389 := by
    simpa [prefixWord, tailWord_6155389, baseEnd_6155389] using wordTrace_append hprefix tailTrace_6155389
  have hstable : (prefixWord ++ tailWord_6155389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6155389).length < 2 ^ (prefixWord ++ tailWord_6155389).sum := by decide
  have hdescent : baseEnd_6155389 < baseStart_6155389 := by decide
  rcases family_descends (prefixWord ++ tailWord_6155389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6155416 : List Nat := [2, 1, 2, 4, 2, 1, 2, 3, 6]
def baseStart_6155416 : Nat := 118140960795 + 6155416 * 2 ^ 59
def prefixEnd_6155416 : Nat := 4983230072969 + 3 ^ 40 * 6155416 * 2
def baseEnd_6155416 : Nat := 351187448486199348921307

theorem tailTrace_6155416 : CollatzResearch.WordTrace tailWord_6155416 prefixEnd_6155416 351187448486199348921307 := by
  unfold tailWord_6155416
  simp only [CollatzResearch.WordTrace]
  refine ⟨112253232733993284101359051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149670976978657712135145401 112253232733993284101359051)
  ·
    refine ⟨168379849100989926152038577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112253232733993284101359051 168379849100989926152038577)
    ·
      refine ⟨126284886825742444614028933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168379849100989926152038577 126284886825742444614028933)
      ·
        refine ⟨23678416279826708365130425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 126284886825742444614028933 23678416279826708365130425)
        ·
          refine ⟨17758812209870031273847819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23678416279826708365130425 17758812209870031273847819)
          ·
            refine ⟨26638218314805046910771729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17758812209870031273847819 26638218314805046910771729)
            ·
              refine ⟨19978663736103785183078797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26638218314805046910771729 19978663736103785183078797)
              ·
                refine ⟨7491998901038919443654549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19978663736103785183078797 7491998901038919443654549)
                ·
                  refine ⟨351187448486199348921307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7491998901038919443654549 351187448486199348921307)
                  ·
                    rfl

theorem cell23_6155416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 3, 6].length) (baseStart_6155416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6155416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6155416 prefixEnd_6155416 := by exact prefixLift 6155416
  have htrace : WordTrace (prefixWord ++ tailWord_6155416) baseStart_6155416 baseEnd_6155416 := by
    simpa [prefixWord, tailWord_6155416, baseEnd_6155416] using wordTrace_append hprefix tailTrace_6155416
  have hstable : (prefixWord ++ tailWord_6155416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6155416).length < 2 ^ (prefixWord ++ tailWord_6155416).sum := by decide
  have hdescent : baseEnd_6155416 < baseStart_6155416 := by decide
  rcases family_descends (prefixWord ++ tailWord_6155416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6155437 : List Nat := [1, 5, 2, 1, 3, 1, 2, 3, 1, 4]
def baseStart_6155437 : Nat := 118140960795 + 6155437 * 2 ^ 59
def prefixEnd_6155437 : Nat := 4983230072969 + 3 ^ 40 * 6155437 * 2
def baseEnd_6155437 : Nat := 1053565939823179519376389

theorem tailTrace_6155437 : CollatzResearch.WordTrace tailWord_6155437 prefixEnd_6155437 1053565939823179519376389 := by
  unfold tailWord_6155437
  simp only [CollatzResearch.WordTrace]
  refine ⟨224507231400910488789232565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149671487600606992526155043 224507231400910488789232565)
  ·
    refine ⟨21047552943835358323990553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 224507231400910488789232565 21047552943835358323990553)
    ·
      refine ⟨15785664707876518742992915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21047552943835358323990553 15785664707876518742992915)
      ·
        refine ⟨23678497061814778114489373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15785664707876518742992915 23678497061814778114489373)
        ·
          refine ⟨8879436398180541792933515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23678497061814778114489373 8879436398180541792933515)
          ·
            refine ⟨13319154597270812689400273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8879436398180541792933515 13319154597270812689400273)
            ·
              refine ⟨9989365947953109517050205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13319154597270812689400273 9989365947953109517050205)
              ·
                refine ⟨3746012230482416068893827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9989365947953109517050205 3746012230482416068893827)
                ·
                  refine ⟨5619018345723624103340741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3746012230482416068893827 5619018345723624103340741)
                  ·
                    refine ⟨1053565939823179519376389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5619018345723624103340741 1053565939823179519376389)
                    ·
                      rfl

theorem cell23_6155437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 2, 3, 1, 4].length) (baseStart_6155437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6155437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6155437 prefixEnd_6155437 := by exact prefixLift 6155437
  have htrace : WordTrace (prefixWord ++ tailWord_6155437) baseStart_6155437 baseEnd_6155437 := by
    simpa [prefixWord, tailWord_6155437, baseEnd_6155437] using wordTrace_append hprefix tailTrace_6155437
  have hstable : (prefixWord ++ tailWord_6155437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6155437).length < 2 ^ (prefixWord ++ tailWord_6155437).sum := by decide
  have hdescent : baseEnd_6155437 < baseStart_6155437 := by decide
  rcases family_descends (prefixWord ++ tailWord_6155437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6155453 : List Nat := [1, 4, 1, 2, 1, 1, 2, 4, 2, 3, 2]
def baseStart_6155453 : Nat := 118140960795 + 6155453 * 2 ^ 59
def prefixEnd_6155453 : Nat := 4983230072969 + 3 ^ 40 * 6155453 * 2
def baseEnd_6155453 : Nat := 3160706035160010495529093

theorem tailTrace_6155453 : CollatzResearch.WordTrace tailWord_6155453 prefixEnd_6155453 3160706035160010495529093 := by
  unfold tailWord_6155453
  simp only [CollatzResearch.WordTrace]
  refine ⟨224507814968852523521815013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149671876645901682347876675 224507814968852523521815013)
  ·
    refine ⟨42095215306659848160340315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 224507814968852523521815013 42095215306659848160340315)
    ·
      refine ⟨63142822959989772240510473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42095215306659848160340315 63142822959989772240510473)
      ·
        refine ⟨47357117219992329180382855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63142822959989772240510473 47357117219992329180382855)
        ·
          refine ⟨71035675829988493770574283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47357117219992329180382855 71035675829988493770574283)
          ·
            refine ⟨106553513744982740655861425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71035675829988493770574283 106553513744982740655861425)
            ·
              refine ⟨79915135308737055491896069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106553513744982740655861425 79915135308737055491896069)
              ·
                refine ⟨14984087870388197904730513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 79915135308737055491896069 14984087870388197904730513)
                ·
                  refine ⟨11238065902791148428547885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14984087870388197904730513 11238065902791148428547885)
                  ·
                    refine ⟨4214274713546680660705457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11238065902791148428547885 4214274713546680660705457)
                    ·
                      refine ⟨3160706035160010495529093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4214274713546680660705457 3160706035160010495529093)
                      ·
                        rfl

theorem cell23_6155453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 4, 2, 3, 2].length) (baseStart_6155453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6155453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6155453 prefixEnd_6155453 := by exact prefixLift 6155453
  have htrace : WordTrace (prefixWord ++ tailWord_6155453) baseStart_6155453 baseEnd_6155453 := by
    simpa [prefixWord, tailWord_6155453, baseEnd_6155453] using wordTrace_append hprefix tailTrace_6155453
  have hstable : (prefixWord ++ tailWord_6155453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6155453).length < 2 ^ (prefixWord ++ tailWord_6155453).sum := by decide
  have hdescent : baseEnd_6155453 < baseStart_6155453 := by decide
  rcases family_descends (prefixWord ++ tailWord_6155453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6155496 : List Nat := [2, 1, 4, 1, 2, 1, 2, 1, 3, 2, 4]
def baseStart_6155496 : Nat := 118140960795 + 6155496 * 2 ^ 59
def prefixEnd_6155496 : Nat := 4983230072969 + 3 ^ 40 * 6155496 * 2
def baseEnd_6155496 : Nat := 3160728114828153827291395

theorem tailTrace_6155496 : CollatzResearch.WordTrace tailWord_6155496 prefixEnd_6155496 3160728114828153827291395 := by
  unfold tailWord_6155496
  simp only [CollatzResearch.WordTrace]
  refine ⟨112254691653848370932815171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149672922205131161243753561 112254691653848370932815171)
  ·
    refine ⟨168382037480772556399222757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112254691653848370932815171 168382037480772556399222757)
    ·
      refine ⟨31571632027644854324854267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 168382037480772556399222757 31571632027644854324854267)
      ·
        refine ⟨47357448041467281487281401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31571632027644854324854267 47357448041467281487281401)
        ·
          refine ⟨35518086031100461115461051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47357448041467281487281401 35518086031100461115461051)
          ·
            refine ⟨53277129046650691673191577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35518086031100461115461051 53277129046650691673191577)
            ·
              refine ⟨39957846784988018754893683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53277129046650691673191577 39957846784988018754893683)
              ·
                refine ⟨59936770177482028132340525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39957846784988018754893683 59936770177482028132340525)
                ·
                  refine ⟨22476288816555760549627697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59936770177482028132340525 22476288816555760549627697)
                  ·
                    refine ⟨16857216612416820412220773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22476288816555760549627697 16857216612416820412220773)
                    ·
                      refine ⟨3160728114828153827291395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16857216612416820412220773 3160728114828153827291395)
                      ·
                        rfl

theorem cell23_6155496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 1, 3, 2, 4].length) (baseStart_6155496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6155496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6155496 prefixEnd_6155496 := by exact prefixLift 6155496
  have htrace : WordTrace (prefixWord ++ tailWord_6155496) baseStart_6155496 baseEnd_6155496 := by
    simpa [prefixWord, tailWord_6155496, baseEnd_6155496] using wordTrace_append hprefix tailTrace_6155496
  have hstable : (prefixWord ++ tailWord_6155496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6155496).length < 2 ^ (prefixWord ++ tailWord_6155496).sum := by decide
  have hdescent : baseEnd_6155496 < baseStart_6155496 := by decide
  rcases family_descends (prefixWord ++ tailWord_6155496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6155503 : List Nat := [1, 1, 2, 1, 7, 1, 2, 1, 1, 1, 5]
def baseStart_6155503 : Nat := 118140960795 + 6155503 * 2 ^ 59
def prefixEnd_6155503 : Nat := 4983230072969 + 3 ^ 40 * 6155503 * 2
def baseEnd_6155503 : Nat := 3160731709192735299903863

theorem tailTrace_6155503 : CollatzResearch.WordTrace tailWord_6155503 prefixEnd_6155503 3160731709192735299903863 := by
  unfold tailWord_6155503
  simp only [CollatzResearch.WordTrace]
  refine ⟨224509638618671382061135163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149673092412447588040756775 224509638618671382061135163)
  ·
    refine ⟨336764457928007073091702745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224509638618671382061135163 336764457928007073091702745)
    ·
      refine ⟨252573343446005304818777059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 336764457928007073091702745 252573343446005304818777059)
      ·
        refine ⟨378860015169007957228165589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252573343446005304818777059 378860015169007957228165589)
        ·
          refine ⟨8879531605523623997535131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 378860015169007957228165589 8879531605523623997535131)
          ·
            refine ⟨13319297408285435996302697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8879531605523623997535131 13319297408285435996302697)
            ·
              refine ⟨9989473056214076997227023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13319297408285435996302697 9989473056214076997227023)
              ·
                refine ⟨14984209584321115495840535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9989473056214076997227023 14984209584321115495840535)
                ·
                  refine ⟨22476314376481673243760803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14984209584321115495840535 22476314376481673243760803)
                  ·
                    refine ⟨33714471564722509865641205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22476314376481673243760803 33714471564722509865641205)
                    ·
                      refine ⟨3160731709192735299903863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33714471564722509865641205 3160731709192735299903863)
                      ·
                        rfl

theorem cell23_6155503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 2, 1, 1, 1, 5].length) (baseStart_6155503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6155503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6155503 prefixEnd_6155503 := by exact prefixLift 6155503
  have htrace : WordTrace (prefixWord ++ tailWord_6155503) baseStart_6155503 baseEnd_6155503 := by
    simpa [prefixWord, tailWord_6155503, baseEnd_6155503] using wordTrace_append hprefix tailTrace_6155503
  have hstable : (prefixWord ++ tailWord_6155503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6155503).length < 2 ^ (prefixWord ++ tailWord_6155503).sum := by decide
  have hdescent : baseEnd_6155503 < baseStart_6155503 := by decide
  rcases family_descends (prefixWord ++ tailWord_6155503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6155539 : List Nat := [1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 10]
def baseStart_6155539 : Nat := 118140960795 + 6155539 * 2 ^ 59
def prefixEnd_6155539 : Nat := 4983230072969 + 3 ^ 40 * 6155539 * 2
def baseEnd_6155539 : Nat := 3160750194496297159053697

theorem tailTrace_6155539 : CollatzResearch.WordTrace tailWord_6155539 prefixEnd_6155539 3160750194496297159053697 := by
  unfold tailWord_6155539
  simp only [CollatzResearch.WordTrace]
  refine ⟨224510951646540960209445671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149673967764360640139630447 224510951646540960209445671)
  ·
    refine ⟨336766427469811440314168507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224510951646540960209445671 336766427469811440314168507)
    ·
      refine ⟨505149641204717160471252761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 336766427469811440314168507 505149641204717160471252761)
      ·
        refine ⟨378862230903537870353439571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 505149641204717160471252761 378862230903537870353439571)
        ·
          refine ⟨568293346355306805530159357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 378862230903537870353439571 568293346355306805530159357)
          ·
            refine ⟨213110004883240052073809759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 568293346355306805530159357 213110004883240052073809759)
            ·
              refine ⟨319665007324860078110714639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 213110004883240052073809759 319665007324860078110714639)
              ·
                refine ⟨479497510987290117166071959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 319665007324860078110714639 479497510987290117166071959)
                ·
                  refine ⟨719246266480935175749107939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 479497510987290117166071959 719246266480935175749107939)
                  ·
                    refine ⟨1078869399721402763623661909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 719246266480935175749107939 1078869399721402763623661909)
                    ·
                      refine ⟨3160750194496297159053697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 1078869399721402763623661909 3160750194496297159053697)
                      ·
                        rfl

theorem cell23_6155539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 10].length) (baseStart_6155539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6155539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6155539 prefixEnd_6155539 := by exact prefixLift 6155539
  have htrace : WordTrace (prefixWord ++ tailWord_6155539) baseStart_6155539 baseEnd_6155539 := by
    simpa [prefixWord, tailWord_6155539, baseEnd_6155539] using wordTrace_append hprefix tailTrace_6155539
  have hstable : (prefixWord ++ tailWord_6155539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6155539).length < 2 ^ (prefixWord ++ tailWord_6155539).sum := by decide
  have hdescent : baseEnd_6155539 < baseStart_6155539 := by decide
  rcases family_descends (prefixWord ++ tailWord_6155539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6155596 : List Nat := [2, 2, 1, 3, 2, 2, 1, 1, 9]
def baseStart_6155596 : Nat := 118140960795 + 6155596 * 2 ^ 59
def prefixEnd_6155596 : Nat := 4983230072969 + 3 ^ 40 * 6155596 * 2
def baseEnd_6155596 : Nat := 351197718099289270671215

theorem tailTrace_6155596 : CollatzResearch.WordTrace tailWord_6155596 prefixEnd_6155596 351197718099289270671215 := by
  unfold tailWord_6155596
  simp only [CollatzResearch.WordTrace]
  refine ⟨112256515303667229472135321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149675353738222972629513761 112256515303667229472135321)
  ·
    refine ⟨84192386477750422104101491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112256515303667229472135321 84192386477750422104101491)
    ·
      refine ⟨126288579716625633156152237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84192386477750422104101491 126288579716625633156152237)
      ·
        refine ⟨47358217393734612433557089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126288579716625633156152237 47358217393734612433557089)
        ·
          refine ⟨35518663045300959325167817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47358217393734612433557089 35518663045300959325167817)
          ·
            refine ⟨26638997283975719493875863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35518663045300959325167817 26638997283975719493875863)
            ·
              refine ⟨39958495925963579240813795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26638997283975719493875863 39958495925963579240813795)
              ·
                refine ⟨59937743888945368861220693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39958495925963579240813795 59937743888945368861220693)
                ·
                  refine ⟨351197718099289270671215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 59937743888945368861220693 351197718099289270671215)
                  ·
                    rfl

theorem cell23_6155596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 1, 9].length) (baseStart_6155596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6155596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6155596 prefixEnd_6155596 := by exact prefixLift 6155596
  have htrace : WordTrace (prefixWord ++ tailWord_6155596) baseStart_6155596 baseEnd_6155596 := by
    simpa [prefixWord, tailWord_6155596, baseEnd_6155596] using wordTrace_append hprefix tailTrace_6155596
  have hstable : (prefixWord ++ tailWord_6155596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6155596).length < 2 ^ (prefixWord ++ tailWord_6155596).sum := by decide
  have hdescent : baseEnd_6155596 < baseStart_6155596 := by decide
  rcases family_descends (prefixWord ++ tailWord_6155596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6155633 : List Nat := [1, 2, 2, 2, 1, 2, 2, 1, 1, 7, 2]
def baseStart_6155633 : Nat := 118140960795 + 6155633 * 2 ^ 59
def prefixEnd_6155633 : Nat := 4983230072969 + 3 ^ 40 * 6155633 * 2
def baseEnd_6155633 : Nat := 3160798461677819791278265

theorem tailTrace_6155633 : CollatzResearch.WordTrace tailWord_6155633 prefixEnd_6155633 3160798461677819791278265 := by
  unfold tailWord_6155633
  simp only [CollatzResearch.WordTrace]
  refine ⟨224514380108200414263367553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149676253405466942842245035 224514380108200414263367553)
  ·
    refine ⟨168385785081150310697525665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224514380108200414263367553 168385785081150310697525665)
    ·
      refine ⟨126289338810862733023144249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168385785081150310697525665 126289338810862733023144249)
      ·
        refine ⟨94717004108147049767358187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126289338810862733023144249 94717004108147049767358187)
        ·
          refine ⟨142075506162220574651037281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94717004108147049767358187 142075506162220574651037281)
          ·
            refine ⟨106556629621665430988277961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142075506162220574651037281 106556629621665430988277961)
            ·
              refine ⟨79917472216249073241208471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106556629621665430988277961 79917472216249073241208471)
              ·
                refine ⟨119876208324373609861812707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79917472216249073241208471 119876208324373609861812707)
                ·
                  refine ⟨179814312486560414792719061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 119876208324373609861812707 179814312486560414792719061)
                  ·
                    refine ⟨4214397948903759721704353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 179814312486560414792719061 4214397948903759721704353)
                    ·
                      refine ⟨3160798461677819791278265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4214397948903759721704353 3160798461677819791278265)
                      ·
                        rfl

theorem cell23_6155633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 7, 2].length) (baseStart_6155633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6155633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6155633 prefixEnd_6155633 := by exact prefixLift 6155633
  have htrace : WordTrace (prefixWord ++ tailWord_6155633) baseStart_6155633 baseEnd_6155633 := by
    simpa [prefixWord, tailWord_6155633, baseEnd_6155633] using wordTrace_append hprefix tailTrace_6155633
  have hstable : (prefixWord ++ tailWord_6155633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6155633).length < 2 ^ (prefixWord ++ tailWord_6155633).sum := by decide
  have hdescent : baseEnd_6155633 < baseStart_6155633 := by decide
  rcases family_descends (prefixWord ++ tailWord_6155633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6155703 : List Nat := [1, 1, 3, 1, 3, 2, 3, 3, 6]
def baseStart_6155703 : Nat := 118140960795 + 6155703 * 2 ^ 59
def prefixEnd_6155703 : Nat := 4983230072969 + 3 ^ 40 * 6155703 * 2
def baseEnd_6155703 : Nat := 351203822813737168600327

theorem tailTrace_6155703 : CollatzResearch.WordTrace tailWord_6155703 prefixEnd_6155703 351203822813737168600327 := by
  unfold tailWord_6155703
  simp only [CollatzResearch.WordTrace]
  refine ⟨224516933217946816218415763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149677955478631210812277175 224516933217946816218415763)
  ·
    refine ⟨336775399826920224327623645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224516933217946816218415763 336775399826920224327623645)
    ·
      refine ⟨126290774935095084122858867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 336775399826920224327623645 126290774935095084122858867)
      ·
        refine ⟨189436162402642626184288301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126290774935095084122858867 189436162402642626184288301)
        ·
          refine ⟨71038560900990984819108113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 189436162402642626184288301 71038560900990984819108113)
          ·
            refine ⟨53278920675743238614331085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71038560900990984819108113 53278920675743238614331085)
            ·
              refine ⟨19979595253403714480374157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53278920675743238614331085 19979595253403714480374157)
              ·
                refine ⟨7492348220026392930140309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19979595253403714480374157 7492348220026392930140309)
                ·
                  refine ⟨351203822813737168600327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7492348220026392930140309 351203822813737168600327)
                  ·
                    rfl

theorem cell23_6155703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3, 6].length) (baseStart_6155703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6155703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6155703 prefixEnd_6155703 := by exact prefixLift 6155703
  have htrace : WordTrace (prefixWord ++ tailWord_6155703) baseStart_6155703 baseEnd_6155703 := by
    simpa [prefixWord, tailWord_6155703, baseEnd_6155703] using wordTrace_append hprefix tailTrace_6155703
  have hstable : (prefixWord ++ tailWord_6155703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6155703).length < 2 ^ (prefixWord ++ tailWord_6155703).sum := by decide
  have hdescent : baseEnd_6155703 < baseStart_6155703 := by decide
  rcases family_descends (prefixWord ++ tailWord_6155703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6155741 : List Nat := [1, 4, 3, 1, 1, 4, 2, 2, 1, 4]
def baseStart_6155741 : Nat := 118140960795 + 6155741 * 2 ^ 59
def prefixEnd_6155741 : Nat := 4983230072969 + 3 ^ 40 * 6155741 * 2
def baseEnd_6155741 : Nat := 1053617972529501789575923

theorem tailTrace_6155741 : CollatzResearch.WordTrace tailWord_6155741 prefixEnd_6155741 1053617972529501789575923 := by
  unfold tailWord_6155741
  simp only [CollatzResearch.WordTrace]
  refine ⟨224518319191809148708299077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149678879461206099138866051 224518319191809148708299077)
  ·
    refine ⟨42097184848464215382806077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 224518319191809148708299077 42097184848464215382806077)
    ·
      refine ⟨15786444318174080768552279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42097184848464215382806077 15786444318174080768552279)
      ·
        refine ⟨23679666477261121152828419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15786444318174080768552279 23679666477261121152828419)
        ·
          refine ⟨35519499715891681729242629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23679666477261121152828419 35519499715891681729242629)
          ·
            refine ⟨6659906196729690324232993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35519499715891681729242629 6659906196729690324232993)
            ·
              refine ⟨4994929647547267743174745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6659906196729690324232993 4994929647547267743174745)
              ·
                refine ⟨3746197235660450807381059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4994929647547267743174745 3746197235660450807381059)
                ·
                  refine ⟨5619295853490676211071589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3746197235660450807381059 5619295853490676211071589)
                  ·
                    refine ⟨1053617972529501789575923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5619295853490676211071589 1053617972529501789575923)
                    ·
                      rfl

theorem cell23_6155741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 2, 2, 1, 4].length) (baseStart_6155741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6155741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6155741 prefixEnd_6155741 := by exact prefixLift 6155741
  have htrace : WordTrace (prefixWord ++ tailWord_6155741) baseStart_6155741 baseEnd_6155741 := by
    simpa [prefixWord, tailWord_6155741, baseEnd_6155741] using wordTrace_append hprefix tailTrace_6155741
  have hstable : (prefixWord ++ tailWord_6155741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6155741).length < 2 ^ (prefixWord ++ tailWord_6155741).sum := by decide
  have hdescent : baseEnd_6155741 < baseStart_6155741 := by decide
  rcases family_descends (prefixWord ++ tailWord_6155741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6155770 : List Nat := [3, 1, 1, 1, 1, 2, 4, 4, 1, 1, 4]
def baseStart_6155770 : Nat := 118140960795 + 6155770 * 2 ^ 59
def prefixEnd_6155770 : Nat := 4983230072969 + 3 ^ 40 * 6155770 * 2
def baseEnd_6155770 : Nat := 3160868808527485755265135

theorem tailTrace_6155770 : CollatzResearch.WordTrace tailWord_6155770 prefixEnd_6155770 3160868808527485755265135 := by
  unfold tailWord_6155770
  simp only [CollatzResearch.WordTrace]
  refine ⟨56129844227176021665276191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149679584605802724440736509 56129844227176021665276191)
  ·
    refine ⟨84194766340764032497914287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56129844227176021665276191 84194766340764032497914287)
    ·
      refine ⟨126292149511146048746871431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84194766340764032497914287 126292149511146048746871431)
      ·
        refine ⟨189438224266719073120307147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126292149511146048746871431 189438224266719073120307147)
        ·
          refine ⟨284157336400078609680460721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189438224266719073120307147 284157336400078609680460721)
          ·
            refine ⟨213118002300058957260345541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 284157336400078609680460721 213118002300058957260345541)
            ·
              refine ⟨39959625431261054486314789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 213118002300058957260345541 39959625431261054486314789)
              ·
                refine ⟨7492429768361447716184023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39959625431261054486314789 7492429768361447716184023)
                ·
                  refine ⟨11238644652542171574276035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7492429768361447716184023 11238644652542171574276035)
                  ·
                    refine ⟨16857966978813257361414053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11238644652542171574276035 16857966978813257361414053)
                    ·
                      refine ⟨3160868808527485755265135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16857966978813257361414053 3160868808527485755265135)
                      ·
                        rfl

theorem cell23_6155770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 4, 1, 1, 4].length) (baseStart_6155770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6155770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6155770 prefixEnd_6155770 := by exact prefixLift 6155770
  have htrace : WordTrace (prefixWord ++ tailWord_6155770) baseStart_6155770 baseEnd_6155770 := by
    simpa [prefixWord, tailWord_6155770, baseEnd_6155770] using wordTrace_append hprefix tailTrace_6155770
  have hstable : (prefixWord ++ tailWord_6155770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6155770).length < 2 ^ (prefixWord ++ tailWord_6155770).sum := by decide
  have hdescent : baseEnd_6155770 < baseStart_6155770 := by decide
  rcases family_descends (prefixWord ++ tailWord_6155770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6155787 : List Nat := [1, 1, 1, 1, 8, 1, 1, 3, 1, 1, 4]
def baseStart_6155787 : Nat := 118140960795 + 6155787 * 2 ^ 59
def prefixEnd_6155787 : Nat := 4983230072969 + 3 ^ 40 * 6155787 * 2
def baseEnd_6155787 : Nat := 3160877537698612188752557

theorem tailTrace_6155787 : CollatzResearch.WordTrace tailWord_6155787 prefixEnd_6155787 3160877537698612188752557 := by
  unfold tailWord_6155787
  simp only [CollatzResearch.WordTrace]
  refine ⟨224519996949642498564473615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149679997966428332376315743 224519996949642498564473615)
  ·
    refine ⟨336779995424463747846710423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224519996949642498564473615 336779995424463747846710423)
    ·
      refine ⟨505169993136695621770065635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 336779995424463747846710423 505169993136695621770065635)
      ·
        refine ⟨757754989705043432655098453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 505169993136695621770065635 757754989705043432655098453)
        ·
          refine ⟨8879941285605977726426935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 757754989705043432655098453 8879941285605977726426935)
          ·
            refine ⟨13319911928408966589640403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8879941285605977726426935 13319911928408966589640403)
            ·
              refine ⟨19979867892613449884460605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13319911928408966589640403 19979867892613449884460605)
              ·
                refine ⟨7492450459730043706672727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19979867892613449884460605 7492450459730043706672727)
                ·
                  refine ⟨11238675689595065560009091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7492450459730043706672727 11238675689595065560009091)
                  ·
                    refine ⟨16858013534392598340013637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11238675689595065560009091 16858013534392598340013637)
                    ·
                      refine ⟨3160877537698612188752557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16858013534392598340013637 3160877537698612188752557)
                      ·
                        rfl

theorem cell23_6155787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 3, 1, 1, 4].length) (baseStart_6155787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6155787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6155787 prefixEnd_6155787 := by exact prefixLift 6155787
  have htrace : WordTrace (prefixWord ++ tailWord_6155787) baseStart_6155787 baseEnd_6155787 := by
    simpa [prefixWord, tailWord_6155787, baseEnd_6155787] using wordTrace_append hprefix tailTrace_6155787
  have hstable : (prefixWord ++ tailWord_6155787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6155787).length < 2 ^ (prefixWord ++ tailWord_6155787).sum := by decide
  have hdescent : baseEnd_6155787 < baseStart_6155787 := by decide
  rcases family_descends (prefixWord ++ tailWord_6155787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6155797 : List Nat := [1, 3, 2, 1, 3, 2, 3, 2, 2, 4]
def baseStart_6155797 : Nat := 118140960795 + 6155797 * 2 ^ 59
def prefixEnd_6155797 : Nat := 4983230072969 + 3 ^ 40 * 6155797 * 2
def baseEnd_6155797 : Nat := 1053627557501719049875837

theorem tailTrace_6155797 : CollatzResearch.WordTrace tailWord_6155797 prefixEnd_6155797 1053627557501719049875837 := by
  unfold tailWord_6155797
  simp only [CollatzResearch.WordTrace]
  refine ⟨224520361679606270272337645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149680241119737513514891763 224520361679606270272337645)
  ·
    refine ⟨84195135629852351352126617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 224520361679606270272337645 84195135629852351352126617)
    ·
      refine ⟨63146351722389263514094963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84195135629852351352126617 63146351722389263514094963)
      ·
        refine ⟨94719527583583895271142445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63146351722389263514094963 94719527583583895271142445)
        ·
          refine ⟨35519822843843960726678417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94719527583583895271142445 35519822843843960726678417)
          ·
            refine ⟨26639867132882970545008813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35519822843843960726678417 26639867132882970545008813)
            ·
              refine ⟨9989950174831113954378305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26639867132882970545008813 9989950174831113954378305)
              ·
                refine ⟨7492462631123335465783729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9989950174831113954378305 7492462631123335465783729)
                ·
                  refine ⟨5619346973342501599337797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7492462631123335465783729 5619346973342501599337797)
                  ·
                    refine ⟨1053627557501719049875837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5619346973342501599337797 1053627557501719049875837)
                    ·
                      rfl

theorem cell23_6155797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3, 2, 2, 4].length) (baseStart_6155797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6155797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6155797 prefixEnd_6155797 := by exact prefixLift 6155797
  have htrace : WordTrace (prefixWord ++ tailWord_6155797) baseStart_6155797 baseEnd_6155797 := by
    simpa [prefixWord, tailWord_6155797, baseEnd_6155797] using wordTrace_append hprefix tailTrace_6155797
  have hstable : (prefixWord ++ tailWord_6155797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6155797).length < 2 ^ (prefixWord ++ tailWord_6155797).sum := by decide
  have hdescent : baseEnd_6155797 < baseStart_6155797 := by decide
  rcases family_descends (prefixWord ++ tailWord_6155797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6155803 : List Nat := [1, 1, 1, 1, 1, 1, 3, 1, 1, 9, 3]
def baseStart_6155803 : Nat := 118140960795 + 6155803 * 2 ^ 59
def prefixEnd_6155803 : Nat := 4983230072969 + 3 ^ 40 * 6155803 * 2
def baseEnd_6155803 : Nat := 3160885753389084126152483

theorem tailTrace_6155803 : CollatzResearch.WordTrace tailWord_6155803 prefixEnd_6155803 3160885753389084126152483 := by
  unfold tailWord_6155803
  simp only [CollatzResearch.WordTrace]
  refine ⟨224520580517584533297056063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149680387011723022198037375 224520580517584533297056063)
  ·
    refine ⟨336780870776376799945584095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224520580517584533297056063 336780870776376799945584095)
    ·
      refine ⟨505171306164565199918376143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 336780870776376799945584095 505171306164565199918376143)
      ·
        refine ⟨757756959246847799877564215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 505171306164565199918376143 757756959246847799877564215)
        ·
          refine ⟨1136635438870271699816346323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 757756959246847799877564215 1136635438870271699816346323)
          ·
            refine ⟨1704953158305407549724519485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1136635438870271699816346323 1704953158305407549724519485)
            ·
              refine ⟨639357434364527831146694807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1704953158305407549724519485 639357434364527831146694807)
              ·
                refine ⟨959036151546791746720042211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 639357434364527831146694807 959036151546791746720042211)
                ·
                  refine ⟨1438554227320187620080063317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 959036151546791746720042211 1438554227320187620080063317)
                  ·
                    refine ⟨8429028675704224336406621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 1438554227320187620080063317 8429028675704224336406621)
                    ·
                      refine ⟨3160885753389084126152483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8429028675704224336406621 3160885753389084126152483)
                      ·
                        rfl

theorem cell23_6155803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 9, 3].length) (baseStart_6155803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6155803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6155803 prefixEnd_6155803 := by exact prefixLift 6155803
  have htrace : WordTrace (prefixWord ++ tailWord_6155803) baseStart_6155803 baseEnd_6155803 := by
    simpa [prefixWord, tailWord_6155803, baseEnd_6155803] using wordTrace_append hprefix tailTrace_6155803
  have hstable : (prefixWord ++ tailWord_6155803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6155803).length < 2 ^ (prefixWord ++ tailWord_6155803).sum := by decide
  have hdescent : baseEnd_6155803 < baseStart_6155803 := by decide
  rcases family_descends (prefixWord ++ tailWord_6155803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6155804 : List Nat := [2, 2, 3, 1, 2, 1, 4, 1, 3, 2, 2]
def baseStart_6155804 : Nat := 118140960795 + 6155804 * 2 ^ 59
def prefixEnd_6155804 : Nat := 4983230072969 + 3 ^ 40 * 6155804 * 2
def baseEnd_6155804 : Nat := 3160886266869738622239979

theorem tailTrace_6155804 : CollatzResearch.WordTrace tailWord_6155804 prefixEnd_6155804 3160886266869738622239979 := by
  unfold tailWord_6155804
  simp only [CollatzResearch.WordTrace]
  refine ⟨112260308495290455233921233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149680411327053940311894977 112260308495290455233921233)
  ·
    refine ⟨84195231371467841425440925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112260308495290455233921233 84195231371467841425440925)
    ·
      refine ⟨31573211764300440534540347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84195231371467841425440925 31573211764300440534540347)
      ·
        refine ⟨47359817646450660801810521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31573211764300440534540347 47359817646450660801810521)
        ·
          refine ⟨35519863234837995601357891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47359817646450660801810521 35519863234837995601357891)
          ·
            refine ⟨53279794852256993402036837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35519863234837995601357891 53279794852256993402036837)
            ·
              refine ⟨9989961534798186262881907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53279794852256993402036837 9989961534798186262881907)
              ·
                refine ⟨14984942302197279394322861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9989961534798186262881907 14984942302197279394322861)
                ·
                  refine ⟨5619353363323979772871073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14984942302197279394322861 5619353363323979772871073)
                  ·
                    refine ⟨4214515022492984829653305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5619353363323979772871073 4214515022492984829653305)
                    ·
                      refine ⟨3160886266869738622239979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4214515022492984829653305 3160886266869738622239979)
                      ·
                        rfl

theorem cell23_6155804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4, 1, 3, 2, 2].length) (baseStart_6155804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6155804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6155804 prefixEnd_6155804 := by exact prefixLift 6155804
  have htrace : WordTrace (prefixWord ++ tailWord_6155804) baseStart_6155804 baseEnd_6155804 := by
    simpa [prefixWord, tailWord_6155804, baseEnd_6155804] using wordTrace_append hprefix tailTrace_6155804
  have hstable : (prefixWord ++ tailWord_6155804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6155804).length < 2 ^ (prefixWord ++ tailWord_6155804).sum := by decide
  have hdescent : baseEnd_6155804 < baseStart_6155804 := by decide
  rcases family_descends (prefixWord ++ tailWord_6155804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6155843 : List Nat := [1, 1, 1, 3, 1, 2, 1, 1, 3, 5, 4]
def baseStart_6155843 : Nat := 118140960795 + 6155843 * 2 ^ 59
def prefixEnd_6155843 : Nat := 4983230072969 + 3 ^ 40 * 6155843 * 2
def baseEnd_6155843 : Nat := 3160906292615263969652299

theorem tailTrace_6155843 : CollatzResearch.WordTrace tailWord_6155843 prefixEnd_6155843 3160906292615263969652299 := by
  unfold tailWord_6155843
  simp only [CollatzResearch.WordTrace]
  refine ⟨224522039437439620128512183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149681359624959746752341455 224522039437439620128512183)
  ·
    refine ⟨336783059156159430192768275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224522039437439620128512183 336783059156159430192768275)
    ·
      refine ⟨505174588734239145289152413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 336783059156159430192768275 505174588734239145289152413)
      ·
        refine ⟨189440470775339679483432155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 505174588734239145289152413 189440470775339679483432155)
        ·
          refine ⟨284160706163009519225148233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189440470775339679483432155 284160706163009519225148233)
          ·
            refine ⟨213120529622257139418861175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 284160706163009519225148233 213120529622257139418861175)
            ·
              refine ⟨319680794433385709128291763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 213120529622257139418861175 319680794433385709128291763)
              ·
                refine ⟨479521191650078563692437645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 319680794433385709128291763 479521191650078563692437645)
                ·
                  refine ⟨179820446868779461384664117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 479521191650078563692437645 179820446868779461384664117)
                  ·
                    refine ⟨16858166893948074504812261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 179820446868779461384664117 16858166893948074504812261)
                    ·
                      refine ⟨3160906292615263969652299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16858166893948074504812261 3160906292615263969652299)
                      ·
                        rfl

theorem cell23_6155843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 5, 4].length) (baseStart_6155843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6155843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6155843 prefixEnd_6155843 := by exact prefixLift 6155843
  have htrace : WordTrace (prefixWord ++ tailWord_6155843) baseStart_6155843 baseEnd_6155843 := by
    simpa [prefixWord, tailWord_6155843, baseEnd_6155843] using wordTrace_append hprefix tailTrace_6155843
  have hstable : (prefixWord ++ tailWord_6155843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6155843).length < 2 ^ (prefixWord ++ tailWord_6155843).sum := by decide
  have hdescent : baseEnd_6155843 < baseStart_6155843 := by decide
  rcases family_descends (prefixWord ++ tailWord_6155843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6155860 : List Nat := [2, 4, 1, 1, 1, 2, 2, 1, 2, 3, 4]
def baseStart_6155860 : Nat := 118140960795 + 6155860 * 2 ^ 59
def prefixEnd_6155860 : Nat := 4983230072969 + 3 ^ 40 * 6155860 * 2
def baseEnd_6155860 : Nat := 3160915021786390403139721

theorem tailTrace_6155860 : CollatzResearch.WordTrace tailWord_6155860 prefixEnd_6155860 3160915021786390403139721 := by
  unfold tailWord_6155860
  simp only [CollatzResearch.WordTrace]
  refine ⟨112261329739189016015940517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149681772985585354687920689 112261329739189016015940517)
  ·
    refine ⟨21048999326097940502988847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112261329739189016015940517 21048999326097940502988847)
    ·
      refine ⟨31573498989146910754483271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21048999326097940502988847 31573498989146910754483271)
      ·
        refine ⟨47360248483720366131724907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31573498989146910754483271 47360248483720366131724907)
        ·
          refine ⟨71040372725580549197587361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47360248483720366131724907 71040372725580549197587361)
          ·
            refine ⟨53280279544185411898190521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71040372725580549197587361 53280279544185411898190521)
            ·
              refine ⟨39960209658139058923642891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53280279544185411898190521 39960209658139058923642891)
              ·
                refine ⟨59940314487208588385464337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39960209658139058923642891 59940314487208588385464337)
                ·
                  refine ⟨44955235865406441289098253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59940314487208588385464337 44955235865406441289098253)
                  ·
                    refine ⟨16858213449527415483411845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44955235865406441289098253 16858213449527415483411845)
                    ·
                      refine ⟨3160915021786390403139721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16858213449527415483411845 3160915021786390403139721)
                      ·
                        rfl

theorem cell23_6155860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 1, 2, 3, 4].length) (baseStart_6155860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6155860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6155860 prefixEnd_6155860 := by exact prefixLift 6155860
  have htrace : WordTrace (prefixWord ++ tailWord_6155860) baseStart_6155860 baseEnd_6155860 := by
    simpa [prefixWord, tailWord_6155860, baseEnd_6155860] using wordTrace_append hprefix tailTrace_6155860
  have hstable : (prefixWord ++ tailWord_6155860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6155860).length < 2 ^ (prefixWord ++ tailWord_6155860).sum := by decide
  have hdescent : baseEnd_6155860 < baseStart_6155860 := by decide
  rcases family_descends (prefixWord ++ tailWord_6155860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6155894 : List Nat := [5, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2]
def baseStart_6155894 : Nat := 118140960795 + 6155894 * 2 ^ 59
def prefixEnd_6155894 : Nat := 4983230072969 + 3 ^ 40 * 6155894 * 2
def baseEnd_6155894 : Nat := 3160932480128643270114565

theorem tailTrace_6155894 : CollatzResearch.WordTrace tailWord_6155894 prefixEnd_6155894 3160932480128643270114565 := by
  unfold tailWord_6155894
  simp only [CollatzResearch.WordTrace]
  refine ⟨14032743722515928489913671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 149682599706836570559079157 14032743722515928489913671)
  ·
    refine ⟨21049115583773892734870507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14032743722515928489913671 21049115583773892734870507)
    ·
      refine ⟨31573673375660839102305761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21049115583773892734870507 31573673375660839102305761)
      ·
        refine ⟨23680255031745629326729321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31573673375660839102305761 23680255031745629326729321)
        ·
          refine ⟨17760191273809221995046991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23680255031745629326729321 17760191273809221995046991)
          ·
            refine ⟨26640286910713832992570487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17760191273809221995046991 26640286910713832992570487)
            ·
              refine ⟨39960430366070749488855731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26640286910713832992570487 39960430366070749488855731)
              ·
                refine ⟨59940645549106124233283597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39960430366070749488855731 59940645549106124233283597)
                ·
                  refine ⟨22477742080914796587481349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59940645549106124233283597 22477742080914796587481349)
                  ·
                    refine ⟨4214576640171524360152753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22477742080914796587481349 4214576640171524360152753)
                    ·
                      refine ⟨3160932480128643270114565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4214576640171524360152753 3160932480128643270114565)
                      ·
                        rfl

theorem cell23_6155894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2].length) (baseStart_6155894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6155894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6155894 prefixEnd_6155894 := by exact prefixLift 6155894
  have htrace : WordTrace (prefixWord ++ tailWord_6155894) baseStart_6155894 baseEnd_6155894 := by
    simpa [prefixWord, tailWord_6155894, baseEnd_6155894] using wordTrace_append hprefix tailTrace_6155894
  have hstable : (prefixWord ++ tailWord_6155894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6155894).length < 2 ^ (prefixWord ++ tailWord_6155894).sum := by decide
  have hdescent : baseEnd_6155894 < baseStart_6155894 := by decide
  rcases family_descends (prefixWord ++ tailWord_6155894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6155903 : List Nat := [1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 8]
def baseStart_6155903 : Nat := 118140960795 + 6155903 * 2 ^ 59
def prefixEnd_6155903 : Nat := 4983230072969 + 3 ^ 40 * 6155903 * 2
def baseEnd_6155903 : Nat := 3160937101454533734902023

theorem tailTrace_6155903 : CollatzResearch.WordTrace tailWord_6155903 prefixEnd_6155903 3160937101454533734902023 := by
  unfold tailWord_6155903
  simp only [CollatzResearch.WordTrace]
  refine ⟨224524227817222250375696363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149682818544814833583797575 224524227817222250375696363)
  ·
    refine ⟨336786341725833375563544545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224524227817222250375696363 336786341725833375563544545)
    ·
      refine ⟨252589756294375031672658409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 336786341725833375563544545 252589756294375031672658409)
      ·
        refine ⟨189442317220781273754493807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 252589756294375031672658409 189442317220781273754493807)
        ·
          refine ⟨284163475831171910631740711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189442317220781273754493807 284163475831171910631740711)
          ·
            refine ⟨426245213746757865947611067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 284163475831171910631740711 426245213746757865947611067)
            ·
              refine ⟨639367820620136798921416601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 426245213746757865947611067 639367820620136798921416601)
              ·
                refine ⟨479525865465102599191062451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 639367820620136798921416601 479525865465102599191062451)
                ·
                  refine ⟨719288798197653898786593677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 479525865465102599191062451 719288798197653898786593677)
                  ·
                    refine ⟨269733299324120212044972629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 719288798197653898786593677 269733299324120212044972629)
                    ·
                      refine ⟨3160937101454533734902023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 269733299324120212044972629 3160937101454533734902023)
                      ·
                        rfl

theorem cell23_6155903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 8].length) (baseStart_6155903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6155903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6155903 prefixEnd_6155903 := by exact prefixLift 6155903
  have htrace : WordTrace (prefixWord ++ tailWord_6155903) baseStart_6155903 baseEnd_6155903 := by
    simpa [prefixWord, tailWord_6155903, baseEnd_6155903] using wordTrace_append hprefix tailTrace_6155903
  have hstable : (prefixWord ++ tailWord_6155903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6155903).length < 2 ^ (prefixWord ++ tailWord_6155903).sum := by decide
  have hdescent : baseEnd_6155903 < baseStart_6155903 := by decide
  rcases family_descends (prefixWord ++ tailWord_6155903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6155911 : List Nat := [1, 1, 4, 2, 1, 4, 2, 2, 2, 2, 2]
def baseStart_6155911 : Nat := 118140960795 + 6155911 * 2 ^ 59
def prefixEnd_6155911 : Nat := 4983230072969 + 3 ^ 40 * 6155911 * 2
def baseEnd_6155911 : Nat := 3160941209299769703601987

theorem tailTrace_6155911 : CollatzResearch.WordTrace tailWord_6155911 prefixEnd_6155911 3160941209299769703601987 := by
  unfold tailWord_6155911
  simp only [CollatzResearch.WordTrace]
  refine ⟨224524519601193267741987587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149683013067462178494658391 224524519601193267741987587)
  ·
    refine ⟨336786779401789901612981381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224524519601193267741987587 336786779401789901612981381)
    ·
      refine ⟨63147521137835606552434009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 336786779401789901612981381 63147521137835606552434009)
      ·
        refine ⟨47360640853376704914325507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63147521137835606552434009 47360640853376704914325507)
        ·
          refine ⟨71040961280065057371488261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47360640853376704914325507 71040961280065057371488261)
          ·
            refine ⟨13320180240012198257154049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71040961280065057371488261 13320180240012198257154049)
            ·
              refine ⟨9990135180009148692865537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13320180240012198257154049 9990135180009148692865537)
              ·
                refine ⟨7492601385006861519649153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9990135180009148692865537 7492601385006861519649153)
                ·
                  refine ⟨5619451038755146139736865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7492601385006861519649153 5619451038755146139736865)
                  ·
                    refine ⟨4214588279066359604802649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5619451038755146139736865 4214588279066359604802649)
                    ·
                      refine ⟨3160941209299769703601987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4214588279066359604802649 3160941209299769703601987)
                      ·
                        rfl

theorem cell23_6155911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2, 2, 2, 2, 2].length) (baseStart_6155911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6155911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6155911 prefixEnd_6155911 := by exact prefixLift 6155911
  have htrace : WordTrace (prefixWord ++ tailWord_6155911) baseStart_6155911 baseEnd_6155911 := by
    simpa [prefixWord, tailWord_6155911, baseEnd_6155911] using wordTrace_append hprefix tailTrace_6155911
  have hstable : (prefixWord ++ tailWord_6155911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6155911).length < 2 ^ (prefixWord ++ tailWord_6155911).sum := by decide
  have hdescent : baseEnd_6155911 < baseStart_6155911 := by decide
  rcases family_descends (prefixWord ++ tailWord_6155911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6155924 : List Nat := [2, 4, 2, 2, 2, 1, 1, 1, 2, 2, 4]
def baseStart_6155924 : Nat := 118140960795 + 6155924 * 2 ^ 59
def prefixEnd_6155924 : Nat := 4983230072969 + 3 ^ 40 * 6155924 * 2
def baseEnd_6155924 : Nat := 3160947884548278152739427

theorem tailTrace_6155924 : CollatzResearch.WordTrace tailWord_6155924 prefixEnd_6155924 3160947884548278152739427 := by
  unfold tailWord_6155924
  simp only [CollatzResearch.WordTrace]
  refine ⟨112262496875073085481105413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149683329166764113974807217 112262496875073085481105413)
  ·
    refine ⟨21049218164076203527707265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112262496875073085481105413 21049218164076203527707265)
    ·
      refine ⟨15786913623057152645780449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21049218164076203527707265 15786913623057152645780449)
      ·
        refine ⟨11840185217292864484335337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15786913623057152645780449 11840185217292864484335337)
        ·
          refine ⟨8880138912969648363251503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11840185217292864484335337 8880138912969648363251503)
          ·
            refine ⟨13320208369454472544877255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8880138912969648363251503 13320208369454472544877255)
            ·
              refine ⟨19980312554181708817315883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13320208369454472544877255 19980312554181708817315883)
              ·
                refine ⟨29970468831272563225973825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19980312554181708817315883 29970468831272563225973825)
                ·
                  refine ⟨22477851623454422419480369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29970468831272563225973825 22477851623454422419480369)
                  ·
                    refine ⟨16858388717590816814610277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22477851623454422419480369 16858388717590816814610277)
                    ·
                      refine ⟨3160947884548278152739427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16858388717590816814610277 3160947884548278152739427)
                      ·
                        rfl

theorem cell23_6155924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_6155924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6155924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6155924 prefixEnd_6155924 := by exact prefixLift 6155924
  have htrace : WordTrace (prefixWord ++ tailWord_6155924) baseStart_6155924 baseEnd_6155924 := by
    simpa [prefixWord, tailWord_6155924, baseEnd_6155924] using wordTrace_append hprefix tailTrace_6155924
  have hstable : (prefixWord ++ tailWord_6155924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6155924).length < 2 ^ (prefixWord ++ tailWord_6155924).sum := by decide
  have hdescent : baseEnd_6155924 < baseStart_6155924 := by decide
  rcases family_descends (prefixWord ++ tailWord_6155924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6155927 : List Nat := [1, 1, 3, 3, 2, 3, 1, 1, 2, 3, 3]
def baseStart_6155927 : Nat := 118140960795 + 6155927 * 2 ^ 59
def prefixEnd_6155927 : Nat := 4983230072969 + 3 ^ 40 * 6155927 * 2
def baseEnd_6155927 : Nat := 3160949424990241641001913

theorem tailTrace_6155927 : CollatzResearch.WordTrace tailWord_6155927 prefixEnd_6155927 3160949424990241641001913 := by
  unfold tailWord_6155927
  simp only [CollatzResearch.WordTrace]
  refine ⟨224525103169135302474570035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149683402112756868316380023 224525103169135302474570035)
  ·
    refine ⟨336787654753702953711855053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224525103169135302474570035 336787654753702953711855053)
    ·
      refine ⟨126295370532638607641945645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 336787654753702953711855053 126295370532638607641945645)
      ·
        refine ⟨47360763949739477865729617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126295370532638607641945645 47360763949739477865729617)
        ·
          refine ⟨35520572962304608399297213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47360763949739477865729617 35520572962304608399297213)
          ·
            refine ⟨13320214860864228149736455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35520572962304608399297213 13320214860864228149736455)
            ·
              refine ⟨19980322291296342224604683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13320214860864228149736455 19980322291296342224604683)
              ·
                refine ⟨29970483436944513336907025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19980322291296342224604683 29970483436944513336907025)
                ·
                  refine ⟨22477862577708385002680269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29970483436944513336907025 22477862577708385002680269)
                  ·
                    refine ⟨8429198466640644376005101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22477862577708385002680269 8429198466640644376005101)
                    ·
                      refine ⟨3160949424990241641001913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8429198466640644376005101 3160949424990241641001913)
                      ·
                        rfl

theorem cell23_6155927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 1, 2, 3, 3].length) (baseStart_6155927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6155927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6155927 prefixEnd_6155927 := by exact prefixLift 6155927
  have htrace : WordTrace (prefixWord ++ tailWord_6155927) baseStart_6155927 baseEnd_6155927 := by
    simpa [prefixWord, tailWord_6155927, baseEnd_6155927] using wordTrace_append hprefix tailTrace_6155927
  have hstable : (prefixWord ++ tailWord_6155927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6155927).length < 2 ^ (prefixWord ++ tailWord_6155927).sum := by decide
  have hdescent : baseEnd_6155927 < baseStart_6155927 := by decide
  rcases family_descends (prefixWord ++ tailWord_6155927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6155967 : List Nat := [1, 1, 2, 2, 2, 3, 1, 1, 4, 4, 2]
def baseStart_6155967 : Nat := 118140960795 + 6155967 * 2 ^ 59
def prefixEnd_6155967 : Nat := 4983230072969 + 3 ^ 40 * 6155967 * 2
def baseEnd_6155967 : Nat := 3160969964216421484501729

theorem tailTrace_6155967 : CollatzResearch.WordTrace tailWord_6155967 prefixEnd_6155967 3160969964216421484501729 := by
  unfold tailWord_6155967
  simp only [CollatzResearch.WordTrace]
  refine ⟨224526562088990389306026155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149684374725993592870684103 224526562088990389306026155)
  ·
    refine ⟨336789843133485583959039233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224526562088990389306026155 336789843133485583959039233)
    ·
      refine ⟨252592382350114187969279425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 336789843133485583959039233 252592382350114187969279425)
      ·
        refine ⟨189444286762585640976959569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 252592382350114187969279425 189444286762585640976959569)
        ·
          refine ⟨142083215071939230732719677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189444286762585640976959569 142083215071939230732719677)
          ·
            refine ⟨53281205651977211524769879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 142083215071939230732719677 53281205651977211524769879)
            ·
              refine ⟨79921808477965817287154819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53281205651977211524769879 79921808477965817287154819)
              ·
                refine ⟨119882712716948725930732229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79921808477965817287154819 119882712716948725930732229)
                ·
                  refine ⟨22478008634427886112012293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 119882712716948725930732229 22478008634427886112012293)
                  ·
                    refine ⟨4214626618955228646002305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22478008634427886112012293 4214626618955228646002305)
                    ·
                      refine ⟨3160969964216421484501729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4214626618955228646002305 3160969964216421484501729)
                      ·
                        rfl

theorem cell23_6155967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 4, 4, 2].length) (baseStart_6155967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6155967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6155967 prefixEnd_6155967 := by exact prefixLift 6155967
  have htrace : WordTrace (prefixWord ++ tailWord_6155967) baseStart_6155967 baseEnd_6155967 := by
    simpa [prefixWord, tailWord_6155967, baseEnd_6155967] using wordTrace_append hprefix tailTrace_6155967
  have hstable : (prefixWord ++ tailWord_6155967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6155967).length < 2 ^ (prefixWord ++ tailWord_6155967).sum := by decide
  have hdescent : baseEnd_6155967 < baseStart_6155967 := by decide
  rcases family_descends (prefixWord ++ tailWord_6155967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6156027 : List Nat := [1, 1, 1, 1, 1, 3, 1, 4, 3, 5, 2]
def baseStart_6156027 : Nat := 118140960795 + 6156027 * 2 ^ 59
def prefixEnd_6156027 : Nat := 4983230072969 + 3 ^ 40 * 6156027 * 2
def baseEnd_6156027 : Nat := 3161000773055691249751453

theorem tailTrace_6156027 : CollatzResearch.WordTrace tailWord_6156027 prefixEnd_6156027 3161000773055691249751453 := by
  unfold tailWord_6156027
  simp only [CollatzResearch.WordTrace]
  refine ⟨224528750468773019553210335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149685833645848679702140223 224528750468773019553210335)
  ·
    refine ⟨336793125703159529329815503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224528750468773019553210335 336793125703159529329815503)
    ·
      refine ⟨505189688554739293994723255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 336793125703159529329815503 505189688554739293994723255)
      ·
        refine ⟨757784532832108940992084883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 505189688554739293994723255 757784532832108940992084883)
        ·
          refine ⟨1136676799248163411488127325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 757784532832108940992084883 1136676799248163411488127325)
          ·
            refine ⟨426253799718061279308047747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1136676799248163411488127325 426253799718061279308047747)
            ·
              refine ⟨639380699577091918962071621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 426253799718061279308047747 639380699577091918962071621)
              ·
                refine ⟨119883881170704734805388429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 639380699577091918962071621 119883881170704734805388429)
                ·
                  refine ⟨44956455439014275552020661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 119883881170704734805388429 44956455439014275552020661)
                  ·
                    refine ⟨4214667697407588333001937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44956455439014275552020661 4214667697407588333001937)
                    ·
                      refine ⟨3161000773055691249751453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4214667697407588333001937 3161000773055691249751453)
                      ·
                        rfl

theorem cell23_6156027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 3, 5, 2].length) (baseStart_6156027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6156027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6156027 prefixEnd_6156027 := by exact prefixLift 6156027
  have htrace : WordTrace (prefixWord ++ tailWord_6156027) baseStart_6156027 baseEnd_6156027 := by
    simpa [prefixWord, tailWord_6156027, baseEnd_6156027] using wordTrace_append hprefix tailTrace_6156027
  have hstable : (prefixWord ++ tailWord_6156027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6156027).length < 2 ^ (prefixWord ++ tailWord_6156027).sum := by decide
  have hdescent : baseEnd_6156027 < baseStart_6156027 := by decide
  rcases family_descends (prefixWord ++ tailWord_6156027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6156067 : List Nat := [1, 1, 1, 4, 2, 1, 2, 1, 6, 4]
def baseStart_6156067 : Nat := 118140960795 + 6156067 * 2 ^ 59
def prefixEnd_6156067 : Nat := 4983230072969 + 3 ^ 40 * 6156067 * 2
def baseEnd_6156067 : Nat := 1053673770760623697750423

theorem tailTrace_6156067 : CollatzResearch.WordTrace tailWord_6156067 prefixEnd_6156067 1053673770760623697750423 := by
  unfold tailWord_6156067
  simp only [CollatzResearch.WordTrace]
  refine ⟨224530209388628106384666455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149686806259085404256444303 224530209388628106384666455)
  ·
    refine ⟨336795314082942159576999683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224530209388628106384666455 336795314082942159576999683)
    ·
      refine ⟨505192971124413239365499525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 336795314082942159576999683 505192971124413239365499525)
      ·
        refine ⟨94723682085827482381031161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 505192971124413239365499525 94723682085827482381031161)
        ·
          refine ⟨71042761564370611785773371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94723682085827482381031161 71042761564370611785773371)
          ·
            refine ⟨106564142346555917678660057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71042761564370611785773371 106564142346555917678660057)
            ·
              refine ⟨79923106759916938258995043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106564142346555917678660057 79923106759916938258995043)
              ·
                refine ⟨119884660139875407388492565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79923106759916938258995043 119884660139875407388492565)
                ·
                  refine ⟨5619593444056659721335589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 119884660139875407388492565 5619593444056659721335589)
                  ·
                    refine ⟨1053673770760623697750423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5619593444056659721335589 1053673770760623697750423)
                    ·
                      rfl

theorem cell23_6156067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 6, 4].length) (baseStart_6156067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6156067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6156067 prefixEnd_6156067 := by exact prefixLift 6156067
  have htrace : WordTrace (prefixWord ++ tailWord_6156067) baseStart_6156067 baseEnd_6156067 := by
    simpa [prefixWord, tailWord_6156067, baseEnd_6156067] using wordTrace_append hprefix tailTrace_6156067
  have hstable : (prefixWord ++ tailWord_6156067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6156067).length < 2 ^ (prefixWord ++ tailWord_6156067).sum := by decide
  have hdescent : baseEnd_6156067 < baseStart_6156067 := by decide
  rcases family_descends (prefixWord ++ tailWord_6156067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6156104 : List Nat := [2, 1, 3, 1, 1, 5, 2, 1, 1, 2, 4]
def baseStart_6156104 : Nat := 118140960795 + 6156104 * 2 ^ 59
def prefixEnd_6156104 : Nat := 4983230072969 + 3 ^ 40 * 6156104 * 2
def baseEnd_6156104 : Nat := 3161040311066087448488599

theorem tailTrace_6156104 : CollatzResearch.WordTrace tailWord_6156104 prefixEnd_6156104 3161040311066087448488599 := by
  unfold tailWord_6156104
  simp only [CollatzResearch.WordTrace]
  refine ⟨112265779444747030851881683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149687705926329374469175577 112265779444747030851881683)
  ·
    refine ⟨168398669167120546277822525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112265779444747030851881683 168398669167120546277822525)
    ·
      refine ⟨63149500937670204854183447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168398669167120546277822525 63149500937670204854183447)
      ·
        refine ⟨94724251406505307281275171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63149500937670204854183447 94724251406505307281275171)
        ·
          refine ⟨142086377109757960921912757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94724251406505307281275171 142086377109757960921912757)
          ·
            refine ⟨13320597854039808836429321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 142086377109757960921912757 13320597854039808836429321)
            ·
              refine ⟨9990448390529856627321991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13320597854039808836429321 9990448390529856627321991)
              ·
                refine ⟨14985672585794784940982987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9990448390529856627321991 14985672585794784940982987)
                ·
                  refine ⟨22478508878692177411474481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14985672585794784940982987 22478508878692177411474481)
                  ·
                    refine ⟨16858881659019133058605861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22478508878692177411474481 16858881659019133058605861)
                    ·
                      refine ⟨3161040311066087448488599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16858881659019133058605861 3161040311066087448488599)
                      ·
                        rfl

theorem cell23_6156104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2, 1, 1, 2, 4].length) (baseStart_6156104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6156104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6156104 prefixEnd_6156104 := by exact prefixLift 6156104
  have htrace : WordTrace (prefixWord ++ tailWord_6156104) baseStart_6156104 baseEnd_6156104 := by
    simpa [prefixWord, tailWord_6156104, baseEnd_6156104] using wordTrace_append hprefix tailTrace_6156104
  have hstable : (prefixWord ++ tailWord_6156104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6156104).length < 2 ^ (prefixWord ++ tailWord_6156104).sum := by decide
  have hdescent : baseEnd_6156104 < baseStart_6156104 := by decide
  rcases family_descends (prefixWord ++ tailWord_6156104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6156108 : List Nat := [2, 2, 1, 3, 4, 1, 1, 2, 3, 2, 2]
def baseStart_6156108 : Nat := 118140960795 + 6156108 * 2 ^ 59
def prefixEnd_6156108 : Nat := 4983230072969 + 3 ^ 40 * 6156108 * 2
def baseEnd_6156108 : Nat := 3161042364988705432838581

theorem tailTrace_6156108 : CollatzResearch.WordTrace tailWord_6156108 prefixEnd_6156108 3161042364988705432838581 := by
  unfold tailWord_6156108
  simp only [CollatzResearch.WordTrace]
  refine ⟨112265852390739785193454489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149687803187653046924605985 112265852390739785193454489)
  ·
    refine ⟨84199389293054838895090867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112265852390739785193454489 84199389293054838895090867)
    ·
      refine ⟨126299083939582258342636301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84199389293054838895090867 126299083939582258342636301)
      ·
        refine ⟨47362156477343346878488613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126299083939582258342636301 47362156477343346878488613)
        ·
          refine ⟨8880404339501877539716615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47362156477343346878488613 8880404339501877539716615)
          ·
            refine ⟨13320606509252816309574923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8880404339501877539716615 13320606509252816309574923)
            ·
              refine ⟨19980909763879224464362385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13320606509252816309574923 19980909763879224464362385)
              ·
                refine ⟨14985682322909418348271789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19980909763879224464362385 14985682322909418348271789)
                ·
                  refine ⟨5619630871091031880601921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14985682322909418348271789 5619630871091031880601921)
                  ·
                    refine ⟨4214723153318273910451441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5619630871091031880601921 4214723153318273910451441)
                    ·
                      refine ⟨3161042364988705432838581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4214723153318273910451441 3161042364988705432838581)
                      ·
                        rfl

theorem cell23_6156108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 2, 3, 2, 2].length) (baseStart_6156108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6156108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6156108 prefixEnd_6156108 := by exact prefixLift 6156108
  have htrace : WordTrace (prefixWord ++ tailWord_6156108) baseStart_6156108 baseEnd_6156108 := by
    simpa [prefixWord, tailWord_6156108, baseEnd_6156108] using wordTrace_append hprefix tailTrace_6156108
  have hstable : (prefixWord ++ tailWord_6156108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6156108).length < 2 ^ (prefixWord ++ tailWord_6156108).sum := by decide
  have hdescent : baseEnd_6156108 < baseStart_6156108 := by decide
  rcases family_descends (prefixWord ++ tailWord_6156108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6156114 : List Nat := [3, 2, 2, 1, 1, 4, 3, 7]
def baseStart_6156114 : Nat := 118140960795 + 6156114 * 2 ^ 59
def prefixEnd_6156114 : Nat := 4983230072969 + 3 ^ 40 * 6156114 * 2
def baseEnd_6156114 : Nat := 117075757254541941087539

theorem tailTrace_6156114 : CollatzResearch.WordTrace tailWord_6156114 prefixEnd_6156114 117075757254541941087539 := by
  unfold tailWord_6156114
  simp only [CollatzResearch.WordTrace]
  refine ⟨56132980904864458352906849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149687949079638555607751597 56132980904864458352906849)
  ·
    refine ⟨42099735678648343764680137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56132980904864458352906849 42099735678648343764680137)
    ·
      refine ⟨31574801758986257823510103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42099735678648343764680137 31574801758986257823510103)
      ·
        refine ⟨47362202638479386735265155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31574801758986257823510103 47362202638479386735265155)
        ·
          refine ⟨71043303957719080102897733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47362202638479386735265155 71043303957719080102897733)
          ·
            refine ⟨13320619492072327519293325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71043303957719080102897733 13320619492072327519293325)
            ·
              refine ⟨4995232309527122819734997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13320619492072327519293325 4995232309527122819734997)
              ·
                refine ⟨117075757254541941087539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4995232309527122819734997 117075757254541941087539)
                ·
                  rfl

theorem cell23_6156114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 3, 7].length) (baseStart_6156114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6156114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6156114 prefixEnd_6156114 := by exact prefixLift 6156114
  have htrace : WordTrace (prefixWord ++ tailWord_6156114) baseStart_6156114 baseEnd_6156114 := by
    simpa [prefixWord, tailWord_6156114, baseEnd_6156114] using wordTrace_append hprefix tailTrace_6156114
  have hstable : (prefixWord ++ tailWord_6156114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6156114).length < 2 ^ (prefixWord ++ tailWord_6156114).sum := by decide
  have hdescent : baseEnd_6156114 < baseStart_6156114 := by decide
  rcases family_descends (prefixWord ++ tailWord_6156114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6156128 : List Nat := [2, 1, 1, 3, 3, 4, 2, 1, 1, 2, 3]
def baseStart_6156128 : Nat := 118140960795 + 6156128 * 2 ^ 59
def prefixEnd_6156128 : Nat := 4983230072969 + 3 ^ 40 * 6156128 * 2
def baseEnd_6156128 : Nat := 3161052634601795354588489

theorem tailTrace_6156128 : CollatzResearch.WordTrace tailWord_6156128 prefixEnd_6156128 3161052634601795354588489 := by
  unfold tailWord_6156128
  simp only [CollatzResearch.WordTrace]
  refine ⟨112266217120703556901318519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149688289494271409201758025 112266217120703556901318519)
  ·
    refine ⟨168399325681055335351977779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112266217120703556901318519 168399325681055335351977779)
    ·
      refine ⟨252598988521583003027966669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168399325681055335351977779 252598988521583003027966669)
      ·
        refine ⟨94724620695593626135487501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 252598988521583003027966669 94724620695593626135487501)
        ·
          refine ⟨35521732760847609800807813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94724620695593626135487501 35521732760847609800807813)
          ·
            refine ⟨6660324892658926837651465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35521732760847609800807813 6660324892658926837651465)
            ·
              refine ⟨4995243669494195128238599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6660324892658926837651465 4995243669494195128238599)
              ·
                refine ⟨7492865504241292692357899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4995243669494195128238599 7492865504241292692357899)
                ·
                  refine ⟨11239298256361939038536849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7492865504241292692357899 11239298256361939038536849)
                  ·
                    refine ⟨8429473692271454278902637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11239298256361939038536849 8429473692271454278902637)
                    ·
                      refine ⟨3161052634601795354588489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8429473692271454278902637 3161052634601795354588489)
                      ·
                        rfl

theorem cell23_6156128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 2, 1, 1, 2, 3].length) (baseStart_6156128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6156128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6156128 prefixEnd_6156128 := by exact prefixLift 6156128
  have htrace : WordTrace (prefixWord ++ tailWord_6156128) baseStart_6156128 baseEnd_6156128 := by
    simpa [prefixWord, tailWord_6156128, baseEnd_6156128] using wordTrace_append hprefix tailTrace_6156128
  have hstable : (prefixWord ++ tailWord_6156128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6156128).length < 2 ^ (prefixWord ++ tailWord_6156128).sum := by decide
  have hdescent : baseEnd_6156128 < baseStart_6156128 := by decide
  rcases family_descends (prefixWord ++ tailWord_6156128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6156158 : List Nat := [4, 2, 3, 1, 1, 1, 3, 1, 1, 3, 3]
def baseStart_6156158 : Nat := 118140960795 + 6156158 * 2 ^ 59
def prefixEnd_6156158 : Nat := 4983230072969 + 3 ^ 40 * 6156158 * 2
def baseEnd_6156158 : Nat := 3161068039021430237213351

theorem tailTrace_6156158 : CollatzResearch.WordTrace tailWord_6156158 prefixEnd_6156158 3161068039021430237213351 := by
  unfold tailWord_6156158
  simp only [CollatzResearch.WordTrace]
  refine ⟨28066691053912303615778641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149689018954198952617486085 28066691053912303615778641)
  ·
    refine ⟨21050018290434227711833981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28066691053912303615778641 21050018290434227711833981)
    ·
      refine ⟨7893756858912835391937743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21050018290434227711833981 7893756858912835391937743)
      ·
        refine ⟨11840635288369253087906615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7893756858912835391937743 11840635288369253087906615)
        ·
          refine ⟨17760952932553879631859923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11840635288369253087906615 17760952932553879631859923)
          ·
            refine ⟨26641429398830819447789885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17760952932553879631859923 26641429398830819447789885)
            ·
              refine ⟨9990536024561557292921207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26641429398830819447789885 9990536024561557292921207)
              ·
                refine ⟨14985804036842335939381811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9990536024561557292921207 14985804036842335939381811)
                ·
                  refine ⟨22478706055263503909072717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14985804036842335939381811 22478706055263503909072717)
                  ·
                    refine ⟨8429514770723813965902269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22478706055263503909072717 8429514770723813965902269)
                    ·
                      refine ⟨3161068039021430237213351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8429514770723813965902269 3161068039021430237213351)
                      ·
                        rfl

theorem cell23_6156158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_6156158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6156158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6156158 prefixEnd_6156158 := by exact prefixLift 6156158
  have htrace : WordTrace (prefixWord ++ tailWord_6156158) baseStart_6156158 baseEnd_6156158 := by
    simpa [prefixWord, tailWord_6156158, baseEnd_6156158] using wordTrace_append hprefix tailTrace_6156158
  have hstable : (prefixWord ++ tailWord_6156158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6156158).length < 2 ^ (prefixWord ++ tailWord_6156158).sum := by decide
  have hdescent : baseEnd_6156158 < baseStart_6156158 := by decide
  rcases family_descends (prefixWord ++ tailWord_6156158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6156177 : List Nat := [1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 4]
def baseStart_6156177 : Nat := 118140960795 + 6156177 * 2 ^ 59
def prefixEnd_6156177 : Nat := 4983230072969 + 3 ^ 40 * 6156177 * 2
def baseEnd_6156177 : Nat := 3161077795153865662875763

theorem tailTrace_6156177 : CollatzResearch.WordTrace tailWord_6156177 prefixEnd_6156177 3161077795153865662875763 := by
  unfold tailWord_6156177
  simp only [CollatzResearch.WordTrace]
  refine ⟨224534221418229595171170785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149689480945486396780780523 224534221418229595171170785)
  ·
    refine ⟨168400666063672196378378089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224534221418229595171170785 168400666063672196378378089)
    ·
      refine ⟨126300499547754147283783567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168400666063672196378378089 126300499547754147283783567)
      ·
        refine ⟨189450749321631220925675351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126300499547754147283783567 189450749321631220925675351)
        ·
          refine ⟨284176123982446831388513027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189450749321631220925675351 284176123982446831388513027)
          ·
            refine ⟨426264185973670247082769541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 284176123982446831388513027 426264185973670247082769541)
            ·
              refine ⟨79924534870063171328019289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 426264185973670247082769541 79924534870063171328019289)
              ·
                refine ⟨59943401152547378496014467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79924534870063171328019289 59943401152547378496014467)
                ·
                  refine ⟨89915101728821067744021701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59943401152547378496014467 89915101728821067744021701)
                  ·
                    refine ⟨16859081574153950202004069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 89915101728821067744021701 16859081574153950202004069)
                    ·
                      refine ⟨3161077795153865662875763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16859081574153950202004069 3161077795153865662875763)
                      ·
                        rfl

theorem cell23_6156177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 4].length) (baseStart_6156177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6156177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6156177 prefixEnd_6156177 := by exact prefixLift 6156177
  have htrace : WordTrace (prefixWord ++ tailWord_6156177) baseStart_6156177 baseEnd_6156177 := by
    simpa [prefixWord, tailWord_6156177, baseEnd_6156177] using wordTrace_append hprefix tailTrace_6156177
  have hstable : (prefixWord ++ tailWord_6156177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6156177).length < 2 ^ (prefixWord ++ tailWord_6156177).sum := by decide
  have hdescent : baseEnd_6156177 < baseStart_6156177 := by decide
  rcases family_descends (prefixWord ++ tailWord_6156177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6156181 : List Nat := [1, 3, 2, 1, 1, 3, 1, 1, 6, 2, 2]
def baseStart_6156181 : Nat := 118140960795 + 6156181 * 2 ^ 59
def prefixEnd_6156181 : Nat := 4983230072969 + 3 ^ 40 * 6156181 * 2
def baseEnd_6156181 : Nat := 3161079849076483647225745

theorem tailTrace_6156181 : CollatzResearch.WordTrace tailWord_6156181 prefixEnd_6156181 3161079849076483647225745 := by
  unfold tailWord_6156181
  simp only [CollatzResearch.WordTrace]
  refine ⟨224534367310215103854316397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149689578206810069236210931 224534367310215103854316397)
  ·
    refine ⟨84200387741330663945368649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 224534367310215103854316397 84200387741330663945368649)
    ·
      refine ⟨63150290805997997959026487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84200387741330663945368649 63150290805997997959026487)
      ·
        refine ⟨94725436208996996938539731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63150290805997997959026487 94725436208996996938539731)
        ·
          refine ⟨142088154313495495407809597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94725436208996996938539731 142088154313495495407809597)
          ·
            refine ⟨53283057867560810777928599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 142088154313495495407809597 53283057867560810777928599)
            ·
              refine ⟨79924586801341216166892899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53283057867560810777928599 79924586801341216166892899)
              ·
                refine ⟨119886880202011824250339349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79924586801341216166892899 119886880202011824250339349)
                ·
                  refine ⟨5619697509469304261734657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 119886880202011824250339349 5619697509469304261734657)
                  ·
                    refine ⟨4214773132101978196300993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5619697509469304261734657 4214773132101978196300993)
                    ·
                      refine ⟨3161079849076483647225745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4214773132101978196300993 3161079849076483647225745)
                      ·
                        rfl

theorem cell23_6156181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 6, 2, 2].length) (baseStart_6156181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6156181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6156181 prefixEnd_6156181 := by exact prefixLift 6156181
  have htrace : WordTrace (prefixWord ++ tailWord_6156181) baseStart_6156181 baseEnd_6156181 := by
    simpa [prefixWord, tailWord_6156181, baseEnd_6156181] using wordTrace_append hprefix tailTrace_6156181
  have hstable : (prefixWord ++ tailWord_6156181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6156181).length < 2 ^ (prefixWord ++ tailWord_6156181).sum := by decide
  have hdescent : baseEnd_6156181 < baseStart_6156181 := by decide
  rcases family_descends (prefixWord ++ tailWord_6156181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6156227 : List Nat := [1, 1, 1, 3, 1, 1, 2, 1, 5, 2, 5]
def baseStart_6156227 : Nat := 118140960795 + 6156227 * 2 ^ 59
def prefixEnd_6156227 : Nat := 4983230072969 + 3 ^ 40 * 6156227 * 2
def baseEnd_6156227 : Nat := 3161103469186590467250533

theorem tailTrace_6156227 : CollatzResearch.WordTrace tailWord_6156227 prefixEnd_6156227 3161103469186590467250533 := by
  unfold tailWord_6156227
  simp only [CollatzResearch.WordTrace]
  refine ⟨224536045068048453710490935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149690696712032302473660623 224536045068048453710490935)
  ·
    refine ⟨336804067602072680565736403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224536045068048453710490935 336804067602072680565736403)
    ·
      refine ⟨505206101403109020848604605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 336804067602072680565736403 505206101403109020848604605)
      ·
        refine ⟨189452288026165882818226727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 505206101403109020848604605 189452288026165882818226727)
        ·
          refine ⟨284178432039248824227340091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189452288026165882818226727 284178432039248824227340091)
          ·
            refine ⟨426267648058873236341010137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 284178432039248824227340091 426267648058873236341010137)
            ·
              refine ⟨319700736044154927255757603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 426267648058873236341010137 319700736044154927255757603)
              ·
                refine ⟨479551104066232390883636405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 319700736044154927255757603 479551104066232390883636405)
                ·
                  refine ⟨44957916006209286645340913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 479551104066232390883636405 44957916006209286645340913)
                  ·
                    refine ⟨33718437004656964984005685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44957916006209286645340913 33718437004656964984005685)
                    ·
                      refine ⟨3161103469186590467250533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33718437004656964984005685 3161103469186590467250533)
                      ·
                        rfl

theorem cell23_6156227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 5, 2, 5].length) (baseStart_6156227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6156227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6156227 prefixEnd_6156227 := by exact prefixLift 6156227
  have htrace : WordTrace (prefixWord ++ tailWord_6156227) baseStart_6156227 baseEnd_6156227 := by
    simpa [prefixWord, tailWord_6156227, baseEnd_6156227] using wordTrace_append hprefix tailTrace_6156227
  have hstable : (prefixWord ++ tailWord_6156227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6156227).length < 2 ^ (prefixWord ++ tailWord_6156227).sum := by decide
  have hdescent : baseEnd_6156227 < baseStart_6156227 := by decide
  rcases family_descends (prefixWord ++ tailWord_6156227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6156234 : List Nat := [3, 1, 2, 1, 2, 1, 3, 3, 2, 5]
def baseStart_6156234 : Nat := 118140960795 + 6156234 * 2 ^ 59
def prefixEnd_6156234 : Nat := 4983230072969 + 3 ^ 40 * 6156234 * 2
def baseEnd_6156234 : Nat := 1053702354517057313287667

theorem tailTrace_6156234 : CollatzResearch.WordTrace tailWord_6156234 prefixEnd_6156234 1053702354517057313287667 := by
  unfold tailWord_6156234
  simp only [CollatzResearch.WordTrace]
  refine ⟨56134075094755773476498939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149690866919348729270663837 56134075094755773476498939)
  ·
    refine ⟨84201112642133660214748409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56134075094755773476498939 84201112642133660214748409)
    ·
      refine ⟨63150834481600245161061307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84201112642133660214748409 63150834481600245161061307)
      ·
        refine ⟨94726251722400367741591961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63150834481600245161061307 94726251722400367741591961)
        ·
          refine ⟨71044688791800275806193971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94726251722400367741591961 71044688791800275806193971)
          ·
            refine ⟨106567033187700413709290957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71044688791800275806193971 106567033187700413709290957)
            ·
              refine ⟨39962637445387655140984109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106567033187700413709290957 39962637445387655140984109)
              ·
                refine ⟨14985989042020370677869041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39962637445387655140984109 14985989042020370677869041)
                ·
                  refine ⟨11239491781515278008401781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14985989042020370677869041 11239491781515278008401781)
                  ·
                    refine ⟨1053702354517057313287667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11239491781515278008401781 1053702354517057313287667)
                    ·
                      rfl

theorem cell23_6156234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 3, 2, 5].length) (baseStart_6156234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6156234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6156234 prefixEnd_6156234 := by exact prefixLift 6156234
  have htrace : WordTrace (prefixWord ++ tailWord_6156234) baseStart_6156234 baseEnd_6156234 := by
    simpa [prefixWord, tailWord_6156234, baseEnd_6156234] using wordTrace_append hprefix tailTrace_6156234
  have hstable : (prefixWord ++ tailWord_6156234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6156234).length < 2 ^ (prefixWord ++ tailWord_6156234).sum := by decide
  have hdescent : baseEnd_6156234 < baseStart_6156234 := by decide
  rcases family_descends (prefixWord ++ tailWord_6156234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6156244 : List Nat := [2, 4, 1, 2, 1, 1, 1, 1, 3, 2, 5]
def baseStart_6156244 : Nat := 118140960795 + 6156244 * 2 ^ 59
def prefixEnd_6156244 : Nat := 4983230072969 + 3 ^ 40 * 6156244 * 2
def baseEnd_6156244 : Nat := 3161112198357716900737955

theorem tailTrace_6156244 : CollatzResearch.WordTrace tailWord_6156244 prefixEnd_6156244 3161112198357716900737955 := by
  unfold tailWord_6156244
  simp only [CollatzResearch.WordTrace]
  refine ⟨112268332554493432806929893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149691110072657910409239857 112268332554493432806929893)
  ·
    refine ⟨21050312353967518651299355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112268332554493432806929893 21050312353967518651299355)
    ·
      refine ⟨31575468530951277976949033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21050312353967518651299355 31575468530951277976949033)
      ·
        refine ⟨23681601398213458482711775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31575468530951277976949033 23681601398213458482711775)
        ·
          refine ⟨35522402097320187724067663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23681601398213458482711775 35522402097320187724067663)
          ·
            refine ⟨53283603145980281586101495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35522402097320187724067663 53283603145980281586101495)
            ·
              refine ⟨79925404718970422379152243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53283603145980281586101495 79925404718970422379152243)
              ·
                refine ⟨119888107078455633568728365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79925404718970422379152243 119888107078455633568728365)
                ·
                  refine ⟨44958040154420862588273137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 119888107078455633568728365 44958040154420862588273137)
                  ·
                    refine ⟨33718530115815646941204853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44958040154420862588273137 33718530115815646941204853)
                    ·
                      refine ⟨3161112198357716900737955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33718530115815646941204853 3161112198357716900737955)
                      ·
                        rfl

theorem cell23_6156244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_6156244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6156244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6156244 prefixEnd_6156244 := by exact prefixLift 6156244
  have htrace : WordTrace (prefixWord ++ tailWord_6156244) baseStart_6156244 baseEnd_6156244 := by
    simpa [prefixWord, tailWord_6156244, baseEnd_6156244] using wordTrace_append hprefix tailTrace_6156244
  have hstable : (prefixWord ++ tailWord_6156244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6156244).length < 2 ^ (prefixWord ++ tailWord_6156244).sum := by decide
  have hdescent : baseEnd_6156244 < baseStart_6156244 := by decide
  rcases family_descends (prefixWord ++ tailWord_6156244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6156271 : List Nat := [1, 1, 2, 1, 4, 2, 3, 1, 2, 4, 2]
def baseStart_6156271 : Nat := 118140960795 + 6156271 * 2 ^ 59
def prefixEnd_6156271 : Nat := 4983230072969 + 3 ^ 40 * 6156271 * 2
def baseEnd_6156271 : Nat := 3161126062335388295100331

theorem tailTrace_6156271 : CollatzResearch.WordTrace tailWord_6156271 prefixEnd_6156271 3161126062335388295100331 := by
  unfold tailWord_6156271
  simp only [CollatzResearch.WordTrace]
  refine ⟨224537649879889049225092667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149691766586592699483395111 224537649879889049225092667)
  ·
    refine ⟨336806474819833573837639001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224537649879889049225092667 336806474819833573837639001)
    ·
      refine ⟨252604856114875180378229251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 336806474819833573837639001 252604856114875180378229251)
      ·
        refine ⟨378907284172312770567343877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252604856114875180378229251 378907284172312770567343877)
        ·
          refine ⟨71045115782308644481376977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 378907284172312770567343877 71045115782308644481376977)
          ·
            refine ⟨53283836836731483361032733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71045115782308644481376977 53283836836731483361032733)
            ·
              refine ⟨19981438813774306260387275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53283836836731483361032733 19981438813774306260387275)
              ·
                refine ⟨29972158220661459390580913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19981438813774306260387275 29972158220661459390580913)
                ·
                  refine ⟨22479118665496094542935685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29972158220661459390580913 22479118665496094542935685)
                  ·
                    refine ⟨4214834749780517726800441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22479118665496094542935685 4214834749780517726800441)
                    ·
                      refine ⟨3161126062335388295100331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4214834749780517726800441 3161126062335388295100331)
                      ·
                        rfl

theorem cell23_6156271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 1, 2, 4, 2].length) (baseStart_6156271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6156271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6156271 prefixEnd_6156271 := by exact prefixLift 6156271
  have htrace : WordTrace (prefixWord ++ tailWord_6156271) baseStart_6156271 baseEnd_6156271 := by
    simpa [prefixWord, tailWord_6156271, baseEnd_6156271] using wordTrace_append hprefix tailTrace_6156271
  have hstable : (prefixWord ++ tailWord_6156271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6156271).length < 2 ^ (prefixWord ++ tailWord_6156271).sum := by decide
  have hdescent : baseEnd_6156271 < baseStart_6156271 := by decide
  rcases family_descends (prefixWord ++ tailWord_6156271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6156281 : List Nat := [1, 2, 1, 3, 1, 5, 1, 2, 3, 4]
def baseStart_6156281 : Nat := 118140960795 + 6156281 * 2 ^ 59
def prefixEnd_6156281 : Nat := 4983230072969 + 3 ^ 40 * 6156281 * 2
def baseEnd_6156281 : Nat := 1053710399047311085325095

theorem tailTrace_6156281 : CollatzResearch.WordTrace tailWord_6156281 prefixEnd_6156281 1053710399047311085325095 := by
  unfold tailWord_6156281
  simp only [CollatzResearch.WordTrace]
  refine ⟨224538014609852820932956697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149692009739901880621971131 224538014609852820932956697)
  ·
    refine ⟨168403510957389615699717523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224538014609852820932956697 168403510957389615699717523)
    ·
      refine ⟨252605266436084423549576285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168403510957389615699717523 252605266436084423549576285)
      ·
        refine ⟨94726974913531658831091107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 252605266436084423549576285 94726974913531658831091107)
        ·
          refine ⟨142090462370297488246636661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94726974913531658831091107 142090462370297488246636661)
          ·
            refine ⟨13320980847215389523122187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 142090462370297488246636661 13320980847215389523122187)
            ·
              refine ⟨19981471270823084284683281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13320980847215389523122187 19981471270823084284683281)
              ·
                refine ⟨14986103453117313213512461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19981471270823084284683281 14986103453117313213512461)
                ·
                  refine ⟨5619788794918992455067173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14986103453117313213512461 5619788794918992455067173)
                  ·
                    refine ⟨1053710399047311085325095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5619788794918992455067173 1053710399047311085325095)
                    ·
                      rfl

theorem cell23_6156281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 2, 3, 4].length) (baseStart_6156281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6156281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6156281 prefixEnd_6156281 := by exact prefixLift 6156281
  have htrace : WordTrace (prefixWord ++ tailWord_6156281) baseStart_6156281 baseEnd_6156281 := by
    simpa [prefixWord, tailWord_6156281, baseEnd_6156281] using wordTrace_append hprefix tailTrace_6156281
  have hstable : (prefixWord ++ tailWord_6156281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6156281).length < 2 ^ (prefixWord ++ tailWord_6156281).sum := by decide
  have hdescent : baseEnd_6156281 < baseStart_6156281 := by decide
  rcases family_descends (prefixWord ++ tailWord_6156281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6156311 : List Nat := [1, 1, 3, 5, 2, 1, 1, 1, 8]
def baseStart_6156311 : Nat := 118140960795 + 6156311 * 2 ^ 59
def prefixEnd_6156311 : Nat := 4983230072969 + 3 ^ 40 * 6156311 * 2
def baseEnd_6156311 : Nat := 351238511284618682066683

theorem tailTrace_6156311 : CollatzResearch.WordTrace tailWord_6156311 prefixEnd_6156311 351238511284618682066683 := by
  unfold tailWord_6156311
  simp only [CollatzResearch.WordTrace]
  refine ⟨224539108799744136056548787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149692739199829424037699191 224539108799744136056548787)
  ·
    refine ⟨336808663199616204084823181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224539108799744136056548787 336808663199616204084823181)
    ·
      refine ⟨126303248699856076531808693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 336808663199616204084823181 126303248699856076531808693)
      ·
        refine ⟨11840929565611507174857065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 126303248699856076531808693 11840929565611507174857065)
        ·
          refine ⟨8880697174208630381142799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11840929565611507174857065 8880697174208630381142799)
          ·
            refine ⟨13321045761312945571714199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8880697174208630381142799 13321045761312945571714199)
            ·
              refine ⟨19981568641969418357571299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13321045761312945571714199 19981568641969418357571299)
              ·
                refine ⟨29972352962954127536356949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19981568641969418357571299 29972352962954127536356949)
                ·
                  refine ⟨351238511284618682066683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29972352962954127536356949 351238511284618682066683)
                  ·
                    rfl

theorem cell23_6156311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 1, 8].length) (baseStart_6156311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6156311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6156311 prefixEnd_6156311 := by exact prefixLift 6156311
  have htrace : WordTrace (prefixWord ++ tailWord_6156311) baseStart_6156311 baseEnd_6156311 := by
    simpa [prefixWord, tailWord_6156311, baseEnd_6156311] using wordTrace_append hprefix tailTrace_6156311
  have hstable : (prefixWord ++ tailWord_6156311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6156311).length < 2 ^ (prefixWord ++ tailWord_6156311).sum := by decide
  have hdescent : baseEnd_6156311 < baseStart_6156311 := by decide
  rcases family_descends (prefixWord ++ tailWord_6156311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6156314 : List Nat := [3, 1, 1, 3, 1, 3, 1, 1, 1, 2, 6]
def baseStart_6156314 : Nat := 118140960795 + 6156314 * 2 ^ 59
def prefixEnd_6156314 : Nat := 4983230072969 + 3 ^ 40 * 6156314 * 2
def baseEnd_6156314 : Nat := 3161148142003531626862633

theorem tailTrace_6156314 : CollatzResearch.WordTrace tailWord_6156314 prefixEnd_6156314 3161148142003531626862633 := by
  unfold tailWord_6156314
  simp only [CollatzResearch.WordTrace]
  refine ⟨56134804554683316892226999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149692812145822178379271997 56134804554683316892226999)
  ·
    refine ⟨84202206832024975338340499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56134804554683316892226999 84202206832024975338340499)
    ·
      refine ⟨126303310248037463007510749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84202206832024975338340499 126303310248037463007510749)
      ·
        refine ⟨47363741343014048627816531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126303310248037463007510749 47363741343014048627816531)
        ·
          refine ⟨71045612014521072941724797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47363741343014048627816531 71045612014521072941724797)
          ·
            refine ⟨26642104505445402353146799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71045612014521072941724797 26642104505445402353146799)
            ·
              refine ⟨39963156758168103529720199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26642104505445402353146799 39963156758168103529720199)
              ·
                refine ⟨59944735137252155294580299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39963156758168103529720199 59944735137252155294580299)
                ·
                  refine ⟨89917102705878232941870449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59944735137252155294580299 89917102705878232941870449)
                  ·
                    refine ⟨67437827029408674706402837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 89917102705878232941870449 67437827029408674706402837)
                    ·
                      refine ⟨3161148142003531626862633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67437827029408674706402837 3161148142003531626862633)
                      ·
                        rfl

theorem cell23_6156314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 1, 1, 2, 6].length) (baseStart_6156314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6156314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6156314 prefixEnd_6156314 := by exact prefixLift 6156314
  have htrace : WordTrace (prefixWord ++ tailWord_6156314) baseStart_6156314 baseEnd_6156314 := by
    simpa [prefixWord, tailWord_6156314, baseEnd_6156314] using wordTrace_append hprefix tailTrace_6156314
  have hstable : (prefixWord ++ tailWord_6156314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6156314).length < 2 ^ (prefixWord ++ tailWord_6156314).sum := by decide
  have hdescent : baseEnd_6156314 < baseStart_6156314 := by decide
  rcases family_descends (prefixWord ++ tailWord_6156314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6156331 : List Nat := [1, 1, 1, 1, 2, 1, 4, 1, 6, 3, 2]
def baseStart_6156331 : Nat := 118140960795 + 6156331 * 2 ^ 59
def prefixEnd_6156331 : Nat := 4983230072969 + 3 ^ 40 * 6156331 * 2
def baseEnd_6156331 : Nat := 3161156871174658060350055

theorem tailTrace_6156331 : CollatzResearch.WordTrace tailWord_6156331 prefixEnd_6156331 3161156871174658060350055 := by
  unfold tailWord_6156331
  simp only [CollatzResearch.WordTrace]
  refine ⟨224539838259671679472276847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149693225506447786314851231 224539838259671679472276847)
  ·
    refine ⟨336809757389507519208415271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224539838259671679472276847 336809757389507519208415271)
    ·
      refine ⟨505214636084261278812622907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 336809757389507519208415271 505214636084261278812622907)
      ·
        refine ⟨757821954126391918218934361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 505214636084261278812622907 757821954126391918218934361)
        ·
          refine ⟨568366465594793938664200771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 757821954126391918218934361 568366465594793938664200771)
          ·
            refine ⟨852549698392190907996301157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 568366465594793938664200771 852549698392190907996301157)
            ·
              refine ⟨159853068448535795249306467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 852549698392190907996301157 159853068448535795249306467)
              ·
                refine ⟨239779602672803692873959701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 159853068448535795249306467 239779602672803692873959701)
                ·
                  refine ⟨11239668875287673103466861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 239779602672803692873959701 11239668875287673103466861)
                  ·
                    refine ⟨4214875828232877413800073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11239668875287673103466861 4214875828232877413800073)
                    ·
                      refine ⟨3161156871174658060350055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4214875828232877413800073 3161156871174658060350055)
                      ·
                        rfl

theorem cell23_6156331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 6, 3, 2].length) (baseStart_6156331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6156331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6156331 prefixEnd_6156331 := by exact prefixLift 6156331
  have htrace : WordTrace (prefixWord ++ tailWord_6156331) baseStart_6156331 baseEnd_6156331 := by
    simpa [prefixWord, tailWord_6156331, baseEnd_6156331] using wordTrace_append hprefix tailTrace_6156331
  have hstable : (prefixWord ++ tailWord_6156331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6156331).length < 2 ^ (prefixWord ++ tailWord_6156331).sum := by decide
  have hdescent : baseEnd_6156331 < baseStart_6156331 := by decide
  rcases family_descends (prefixWord ++ tailWord_6156331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6156338 : List Nat := [3, 2, 1, 1, 2, 3, 2, 2, 3, 1, 3]
def baseStart_6156338 : Nat := 118140960795 + 6156338 * 2 ^ 59
def prefixEnd_6156338 : Nat := 4983230072969 + 3 ^ 40 * 6156338 * 2
def baseEnd_6156338 : Nat := 3161160465539239532962523

theorem tailTrace_6156338 : CollatzResearch.WordTrace tailWord_6156338 prefixEnd_6156338 3161160465539239532962523 := by
  unfold tailWord_6156338
  simp only [CollatzResearch.WordTrace]
  refine ⟨56135023392661579916945417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149693395713764213111854445 56135023392661579916945417)
  ·
    refine ⟨42101267544496184937709063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56135023392661579916945417 42101267544496184937709063)
    ·
      refine ⟨63151901316744277406563595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42101267544496184937709063 63151901316744277406563595)
      ·
        refine ⟨94727851975116416109845393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63151901316744277406563595 94727851975116416109845393)
        ·
          refine ⟨71045888981337312082384045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94727851975116416109845393 71045888981337312082384045)
          ·
            refine ⟨26642208368001492030894017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71045888981337312082384045 26642208368001492030894017)
            ·
              refine ⟨19981656276001119023170513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26642208368001492030894017 19981656276001119023170513)
              ·
                refine ⟨14986242207000839267377885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19981656276001119023170513 14986242207000839267377885)
                ·
                  refine ⟨5619840827625314725266707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14986242207000839267377885 5619840827625314725266707)
                  ·
                    refine ⟨8429761241437972087900061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5619840827625314725266707 8429761241437972087900061)
                    ·
                      refine ⟨3161160465539239532962523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8429761241437972087900061 3161160465539239532962523)
                      ·
                        rfl

theorem cell23_6156338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 2, 3, 1, 3].length) (baseStart_6156338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6156338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6156338 prefixEnd_6156338 := by exact prefixLift 6156338
  have htrace : WordTrace (prefixWord ++ tailWord_6156338) baseStart_6156338 baseEnd_6156338 := by
    simpa [prefixWord, tailWord_6156338, baseEnd_6156338] using wordTrace_append hprefix tailTrace_6156338
  have hstable : (prefixWord ++ tailWord_6156338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6156338).length < 2 ^ (prefixWord ++ tailWord_6156338).sum := by decide
  have hdescent : baseEnd_6156338 < baseStart_6156338 := by decide
  rcases family_descends (prefixWord ++ tailWord_6156338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6156341 : List Nat := [1, 3, 3, 1, 1, 1, 3, 4, 1, 5]
def baseStart_6156341 : Nat := 118140960795 + 6156341 * 2 ^ 59
def prefixEnd_6156341 : Nat := 4983230072969 + 3 ^ 40 * 6156341 * 2
def baseEnd_6156341 : Nat := 1053720668660401007075003

theorem tailTrace_6156341 : CollatzResearch.WordTrace tailWord_6156341 prefixEnd_6156341 1053720668660401007075003 := by
  unfold tailWord_6156341
  simp only [CollatzResearch.WordTrace]
  refine ⟨224540202989635451180140877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149693468659756967453427251 224540202989635451180140877)
  ·
    refine ⟨84202576121113294192552829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 224540202989635451180140877 84202576121113294192552829)
    ·
      refine ⟨31575966045417485322207311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84202576121113294192552829 31575966045417485322207311)
      ·
        refine ⟨47363949068126227983310967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31575966045417485322207311 47363949068126227983310967)
        ·
          refine ⟨71045923602189341974966451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47363949068126227983310967 71045923602189341974966451)
          ·
            refine ⟨106568885403284012962449677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71045923602189341974966451 106568885403284012962449677)
            ·
              refine ⟨39963332026231504860918629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106568885403284012962449677 39963332026231504860918629)
              ·
                refine ⟨7493124754918407161422243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39963332026231504860918629 7493124754918407161422243)
                ·
                  refine ⟨11239687132377610742133365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7493124754918407161422243 11239687132377610742133365)
                  ·
                    refine ⟨1053720668660401007075003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11239687132377610742133365 1053720668660401007075003)
                    ·
                      rfl

theorem cell23_6156341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 4, 1, 5].length) (baseStart_6156341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6156341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6156341 prefixEnd_6156341 := by exact prefixLift 6156341
  have htrace : WordTrace (prefixWord ++ tailWord_6156341) baseStart_6156341 baseEnd_6156341 := by
    simpa [prefixWord, tailWord_6156341, baseEnd_6156341] using wordTrace_append hprefix tailTrace_6156341
  have hstable : (prefixWord ++ tailWord_6156341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6156341).length < 2 ^ (prefixWord ++ tailWord_6156341).sum := by decide
  have hdescent : baseEnd_6156341 < baseStart_6156341 := by decide
  rcases family_descends (prefixWord ++ tailWord_6156341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6156348 : List Nat := [2, 2, 2, 2, 2, 1, 2, 3, 2, 3, 2]
def baseStart_6156348 : Nat := 118140960795 + 6156348 * 2 ^ 59
def prefixEnd_6156348 : Nat := 4983230072969 + 3 ^ 40 * 6156348 * 2
def baseEnd_6156348 : Nat := 3161165600345784493837477

theorem tailTrace_6156348 : CollatzResearch.WordTrace tailWord_6156348 prefixEnd_6156348 3161165600345784493837477 := by
  unfold tailWord_6156348
  simp only [CollatzResearch.WordTrace]
  refine ⟨112270229150305045687822849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149693638867073394250430465 112270229150305045687822849)
  ·
    refine ⟨84202671862728784265867137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112270229150305045687822849 84202671862728784265867137)
    ·
      refine ⟨63152003897046588199400353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84202671862728784265867137 63152003897046588199400353)
      ·
        refine ⟨47364002922784941149550265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63152003897046588199400353 47364002922784941149550265)
        ·
          refine ⟨35523002192088705862162699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47364002922784941149550265 35523002192088705862162699)
          ·
            refine ⟨53284503288133058793244049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35523002192088705862162699 53284503288133058793244049)
            ·
              refine ⟨39963377466099794094933037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53284503288133058793244049 39963377466099794094933037)
              ·
                refine ⟨14986266549787422785599889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39963377466099794094933037 14986266549787422785599889)
                ·
                  refine ⟨11239699912340567089199917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14986266549787422785599889 11239699912340567089199917)
                  ·
                    refine ⟨4214887467127712658449969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11239699912340567089199917 4214887467127712658449969)
                    ·
                      refine ⟨3161165600345784493837477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4214887467127712658449969 3161165600345784493837477)
                      ·
                        rfl

theorem cell23_6156348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 3, 2, 3, 2].length) (baseStart_6156348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6156348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6156348 prefixEnd_6156348 := by exact prefixLift 6156348
  have htrace : WordTrace (prefixWord ++ tailWord_6156348) baseStart_6156348 baseEnd_6156348 := by
    simpa [prefixWord, tailWord_6156348, baseEnd_6156348] using wordTrace_append hprefix tailTrace_6156348
  have hstable : (prefixWord ++ tailWord_6156348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6156348).length < 2 ^ (prefixWord ++ tailWord_6156348).sum := by decide
  have hdescent : baseEnd_6156348 < baseStart_6156348 := by decide
  rcases family_descends (prefixWord ++ tailWord_6156348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6156361 : List Nat := [1, 2, 1, 1, 2, 2, 3, 5, 1, 1, 4]
def baseStart_6156361 : Nat := 118140960795 + 6156361 * 2 ^ 59
def prefixEnd_6156361 : Nat := 4983230072969 + 3 ^ 40 * 6156361 * 2
def baseEnd_6156361 : Nat := 3161172275594292942974917

theorem tailTrace_6156361 : CollatzResearch.WordTrace tailWord_6156361 prefixEnd_6156361 3161172275594292942974917 := by
  unfold tailWord_6156361
  simp only [CollatzResearch.WordTrace]
  refine ⟨224540932449562994595868937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149693954966375329730579291 224540932449562994595868937)
  ·
    refine ⟨168405699337172245946901703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224540932449562994595868937 168405699337172245946901703)
    ·
      refine ⟨252608549005758368920352555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168405699337172245946901703 252608549005758368920352555)
      ·
        refine ⟨378912823508637553380528833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252608549005758368920352555 378912823508637553380528833)
        ·
          refine ⟨284184617631478165035396625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 378912823508637553380528833 284184617631478165035396625)
          ·
            refine ⟨213138463223608623776547469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 284184617631478165035396625 213138463223608623776547469)
            ·
              refine ⟨79926923708853233916205301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 213138463223608623776547469 79926923708853233916205301)
              ·
                refine ⟨7493149097704990679644247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 79926923708853233916205301 7493149097704990679644247)
                ·
                  refine ⟨11239723646557486019466371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7493149097704990679644247 11239723646557486019466371)
                  ·
                    refine ⟨16859585469836229029199557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11239723646557486019466371 16859585469836229029199557)
                    ·
                      refine ⟨3161172275594292942974917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16859585469836229029199557 3161172275594292942974917)
                      ·
                        rfl

theorem cell23_6156361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 5, 1, 1, 4].length) (baseStart_6156361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6156361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6156361 prefixEnd_6156361 := by exact prefixLift 6156361
  have htrace : WordTrace (prefixWord ++ tailWord_6156361) baseStart_6156361 baseEnd_6156361 := by
    simpa [prefixWord, tailWord_6156361, baseEnd_6156361] using wordTrace_append hprefix tailTrace_6156361
  have hstable : (prefixWord ++ tailWord_6156361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6156361).length < 2 ^ (prefixWord ++ tailWord_6156361).sum := by decide
  have hdescent : baseEnd_6156361 < baseStart_6156361 := by decide
  rcases family_descends (prefixWord ++ tailWord_6156361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6156365 : List Nat := [1, 6, 1, 1, 1, 1, 3, 2, 2, 3, 2]
def baseStart_6156365 : Nat := 118140960795 + 6156365 * 2 ^ 59
def prefixEnd_6156365 : Nat := 4983230072969 + 3 ^ 40 * 6156365 * 2
def baseEnd_6156365 : Nat := 3161174329516910927324899

theorem tailTrace_6156365 : CollatzResearch.WordTrace tailWord_6156365 prefixEnd_6156365 3161174329516910927324899 := by
  unfold tailWord_6156365
  simp only [CollatzResearch.WordTrace]
  refine ⟨224541078341548503279014549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149694052227699002186009699 224541078341548503279014549)
  ·
    refine ⟨10525363047260086091203807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 224541078341548503279014549 10525363047260086091203807)
    ·
      refine ⟨15788044570890129136805711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10525363047260086091203807 15788044570890129136805711)
      ·
        refine ⟨23682066856335193705208567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15788044570890129136805711 23682066856335193705208567)
        ·
          refine ⟨35523100284502790557812851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23682066856335193705208567 35523100284502790557812851)
          ·
            refine ⟨53284650426754185836719277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35523100284502790557812851 53284650426754185836719277)
            ·
              refine ⟨19981743910032819688769729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53284650426754185836719277 19981743910032819688769729)
              ·
                refine ⟨14986307932524614766577297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19981743910032819688769729 14986307932524614766577297)
                ·
                  refine ⟨11239730949393461074932973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14986307932524614766577297 11239730949393461074932973)
                  ·
                    refine ⟨4214899106022547903099865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11239730949393461074932973 4214899106022547903099865)
                    ·
                      refine ⟨3161174329516910927324899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4214899106022547903099865 3161174329516910927324899)
                      ·
                        rfl

theorem cell23_6156365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 2, 2, 3, 2].length) (baseStart_6156365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6156365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6156365 prefixEnd_6156365 := by exact prefixLift 6156365
  have htrace : WordTrace (prefixWord ++ tailWord_6156365) baseStart_6156365 baseEnd_6156365 := by
    simpa [prefixWord, tailWord_6156365, baseEnd_6156365] using wordTrace_append hprefix tailTrace_6156365
  have hstable : (prefixWord ++ tailWord_6156365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6156365).length < 2 ^ (prefixWord ++ tailWord_6156365).sum := by decide
  have hdescent : baseEnd_6156365 < baseStart_6156365 := by decide
  rcases family_descends (prefixWord ++ tailWord_6156365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6156384 : List Nat := [2, 1, 1, 3, 2, 3, 1, 10]
def baseStart_6156384 : Nat := 118140960795 + 6156384 * 2 ^ 59
def prefixEnd_6156384 : Nat := 4983230072969 + 3 ^ 40 * 6156384 * 2
def baseEnd_6156384 : Nat := 117080892061086901962493

theorem tailTrace_6156384 : CollatzResearch.WordTrace tailWord_6156384 prefixEnd_6156384 117080892061086901962493 := by
  unfold tailWord_6156384
  simp only [CollatzResearch.WordTrace]
  refine ⟨112270885664239834761978103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149694514218986446349304137 112270885664239834761978103)
  ·
    refine ⟨168406328496359752142967155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112270885664239834761978103 168406328496359752142967155)
    ·
      refine ⟨252609492744539628214450733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168406328496359752142967155 252609492744539628214450733)
      ·
        refine ⟨94728559779202360580419025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 252609492744539628214450733 94728559779202360580419025)
        ·
          refine ⟨71046419834401770435314269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94728559779202360580419025 71046419834401770435314269)
          ·
            refine ⟨26642407437900663913242851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71046419834401770435314269 26642407437900663913242851)
            ·
              refine ⟨39963611156850995869864277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26642407437900663913242851 39963611156850995869864277)
              ·
                refine ⟨117080892061086901962493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 39963611156850995869864277 117080892061086901962493)
                ·
                  rfl

theorem cell23_6156384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 10].length) (baseStart_6156384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6156384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6156384 prefixEnd_6156384 := by exact prefixLift 6156384
  have htrace : WordTrace (prefixWord ++ tailWord_6156384) baseStart_6156384 baseEnd_6156384 := by
    simpa [prefixWord, tailWord_6156384, baseEnd_6156384] using wordTrace_append hprefix tailTrace_6156384
  have hstable : (prefixWord ++ tailWord_6156384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6156384).length < 2 ^ (prefixWord ++ tailWord_6156384).sum := by decide
  have hdescent : baseEnd_6156384 < baseStart_6156384 := by decide
  rcases family_descends (prefixWord ++ tailWord_6156384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6156391 : List Nat := [1, 1, 5, 1, 1, 2, 2, 3, 1, 2, 4]
def baseStart_6156391 : Nat := 118140960795 + 6156391 * 2 ^ 59
def prefixEnd_6156391 : Nat := 4983230072969 + 3 ^ 40 * 6156391 * 2
def baseEnd_6156391 : Nat := 3161187680013927825599779

theorem tailTrace_6156391 : CollatzResearch.WordTrace tailWord_6156391 prefixEnd_6156391 3161187680013927825599779 := by
  unfold tailWord_6156391
  simp only [CollatzResearch.WordTrace]
  refine ⟨224542026639454309719461027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149694684426302873146307351 224542026639454309719461027)
  ·
    refine ⟨336813039959181464579191541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224542026639454309719461027 336813039959181464579191541)
    ·
      refine ⟨31576222496173262304299207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 336813039959181464579191541 31576222496173262304299207)
      ·
        refine ⟨47364333744259893456448811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31576222496173262304299207 47364333744259893456448811)
        ·
          refine ⟨71046500616389840184673217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47364333744259893456448811 71046500616389840184673217)
          ·
            refine ⟨53284875462292380138504913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71046500616389840184673217 53284875462292380138504913)
            ·
              refine ⟨39963656596719285103878685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53284875462292380138504913 39963656596719285103878685)
              ·
                refine ⟨14986371223769731913954507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39963656596719285103878685 14986371223769731913954507)
                ·
                  refine ⟨22479556835654597870931761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14986371223769731913954507 22479556835654597870931761)
                  ·
                    refine ⟨16859667626740948403198821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22479556835654597870931761 16859667626740948403198821)
                    ·
                      refine ⟨3161187680013927825599779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16859667626740948403198821 3161187680013927825599779)
                      ·
                        rfl

theorem cell23_6156391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 3, 1, 2, 4].length) (baseStart_6156391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6156391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6156391 prefixEnd_6156391 := by exact prefixLift 6156391
  have htrace : WordTrace (prefixWord ++ tailWord_6156391) baseStart_6156391 baseEnd_6156391 := by
    simpa [prefixWord, tailWord_6156391, baseEnd_6156391] using wordTrace_append hprefix tailTrace_6156391
  have hstable : (prefixWord ++ tailWord_6156391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6156391).length < 2 ^ (prefixWord ++ tailWord_6156391).sum := by decide
  have hdescent : baseEnd_6156391 < baseStart_6156391 := by decide
  rcases family_descends (prefixWord ++ tailWord_6156391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6156398 : List Nat := [4, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3]
def baseStart_6156398 : Nat := 118140960795 + 6156398 * 2 ^ 59
def prefixEnd_6156398 : Nat := 4983230072969 + 3 ^ 40 * 6156398 * 2
def baseEnd_6156398 : Nat := 3161191274378509298212247

theorem tailTrace_6156398 : CollatzResearch.WordTrace tailWord_6156398 prefixEnd_6156398 3161191274378509298212247 := by
  unfold tailWord_6156398
  simp only [CollatzResearch.WordTrace]
  refine ⟨28067785243803618739370731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149694854633619299943310565 28067785243803618739370731)
  ·
    refine ⟨42101677865705428109056097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28067785243803618739370731 42101677865705428109056097)
    ·
      refine ⟨31576258399279071081792073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42101677865705428109056097 31576258399279071081792073)
      ·
        refine ⟨23682193799459303311344055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31576258399279071081792073 23682193799459303311344055)
        ·
          refine ⟨35523290699188954967016083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23682193799459303311344055 35523290699188954967016083)
          ·
            refine ⟨53284936048783432450524125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35523290699188954967016083 53284936048783432450524125)
            ·
              refine ⟨19981851018293787168946547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53284936048783432450524125 19981851018293787168946547)
              ·
                refine ⟨29972776527440680753419821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19981851018293787168946547 29972776527440680753419821)
                ·
                  refine ⟨11239791197790255282532433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29972776527440680753419821 11239791197790255282532433)
                  ·
                    refine ⟨8429843398342691461899325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11239791197790255282532433 8429843398342691461899325)
                    ·
                      refine ⟨3161191274378509298212247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8429843398342691461899325 3161191274378509298212247)
                      ·
                        rfl

theorem cell23_6156398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3].length) (baseStart_6156398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6156398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6156398 prefixEnd_6156398 := by exact prefixLift 6156398
  have htrace : WordTrace (prefixWord ++ tailWord_6156398) baseStart_6156398 baseEnd_6156398 := by
    simpa [prefixWord, tailWord_6156398, baseEnd_6156398] using wordTrace_append hprefix tailTrace_6156398
  have hstable : (prefixWord ++ tailWord_6156398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6156398).length < 2 ^ (prefixWord ++ tailWord_6156398).sum := by decide
  have hdescent : baseEnd_6156398 < baseStart_6156398 := by decide
  rcases family_descends (prefixWord ++ tailWord_6156398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6156445 : List Nat := [1, 4, 2, 1, 1, 3, 2, 3, 2, 1, 3]
def baseStart_6156445 : Nat := 118140960795 + 6156445 * 2 ^ 59
def prefixEnd_6156445 : Nat := 4983230072969 + 3 ^ 40 * 6156445 * 2
def baseEnd_6156445 : Nat := 3161215407969270614324531

theorem tailTrace_6156445 : CollatzResearch.WordTrace tailWord_6156445 prefixEnd_6156445 3161215407969270614324531 := by
  unfold tailWord_6156445
  simp only [CollatzResearch.WordTrace]
  refine ⟨224543996181258676941926789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149695997454172451294617859 224543996181258676941926789)
  ·
    refine ⟨42101999283986001926611273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 224543996181258676941926789 42101999283986001926611273)
    ·
      refine ⟨31576499462989501444958455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42101999283986001926611273 31576499462989501444958455)
      ·
        refine ⟨47364749194484252167437683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31576499462989501444958455 47364749194484252167437683)
        ·
          refine ⟨71047123791726378251156525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47364749194484252167437683 71047123791726378251156525)
          ·
            refine ⟨26642671421897391844183697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71047123791726378251156525 26642671421897391844183697)
            ·
              refine ⟨19982003566423043883137773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26642671421897391844183697 19982003566423043883137773)
              ·
                refine ⟨7493251337408641456176665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19982003566423043883137773 7493251337408641456176665)
                ·
                  refine ⟨5619938503056481092132499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7493251337408641456176665 5619938503056481092132499)
                  ·
                    refine ⟨8429907754584721638198749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5619938503056481092132499 8429907754584721638198749)
                    ·
                      refine ⟨3161215407969270614324531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8429907754584721638198749 3161215407969270614324531)
                      ·
                        rfl

theorem cell23_6156445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 3, 2, 1, 3].length) (baseStart_6156445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6156445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6156445 prefixEnd_6156445 := by exact prefixLift 6156445
  have htrace : WordTrace (prefixWord ++ tailWord_6156445) baseStart_6156445 baseEnd_6156445 := by
    simpa [prefixWord, tailWord_6156445, baseEnd_6156445] using wordTrace_append hprefix tailTrace_6156445
  have hstable : (prefixWord ++ tailWord_6156445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6156445).length < 2 ^ (prefixWord ++ tailWord_6156445).sum := by decide
  have hdescent : baseEnd_6156445 < baseStart_6156445 := by decide
  rcases family_descends (prefixWord ++ tailWord_6156445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6156491 : List Nat := [1, 1, 1, 1, 3, 2, 6, 1, 7]
def baseStart_6156491 : Nat := 118140960795 + 6156491 * 2 ^ 59
def prefixEnd_6156491 : Nat := 4983230072969 + 3 ^ 40 * 6156491 * 2
def baseEnd_6156491 : Nat := 351248780897708603816591

theorem tailTrace_6156491 : CollatzResearch.WordTrace tailWord_6156491 prefixEnd_6156491 351248780897708603816591 := by
  unfold tailWord_6156491
  simp only [CollatzResearch.WordTrace]
  refine ⟨224545673939092026798101327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149697115959394684532067551 224545673939092026798101327)
  ·
    refine ⟨336818510908638040197151991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224545673939092026798101327 336818510908638040197151991)
    ·
      refine ⟨505227766362957060295727987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 336818510908638040197151991 505227766362957060295727987)
      ·
        refine ⟨757841649544435590443591981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 505227766362957060295727987 757841649544435590443591981)
        ·
          refine ⟨284190618579163346416346993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 757841649544435590443591981 284190618579163346416346993)
          ·
            refine ⟨213142963934372509812260245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 284190618579163346416346993 213142963934372509812260245)
            ·
              refine ⟨9991076434423711397449699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 213142963934372509812260245 9991076434423711397449699)
              ·
                refine ⟨14986614651635567096174549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9991076434423711397449699 14986614651635567096174549)
                ·
                  refine ⟨351248780897708603816591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14986614651635567096174549 351248780897708603816591)
                  ·
                    rfl

theorem cell23_6156491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6, 1, 7].length) (baseStart_6156491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6156491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6156491 prefixEnd_6156491 := by exact prefixLift 6156491
  have htrace : WordTrace (prefixWord ++ tailWord_6156491) baseStart_6156491 baseEnd_6156491 := by
    simpa [prefixWord, tailWord_6156491, baseEnd_6156491] using wordTrace_append hprefix tailTrace_6156491
  have hstable : (prefixWord ++ tailWord_6156491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6156491).length < 2 ^ (prefixWord ++ tailWord_6156491).sum := by decide
  have hdescent : baseEnd_6156491 < baseStart_6156491 := by decide
  rcases family_descends (prefixWord ++ tailWord_6156491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6156498 : List Nat := [3, 2, 2, 2, 1, 2, 2, 1, 2, 2, 4]
def baseStart_6156498 : Nat := 118140960795 + 6156498 * 2 ^ 59
def prefixEnd_6156498 : Nat := 4983230072969 + 3 ^ 40 * 6156498 * 2
def baseEnd_6156498 : Nat := 3161242622443958906961787

theorem tailTrace_6156498 : CollatzResearch.WordTrace tailWord_6156498 prefixEnd_6156498 3161242622443958906961787 := by
  unfold tailWord_6156498
  simp only [CollatzResearch.WordTrace]
  refine ⟨56136482312516666748401537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149697286166711111329070765 56136482312516666748401537)
  ·
    refine ⟨42102361734387500061301153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56136482312516666748401537 42102361734387500061301153)
    ·
      refine ⟨31576771300790625045975865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42102361734387500061301153 31576771300790625045975865)
      ·
        refine ⟨23682578475592968784481899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31576771300790625045975865 23682578475592968784481899)
        ·
          refine ⟨35523867713389453176722849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23682578475592968784481899 35523867713389453176722849)
          ·
            refine ⟨26642900785042089882542137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35523867713389453176722849 26642900785042089882542137)
            ·
              refine ⟨19982175588781567411906603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26642900785042089882542137 19982175588781567411906603)
              ·
                refine ⟨29973263383172351117859905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19982175588781567411906603 29973263383172351117859905)
                ·
                  refine ⟨22479947537379263338394929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29973263383172351117859905 22479947537379263338394929)
                  ·
                    refine ⟨16859960653034447503796197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22479947537379263338394929 16859960653034447503796197)
                    ·
                      refine ⟨3161242622443958906961787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16859960653034447503796197 3161242622443958906961787)
                      ·
                        rfl

theorem cell23_6156498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_6156498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6156498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6156498 prefixEnd_6156498 := by exact prefixLift 6156498
  have htrace : WordTrace (prefixWord ++ tailWord_6156498) baseStart_6156498 baseEnd_6156498 := by
    simpa [prefixWord, tailWord_6156498, baseEnd_6156498] using wordTrace_append hprefix tailTrace_6156498
  have hstable : (prefixWord ++ tailWord_6156498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6156498).length < 2 ^ (prefixWord ++ tailWord_6156498).sum := by decide
  have hdescent : baseEnd_6156498 < baseStart_6156498 := by decide
  rcases family_descends (prefixWord ++ tailWord_6156498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6156531 : List Nat := [1, 1, 1, 2, 2, 4, 2, 2, 1, 2, 5]
def baseStart_6156531 : Nat := 118140960795 + 6156531 * 2 ^ 59
def prefixEnd_6156531 : Nat := 4983230072969 + 3 ^ 40 * 6156531 * 2
def baseEnd_6156531 : Nat := 3161259567305557277849135

theorem tailTrace_6156531 : CollatzResearch.WordTrace tailWord_6156531 prefixEnd_6156531 3161259567305557277849135 := by
  unfold tailWord_6156531
  simp only [CollatzResearch.WordTrace]
  refine ⟨224547132858947113629557447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149698088572631409086371631 224547132858947113629557447)
  ·
    refine ⟨336820699288420670444336171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224547132858947113629557447 336820699288420670444336171)
    ·
      refine ⟨505231048932631005666504257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 336820699288420670444336171 505231048932631005666504257)
      ·
        refine ⟨378923286699473254249878193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 505231048932631005666504257 378923286699473254249878193)
        ·
          refine ⟨284192465024604940687408645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 378923286699473254249878193 284192465024604940687408645)
          ·
            refine ⟨53286087192113426378889121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 284192465024604940687408645 53286087192113426378889121)
            ·
              refine ⟨39964565394085069784166841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53286087192113426378889121 39964565394085069784166841)
              ·
                refine ⟨29973424045563802338125131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39964565394085069784166841 29973424045563802338125131)
                ·
                  refine ⟨44960136068345703507187697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29973424045563802338125131 44960136068345703507187697)
                  ·
                    refine ⟨33720102051259277630390773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44960136068345703507187697 33720102051259277630390773)
                    ·
                      refine ⟨3161259567305557277849135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33720102051259277630390773 3161259567305557277849135)
                      ·
                        rfl

theorem cell23_6156531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 2, 1, 2, 5].length) (baseStart_6156531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6156531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6156531 prefixEnd_6156531 := by exact prefixLift 6156531
  have htrace : WordTrace (prefixWord ++ tailWord_6156531) baseStart_6156531 baseEnd_6156531 := by
    simpa [prefixWord, tailWord_6156531, baseEnd_6156531] using wordTrace_append hprefix tailTrace_6156531
  have hstable : (prefixWord ++ tailWord_6156531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6156531).length < 2 ^ (prefixWord ++ tailWord_6156531).sum := by decide
  have hdescent : baseEnd_6156531 < baseStart_6156531 := by decide
  rcases family_descends (prefixWord ++ tailWord_6156531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6156538 : List Nat := [3, 1, 1, 1, 1, 6, 1, 2, 2, 5]
def baseStart_6156538 : Nat := 118140960795 + 6156538 * 2 ^ 59
def prefixEnd_6156538 : Nat := 4983230072969 + 3 ^ 40 * 6156538 * 2
def baseEnd_6156538 : Nat := 1053754387223379583487201

theorem tailTrace_6156538 : CollatzResearch.WordTrace tailWord_6156538 prefixEnd_6156538 1053754387223379583487201 := by
  unfold tailWord_6156538
  simp only [CollatzResearch.WordTrace]
  refine ⟨56136847042480438456265567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149698258779947835883374845 56136847042480438456265567)
  ·
    refine ⟨84205270563720657684398351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56136847042480438456265567 84205270563720657684398351)
    ·
      refine ⟨126307905845580986526597527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84205270563720657684398351 126307905845580986526597527)
      ·
        refine ⟨189461858768371479789896291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126307905845580986526597527 189461858768371479789896291)
        ·
          refine ⟨284192788152557219684844437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189461858768371479789896291 284192788152557219684844437)
          ·
            refine ⟨13321536944651119672727083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 284192788152557219684844437 13321536944651119672727083)
            ·
              refine ⟨19982305416976679509090625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13321536944651119672727083 19982305416976679509090625)
              ·
                refine ⟨14986729062732509631817969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19982305416976679509090625 14986729062732509631817969)
                ·
                  refine ⟨11240046797049382223863477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14986729062732509631817969 11240046797049382223863477)
                  ·
                    refine ⟨1053754387223379583487201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11240046797049382223863477 1053754387223379583487201)
                    ·
                      rfl

theorem cell23_6156538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 2, 2, 5].length) (baseStart_6156538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6156538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6156538 prefixEnd_6156538 := by exact prefixLift 6156538
  have htrace : WordTrace (prefixWord ++ tailWord_6156538) baseStart_6156538 baseEnd_6156538 := by
    simpa [prefixWord, tailWord_6156538, baseEnd_6156538] using wordTrace_append hprefix tailTrace_6156538
  have hstable : (prefixWord ++ tailWord_6156538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6156538).length < 2 ^ (prefixWord ++ tailWord_6156538).sum := by decide
  have hdescent : baseEnd_6156538 < baseStart_6156538 := by decide
  rcases family_descends (prefixWord ++ tailWord_6156538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6156542 : List Nat := [4, 2, 2, 1, 1, 1, 5, 2, 5]
def baseStart_6156542 : Nat := 118140960795 + 6156542 * 2 ^ 59
def prefixEnd_6156542 : Nat := 4983230072969 + 3 ^ 40 * 6156542 * 2
def baseEnd_6156542 : Nat := 351251690621417414979065

theorem tailTrace_6156542 : CollatzResearch.WordTrace tailWord_6156542 prefixEnd_6156542 351251690621417414979065 := by
  unfold tailWord_6156542
  simp only [CollatzResearch.WordTrace]
  refine ⟨28068441757738407813525985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149698356041271508338805253 28068441757738407813525985)
  ·
    refine ⟨21051331318303805860144489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28068441757738407813525985 21051331318303805860144489)
    ·
      refine ⟨15788498488727854395108367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21051331318303805860144489 15788498488727854395108367)
      ·
        refine ⟨23682747733091781592662551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15788498488727854395108367 23682747733091781592662551)
        ·
          refine ⟨35524121599637672388993827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23682747733091781592662551 35524121599637672388993827)
          ·
            refine ⟨53286182399456508583490741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35524121599637672388993827 53286182399456508583490741)
            ·
              refine ⟨4995579599949047679702257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53286182399456508583490741 4995579599949047679702257)
              ·
                refine ⟨3746684699961785759776693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4995579599949047679702257 3746684699961785759776693)
                ·
                  refine ⟨351251690621417414979065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3746684699961785759776693 351251690621417414979065)
                  ·
                    rfl

theorem cell23_6156542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 5, 2, 5].length) (baseStart_6156542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6156542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6156542 prefixEnd_6156542 := by exact prefixLift 6156542
  have htrace : WordTrace (prefixWord ++ tailWord_6156542) baseStart_6156542 baseEnd_6156542 := by
    simpa [prefixWord, tailWord_6156542, baseEnd_6156542] using wordTrace_append hprefix tailTrace_6156542
  have hstable : (prefixWord ++ tailWord_6156542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6156542).length < 2 ^ (prefixWord ++ tailWord_6156542).sum := by decide
  have hdescent : baseEnd_6156542 < baseStart_6156542 := by decide
  rcases family_descends (prefixWord ++ tailWord_6156542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6156558 : List Nat := [4, 1, 1, 2, 1, 2, 1, 2, 4, 1, 4]
def baseStart_6156558 : Nat := 118140960795 + 6156558 * 2 ^ 59
def prefixEnd_6156558 : Nat := 4983230072969 + 3 ^ 40 * 6156558 * 2
def baseEnd_6156558 : Nat := 3161273431283228672211511

theorem tailTrace_6156558 : CollatzResearch.WordTrace tailWord_6156558 prefixEnd_6156558 3161273431283228672211511 := by
  unfold tailWord_6156558
  simp only [CollatzResearch.WordTrace]
  refine ⟨28068514703731162155098791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149698745086566198160526885 28068514703731162155098791)
  ·
    refine ⟨42102772055596743232648187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28068514703731162155098791 42102772055596743232648187)
    ·
      refine ⟨63154158083395114848972281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42102772055596743232648187 63154158083395114848972281)
      ·
        refine ⟨47365618562546336136729211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63154158083395114848972281 47365618562546336136729211)
        ·
          refine ⟨71048427843819504205093817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47365618562546336136729211 71048427843819504205093817)
          ·
            refine ⟨53286320882864628153820363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71048427843819504205093817 53286320882864628153820363)
            ·
              refine ⟨79929481324296942230730545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53286320882864628153820363 79929481324296942230730545)
              ·
                refine ⟨59947110993222706673047909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79929481324296942230730545 59947110993222706673047909)
                ·
                  refine ⟨11240083311229257501196483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59947110993222706673047909 11240083311229257501196483)
                  ·
                    refine ⟨16860124966843886251794725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11240083311229257501196483 16860124966843886251794725)
                    ·
                      refine ⟨3161273431283228672211511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16860124966843886251794725 3161273431283228672211511)
                      ·
                        rfl

theorem cell23_6156558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 2, 4, 1, 4].length) (baseStart_6156558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6156558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6156558 prefixEnd_6156558 := by exact prefixLift 6156558
  have htrace : WordTrace (prefixWord ++ tailWord_6156558) baseStart_6156558 baseEnd_6156558 := by
    simpa [prefixWord, tailWord_6156558, baseEnd_6156558] using wordTrace_append hprefix tailTrace_6156558
  have hstable : (prefixWord ++ tailWord_6156558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6156558).length < 2 ^ (prefixWord ++ tailWord_6156558).sum := by decide
  have hdescent : baseEnd_6156558 < baseStart_6156558 := by decide
  rcases family_descends (prefixWord ++ tailWord_6156558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6156568 : List Nat := [2, 1, 2, 3, 1, 2, 2, 1, 5, 4]
def baseStart_6156568 : Nat := 118140960795 + 6156568 * 2 ^ 59
def prefixEnd_6156568 : Nat := 4983230072969 + 3 ^ 40 * 6156568 * 2
def baseEnd_6156568 : Nat := 1053759522029924544362155

theorem tailTrace_6156568 : CollatzResearch.WordTrace tailWord_6156568 prefixEnd_6156568 1053759522029924544362155 := by
  unfold tailWord_6156568
  simp only [CollatzResearch.WordTrace]
  refine ⟨112274241179906534474327179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149698988239875379299102905 112274241179906534474327179)
  ·
    refine ⟨168411361769859801711490769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112274241179906534474327179 168411361769859801711490769)
    ·
      refine ⟨126308521327394851283618077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168411361769859801711490769 126308521327394851283618077)
      ·
        refine ⟨47365695497773069231356779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126308521327394851283618077 47365695497773069231356779)
        ·
          refine ⟨71048543246659603847035169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47365695497773069231356779 71048543246659603847035169)
          ·
            refine ⟨53286407434994702885276377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71048543246659603847035169 53286407434994702885276377)
            ·
              refine ⟨39964805576246027163957283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53286407434994702885276377 39964805576246027163957283)
              ·
                refine ⟨59947208364369040745935925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39964805576246027163957283 59947208364369040745935925)
                ·
                  refine ⟨5620050784159597569931493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59947208364369040745935925 5620050784159597569931493)
                  ·
                    refine ⟨1053759522029924544362155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5620050784159597569931493 1053759522029924544362155)
                    ·
                      rfl

theorem cell23_6156568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 1, 5, 4].length) (baseStart_6156568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6156568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6156568 prefixEnd_6156568 := by exact prefixLift 6156568
  have htrace : WordTrace (prefixWord ++ tailWord_6156568) baseStart_6156568 baseEnd_6156568 := by
    simpa [prefixWord, tailWord_6156568, baseEnd_6156568] using wordTrace_append hprefix tailTrace_6156568
  have hstable : (prefixWord ++ tailWord_6156568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6156568).length < 2 ^ (prefixWord ++ tailWord_6156568).sum := by decide
  have hdescent : baseEnd_6156568 < baseStart_6156568 := by decide
  rcases family_descends (prefixWord ++ tailWord_6156568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6156571 : List Nat := [1, 1, 1, 1, 1, 1, 6, 1, 2, 4, 4]
def baseStart_6156571 : Nat := 118140960795 + 6156571 * 2 ^ 59
def prefixEnd_6156571 : Nat := 4983230072969 + 3 ^ 40 * 6156571 * 2
def baseEnd_6156571 : Nat := 3161280106531737121348951

theorem tailTrace_6156571 : CollatzResearch.WordTrace tailWord_6156571 prefixEnd_6156571 3161280106531737121348951 := by
  unfold tailWord_6156571
  simp only [CollatzResearch.WordTrace]
  refine ⟨224548591778802200461013567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149699061185868133640675711 224548591778802200461013567)
  ·
    refine ⟨336822887668203300691520351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224548591778802200461013567 336822887668203300691520351)
    ·
      refine ⟨505234331502304951037280527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 336822887668203300691520351 505234331502304951037280527)
      ·
        refine ⟨757851497253457426555920791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 505234331502304951037280527 757851497253457426555920791)
        ·
          refine ⟨1136777245880186139833881187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 757851497253457426555920791 1136777245880186139833881187)
          ·
            refine ⟨1705165868820279209750821781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1136777245880186139833881187 1705165868820279209750821781)
            ·
              refine ⟨79929650100950587957069771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1705165868820279209750821781 79929650100950587957069771)
              ·
                refine ⟨119894475151425881935604657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79929650100950587957069771 119894475151425881935604657)
                ·
                  refine ⟨89920856363569411451703493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 119894475151425881935604657 89920856363569411451703493)
                  ·
                    refine ⟨16860160568169264647194405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 89920856363569411451703493 16860160568169264647194405)
                    ·
                      refine ⟨3161280106531737121348951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16860160568169264647194405 3161280106531737121348951)
                      ·
                        rfl

theorem cell23_6156571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 2, 4, 4].length) (baseStart_6156571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6156571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6156571 prefixEnd_6156571 := by exact prefixLift 6156571
  have htrace : WordTrace (prefixWord ++ tailWord_6156571) baseStart_6156571 baseEnd_6156571 := by
    simpa [prefixWord, tailWord_6156571, baseEnd_6156571] using wordTrace_append hprefix tailTrace_6156571
  have hstable : (prefixWord ++ tailWord_6156571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6156571).length < 2 ^ (prefixWord ++ tailWord_6156571).sum := by decide
  have hdescent : baseEnd_6156571 < baseStart_6156571 := by decide
  rcases family_descends (prefixWord ++ tailWord_6156571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6156575 : List Nat := [1, 1, 2, 4, 3, 2, 2, 1, 2, 1, 4]
def baseStart_6156575 : Nat := 118140960795 + 6156575 * 2 ^ 59
def prefixEnd_6156575 : Nat := 4983230072969 + 3 ^ 40 * 6156575 * 2
def baseEnd_6156575 : Nat := 3161282160454355105698933

theorem tailTrace_6156575 : CollatzResearch.WordTrace tailWord_6156575 prefixEnd_6156575 3161282160454355105698933 := by
  unfold tailWord_6156575
  simp only [CollatzResearch.WordTrace]
  refine ⟨224548737670787709144159179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149699158447191806096106119 224548737670787709144159179)
  ·
    refine ⟨336823106506181563716238769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224548737670787709144159179 336823106506181563716238769)
    ·
      refine ⟨252617329879636172787179077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 336823106506181563716238769 252617329879636172787179077)
      ·
        refine ⟨47365749352431782397596077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 252617329879636172787179077 47365749352431782397596077)
        ·
          refine ⟨17762156007161918399098529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47365749352431782397596077 17762156007161918399098529)
          ·
            refine ⟨13321617005371438799323897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17762156007161918399098529 13321617005371438799323897)
            ·
              refine ⟨9991212754028579099492923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13321617005371438799323897 9991212754028579099492923)
              ·
                refine ⟨14986819131042868649239385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9991212754028579099492923 14986819131042868649239385)
                ·
                  refine ⟨11240114348282151486929539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14986819131042868649239385 11240114348282151486929539)
                  ·
                    refine ⟨16860171522423227230394309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11240114348282151486929539 16860171522423227230394309)
                    ·
                      refine ⟨3161282160454355105698933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16860171522423227230394309 3161282160454355105698933)
                      ·
                        rfl

theorem cell23_6156575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2, 1, 2, 1, 4].length) (baseStart_6156575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6156575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6156575 prefixEnd_6156575 := by exact prefixLift 6156575
  have htrace : WordTrace (prefixWord ++ tailWord_6156575) baseStart_6156575 baseEnd_6156575 := by
    simpa [prefixWord, tailWord_6156575, baseEnd_6156575] using wordTrace_append hprefix tailTrace_6156575
  have hstable : (prefixWord ++ tailWord_6156575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6156575).length < 2 ^ (prefixWord ++ tailWord_6156575).sum := by decide
  have hdescent : baseEnd_6156575 < baseStart_6156575 := by decide
  rcases family_descends (prefixWord ++ tailWord_6156575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6156602 : List Nat := [3, 1, 1, 1, 4, 3, 1, 4, 1, 4]
def baseStart_6156602 : Nat := 118140960795 + 6156602 * 2 ^ 59
def prefixEnd_6156602 : Nat := 4983230072969 + 3 ^ 40 * 6156602 * 2
def baseEnd_6156602 : Nat := 1053765341477342166687103

theorem tailTrace_6156602 : CollatzResearch.WordTrace tailWord_6156602 prefixEnd_6156602 1053765341477342166687103 := by
  unfold tailWord_6156602
  simp only [CollatzResearch.WordTrace]
  refine ⟨56137430610422473188848015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149699814961126595170261373 56137430610422473188848015)
  ·
    refine ⟨84206145915633709783272023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56137430610422473188848015 84206145915633709783272023)
    ·
      refine ⟨126309218873450564674908035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84206145915633709783272023 126309218873450564674908035)
      ·
        refine ⟨189463828310175847012362053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126309218873450564674908035 189463828310175847012362053)
        ·
          refine ⟨35524467808157971314817885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 189463828310175847012362053 35524467808157971314817885)
          ·
            refine ⟨13321675428059239243056707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35524467808157971314817885 13321675428059239243056707)
            ·
              refine ⟨19982513142088858864585061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13321675428059239243056707 19982513142088858864585061)
              ·
                refine ⟨3746721214141661037109699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19982513142088858864585061 3746721214141661037109699)
                ·
                  refine ⟨5620081821212491555664549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3746721214141661037109699 5620081821212491555664549)
                  ·
                    refine ⟨1053765341477342166687103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5620081821212491555664549 1053765341477342166687103)
                    ·
                      rfl

theorem cell23_6156602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 4, 1, 4].length) (baseStart_6156602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6156602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6156602 prefixEnd_6156602 := by exact prefixLift 6156602
  have htrace : WordTrace (prefixWord ++ tailWord_6156602) baseStart_6156602 baseEnd_6156602 := by
    simpa [prefixWord, tailWord_6156602, baseEnd_6156602] using wordTrace_append hprefix tailTrace_6156602
  have hstable : (prefixWord ++ tailWord_6156602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6156602).length < 2 ^ (prefixWord ++ tailWord_6156602).sum := by decide
  have hdescent : baseEnd_6156602 < baseStart_6156602 := by decide
  rcases family_descends (prefixWord ++ tailWord_6156602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6156625 : List Nat := [1, 2, 2, 1, 4, 2, 1, 1, 5, 1, 3]
def baseStart_6156625 : Nat := 118140960795 + 6156625 * 2 ^ 59
def prefixEnd_6156625 : Nat := 4983230072969 + 3 ^ 40 * 6156625 * 2
def baseEnd_6156625 : Nat := 3161307834487079910073703

theorem tailTrace_6156625 : CollatzResearch.WordTrace tailWord_6156625 prefixEnd_6156625 3161307834487079910073703 := by
  unfold tailWord_6156625
  simp only [CollatzResearch.WordTrace]
  refine ⟨224550561320606567683479329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149700374213737711788986219 224550561320606567683479329)
  ·
    refine ⟨168412920990454925762609497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224550561320606567683479329 168412920990454925762609497)
    ·
      refine ⟨126309690742841194321957123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168412920990454925762609497 126309690742841194321957123)
      ·
        refine ⟨189464536114261791482935685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126309690742841194321957123 189464536114261791482935685)
        ·
          refine ⟨35524600521424085903050441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 189464536114261791482935685 35524600521424085903050441)
          ·
            refine ⟨26643450391068064427287831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35524600521424085903050441 26643450391068064427287831)
            ·
              refine ⟨39965175586602096640931747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26643450391068064427287831 39965175586602096640931747)
              ·
                refine ⟨59947763379903144961397621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39965175586602096640931747 59947763379903144961397621)
                ·
                  refine ⟨5620102816865919840131027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59947763379903144961397621 5620102816865919840131027)
                  ·
                    refine ⟨8430154225298879760196541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5620102816865919840131027 8430154225298879760196541)
                    ·
                      refine ⟨3161307834487079910073703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8430154225298879760196541 3161307834487079910073703)
                      ·
                        rfl

theorem cell23_6156625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 1, 5, 1, 3].length) (baseStart_6156625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6156625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6156625 prefixEnd_6156625 := by exact prefixLift 6156625
  have htrace : WordTrace (prefixWord ++ tailWord_6156625) baseStart_6156625 baseEnd_6156625 := by
    simpa [prefixWord, tailWord_6156625, baseEnd_6156625] using wordTrace_append hprefix tailTrace_6156625
  have hstable : (prefixWord ++ tailWord_6156625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6156625).length < 2 ^ (prefixWord ++ tailWord_6156625).sum := by decide
  have hdescent : baseEnd_6156625 < baseStart_6156625 := by decide
  rcases family_descends (prefixWord ++ tailWord_6156625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6156629 : List Nat := [1, 3, 2, 2, 5, 1, 1, 1, 2, 2, 3]
def baseStart_6156629 : Nat := 118140960795 + 6156629 * 2 ^ 59
def prefixEnd_6156629 : Nat := 4983230072969 + 3 ^ 40 * 6156629 * 2
def baseEnd_6156629 : Nat := 3161309888409697894423685

theorem tailTrace_6156629 : CollatzResearch.WordTrace tailWord_6156629 prefixEnd_6156629 3161309888409697894423685 := by
  unfold tailWord_6156629
  simp only [CollatzResearch.WordTrace]
  refine ⟨224550707212592076366624941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149700471475061384244416627 224550707212592076366624941)
  ·
    refine ⟨84206515204722028637484353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 224550707212592076366624941 84206515204722028637484353)
    ·
      refine ⟨63154886403541521478113265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84206515204722028637484353 63154886403541521478113265)
      ·
        refine ⟨47366164802656141108584949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63154886403541521478113265 47366164802656141108584949)
        ·
          refine ⟨4440577950249013228929839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47366164802656141108584949 4440577950249013228929839)
          ·
            refine ⟨6660866925373519843394759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4440577950249013228929839 6660866925373519843394759)
            ·
              refine ⟨9991300388060279765092139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6660866925373519843394759 9991300388060279765092139)
              ·
                refine ⟨14986950582090419647638209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9991300388060279765092139 14986950582090419647638209)
                ·
                  refine ⟨11240212936567814735728657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14986950582090419647638209 11240212936567814735728657)
                  ·
                    refine ⟨8430159702425861051796493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11240212936567814735728657 8430159702425861051796493)
                    ·
                      refine ⟨3161309888409697894423685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8430159702425861051796493 3161309888409697894423685)
                      ·
                        rfl

theorem cell23_6156629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 1, 1, 2, 2, 3].length) (baseStart_6156629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6156629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6156629 prefixEnd_6156629 := by exact prefixLift 6156629
  have htrace : WordTrace (prefixWord ++ tailWord_6156629) baseStart_6156629 baseEnd_6156629 := by
    simpa [prefixWord, tailWord_6156629, baseEnd_6156629] using wordTrace_append hprefix tailTrace_6156629
  have hstable : (prefixWord ++ tailWord_6156629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6156629).length < 2 ^ (prefixWord ++ tailWord_6156629).sum := by decide
  have hdescent : baseEnd_6156629 < baseStart_6156629 := by decide
  rcases family_descends (prefixWord ++ tailWord_6156629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6156636 : List Nat := [2, 2, 4, 3, 1, 1, 2, 3, 1, 4]
def baseStart_6156636 : Nat := 118140960795 + 6156636 * 2 ^ 59
def prefixEnd_6156636 : Nat := 4983230072969 + 3 ^ 40 * 6156636 * 2
def baseEnd_6156636 : Nat := 1053771160924759789012051

theorem tailTrace_6156636 : CollatzResearch.WordTrace tailWord_6156636 prefixEnd_6156636 1053771160924759789012051 := by
  unfold tailWord_6156636
  simp only [CollatzResearch.WordTrace]
  refine ⟨112275481261783358281064881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149700641682377811041419841 112275481261783358281064881)
  ·
    refine ⟨84206610946337518710798661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112275481261783358281064881 84206610946337518710798661)
    ·
      refine ⟨15788739552438284758274749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84206610946337518710798661 15788739552438284758274749)
      ·
        refine ⟨5920777332164356784353031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15788739552438284758274749 5920777332164356784353031)
        ·
          refine ⟨8881165998246535176529547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5920777332164356784353031 8881165998246535176529547)
          ·
            refine ⟨13321748997369802764794321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8881165998246535176529547 13321748997369802764794321)
            ·
              refine ⟨9991311748027352073595741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13321748997369802764794321 9991311748027352073595741)
              ·
                refine ⟨3746741905510257027598403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9991311748027352073595741 3746741905510257027598403)
                ·
                  refine ⟨5620112858265385541397605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3746741905510257027598403 5620112858265385541397605)
                  ·
                    refine ⟨1053771160924759789012051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5620112858265385541397605 1053771160924759789012051)
                    ·
                      rfl

theorem cell23_6156636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 2, 3, 1, 4].length) (baseStart_6156636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6156636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6156636 prefixEnd_6156636 := by exact prefixLift 6156636
  have htrace : WordTrace (prefixWord ++ tailWord_6156636) baseStart_6156636 baseEnd_6156636 := by
    simpa [prefixWord, tailWord_6156636, baseEnd_6156636] using wordTrace_append hprefix tailTrace_6156636
  have hstable : (prefixWord ++ tailWord_6156636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6156636).length < 2 ^ (prefixWord ++ tailWord_6156636).sum := by decide
  have hdescent : baseEnd_6156636 < baseStart_6156636 := by decide
  rcases family_descends (prefixWord ++ tailWord_6156636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6156645 : List Nat := [1, 3, 1, 3, 1, 4, 1, 3, 1, 5]
def baseStart_6156645 : Nat := 118140960795 + 6156645 * 2 ^ 59
def prefixEnd_6156645 : Nat := 4983230072969 + 3 ^ 40 * 6156645 * 2
def baseEnd_6156645 : Nat := 1053772701366723277274537

theorem tailTrace_6156645 : CollatzResearch.WordTrace tailWord_6156645 prefixEnd_6156645 1053772701366723277274537 := by
  unfold tailWord_6156645
  simp only [CollatzResearch.WordTrace]
  refine ⟨224551290780534111099207389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149700860520356074066138259 224551290780534111099207389)
  ·
    refine ⟨84206734042700291662202771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 224551290780534111099207389 84206734042700291662202771)
    ·
      refine ⟨126310101064050437493304157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84206734042700291662202771 126310101064050437493304157)
      ·
        refine ⟨47366287899018914059989059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126310101064050437493304157 47366287899018914059989059)
        ·
          refine ⟨71049431848528371089983589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47366287899018914059989059 71049431848528371089983589)
          ·
            refine ⟨13321768471599069579371923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71049431848528371089983589 13321768471599069579371923)
            ·
              refine ⟨19982652707398604369057885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13321768471599069579371923 19982652707398604369057885)
              ·
                refine ⟨7493494765274476638396707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19982652707398604369057885 7493494765274476638396707)
                ·
                  refine ⟨11240242147911714957595061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7493494765274476638396707 11240242147911714957595061)
                  ·
                    refine ⟨1053772701366723277274537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11240242147911714957595061 1053772701366723277274537)
                    ·
                      rfl

theorem cell23_6156645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 3, 1, 5].length) (baseStart_6156645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6156645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6156645 prefixEnd_6156645 := by exact prefixLift 6156645
  have htrace : WordTrace (prefixWord ++ tailWord_6156645) baseStart_6156645 baseEnd_6156645 := by
    simpa [prefixWord, tailWord_6156645, baseEnd_6156645] using wordTrace_append hprefix tailTrace_6156645
  have hstable : (prefixWord ++ tailWord_6156645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6156645).length < 2 ^ (prefixWord ++ tailWord_6156645).sum := by decide
  have hdescent : baseEnd_6156645 < baseStart_6156645 := by decide
  rcases family_descends (prefixWord ++ tailWord_6156645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6156668 : List Nat := [2, 2, 2, 1, 1, 1, 2, 1, 2, 6, 3]
def baseStart_6156668 : Nat := 118140960795 + 6156668 * 2 ^ 59
def prefixEnd_6156668 : Nat := 4983230072969 + 3 ^ 40 * 6156668 * 2
def baseEnd_6156668 : Nat := 3161329914155223241836005

theorem tailTrace_6156668 : CollatzResearch.WordTrace tailWord_6156668 prefixEnd_6156668 3161329914155223241836005 := by
  unfold tailWord_6156668
  simp only [CollatzResearch.WordTrace]
  refine ⟨112276064829725393013647329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149701419772967190684863105 112276064829725393013647329)
  ·
    refine ⟨84207048622294044760235497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112276064829725393013647329 84207048622294044760235497)
    ·
      refine ⟨63155286466720533570176623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84207048622294044760235497 63155286466720533570176623)
      ·
        refine ⟨94732929700080800355264935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63155286466720533570176623 94732929700080800355264935)
        ·
          refine ⟨142099394550121200532897403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94732929700080800355264935 142099394550121200532897403)
          ·
            refine ⟨213149091825181800799346105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142099394550121200532897403 213149091825181800799346105)
            ·
              refine ⟨159861818868886350599509579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 213149091825181800799346105 159861818868886350599509579)
              ·
                refine ⟨239792728303329525899264369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 159861818868886350599509579 239792728303329525899264369)
                ·
                  refine ⟨179844546227497144424448277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 239792728303329525899264369 179844546227497144424448277)
                  ·
                    refine ⟨8430213104413928644896013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 179844546227497144424448277 8430213104413928644896013)
                    ·
                      refine ⟨3161329914155223241836005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8430213104413928644896013 3161329914155223241836005)
                      ·
                        rfl

theorem cell23_6156668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 2, 6, 3].length) (baseStart_6156668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6156668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6156668 prefixEnd_6156668 := by exact prefixLift 6156668
  have htrace : WordTrace (prefixWord ++ tailWord_6156668) baseStart_6156668 baseEnd_6156668 := by
    simpa [prefixWord, tailWord_6156668, baseEnd_6156668] using wordTrace_append hprefix tailTrace_6156668
  have hstable : (prefixWord ++ tailWord_6156668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6156668).length < 2 ^ (prefixWord ++ tailWord_6156668).sum := by decide
  have hdescent : baseEnd_6156668 < baseStart_6156668 := by decide
  rcases family_descends (prefixWord ++ tailWord_6156668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6156702 : List Nat := [4, 3, 1, 2, 1, 1, 1, 3, 1, 1, 5]
def baseStart_6156702 : Nat := 118140960795 + 6156702 * 2 ^ 59
def prefixEnd_6156702 : Nat := 4983230072969 + 3 ^ 40 * 6156702 * 2
def baseEnd_6156702 : Nat := 3161347372497476108810849

theorem tailTrace_6156702 : CollatzResearch.WordTrace tailWord_6156702 prefixEnd_6156702 3161347372497476108810849 := by
  unfold tailWord_6156702
  simp only [CollatzResearch.WordTrace]
  refine ⟨28069171217665951229254045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149702246494218406556021573 28069171217665951229254045)
  ·
    refine ⟨10525939206624731710970267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28069171217665951229254045 10525939206624731710970267)
    ·
      refine ⟨15788908809937097566455401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10525939206624731710970267 15788908809937097566455401)
      ·
        refine ⟨11841681607452823174841551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15788908809937097566455401 11841681607452823174841551)
        ·
          refine ⟨17762522411179234762262327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11841681607452823174841551 17762522411179234762262327)
          ·
            refine ⟨26643783616768852143393491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17762522411179234762262327 26643783616768852143393491)
            ·
              refine ⟨39965675425153278215090237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26643783616768852143393491 39965675425153278215090237)
              ·
                refine ⟨14987128284432479330658839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39965675425153278215090237 14987128284432479330658839)
                ·
                  refine ⟨22480692426648718995988259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14987128284432479330658839 22480692426648718995988259)
                  ·
                    refine ⟨33721038639973078493982389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22480692426648718995988259 33721038639973078493982389)
                    ·
                      refine ⟨3161347372497476108810849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33721038639973078493982389 3161347372497476108810849)
                      ·
                        rfl

theorem cell23_6156702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_6156702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6156702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6156702 prefixEnd_6156702 := by exact prefixLift 6156702
  have htrace : WordTrace (prefixWord ++ tailWord_6156702) baseStart_6156702 baseEnd_6156702 := by
    simpa [prefixWord, tailWord_6156702, baseEnd_6156702] using wordTrace_append hprefix tailTrace_6156702
  have hstable : (prefixWord ++ tailWord_6156702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6156702).length < 2 ^ (prefixWord ++ tailWord_6156702).sum := by decide
  have hdescent : baseEnd_6156702 < baseStart_6156702 := by decide
  rcases family_descends (prefixWord ++ tailWord_6156702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6156765 : List Nat := [1, 4, 3, 1, 1, 1, 2, 2, 2, 6]
def baseStart_6156765 : Nat := 118140960795 + 6156765 * 2 ^ 59
def prefixEnd_6156765 : Nat := 4983230072969 + 3 ^ 40 * 6156765 * 2
def baseEnd_6156765 : Nat := 1053793240592903120774353

theorem tailTrace_6156765 : CollatzResearch.WordTrace tailWord_6156765 prefixEnd_6156765 1053793240592903120774353 := by
  unfold tailWord_6156765
  simp only [CollatzResearch.WordTrace]
  refine ⟨224555667540099371593575749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149703778360066247729050499 224555667540099371593575749)
  ·
    refine ⟨42104187663768632173795453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 224555667540099371593575749 42104187663768632173795453)
    ·
      refine ⟨15789070373913237065173295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42104187663768632173795453 15789070373913237065173295)
      ·
        refine ⟨23683605560869855597759943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15789070373913237065173295 23683605560869855597759943)
        ·
          refine ⟨35525408341304783396639915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23683605560869855597759943 35525408341304783396639915)
          ·
            refine ⟨53288112511957175094959873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35525408341304783396639915 53288112511957175094959873)
            ·
              refine ⟨39966084383967881321219905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53288112511957175094959873 39966084383967881321219905)
              ·
                refine ⟨29974563287975910990914929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39966084383967881321219905 29974563287975910990914929)
                ·
                  refine ⟨22480922465981933243186197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29974563287975910990914929 22480922465981933243186197)
                  ·
                    refine ⟨1053793240592903120774353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22480922465981933243186197 1053793240592903120774353)
                    ·
                      rfl

theorem cell23_6156765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_6156765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6156765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6156765 prefixEnd_6156765 := by exact prefixLift 6156765
  have htrace : WordTrace (prefixWord ++ tailWord_6156765) baseStart_6156765 baseEnd_6156765 := by
    simpa [prefixWord, tailWord_6156765, baseEnd_6156765] using wordTrace_append hprefix tailTrace_6156765
  have hstable : (prefixWord ++ tailWord_6156765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6156765).length < 2 ^ (prefixWord ++ tailWord_6156765).sum := by decide
  have hdescent : baseEnd_6156765 < baseStart_6156765 := by decide
  rcases family_descends (prefixWord ++ tailWord_6156765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6156775 : List Nat := [1, 1, 5, 2, 1, 1, 1, 1, 1, 6, 3]
def baseStart_6156775 : Nat := 118140960795 + 6156775 * 2 ^ 59
def prefixEnd_6156775 : Nat := 4983230072969 + 3 ^ 40 * 6156775 * 2
def baseEnd_6156775 : Nat := 3161384856585254323198013

theorem tailTrace_6156775 : CollatzResearch.WordTrace tailWord_6156775 prefixEnd_6156775 3161384856585254323198013 := by
  unfold tailWord_6156775
  simp only [CollatzResearch.WordTrace]
  refine ⟨224556032270063143301439779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149704021513375428867626519 224556032270063143301439779)
  ·
    refine ⟨336834048405094714952159669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224556032270063143301439779 336834048405094714952159669)
    ·
      refine ⟨31578192037977629526764969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 336834048405094714952159669 31578192037977629526764969)
      ·
        refine ⟨23683644028483222145073727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31578192037977629526764969 23683644028483222145073727)
        ·
          refine ⟨35525466042724833217610591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23683644028483222145073727 35525466042724833217610591)
          ·
            refine ⟨53288199064087249826415887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35525466042724833217610591 53288199064087249826415887)
            ·
              refine ⟨79932298596130874739623831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53288199064087249826415887 79932298596130874739623831)
              ·
                refine ⟨119898447894196312109435747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79932298596130874739623831 119898447894196312109435747)
                ·
                  refine ⟨179847671841294468164153621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 119898447894196312109435747 179847671841294468164153621)
                  ·
                    refine ⟨8430359617560678195194701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 179847671841294468164153621 8430359617560678195194701)
                    ·
                      refine ⟨3161384856585254323198013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8430359617560678195194701 3161384856585254323198013)
                      ·
                        rfl

theorem cell23_6156775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 6, 3].length) (baseStart_6156775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6156775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6156775 prefixEnd_6156775 := by exact prefixLift 6156775
  have htrace : WordTrace (prefixWord ++ tailWord_6156775) baseStart_6156775 baseEnd_6156775 := by
    simpa [prefixWord, tailWord_6156775, baseEnd_6156775] using wordTrace_append hprefix tailTrace_6156775
  have hstable : (prefixWord ++ tailWord_6156775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6156775).length < 2 ^ (prefixWord ++ tailWord_6156775).sum := by decide
  have hdescent : baseEnd_6156775 < baseStart_6156775 := by decide
  rcases family_descends (prefixWord ++ tailWord_6156775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6156785 : List Nat := [1, 2, 2, 2, 3, 1, 3, 1, 2, 2, 4]
def baseStart_6156785 : Nat := 118140960795 + 6156785 * 2 ^ 59
def prefixEnd_6156785 : Nat := 4983230072969 + 3 ^ 40 * 6156785 * 2
def baseEnd_6156785 : Nat := 3161389991391799284072967

theorem tailTrace_6156785 : CollatzResearch.WordTrace tailWord_6156785 prefixEnd_6156785 3161389991391799284072967 := by
  unfold tailWord_6156785
  simp only [CollatzResearch.WordTrace]
  refine ⟨224556397000026915009303809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149704264666684610006202539 224556397000026915009303809)
  ·
    refine ⟨168417297750020186256977857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224556397000026915009303809 168417297750020186256977857)
    ·
      refine ⟨126312973312515139692733393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168417297750020186256977857 126312973312515139692733393)
      ·
        refine ⟨94734729984386354769550045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126312973312515139692733393 94734729984386354769550045)
        ·
          refine ⟨35525523744144883038581267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94734729984386354769550045 35525523744144883038581267)
          ·
            refine ⟨53288285616217324557871901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35525523744144883038581267 53288285616217324557871901)
            ·
              refine ⟨19983107106081496709201963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53288285616217324557871901 19983107106081496709201963)
              ·
                refine ⟨29974660659122245063802945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19983107106081496709201963 29974660659122245063802945)
                ·
                  refine ⟨22480995494341683797852209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29974660659122245063802945 22480995494341683797852209)
                  ·
                    refine ⟨16860746620756262848389157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22480995494341683797852209 16860746620756262848389157)
                    ·
                      refine ⟨3161389991391799284072967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16860746620756262848389157 3161389991391799284072967)
                      ·
                        rfl

theorem cell23_6156785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 1, 2, 2, 4].length) (baseStart_6156785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6156785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6156785 prefixEnd_6156785 := by exact prefixLift 6156785
  have htrace : WordTrace (prefixWord ++ tailWord_6156785) baseStart_6156785 baseEnd_6156785 := by
    simpa [prefixWord, tailWord_6156785, baseEnd_6156785] using wordTrace_append hprefix tailTrace_6156785
  have hstable : (prefixWord ++ tailWord_6156785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6156785).length < 2 ^ (prefixWord ++ tailWord_6156785).sum := by decide
  have hdescent : baseEnd_6156785 < baseStart_6156785 := by decide
  rcases family_descends (prefixWord ++ tailWord_6156785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6156812 : List Nat := [2, 2, 1, 2, 4, 1, 1, 5, 5]
def baseStart_6156812 : Nat := 118140960795 + 6156812 * 2 ^ 59
def prefixEnd_6156812 : Nat := 4983230072969 + 3 ^ 40 * 6156812 * 2
def baseEnd_6156812 : Nat := 351267095041052297603927

theorem tailTrace_6156812 : CollatzResearch.WordTrace tailWord_6156812 prefixEnd_6156812 351267095041052297603927 := by
  unfold tailWord_6156812
  simp only [CollatzResearch.WordTrace]
  refine ⟨112278690885464549310268345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149704921180619399080357793 112278690885464549310268345)
  ·
    refine ⟨84209018164098411982701259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112278690885464549310268345 84209018164098411982701259)
    ·
      refine ⟨126313527246147617974051889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84209018164098411982701259 126313527246147617974051889)
      ·
        refine ⟨94735145434610713480538917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126313527246147617974051889 94735145434610713480538917)
        ·
          refine ⟨17762839768989508777601047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94735145434610713480538917 17762839768989508777601047)
          ·
            refine ⟨26644259653484263166401571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17762839768989508777601047 26644259653484263166401571)
            ·
              refine ⟨39966389480226394749602357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26644259653484263166401571 39966389480226394749602357)
              ·
                refine ⟨3746849013771224507775221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39966389480226394749602357 3746849013771224507775221)
                ·
                  refine ⟨351267095041052297603927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3746849013771224507775221 351267095041052297603927)
                  ·
                    rfl

theorem cell23_6156812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 5, 5].length) (baseStart_6156812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6156812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6156812 prefixEnd_6156812 := by exact prefixLift 6156812
  have htrace : WordTrace (prefixWord ++ tailWord_6156812) baseStart_6156812 baseEnd_6156812 := by
    simpa [prefixWord, tailWord_6156812, baseEnd_6156812] using wordTrace_append hprefix tailTrace_6156812
  have hstable : (prefixWord ++ tailWord_6156812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6156812).length < 2 ^ (prefixWord ++ tailWord_6156812).sum := by decide
  have hdescent : baseEnd_6156812 < baseStart_6156812 := by decide
  rcases family_descends (prefixWord ++ tailWord_6156812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6156885 : List Nat := [1, 3, 2, 2, 1, 1, 4, 1, 8]
def baseStart_6156885 : Nat := 118140960795 + 6156885 * 2 ^ 59
def prefixEnd_6156885 : Nat := 4983230072969 + 3 ^ 40 * 6156885 * 2
def baseEnd_6156885 : Nat := 351271259939694321424723

theorem tailTrace_6156885 : CollatzResearch.WordTrace tailWord_6156885 prefixEnd_6156885 351271259939694321424723 := by
  unfold tailWord_6156885
  simp only [CollatzResearch.WordTrace]
  refine ⟨224560044299664632087944109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149706696199776421391962739 224560044299664632087944109)
  ·
    refine ⟨84210016612374237032979041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 224560044299664632087944109 84210016612374237032979041)
    ·
      refine ⟨63157512459280677774734281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84210016612374237032979041 63157512459280677774734281)
      ·
        refine ⟨47368134344460508331050711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63157512459280677774734281 47368134344460508331050711)
        ·
          refine ⟨71052201516690762496576067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47368134344460508331050711 71052201516690762496576067)
          ·
            refine ⟨106578302275036143744864101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71052201516690762496576067 106578302275036143744864101)
            ·
              refine ⟨19983431676569276952162019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 106578302275036143744864101 19983431676569276952162019)
              ·
                refine ⟨29975147514853915428243029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19983431676569276952162019 29975147514853915428243029)
                ·
                  refine ⟨351271259939694321424723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29975147514853915428243029 351271259939694321424723)
                  ·
                    rfl

theorem cell23_6156885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 1, 8].length) (baseStart_6156885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6156885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6156885 prefixEnd_6156885 := by exact prefixLift 6156885
  have htrace : WordTrace (prefixWord ++ tailWord_6156885) baseStart_6156885 baseEnd_6156885 := by
    simpa [prefixWord, tailWord_6156885, baseEnd_6156885] using wordTrace_append hprefix tailTrace_6156885
  have hstable : (prefixWord ++ tailWord_6156885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6156885).length < 2 ^ (prefixWord ++ tailWord_6156885).sum := by decide
  have hdescent : baseEnd_6156885 < baseStart_6156885 := by decide
  rcases family_descends (prefixWord ++ tailWord_6156885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6156922 : List Nat := [3, 1, 1, 1, 1, 1, 1, 2, 5, 5, 2]
def baseStart_6156922 : Nat := 118140960795 + 6156922 * 2 ^ 59
def prefixEnd_6156922 : Nat := 4983230072969 + 3 ^ 40 * 6156922 * 2
def baseEnd_6156922 : Nat := 3161460338241465248059837

theorem tailTrace_6156922 : CollatzResearch.WordTrace tailWord_6156922 prefixEnd_6156922 3161460338241465248059837 := by
  unfold tailWord_6156922
  simp only [CollatzResearch.WordTrace]
  refine ⟨56140348450132646851760255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149707595867020391604694013 56140348450132646851760255)
  ·
    refine ⟨84210522675198970277640383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56140348450132646851760255 84210522675198970277640383)
    ·
      refine ⟨126315784012798455416460575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84210522675198970277640383 126315784012798455416460575)
      ·
        refine ⟨189473676019197683124690863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126315784012798455416460575 189473676019197683124690863)
        ·
          refine ⟨284210514028796524687036295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189473676019197683124690863 284210514028796524687036295)
          ·
            refine ⟨426315771043194787030554443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 284210514028796524687036295 426315771043194787030554443)
            ·
              refine ⟨639473656564792180545831665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 426315771043194787030554443 639473656564792180545831665)
              ·
                refine ⟨479605242423594135409373749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 639473656564792180545831665 479605242423594135409373749)
                ·
                  refine ⟨44962991477211950194628789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 479605242423594135409373749 44962991477211950194628789)
                  ·
                    refine ⟨4215280450988620330746449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44962991477211950194628789 4215280450988620330746449)
                    ·
                      refine ⟨3161460338241465248059837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4215280450988620330746449 3161460338241465248059837)
                      ·
                        rfl

theorem cell23_6156922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 5, 5, 2].length) (baseStart_6156922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6156922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6156922 prefixEnd_6156922 := by exact prefixLift 6156922
  have htrace : WordTrace (prefixWord ++ tailWord_6156922) baseStart_6156922 baseEnd_6156922 := by
    simpa [prefixWord, tailWord_6156922, baseEnd_6156922] using wordTrace_append hprefix tailTrace_6156922
  have hstable : (prefixWord ++ tailWord_6156922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6156922).length < 2 ^ (prefixWord ++ tailWord_6156922).sum := by decide
  have hdescent : baseEnd_6156922 < baseStart_6156922 := by decide
  rcases family_descends (prefixWord ++ tailWord_6156922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
