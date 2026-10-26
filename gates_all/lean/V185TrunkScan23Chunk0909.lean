import V185TrunkScan23Chunk0908

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5380764 : List Nat := [2, 2, 3, 2, 2, 3, 1, 2, 1, 5]
def baseStart_5380764 : Nat := 118140960795 + 5380764 * 2 ^ 59
def prefixEnd_5380764 : Nat := 4983230072969 + 3 ^ 40 * 5380764 * 2
def baseEnd_5380764 : Nat := 920972740136363656601441

theorem tailTrace_5380764 : CollatzResearch.WordTrace tailWord_5380764 prefixEnd_5380764 920972740136363656601441 := by
  unfold tailWord_5380764
  simp only [CollatzResearch.WordTrace]
  refine ⟨98126292939209232087030673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130835057252278976116040897 98126292939209232087030673)
  ·
    refine ⟨73594719704406924065273005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98126292939209232087030673 73594719704406924065273005)
    ·
      refine ⟨27598019889152596524477377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73594719704406924065273005 27598019889152596524477377)
      ·
        refine ⟨20698514916864447393358033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27598019889152596524477377 20698514916864447393358033)
        ·
          refine ⟨15523886187648335545018525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20698514916864447393358033 15523886187648335545018525)
          ·
            refine ⟨5821457320368125829381947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15523886187648335545018525 5821457320368125829381947)
            ·
              refine ⟨8732185980552188744072921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5821457320368125829381947 8732185980552188744072921)
              ·
                refine ⟨6549139485414141558054691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8732185980552188744072921 6549139485414141558054691)
                ·
                  refine ⟨9823709228121212337082037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6549139485414141558054691 9823709228121212337082037)
                  ·
                    refine ⟨920972740136363656601441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9823709228121212337082037 920972740136363656601441)
                    ·
                      rfl

theorem cell23_5380764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 1, 2, 1, 5].length) (baseStart_5380764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5380764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5380764 prefixEnd_5380764 := by exact prefixLift 5380764
  have htrace : WordTrace (prefixWord ++ tailWord_5380764) baseStart_5380764 baseEnd_5380764 := by
    simpa [prefixWord, tailWord_5380764, baseEnd_5380764] using wordTrace_append hprefix tailTrace_5380764
  have hstable : (prefixWord ++ tailWord_5380764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5380764).length < 2 ^ (prefixWord ++ tailWord_5380764).sum := by decide
  have hdescent : baseEnd_5380764 < baseStart_5380764 := by decide
  rcases family_descends (prefixWord ++ tailWord_5380764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5380787 : List Nat := [1, 1, 1, 2, 3, 6, 1, 1, 1, 1, 5]
def baseStart_5380787 : Nat := 118140960795 + 5380787 * 2 ^ 59
def prefixEnd_5380787 : Nat := 4983230072969 + 3 ^ 40 * 5380787 * 2
def baseEnd_5380787 : Nat := 2762930030464144379816717

theorem tailTrace_5380787 : CollatzResearch.WordTrace tailWord_5380787 prefixEnd_5380787 2762930030464144379816717 := by
  unfold tailWord_5380787
  simp only [CollatzResearch.WordTrace]
  refine ⟨196253424757335139102148615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130835616504890092734765743 196253424757335139102148615)
  ·
    refine ⟨294380137136002708653222923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196253424757335139102148615 294380137136002708653222923)
    ·
      refine ⟨441570205704004062979834385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294380137136002708653222923 441570205704004062979834385)
      ·
        refine ⟨331177654278003047234875789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 441570205704004062979834385 331177654278003047234875789)
        ·
          refine ⟨124191620354251142713078421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 331177654278003047234875789 124191620354251142713078421)
          ·
            refine ⟨5821482204105522314675551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 124191620354251142713078421 5821482204105522314675551)
            ·
              refine ⟨8732223306158283472013327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5821482204105522314675551 8732223306158283472013327)
              ·
                refine ⟨13098334959237425208019991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8732223306158283472013327 13098334959237425208019991)
                ·
                  refine ⟨19647502438856137812029987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13098334959237425208019991 19647502438856137812029987)
                  ·
                    refine ⟨29471253658284206718044981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19647502438856137812029987 29471253658284206718044981)
                    ·
                      refine ⟨2762930030464144379816717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29471253658284206718044981 2762930030464144379816717)
                      ·
                        rfl

theorem cell23_5380787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 1, 1, 1, 1, 5].length) (baseStart_5380787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5380787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5380787 prefixEnd_5380787 := by exact prefixLift 5380787
  have htrace : WordTrace (prefixWord ++ tailWord_5380787) baseStart_5380787 baseEnd_5380787 := by
    simpa [prefixWord, tailWord_5380787, baseEnd_5380787] using wordTrace_append hprefix tailTrace_5380787
  have hstable : (prefixWord ++ tailWord_5380787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5380787).length < 2 ^ (prefixWord ++ tailWord_5380787).sum := by decide
  have hdescent : baseEnd_5380787 < baseStart_5380787 := by decide
  rcases family_descends (prefixWord ++ tailWord_5380787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5380817 : List Nat := [1, 2, 2, 1, 2, 3, 4, 1, 1, 3, 3]
def baseStart_5380817 : Nat := 118140960795 + 5380817 * 2 ^ 59
def prefixEnd_5380817 : Nat := 4983230072969 + 3 ^ 40 * 5380817 * 2
def baseEnd_5380817 : Nat := 2762945434883779262441579

theorem tailTrace_5380817 : CollatzResearch.WordTrace tailWord_5380817 prefixEnd_5380817 2762945434883779262441579 := by
  unfold tailWord_5380817
  simp only [CollatzResearch.WordTrace]
  refine ⟨196254518947226454225740705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130836345964817636150493803 196254518947226454225740705)
  ·
    refine ⟨147190889210419840669305529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196254518947226454225740705 147190889210419840669305529)
    ·
      refine ⟨110393166907814880501979147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147190889210419840669305529 110393166907814880501979147)
      ·
        refine ⟨165589750361722320752968721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110393166907814880501979147 165589750361722320752968721)
        ·
          refine ⟨124192312771291740564726541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165589750361722320752968721 124192312771291740564726541)
          ·
            refine ⟨46572117289234402711772453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 124192312771291740564726541 46572117289234402711772453)
            ·
              refine ⟨8732271991731450508457335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46572117289234402711772453 8732271991731450508457335)
              ·
                refine ⟨13098407987597175762686003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8732271991731450508457335 13098407987597175762686003)
                ·
                  refine ⟨19647611981395763644029005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13098407987597175762686003 19647611981395763644029005)
                  ·
                    refine ⟨7367854493023411366510877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19647611981395763644029005 7367854493023411366510877)
                    ·
                      refine ⟨2762945434883779262441579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7367854493023411366510877 2762945434883779262441579)
                      ·
                        rfl

theorem cell23_5380817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4, 1, 1, 3, 3].length) (baseStart_5380817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5380817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5380817 prefixEnd_5380817 := by exact prefixLift 5380817
  have htrace : WordTrace (prefixWord ++ tailWord_5380817) baseStart_5380817 baseEnd_5380817 := by
    simpa [prefixWord, tailWord_5380817, baseEnd_5380817] using wordTrace_append hprefix tailTrace_5380817
  have hstable : (prefixWord ++ tailWord_5380817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5380817).length < 2 ^ (prefixWord ++ tailWord_5380817).sum := by decide
  have hdescent : baseEnd_5380817 < baseStart_5380817 := by decide
  rcases family_descends (prefixWord ++ tailWord_5380817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5380857 : List Nat := [1, 2, 1, 3, 1, 1, 1, 4, 3, 4, 2]
def baseStart_5380857 : Nat := 118140960795 + 5380857 * 2 ^ 59
def prefixEnd_5380857 : Nat := 4983230072969 + 3 ^ 40 * 5380857 * 2
def baseEnd_5380857 : Nat := 2762965974109959105941395

theorem tailTrace_5380857 : CollatzResearch.WordTrace tailWord_5380857 prefixEnd_5380857 2762965974109959105941395 := by
  unfold tailWord_5380857
  simp only [CollatzResearch.WordTrace]
  refine ⟨196255977867081541057196825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130837318578054360704797883 196255977867081541057196825)
  ·
    refine ⟨147191983400311155792897619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196255977867081541057196825 147191983400311155792897619)
    ·
      refine ⟨220787975100466733689346429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147191983400311155792897619 220787975100466733689346429)
      ·
        refine ⟨82795490662675025133504911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 220787975100466733689346429 82795490662675025133504911)
        ·
          refine ⟨124193235994012537700257367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82795490662675025133504911 124193235994012537700257367)
          ·
            refine ⟨186289853991018806550386051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124193235994012537700257367 186289853991018806550386051)
            ·
              refine ⟨279434780986528209825579077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 186289853991018806550386051 279434780986528209825579077)
              ·
                refine ⟨52394021434974039342296077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 279434780986528209825579077 52394021434974039342296077)
                ·
                  refine ⟨19647758038115264753361029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52394021434974039342296077 19647758038115264753361029)
                  ·
                    refine ⟨3683954632146612141255193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19647758038115264753361029 3683954632146612141255193)
                    ·
                      refine ⟨2762965974109959105941395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3683954632146612141255193 2762965974109959105941395)
                      ·
                        rfl

theorem cell23_5380857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 4, 3, 4, 2].length) (baseStart_5380857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5380857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5380857 prefixEnd_5380857 := by exact prefixLift 5380857
  have htrace : WordTrace (prefixWord ++ tailWord_5380857) baseStart_5380857 baseEnd_5380857 := by
    simpa [prefixWord, tailWord_5380857, baseEnd_5380857] using wordTrace_append hprefix tailTrace_5380857
  have hstable : (prefixWord ++ tailWord_5380857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5380857).length < 2 ^ (prefixWord ++ tailWord_5380857).sum := by decide
  have hdescent : baseEnd_5380857 < baseStart_5380857 := by decide
  rcases family_descends (prefixWord ++ tailWord_5380857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5380964 : List Nat := [2, 3, 1, 1, 4, 1, 2, 2, 2, 1, 4]
def baseStart_5380964 : Nat := 118140960795 + 5380964 * 2 ^ 59
def prefixEnd_5380964 : Nat := 4983230072969 + 3 ^ 40 * 5380964 * 2
def baseEnd_5380964 : Nat := 2763020916539990187303403

theorem tailTrace_5380964 : CollatzResearch.WordTrace tailWord_5380964 prefixEnd_5380964 2763020916539990187303403 := by
  unfold tailWord_5380964
  simp only [CollatzResearch.WordTrace]
  refine ⟨98129940238846949165670973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130839920318462598887561297 98129940238846949165670973)
  ·
    refine ⟨36798727589567605937126615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98129940238846949165670973 36798727589567605937126615)
    ·
      refine ⟨55198091384351408905689923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36798727589567605937126615 55198091384351408905689923)
      ·
        refine ⟨82797137076527113358534885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55198091384351408905689923 82797137076527113358534885)
        ·
          refine ⟨15524463201848833754725291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82797137076527113358534885 15524463201848833754725291)
          ·
            refine ⟨23286694802773250632087937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15524463201848833754725291 23286694802773250632087937)
            ·
              refine ⟨17465021102079937974065953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23286694802773250632087937 17465021102079937974065953)
              ·
                refine ⟨13098765826559953480549465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17465021102079937974065953 13098765826559953480549465)
                ·
                  refine ⟨9824074369919965110412099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13098765826559953480549465 9824074369919965110412099)
                  ·
                    refine ⟨14736111554879947665618149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9824074369919965110412099 14736111554879947665618149)
                    ·
                      refine ⟨2763020916539990187303403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14736111554879947665618149 2763020916539990187303403)
                      ·
                        rfl

theorem cell23_5380964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 2, 2, 1, 4].length) (baseStart_5380964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5380964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5380964 prefixEnd_5380964 := by exact prefixLift 5380964
  have htrace : WordTrace (prefixWord ++ tailWord_5380964) baseStart_5380964 baseEnd_5380964 := by
    simpa [prefixWord, tailWord_5380964, baseEnd_5380964] using wordTrace_append hprefix tailTrace_5380964
  have hstable : (prefixWord ++ tailWord_5380964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5380964).length < 2 ^ (prefixWord ++ tailWord_5380964).sum := by decide
  have hdescent : baseEnd_5380964 < baseStart_5380964 := by decide
  rcases family_descends (prefixWord ++ tailWord_5380964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5380981 : List Nat := [1, 3, 4, 1, 1, 3, 1, 1, 2, 4, 2]
def baseStart_5380981 : Nat := 118140960795 + 5380981 * 2 ^ 59
def prefixEnd_5380981 : Nat := 4983230072969 + 3 ^ 40 * 5380981 * 2
def baseEnd_5380981 : Nat := 2763029645711116620790825

theorem tailTrace_5380981 : CollatzResearch.WordTrace tailWord_5380981 prefixEnd_5380981 2763029645711116620790825 := by
  unfold tailWord_5380981
  simp only [CollatzResearch.WordTrace]
  refine ⟨196260500518632310234710797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130840333679088206823140531 196260500518632310234710797)
  ·
    refine ⟨73597687694487116338016549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 196260500518632310234710797 73597687694487116338016549)
    ·
      refine ⟨13799566442716334313378103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73597687694487116338016549 13799566442716334313378103)
      ·
        refine ⟨20699349664074501470067155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13799566442716334313378103 20699349664074501470067155)
        ·
          refine ⟨31049024496111752205100733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20699349664074501470067155 31049024496111752205100733)
          ·
            refine ⟨11643384186041907076912775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31049024496111752205100733 11643384186041907076912775)
            ·
              refine ⟨17465076279062860615369163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11643384186041907076912775 17465076279062860615369163)
              ·
                refine ⟨26197614418594290923053745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17465076279062860615369163 26197614418594290923053745)
                ·
                  refine ⟨19648210813945718192290309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26197614418594290923053745 19648210813945718192290309)
                  ·
                    refine ⟨3684039527614822161054433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19648210813945718192290309 3684039527614822161054433)
                    ·
                      refine ⟨2763029645711116620790825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3684039527614822161054433 2763029645711116620790825)
                      ·
                        rfl

theorem cell23_5380981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 1, 2, 4, 2].length) (baseStart_5380981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5380981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5380981 prefixEnd_5380981 := by exact prefixLift 5380981
  have htrace : WordTrace (prefixWord ++ tailWord_5380981) baseStart_5380981 baseEnd_5380981 := by
    simpa [prefixWord, tailWord_5380981, baseEnd_5380981] using wordTrace_append hprefix tailTrace_5380981
  have hstable : (prefixWord ++ tailWord_5380981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5380981).length < 2 ^ (prefixWord ++ tailWord_5380981).sum := by decide
  have hdescent : baseEnd_5380981 < baseStart_5380981 := by decide
  rcases family_descends (prefixWord ++ tailWord_5380981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5380987 : List Nat := [1, 1, 1, 1, 1, 5, 4, 3, 6]
def baseStart_5380987 : Nat := 118140960795 + 5380987 * 2 ^ 59
def prefixEnd_5380987 : Nat := 4983230072969 + 3 ^ 40 * 5380987 * 2
def baseEnd_5380987 : Nat := 307003636288338177479533

theorem tailTrace_5380987 : CollatzResearch.WordTrace tailWord_5380987 prefixEnd_5380987 307003636288338177479533 := by
  unfold tailWord_5380987
  simp only [CollatzResearch.WordTrace]
  refine ⟨196260719356610573259429215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130840479571073715506286143 196260719356610573259429215)
  ·
    refine ⟨294391079034915859889143823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196260719356610573259429215 294391079034915859889143823)
    ·
      refine ⟨441586618552373789833715735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294391079034915859889143823 441586618552373789833715735)
      ·
        refine ⟨662379927828560684750573603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 441586618552373789833715735 662379927828560684750573603)
        ·
          refine ⟨993569891742841027125860405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 662379927828560684750573603 993569891742841027125860405)
          ·
            refine ⟨93147177350891346293049413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 993569891742841027125860405 93147177350891346293049413)
            ·
              refine ⟨17465095753292127429946765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 93147177350891346293049413 17465095753292127429946765)
              ·
                refine ⟨6549410907484547786230037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17465095753292127429946765 6549410907484547786230037)
                ·
                  refine ⟨307003636288338177479533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6549410907484547786230037 307003636288338177479533)
                  ·
                    rfl

theorem cell23_5380987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 3, 6].length) (baseStart_5380987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5380987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5380987 prefixEnd_5380987 := by exact prefixLift 5380987
  have htrace : WordTrace (prefixWord ++ tailWord_5380987) baseStart_5380987 baseEnd_5380987 := by
    simpa [prefixWord, tailWord_5380987, baseEnd_5380987] using wordTrace_append hprefix tailTrace_5380987
  have hstable : (prefixWord ++ tailWord_5380987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5380987).length < 2 ^ (prefixWord ++ tailWord_5380987).sum := by decide
  have hdescent : baseEnd_5380987 < baseStart_5380987 := by decide
  rcases family_descends (prefixWord ++ tailWord_5380987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5381001 : List Nat := [1, 2, 1, 1, 5, 4, 1, 1, 2, 2, 3]
def baseStart_5381001 : Nat := 118140960795 + 5381001 * 2 ^ 59
def prefixEnd_5381001 : Nat := 4983230072969 + 3 ^ 40 * 5381001 * 2
def baseEnd_5381001 : Nat := 2763039915324206542540733

theorem tailTrace_5381001 : CollatzResearch.WordTrace tailWord_5381001 prefixEnd_5381001 2763039915324206542540733 := by
  unfold tailWord_5381001
  simp only [CollatzResearch.WordTrace]
  refine ⟨196261229978559853650438857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130840819985706569100292571 196261229978559853650438857)
  ·
    refine ⟨147195922483919890237829143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196261229978559853650438857 147195922483919890237829143)
    ·
      refine ⟨220793883725879835356743715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147195922483919890237829143 220793883725879835356743715)
      ·
        refine ⟨331190825588819753035115573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220793883725879835356743715 331190825588819753035115573)
        ·
          refine ⟨31049139898951851847042085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 331190825588819753035115573 31049139898951851847042085)
          ·
            refine ⟨5821713731053472221320391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31049139898951851847042085 5821713731053472221320391)
            ·
              refine ⟨8732570596580208331980587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5821713731053472221320391 8732570596580208331980587)
              ·
                refine ⟨13098855894870312497970881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8732570596580208331980587 13098855894870312497970881)
                ·
                  refine ⟨9824141921152734373478161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13098855894870312497970881 9824141921152734373478161)
                  ·
                    refine ⟨7368106440864550780108621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9824141921152734373478161 7368106440864550780108621)
                    ·
                      refine ⟨2763039915324206542540733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7368106440864550780108621 2763039915324206542540733)
                      ·
                        rfl

theorem cell23_5381001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 1, 1, 2, 2, 3].length) (baseStart_5381001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5381001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5381001 prefixEnd_5381001 := by exact prefixLift 5381001
  have htrace : WordTrace (prefixWord ++ tailWord_5381001) baseStart_5381001 baseEnd_5381001 := by
    simpa [prefixWord, tailWord_5381001, baseEnd_5381001] using wordTrace_append hprefix tailTrace_5381001
  have hstable : (prefixWord ++ tailWord_5381001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5381001).length < 2 ^ (prefixWord ++ tailWord_5381001).sum := by decide
  have hdescent : baseEnd_5381001 < baseStart_5381001 := by decide
  rcases family_descends (prefixWord ++ tailWord_5381001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5381098 : List Nat := [3, 1, 3, 1, 2, 2, 4, 1, 2, 4]
def baseStart_5381098 : Nat := 118140960795 + 5381098 * 2 ^ 59
def prefixEnd_5381098 : Nat := 4983230072969 + 3 ^ 40 * 5381098 * 2
def baseEnd_5381098 : Nat := 921029907649230887675929

theorem tailTrace_5381098 : CollatzResearch.WordTrace tailWord_5381098 prefixEnd_5381098 921029907649230887675929 := by
  unfold tailWord_5381098
  simp only [CollatzResearch.WordTrace]
  refine ⟨49066191964802109804179987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130843178572805626144479965 49066191964802109804179987)
  ·
    refine ⟨73599287947203164706269981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49066191964802109804179987 73599287947203164706269981)
    ·
      refine ⟨27599732980201186764851243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73599287947203164706269981 27599732980201186764851243)
      ·
        refine ⟨41399599470301780147276865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27599732980201186764851243 41399599470301780147276865)
        ·
          refine ⟨31049699602726335110457649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41399599470301780147276865 31049699602726335110457649)
          ·
            refine ⟨23287274702044751332843237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31049699602726335110457649 23287274702044751332843237)
            ·
              refine ⟨4366364006633390874908107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23287274702044751332843237 4366364006633390874908107)
              ·
                refine ⟨6549546009950086312362161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4366364006633390874908107 6549546009950086312362161)
                ·
                  refine ⟨4912159507462564734271621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6549546009950086312362161 4912159507462564734271621)
                  ·
                    refine ⟨921029907649230887675929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4912159507462564734271621 921029907649230887675929)
                    ·
                      rfl

theorem cell23_5381098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 4, 1, 2, 4].length) (baseStart_5381098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5381098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5381098 prefixEnd_5381098 := by exact prefixLift 5381098
  have htrace : WordTrace (prefixWord ++ tailWord_5381098) baseStart_5381098 baseEnd_5381098 := by
    simpa [prefixWord, tailWord_5381098, baseEnd_5381098] using wordTrace_append hprefix tailTrace_5381098
  have hstable : (prefixWord ++ tailWord_5381098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5381098).length < 2 ^ (prefixWord ++ tailWord_5381098).sum := by decide
  have hdescent : baseEnd_5381098 < baseStart_5381098 := by decide
  rcases family_descends (prefixWord ++ tailWord_5381098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5381104 : List Nat := [2, 1, 1, 1, 3, 2, 1, 5, 1, 3, 3]
def baseStart_5381104 : Nat := 118140960795 + 5381104 * 2 ^ 59
def prefixEnd_5381104 : Nat := 4983230072969 + 3 ^ 40 * 5381104 * 2
def baseEnd_5381104 : Nat := 2763092803831619639552759

theorem tailTrace_5381104 : CollatzResearch.WordTrace tailWord_5381104 prefixEnd_5381104 2763092803831619639552759 := by
  unfold tailWord_5381104
  simp only [CollatzResearch.WordTrace]
  refine ⟨98132493348593351120719183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130843324464791134827625577 98132493348593351120719183)
  ·
    refine ⟨147198740022890026681078775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98132493348593351120719183 147198740022890026681078775)
    ·
      refine ⟨220798110034335040021618163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147198740022890026681078775 220798110034335040021618163)
      ·
        refine ⟨331197165051502560032427245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220798110034335040021618163 331197165051502560032427245)
        ·
          refine ⟨124198936894313460012160217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 331197165051502560032427245 124198936894313460012160217)
          ·
            refine ⟨93149202670735095009120163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124198936894313460012160217 93149202670735095009120163)
            ·
              refine ⟨139723804006102642513680245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93149202670735095009120163 139723804006102642513680245)
              ·
                refine ⟨13099106625572122735657523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 139723804006102642513680245 13099106625572122735657523)
                ·
                  refine ⟨19648659938358184103486285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13099106625572122735657523 19648659938358184103486285)
                  ·
                    refine ⟨7368247476884319038807357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19648659938358184103486285 7368247476884319038807357)
                    ·
                      refine ⟨2763092803831619639552759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7368247476884319038807357 2763092803831619639552759)
                      ·
                        rfl

theorem cell23_5381104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 5, 1, 3, 3].length) (baseStart_5381104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5381104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5381104 prefixEnd_5381104 := by exact prefixLift 5381104
  have htrace : WordTrace (prefixWord ++ tailWord_5381104) baseStart_5381104 baseEnd_5381104 := by
    simpa [prefixWord, tailWord_5381104, baseEnd_5381104] using wordTrace_append hprefix tailTrace_5381104
  have hstable : (prefixWord ++ tailWord_5381104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5381104).length < 2 ^ (prefixWord ++ tailWord_5381104).sum := by decide
  have hdescent : baseEnd_5381104 < baseStart_5381104 := by decide
  rcases family_descends (prefixWord ++ tailWord_5381104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5381118 : List Nat := [4, 2, 2, 2, 2, 1, 1, 2, 1, 2, 4]
def baseStart_5381118 : Nat := 118140960795 + 5381118 * 2 ^ 59
def prefixEnd_5381118 : Nat := 4983230072969 + 3 ^ 40 * 5381118 * 2
def baseEnd_5381118 : Nat := 2763099992560782584777695

theorem tailTrace_5381118 : CollatzResearch.WordTrace tailWord_5381118 prefixEnd_5381118 2763099992560782584777695 := by
  unfold tailWord_5381118
  simp only [CollatzResearch.WordTrace]
  refine ⟨24533187164891997829056001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130843664879423988421632005 24533187164891997829056001)
  ·
    refine ⟨18399890373668998371792001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24533187164891997829056001 18399890373668998371792001)
    ·
      refine ⟨13799917780251748778844001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18399890373668998371792001 13799917780251748778844001)
      ·
        refine ⟨10349938335188811584133001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13799917780251748778844001 10349938335188811584133001)
        ·
          refine ⟨7762453751391608688099751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10349938335188811584133001 7762453751391608688099751)
          ·
            refine ⟨11643680627087413032149627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7762453751391608688099751 11643680627087413032149627)
            ·
              refine ⟨17465520940631119548224441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11643680627087413032149627 17465520940631119548224441)
              ·
                refine ⟨13099140705473339661168331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17465520940631119548224441 13099140705473339661168331)
                ·
                  refine ⟨19648711058210009491752497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13099140705473339661168331 19648711058210009491752497)
                  ·
                    refine ⟨14736533293657507118814373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19648711058210009491752497 14736533293657507118814373)
                    ·
                      refine ⟨2763099992560782584777695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14736533293657507118814373 2763099992560782584777695)
                      ·
                        rfl

theorem cell23_5381118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_5381118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5381118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5381118 prefixEnd_5381118 := by exact prefixLift 5381118
  have htrace : WordTrace (prefixWord ++ tailWord_5381118) baseStart_5381118 baseEnd_5381118 := by
    simpa [prefixWord, tailWord_5381118, baseEnd_5381118] using wordTrace_append hprefix tailTrace_5381118
  have hstable : (prefixWord ++ tailWord_5381118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5381118).length < 2 ^ (prefixWord ++ tailWord_5381118).sum := by decide
  have hdescent : baseEnd_5381118 < baseStart_5381118 := by decide
  rcases family_descends (prefixWord ++ tailWord_5381118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5381121 : List Nat := [1, 2, 4, 1, 2, 3, 1, 2, 1, 3, 3]
def baseStart_5381121 : Nat := 118140960795 + 5381121 * 2 ^ 59
def prefixEnd_5381121 : Nat := 4983230072969 + 3 ^ 40 * 5381121 * 2
def baseEnd_5381121 : Nat := 2763101533002746073040181

theorem tailTrace_5381121 : CollatzResearch.WordTrace tailWord_5381121 prefixEnd_5381121 2763101533002746073040181 := by
  unfold tailWord_5381121
  simp only [CollatzResearch.WordTrace]
  refine ⟨196265606738125114144807217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130843737825416742763204811 196265606738125114144807217)
  ·
    refine ⟨147199205053593835608605413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196265606738125114144807217 147199205053593835608605413)
    ·
      refine ⟨27599850947548844176613515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 147199205053593835608605413 27599850947548844176613515)
      ·
        refine ⟨41399776421323266264920273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27599850947548844176613515 41399776421323266264920273)
        ·
          refine ⟨31049832315992449698690205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41399776421323266264920273 31049832315992449698690205)
          ·
            refine ⟨11643687118497168637008827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31049832315992449698690205 11643687118497168637008827)
            ·
              refine ⟨17465530677745752955513241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11643687118497168637008827 17465530677745752955513241)
              ·
                refine ⟨13099148008309314716634931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17465530677745752955513241 13099148008309314716634931)
                ·
                  refine ⟨19648722012463972074952397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13099148008309314716634931 19648722012463972074952397)
                  ·
                    refine ⟨7368270754673989528107149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19648722012463972074952397 7368270754673989528107149)
                    ·
                      refine ⟨2763101533002746073040181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7368270754673989528107149 2763101533002746073040181)
                      ·
                        rfl

theorem cell23_5381121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 2, 1, 3, 3].length) (baseStart_5381121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5381121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5381121 prefixEnd_5381121 := by exact prefixLift 5381121
  have htrace : WordTrace (prefixWord ++ tailWord_5381121) baseStart_5381121 baseEnd_5381121 := by
    simpa [prefixWord, tailWord_5381121, baseEnd_5381121] using wordTrace_append hprefix tailTrace_5381121
  have hstable : (prefixWord ++ tailWord_5381121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5381121).length < 2 ^ (prefixWord ++ tailWord_5381121).sum := by decide
  have hdescent : baseEnd_5381121 < baseStart_5381121 := by decide
  rcases family_descends (prefixWord ++ tailWord_5381121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5381122 : List Nat := [3, 4, 1, 3, 1, 1, 3, 1, 1, 1, 4]
def baseStart_5381122 : Nat := 118140960795 + 5381122 * 2 ^ 59
def prefixEnd_5381122 : Nat := 4983230072969 + 3 ^ 40 * 5381122 * 2
def baseEnd_5381122 : Nat := 2763102046483400569127677

theorem tailTrace_5381122 : CollatzResearch.WordTrace tailWord_5381122 prefixEnd_5381122 2763102046483400569127677 := by
  unfold tailWord_5381122
  simp only [CollatzResearch.WordTrace]
  refine ⟨49066410802780372828898405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130843762140747660877062413 49066410802780372828898405)
  ·
    refine ⟨9199952025521319905418451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49066410802780372828898405 9199952025521319905418451)
    ·
      refine ⟨13799928038281979858127677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9199952025521319905418451 13799928038281979858127677)
      ·
        refine ⟨5174973014355742446797879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13799928038281979858127677 5174973014355742446797879)
        ·
          refine ⟨7762459521533613670196819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5174973014355742446797879 7762459521533613670196819)
          ·
            refine ⟨11643689282300420505295229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7762459521533613670196819 11643689282300420505295229)
            ·
              refine ⟨4366383480862657689485711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11643689282300420505295229 4366383480862657689485711)
              ·
                refine ⟨6549575221293986534228567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4366383480862657689485711 6549575221293986534228567)
                ·
                  refine ⟨9824362831940979801342851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6549575221293986534228567 9824362831940979801342851)
                  ·
                    refine ⟨14736544247911469702014277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9824362831940979801342851 14736544247911469702014277)
                    ·
                      refine ⟨2763102046483400569127677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14736544247911469702014277 2763102046483400569127677)
                      ·
                        rfl

theorem cell23_5381122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_5381122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5381122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5381122 prefixEnd_5381122 := by exact prefixLift 5381122
  have htrace : WordTrace (prefixWord ++ tailWord_5381122) baseStart_5381122 baseEnd_5381122 := by
    simpa [prefixWord, tailWord_5381122, baseEnd_5381122] using wordTrace_append hprefix tailTrace_5381122
  have hstable : (prefixWord ++ tailWord_5381122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5381122).length < 2 ^ (prefixWord ++ tailWord_5381122).sum := by decide
  have hdescent : baseEnd_5381122 < baseStart_5381122 := by decide
  rcases family_descends (prefixWord ++ tailWord_5381122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5381137 : List Nat := [1, 2, 2, 1, 1, 2, 1, 2, 3, 8]
def baseStart_5381137 : Nat := 118140960795 + 5381137 * 2 ^ 59
def prefixEnd_5381137 : Nat := 4983230072969 + 3 ^ 40 * 5381137 * 2
def baseEnd_5381137 : Nat := 921036582897739336813369

theorem tailTrace_5381137 : CollatzResearch.WordTrace tailWord_5381137 prefixEnd_5381137 921036582897739336813369 := by
  unfold tailWord_5381137
  simp only [CollatzResearch.WordTrace]
  refine ⟨196266190306067148877389665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130844126870711432584926443 196266190306067148877389665)
  ·
    refine ⟨147199642729550361658042249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196266190306067148877389665 147199642729550361658042249)
    ·
      refine ⟨110399732047162771243531687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147199642729550361658042249 110399732047162771243531687)
      ·
        refine ⟨165599598070744156865297531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110399732047162771243531687 165599598070744156865297531)
        ·
          refine ⟨248399397106116235297946297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165599598070744156865297531 248399397106116235297946297)
          ·
            refine ⟨186299547829587176473459723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 248399397106116235297946297 186299547829587176473459723)
            ·
              refine ⟨279449321744380764710189585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 186299547829587176473459723 279449321744380764710189585)
              ·
                refine ⟨209586991308285573532642189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 279449321744380764710189585 209586991308285573532642189)
                ·
                  refine ⟨78595121740607090074740821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 209586991308285573532642189 78595121740607090074740821)
                  ·
                    refine ⟨921036582897739336813369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 78595121740607090074740821 921036582897739336813369)
                    ·
                      rfl

theorem cell23_5381137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 8].length) (baseStart_5381137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5381137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5381137 prefixEnd_5381137 := by exact prefixLift 5381137
  have htrace : WordTrace (prefixWord ++ tailWord_5381137) baseStart_5381137 baseEnd_5381137 := by
    simpa [prefixWord, tailWord_5381137, baseEnd_5381137] using wordTrace_append hprefix tailTrace_5381137
  have hstable : (prefixWord ++ tailWord_5381137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5381137).length < 2 ^ (prefixWord ++ tailWord_5381137).sum := by decide
  have hdescent : baseEnd_5381137 < baseStart_5381137 := by decide
  rcases family_descends (prefixWord ++ tailWord_5381137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5381144 : List Nat := [2, 1, 2, 3, 2, 2, 1, 1, 2, 3, 4]
def baseStart_5381144 : Nat := 118140960795 + 5381144 * 2 ^ 59
def prefixEnd_5381144 : Nat := 4983230072969 + 3 ^ 40 * 5381144 * 2
def baseEnd_5381144 : Nat := 2763113343057799483052575

theorem tailTrace_5381144 : CollatzResearch.WordTrace tailWord_5381144 prefixEnd_5381144 2763113343057799483052575 := by
  unfold tailWord_5381144
  simp only [CollatzResearch.WordTrace]
  refine ⟨98133222808520894536447243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130844297078027859381929657 98133222808520894536447243)
  ·
    refine ⟨147199834212781341804670865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98133222808520894536447243 147199834212781341804670865)
    ·
      refine ⟨110399875659586006353503149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147199834212781341804670865 110399875659586006353503149)
      ·
        refine ⟨41399953372344752382563681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110399875659586006353503149 41399953372344752382563681)
        ·
          refine ⟨31049965029258564286922761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41399953372344752382563681 31049965029258564286922761)
          ·
            refine ⟨23287473771943923215192071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31049965029258564286922761 23287473771943923215192071)
            ·
              refine ⟨34931210657915884822788107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23287473771943923215192071 34931210657915884822788107)
              ·
                refine ⟨52396815986873827234182161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34931210657915884822788107 52396815986873827234182161)
                ·
                  refine ⟨39297611990155370425636621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52396815986873827234182161 39297611990155370425636621)
                  ·
                    refine ⟨14736604496308263909613733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39297611990155370425636621 14736604496308263909613733)
                    ·
                      refine ⟨2763113343057799483052575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14736604496308263909613733 2763113343057799483052575)
                      ·
                        rfl

theorem cell23_5381144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 1, 2, 3, 4].length) (baseStart_5381144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5381144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5381144 prefixEnd_5381144 := by exact prefixLift 5381144
  have htrace : WordTrace (prefixWord ++ tailWord_5381144) baseStart_5381144 baseEnd_5381144 := by
    simpa [prefixWord, tailWord_5381144, baseEnd_5381144] using wordTrace_append hprefix tailTrace_5381144
  have hstable : (prefixWord ++ tailWord_5381144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5381144).length < 2 ^ (prefixWord ++ tailWord_5381144).sum := by decide
  have hdescent : baseEnd_5381144 < baseStart_5381144 := by decide
  rcases family_descends (prefixWord ++ tailWord_5381144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5381154 : List Nat := [3, 3, 1, 1, 1, 3, 1, 1, 1, 8]
def baseStart_5381154 : Nat := 118140960795 + 5381154 * 2 ^ 59
def prefixEnd_5381154 : Nat := 4983230072969 + 3 ^ 40 * 5381154 * 2
def baseEnd_5381154 : Nat := 921039492621448147975843

theorem tailTrace_5381154 : CollatzResearch.WordTrace tailWord_5381154 prefixEnd_5381154 921039492621448147975843 := by
  unfold tailWord_5381154
  simp only [CollatzResearch.WordTrace]
  refine ⟨49066702586751390195189629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130844540231337040520505677 49066702586751390195189629)
  ·
    refine ⟨18400013470031771323196111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49066702586751390195189629 18400013470031771323196111)
    ·
      refine ⟨27600020205047656984794167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18400013470031771323196111 27600020205047656984794167)
      ·
        refine ⟨41400030307571485477191251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27600020205047656984794167 41400030307571485477191251)
        ·
          refine ⟨62100045461357228215786877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41400030307571485477191251 62100045461357228215786877)
          ·
            refine ⟨23287517048008960580920079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62100045461357228215786877 23287517048008960580920079)
            ·
              refine ⟨34931275572013440871380119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23287517048008960580920079 34931275572013440871380119)
              ·
                refine ⟨52396913358020161307070179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34931275572013440871380119 52396913358020161307070179)
                ·
                  refine ⟨78595370037030241960605269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52396913358020161307070179 78595370037030241960605269)
                  ·
                    refine ⟨921039492621448147975843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 78595370037030241960605269 921039492621448147975843)
                    ·
                      rfl

theorem cell23_5381154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 1, 1, 8].length) (baseStart_5381154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5381154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5381154 prefixEnd_5381154 := by exact prefixLift 5381154
  have htrace : WordTrace (prefixWord ++ tailWord_5381154) baseStart_5381154 baseEnd_5381154 := by
    simpa [prefixWord, tailWord_5381154, baseEnd_5381154] using wordTrace_append hprefix tailTrace_5381154
  have hstable : (prefixWord ++ tailWord_5381154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5381154).length < 2 ^ (prefixWord ++ tailWord_5381154).sum := by decide
  have hdescent : baseEnd_5381154 < baseStart_5381154 := by decide
  rcases family_descends (prefixWord ++ tailWord_5381154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5381164 : List Nat := [2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 3]
def baseStart_5381164 : Nat := 118140960795 + 5381164 * 2 ^ 59
def prefixEnd_5381164 : Nat := 4983230072969 + 3 ^ 40 * 5381164 * 2
def baseEnd_5381164 : Nat := 2763123612670889404802483

theorem tailTrace_5381164 : CollatzResearch.WordTrace tailWord_5381164 prefixEnd_5381164 2763123612670889404802483 := by
  unfold tailWord_5381164
  simp only [CollatzResearch.WordTrace]
  refine ⟨98133587538484666244311273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130844783384646221659081697 98133587538484666244311273)
  ·
    refine ⟨73600190653863499683233455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98133587538484666244311273 73600190653863499683233455)
    ·
      refine ⟨110400285980795249524850183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73600190653863499683233455 110400285980795249524850183)
      ·
        refine ⟨165600428971192874287275275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110400285980795249524850183 165600428971192874287275275)
        ·
          refine ⟨248400643456789311430912913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165600428971192874287275275 248400643456789311430912913)
          ·
            refine ⟨186300482592591983573184685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 248400643456789311430912913 186300482592591983573184685)
            ·
              refine ⟨69862680972221993839944257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 186300482592591983573184685 69862680972221993839944257)
              ·
                refine ⟨52397010729166495379958193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69862680972221993839944257 52397010729166495379958193)
                ·
                  refine ⟨39297758046874871534968645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52397010729166495379958193 39297758046874871534968645)
                  ·
                    refine ⟨7368329633789038412806621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39297758046874871534968645 7368329633789038412806621)
                    ·
                      refine ⟨2763123612670889404802483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7368329633789038412806621 2763123612670889404802483)
                      ·
                        rfl

theorem cell23_5381164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 3].length) (baseStart_5381164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5381164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5381164 prefixEnd_5381164 := by exact prefixLift 5381164
  have htrace : WordTrace (prefixWord ++ tailWord_5381164) baseStart_5381164 baseEnd_5381164 := by
    simpa [prefixWord, tailWord_5381164, baseEnd_5381164] using wordTrace_append hprefix tailTrace_5381164
  have hstable : (prefixWord ++ tailWord_5381164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5381164).length < 2 ^ (prefixWord ++ tailWord_5381164).sum := by decide
  have hdescent : baseEnd_5381164 < baseStart_5381164 := by decide
  rcases family_descends (prefixWord ++ tailWord_5381164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5381182 : List Nat := [4, 2, 1, 3, 1, 1, 4, 1, 1, 3, 2]
def baseStart_5381182 : Nat := 118140960795 + 5381182 * 2 ^ 59
def prefixEnd_5381182 : Nat := 4983230072969 + 3 ^ 40 * 5381182 * 2
def baseEnd_5381182 : Nat := 2763132855322670334377401

theorem tailTrace_5381182 : CollatzResearch.WordTrace tailWord_5381182 prefixEnd_5381182 2763132855322670334377401 := by
  unfold tailWord_5381182
  simp only [CollatzResearch.WordTrace]
  refine ⟨24533478948863015195347225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130845221060602747708518533 24533478948863015195347225)
  ·
    refine ⟨18400109211647261396510419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24533478948863015195347225 18400109211647261396510419)
    ·
      refine ⟨27600163817470892094765629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18400109211647261396510419 27600163817470892094765629)
      ·
        refine ⟨10350061431551584535537111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27600163817470892094765629 10350061431551584535537111)
        ·
          refine ⟨15525092147327376803305667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10350061431551584535537111 15525092147327376803305667)
          ·
            refine ⟨23287638220991065204958501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15525092147327376803305667 23287638220991065204958501)
            ·
              refine ⟨4366432166435824725929719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23287638220991065204958501 4366432166435824725929719)
              ·
                refine ⟨6549648249653737088894579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4366432166435824725929719 6549648249653737088894579)
                ·
                  refine ⟨9824472374480605633341869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6549648249653737088894579 9824472374480605633341869)
                  ·
                    refine ⟨3684177140430227112503201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9824472374480605633341869 3684177140430227112503201)
                    ·
                      refine ⟨2763132855322670334377401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3684177140430227112503201 2763132855322670334377401)
                      ·
                        rfl

theorem cell23_5381182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 4, 1, 1, 3, 2].length) (baseStart_5381182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5381182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5381182 prefixEnd_5381182 := by exact prefixLift 5381182
  have htrace : WordTrace (prefixWord ++ tailWord_5381182) baseStart_5381182 baseEnd_5381182 := by
    simpa [prefixWord, tailWord_5381182, baseEnd_5381182] using wordTrace_append hprefix tailTrace_5381182
  have hstable : (prefixWord ++ tailWord_5381182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5381182).length < 2 ^ (prefixWord ++ tailWord_5381182).sum := by decide
  have hdescent : baseEnd_5381182 < baseStart_5381182 := by decide
  rcases family_descends (prefixWord ++ tailWord_5381182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5381201 : List Nat := [1, 2, 2, 1, 3, 1, 4, 4, 5]
def baseStart_5381201 : Nat := 118140960795 + 5381201 * 2 ^ 59
def prefixEnd_5381201 : Nat := 4983230072969 + 3 ^ 40 * 5381201 * 2
def baseEnd_5381201 : Nat := 307015845717233973337757

theorem tailTrace_5381201 : CollatzResearch.WordTrace tailWord_5381201 prefixEnd_5381201 307015845717233973337757 := by
  unfold tailWord_5381201
  simp only [CollatzResearch.WordTrace]
  refine ⟨196268524577835287807719457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130845683051890191871812971 196268524577835287807719457)
  ·
    refine ⟨147201393433376465855789593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196268524577835287807719457 147201393433376465855789593)
    ·
      refine ⟨110401045075032349391842195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147201393433376465855789593 110401045075032349391842195)
      ·
        refine ⟨165601567612548524087763293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110401045075032349391842195 165601567612548524087763293)
        ·
          refine ⟨62100587854705696532911235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 165601567612548524087763293 62100587854705696532911235)
          ·
            refine ⟨93150881782058544799366853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62100587854705696532911235 93150881782058544799366853)
            ·
              refine ⟨17465790334135977149881285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 93150881782058544799366853 17465790334135977149881285)
              ·
                refine ⟨3274835687650495715602741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17465790334135977149881285 3274835687650495715602741)
                ·
                  refine ⟨307015845717233973337757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3274835687650495715602741 307015845717233973337757)
                  ·
                    rfl

theorem cell23_5381201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 4, 5].length) (baseStart_5381201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5381201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5381201 prefixEnd_5381201 := by exact prefixLift 5381201
  have htrace : WordTrace (prefixWord ++ tailWord_5381201) baseStart_5381201 baseEnd_5381201 := by
    simpa [prefixWord, tailWord_5381201, baseEnd_5381201] using wordTrace_append hprefix tailTrace_5381201
  have hstable : (prefixWord ++ tailWord_5381201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5381201).length < 2 ^ (prefixWord ++ tailWord_5381201).sum := by decide
  have hdescent : baseEnd_5381201 < baseStart_5381201 := by decide
  rcases family_descends (prefixWord ++ tailWord_5381201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5381212 : List Nat := [2, 2, 4, 1, 1, 1, 5, 1, 2, 2, 2]
def baseStart_5381212 : Nat := 118140960795 + 5381212 * 2 ^ 59
def prefixEnd_5381212 : Nat := 4983230072969 + 3 ^ 40 * 5381212 * 2
def baseEnd_5381212 : Nat := 2763148259742305217002263

theorem tailTrace_5381212 : CollatzResearch.WordTrace tailWord_5381212 prefixEnd_5381212 2763148259742305217002263 := by
  unfold tailWord_5381212
  simp only [CollatzResearch.WordTrace]
  refine ⟨98134462890397718343184945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130845950520530291124246593 98134462890397718343184945)
  ·
    refine ⟨73600847167798288757388709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98134462890397718343184945 73600847167798288757388709)
    ·
      refine ⟨13800158843962179142010383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73600847167798288757388709 13800158843962179142010383)
      ·
        refine ⟨20700238265943268713015575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13800158843962179142010383 20700238265943268713015575)
        ·
          refine ⟨31050357398914903069523363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20700238265943268713015575 31050357398914903069523363)
          ·
            refine ⟨46575536098372354604285045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31050357398914903069523363 46575536098372354604285045)
            ·
              refine ⟨4366456509222408244151723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46575536098372354604285045 4366456509222408244151723)
              ·
                refine ⟨6549684763833612366227585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4366456509222408244151723 6549684763833612366227585)
                ·
                  refine ⟨4912263572875209274670689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6549684763833612366227585 4912263572875209274670689)
                  ·
                    refine ⟨3684197679656406956003017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4912263572875209274670689 3684197679656406956003017)
                    ·
                      refine ⟨2763148259742305217002263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3684197679656406956003017 2763148259742305217002263)
                      ·
                        rfl

theorem cell23_5381212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 5, 1, 2, 2, 2].length) (baseStart_5381212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5381212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5381212 prefixEnd_5381212 := by exact prefixLift 5381212
  have htrace : WordTrace (prefixWord ++ tailWord_5381212) baseStart_5381212 baseEnd_5381212 := by
    simpa [prefixWord, tailWord_5381212, baseEnd_5381212] using wordTrace_append hprefix tailTrace_5381212
  have hstable : (prefixWord ++ tailWord_5381212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5381212).length < 2 ^ (prefixWord ++ tailWord_5381212).sum := by decide
  have hdescent : baseEnd_5381212 < baseStart_5381212 := by decide
  rcases family_descends (prefixWord ++ tailWord_5381212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5381251 : List Nat := [1, 1, 1, 3, 3, 2, 3, 2, 2, 1, 4]
def baseStart_5381251 : Nat := 118140960795 + 5381251 * 2 ^ 59
def prefixEnd_5381251 : Nat := 4983230072969 + 3 ^ 40 * 5381251 * 2
def baseEnd_5381251 : Nat := 2763168285487830564414583

theorem tailTrace_5381251 : CollatzResearch.WordTrace tailWord_5381251 prefixEnd_5381251 2763168285487830564414583 := by
  unfold tailWord_5381251
  simp only [CollatzResearch.WordTrace]
  refine ⟨196270348227654146347039607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130846898818436097564693071 196270348227654146347039607)
  ·
    refine ⟨294405522341481219520559411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196270348227654146347039607 294405522341481219520559411)
    ·
      refine ⟨441608283512221829280839117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294405522341481219520559411 441608283512221829280839117)
      ·
        refine ⟨165603106317083185980314669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 441608283512221829280839117 165603106317083185980314669)
        ·
          refine ⟨62101164868906194742618001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 165603106317083185980314669 62101164868906194742618001)
          ·
            refine ⟨46575873651679646056963501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62101164868906194742618001 46575873651679646056963501)
            ·
              refine ⟨17465952619379867271361313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46575873651679646056963501 17465952619379867271361313)
              ·
                refine ⟨13099464464534900453520985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17465952619379867271361313 13099464464534900453520985)
                ·
                  refine ⟨9824598348401175340140739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13099464464534900453520985 9824598348401175340140739)
                  ·
                    refine ⟨14736897522601763010211109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9824598348401175340140739 14736897522601763010211109)
                    ·
                      refine ⟨2763168285487830564414583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14736897522601763010211109 2763168285487830564414583)
                      ·
                        rfl

theorem cell23_5381251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 2, 2, 1, 4].length) (baseStart_5381251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5381251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5381251 prefixEnd_5381251 := by exact prefixLift 5381251
  have htrace : WordTrace (prefixWord ++ tailWord_5381251) baseStart_5381251 baseEnd_5381251 := by
    simpa [prefixWord, tailWord_5381251, baseEnd_5381251] using wordTrace_append hprefix tailTrace_5381251
  have hstable : (prefixWord ++ tailWord_5381251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5381251).length < 2 ^ (prefixWord ++ tailWord_5381251).sum := by decide
  have hdescent : baseEnd_5381251 < baseStart_5381251 := by decide
  rcases family_descends (prefixWord ++ tailWord_5381251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5381264 : List Nat := [2, 1, 1, 1, 1, 1, 4, 2, 2, 4, 4]
def baseStart_5381264 : Nat := 118140960795 + 5381264 * 2 ^ 59
def prefixEnd_5381264 : Nat := 4983230072969 + 3 ^ 40 * 5381264 * 2
def baseEnd_5381264 : Nat := 2763174960736339013552023

theorem tailTrace_5381264 : CollatzResearch.WordTrace tailWord_5381264 prefixEnd_5381264 2763174960736339013552023 := by
  unfold tailWord_5381264
  simp only [CollatzResearch.WordTrace]
  refine ⟨98135411188303524783631423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130847214917738033044841897 98135411188303524783631423)
  ·
    refine ⟨147203116782455287175447135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98135411188303524783631423 147203116782455287175447135)
    ·
      refine ⟨220804675173682930763170703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147203116782455287175447135 220804675173682930763170703)
      ·
        refine ⟨331207012760524396144756055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220804675173682930763170703 331207012760524396144756055)
        ·
          refine ⟨496810519140786594217134083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 331207012760524396144756055 496810519140786594217134083)
          ·
            refine ⟨745215778711179891325701125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 496810519140786594217134083 745215778711179891325701125)
            ·
              refine ⟨139727958508346229623568961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 745215778711179891325701125 139727958508346229623568961)
              ·
                refine ⟨104795968881259672217676721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 139727958508346229623568961 104795968881259672217676721)
                ·
                  refine ⟨78596976660944754163257541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 104795968881259672217676721 78596976660944754163257541)
                  ·
                    refine ⟨14736933123927141405610789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 78596976660944754163257541 14736933123927141405610789)
                    ·
                      refine ⟨2763174960736339013552023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14736933123927141405610789 2763174960736339013552023)
                      ·
                        rfl

theorem cell23_5381264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4, 4].length) (baseStart_5381264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5381264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5381264 prefixEnd_5381264 := by exact prefixLift 5381264
  have htrace : WordTrace (prefixWord ++ tailWord_5381264) baseStart_5381264 baseEnd_5381264 := by
    simpa [prefixWord, tailWord_5381264, baseEnd_5381264] using wordTrace_append hprefix tailTrace_5381264
  have hstable : (prefixWord ++ tailWord_5381264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5381264).length < 2 ^ (prefixWord ++ tailWord_5381264).sum := by decide
  have hdescent : baseEnd_5381264 < baseStart_5381264 := by decide
  rcases family_descends (prefixWord ++ tailWord_5381264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5381308 : List Nat := [2, 2, 2, 3, 2, 2, 2, 2, 6]
def baseStart_5381308 : Nat := 118140960795 + 5381308 * 2 ^ 59
def prefixEnd_5381308 : Nat := 4983230072969 + 3 ^ 40 * 5381308 * 2
def baseEnd_5381308 : Nat := 307021950431681871266869

theorem tailTrace_5381308 : CollatzResearch.WordTrace tailWord_5381308 prefixEnd_5381308 307021950431681871266869 := by
  unfold tailWord_5381308
  simp only [CollatzResearch.WordTrace]
  refine ⟨98136213594223822540932289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130848284792298430054576385 98136213594223822540932289)
  ·
    refine ⟨73602160195667866905699217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98136213594223822540932289 73602160195667866905699217)
    ·
      refine ⟨55201620146750900179274413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73602160195667866905699217 55201620146750900179274413)
      ·
        refine ⟨20700607555031587567227905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55201620146750900179274413 20700607555031587567227905)
        ·
          refine ⟨15525455666273690675420929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20700607555031587567227905 15525455666273690675420929)
          ·
            refine ⟨11644091749705268006565697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15525455666273690675420929 11644091749705268006565697)
            ·
              refine ⟨8733068812278951004924273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11644091749705268006565697 8733068812278951004924273)
              ·
                refine ⟨6549801609209213253693205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8733068812278951004924273 6549801609209213253693205)
                ·
                  refine ⟨307021950431681871266869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6549801609209213253693205 307021950431681871266869)
                  ·
                    rfl

theorem cell23_5381308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2, 2, 6].length) (baseStart_5381308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5381308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5381308 prefixEnd_5381308 := by exact prefixLift 5381308
  have htrace : WordTrace (prefixWord ++ tailWord_5381308) baseStart_5381308 baseEnd_5381308 := by
    simpa [prefixWord, tailWord_5381308, baseEnd_5381308] using wordTrace_append hprefix tailTrace_5381308
  have hstable : (prefixWord ++ tailWord_5381308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5381308).length < 2 ^ (prefixWord ++ tailWord_5381308).sum := by decide
  have hdescent : baseEnd_5381308 < baseStart_5381308 := by decide
  rcases family_descends (prefixWord ++ tailWord_5381308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5381345 : List Nat := [1, 2, 3, 1, 3, 2, 3, 1, 2, 3, 2]
def baseStart_5381345 : Nat := 118140960795 + 5381345 * 2 ^ 59
def prefixEnd_5381345 : Nat := 4983230072969 + 3 ^ 40 * 5381345 * 2
def baseEnd_5381345 : Nat := 2763216552669353196639151

theorem tailTrace_5381345 : CollatzResearch.WordTrace tailWord_5381345 prefixEnd_5381345 2763216552669353196639151 := by
  unfold tailWord_5381345
  simp only [CollatzResearch.WordTrace]
  refine ⟨196273776689313600400961489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130849184459542400267307659 196273776689313600400961489)
  ·
    refine ⟨147205332516985200300721117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196273776689313600400961489 147205332516985200300721117)
    ·
      refine ⟨55201999693869450112770419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147205332516985200300721117 55201999693869450112770419)
      ·
        refine ⟨82802999540804175169155629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55201999693869450112770419 82802999540804175169155629)
        ·
          refine ⟨31051124827801565688433361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82802999540804175169155629 31051124827801565688433361)
          ·
            refine ⟨23288343620851174266325021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31051124827801565688433361 23288343620851174266325021)
            ·
              refine ⟨8733128857819190349871883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23288343620851174266325021 8733128857819190349871883)
              ·
                refine ⟨13099693286728785524807825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8733128857819190349871883 13099693286728785524807825)
                ·
                  refine ⟨9824769965046589143605869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13099693286728785524807825 9824769965046589143605869)
                  ·
                    refine ⟨3684288736892470928852201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9824769965046589143605869 3684288736892470928852201)
                    ·
                      refine ⟨2763216552669353196639151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3684288736892470928852201 2763216552669353196639151)
                      ·
                        rfl

theorem cell23_5381345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3, 1, 2, 3, 2].length) (baseStart_5381345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5381345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5381345 prefixEnd_5381345 := by exact prefixLift 5381345
  have htrace : WordTrace (prefixWord ++ tailWord_5381345) baseStart_5381345 baseEnd_5381345 := by
    simpa [prefixWord, tailWord_5381345, baseEnd_5381345] using wordTrace_append hprefix tailTrace_5381345
  have hstable : (prefixWord ++ tailWord_5381345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5381345).length < 2 ^ (prefixWord ++ tailWord_5381345).sum := by decide
  have hdescent : baseEnd_5381345 < baseStart_5381345 := by decide
  rcases family_descends (prefixWord ++ tailWord_5381345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5381352 : List Nat := [2, 1, 4, 1, 2, 1, 4, 3, 1, 1, 3]
def baseStart_5381352 : Nat := 118140960795 + 5381352 * 2 ^ 59
def prefixEnd_5381352 : Nat := 4983230072969 + 3 ^ 40 * 5381352 * 2
def baseEnd_5381352 : Nat := 2763220147033934669251619

theorem tailTrace_5381352 : CollatzResearch.WordTrace tailWord_5381352 prefixEnd_5381352 2763220147033934669251619 := by
  unfold tailWord_5381352
  simp only [CollatzResearch.WordTrace]
  refine ⟨98137016000144120298233155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130849354666858827064310873 98137016000144120298233155)
  ·
    refine ⟨147205524000216180447349733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98137016000144120298233155 147205524000216180447349733)
    ·
      refine ⟨27601035750040533833878075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 147205524000216180447349733 27601035750040533833878075)
      ·
        refine ⟨41401553625060800750817113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27601035750040533833878075 41401553625060800750817113)
        ·
          refine ⟨31051165218795600563112835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41401553625060800750817113 31051165218795600563112835)
          ·
            refine ⟨46576747828193400844669253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31051165218795600563112835 46576747828193400844669253)
            ·
              refine ⟨8733140217786262658375485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46576747828193400844669253 8733140217786262658375485)
              ·
                refine ⟨3274927581669848496890807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8733140217786262658375485 3274927581669848496890807)
                ·
                  refine ⟨4912391372504772745336211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3274927581669848496890807 4912391372504772745336211)
                  ·
                    refine ⟨7368587058757159118004317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4912391372504772745336211 7368587058757159118004317)
                    ·
                      refine ⟨2763220147033934669251619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7368587058757159118004317 2763220147033934669251619)
                      ·
                        rfl

theorem cell23_5381352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4, 3, 1, 1, 3].length) (baseStart_5381352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5381352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5381352 prefixEnd_5381352 := by exact prefixLift 5381352
  have htrace : WordTrace (prefixWord ++ tailWord_5381352) baseStart_5381352 baseEnd_5381352 := by
    simpa [prefixWord, tailWord_5381352, baseEnd_5381352] using wordTrace_append hprefix tailTrace_5381352
  have hstable : (prefixWord ++ tailWord_5381352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5381352).length < 2 ^ (prefixWord ++ tailWord_5381352).sum := by decide
  have hdescent : baseEnd_5381352 < baseStart_5381352 := by decide
  rcases family_descends (prefixWord ++ tailWord_5381352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5381355 : List Nat := [1, 1, 1, 1, 2, 8, 2, 1, 1, 5]
def baseStart_5381355 : Nat := 118140960795 + 5381355 * 2 ^ 59
def prefixEnd_5381355 : Nat := 4983230072969 + 3 ^ 40 * 5381355 * 2
def baseEnd_5381355 : Nat := 921073895825299385838035

theorem tailTrace_5381355 : CollatzResearch.WordTrace tailWord_5381355 prefixEnd_5381355 921073895825299385838035 := by
  unfold tailWord_5381355
  simp only [CollatzResearch.WordTrace]
  refine ⟨196274141419277372108825519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130849427612851581405883679 196274141419277372108825519)
  ·
    refine ⟨294411212128916058163238279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196274141419277372108825519 294411212128916058163238279)
    ·
      refine ⟨441616818193374087244857419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294411212128916058163238279 441616818193374087244857419)
      ·
        refine ⟨662425227290061130867286129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 441616818193374087244857419 662425227290061130867286129)
        ·
          refine ⟨496818920467545848150464597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 662425227290061130867286129 496818920467545848150464597)
          ·
            refine ⟨5822096724229052908013257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 496818920467545848150464597 5822096724229052908013257)
            ·
              refine ⟨4366572543171789681009943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5822096724229052908013257 4366572543171789681009943)
              ·
                refine ⟨6549858814757684521514915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4366572543171789681009943 6549858814757684521514915)
                ·
                  refine ⟨9824788222136526782272373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6549858814757684521514915 9824788222136526782272373)
                  ·
                    refine ⟨921073895825299385838035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9824788222136526782272373 921073895825299385838035)
                    ·
                      rfl

theorem cell23_5381355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 2, 1, 1, 5].length) (baseStart_5381355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5381355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5381355 prefixEnd_5381355 := by exact prefixLift 5381355
  have htrace : WordTrace (prefixWord ++ tailWord_5381355) baseStart_5381355 baseEnd_5381355 := by
    simpa [prefixWord, tailWord_5381355, baseEnd_5381355] using wordTrace_append hprefix tailTrace_5381355
  have hstable : (prefixWord ++ tailWord_5381355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5381355).length < 2 ^ (prefixWord ++ tailWord_5381355).sum := by decide
  have hdescent : baseEnd_5381355 < baseStart_5381355 := by decide
  rcases family_descends (prefixWord ++ tailWord_5381355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5381361 : List Nat := [1, 2, 2, 2, 2, 1, 1, 5, 1, 1, 5]
def baseStart_5381361 : Nat := 118140960795 + 5381361 * 2 ^ 59
def prefixEnd_5381361 : Nat := 4983230072969 + 3 ^ 40 * 5381361 * 2
def baseEnd_5381361 : Nat := 2763224768359825134039077

theorem tailTrace_5381361 : CollatzResearch.WordTrace tailWord_5381361 prefixEnd_5381361 2763224768359825134039077 := by
  unfold tailWord_5381361
  simp only [CollatzResearch.WordTrace]
  refine ⟨196274360257255635133543937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130849573504837090089029291 196274360257255635133543937)
  ·
    refine ⟨147205770192941726350157953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196274360257255635133543937 147205770192941726350157953)
    ·
      refine ⟨110404327644706294762618465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147205770192941726350157953 110404327644706294762618465)
      ·
        refine ⟨82803245733529721071963849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110404327644706294762618465 82803245733529721071963849)
        ·
          refine ⟨62102434300147290803972887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82803245733529721071963849 62102434300147290803972887)
          ·
            refine ⟨93153651450220936205959331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62102434300147290803972887 93153651450220936205959331)
            ·
              refine ⟨139730477175331404308938997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93153651450220936205959331 139730477175331404308938997)
              ·
                refine ⟨13099732235187319153963031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 139730477175331404308938997 13099732235187319153963031)
                ·
                  refine ⟨19649598352780978730944547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13099732235187319153963031 19649598352780978730944547)
                  ·
                    refine ⟨29474397529171468096416821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19649598352780978730944547 29474397529171468096416821)
                    ·
                      refine ⟨2763224768359825134039077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29474397529171468096416821 2763224768359825134039077)
                      ·
                        rfl

theorem cell23_5381361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 5, 1, 1, 5].length) (baseStart_5381361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5381361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5381361 prefixEnd_5381361 := by exact prefixLift 5381361
  have htrace : WordTrace (prefixWord ++ tailWord_5381361) baseStart_5381361 baseEnd_5381361 := by
    simpa [prefixWord, tailWord_5381361, baseEnd_5381361] using wordTrace_append hprefix tailTrace_5381361
  have hstable : (prefixWord ++ tailWord_5381361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5381361).length < 2 ^ (prefixWord ++ tailWord_5381361).sum := by decide
  have hdescent : baseEnd_5381361 < baseStart_5381361 := by decide
  rcases family_descends (prefixWord ++ tailWord_5381361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5381375 : List Nat := [1, 1, 2, 2, 1, 5, 1, 3, 3, 2, 2]
def baseStart_5381375 : Nat := 118140960795 + 5381375 * 2 ^ 59
def prefixEnd_5381375 : Nat := 4983230072969 + 3 ^ 40 * 5381375 * 2
def baseEnd_5381375 : Nat := 2763231957088988079264013

theorem tailTrace_5381375 : CollatzResearch.WordTrace tailWord_5381375 prefixEnd_5381375 2763231957088988079264013 := by
  unfold tailWord_5381375
  simp only [CollatzResearch.WordTrace]
  refine ⟨196274870879204915524553579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130849913919469943683035719 196274870879204915524553579)
  ·
    refine ⟨294412306318807373286830369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196274870879204915524553579 294412306318807373286830369)
    ·
      refine ⟨220809229739105529965122777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 294412306318807373286830369 220809229739105529965122777)
      ·
        refine ⟨165606922304329147473842083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 220809229739105529965122777 165606922304329147473842083)
        ·
          refine ⟨248410383456493721210763125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165606922304329147473842083 248410383456493721210763125)
          ·
            refine ⟨23288473449046286363509043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 248410383456493721210763125 23288473449046286363509043)
            ·
              refine ⟨34932710173569429545263565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23288473449046286363509043 34932710173569429545263565)
              ·
                refine ⟨13099766315088536079473837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34932710173569429545263565 13099766315088536079473837)
                ·
                  refine ⟨4912412368158201029802689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13099766315088536079473837 4912412368158201029802689)
                  ·
                    refine ⟨3684309276118650772352017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4912412368158201029802689 3684309276118650772352017)
                    ·
                      refine ⟨2763231957088988079264013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3684309276118650772352017 2763231957088988079264013)
                      ·
                        rfl

theorem cell23_5381375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 3, 3, 2, 2].length) (baseStart_5381375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5381375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5381375 prefixEnd_5381375 := by exact prefixLift 5381375
  have htrace : WordTrace (prefixWord ++ tailWord_5381375) baseStart_5381375 baseEnd_5381375 := by
    simpa [prefixWord, tailWord_5381375, baseEnd_5381375] using wordTrace_append hprefix tailTrace_5381375
  have hstable : (prefixWord ++ tailWord_5381375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5381375).length < 2 ^ (prefixWord ++ tailWord_5381375).sum := by decide
  have hdescent : baseEnd_5381375 < baseStart_5381375 := by decide
  rcases family_descends (prefixWord ++ tailWord_5381375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5381385 : List Nat := [1, 2, 1, 1, 3, 3, 5, 1, 2, 4]
def baseStart_5381385 : Nat := 118140960795 + 5381385 * 2 ^ 59
def prefixEnd_5381385 : Nat := 4983230072969 + 3 ^ 40 * 5381385 * 2
def baseEnd_5381385 : Nat := 921079030631844346712989

theorem tailTrace_5381385 : CollatzResearch.WordTrace tailWord_5381385 prefixEnd_5381385 921079030631844346712989 := by
  unfold tailWord_5381385
  simp only [CollatzResearch.WordTrace]
  refine ⟨196275235609168687232417609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130850157072779124821611739 196275235609168687232417609)
  ·
    refine ⟨147206426706876515424313207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196275235609168687232417609 147206426706876515424313207)
    ·
      refine ⟨220809640060314773136469811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147206426706876515424313207 220809640060314773136469811)
      ·
        refine ⟨331214460090472159704704717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220809640060314773136469811 331214460090472159704704717)
        ·
          refine ⟨124205422533927059889264269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 331214460090472159704704717 124205422533927059889264269)
          ·
            refine ⟨46577033450222647458474101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 124205422533927059889264269 46577033450222647458474101)
            ·
              refine ⟨4366596885958373199231947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46577033450222647458474101 4366596885958373199231947)
              ·
                refine ⟨6549895328937559798847921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4366596885958373199231947 6549895328937559798847921)
                ·
                  refine ⟨4912421496703169849135941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6549895328937559798847921 4912421496703169849135941)
                  ·
                    refine ⟨921079030631844346712989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4912421496703169849135941 921079030631844346712989)
                    ·
                      rfl

theorem cell23_5381385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 5, 1, 2, 4].length) (baseStart_5381385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5381385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5381385 prefixEnd_5381385 := by exact prefixLift 5381385
  have htrace : WordTrace (prefixWord ++ tailWord_5381385) baseStart_5381385 baseEnd_5381385 := by
    simpa [prefixWord, tailWord_5381385, baseEnd_5381385] using wordTrace_append hprefix tailTrace_5381385
  have hstable : (prefixWord ++ tailWord_5381385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5381385).length < 2 ^ (prefixWord ++ tailWord_5381385).sum := by decide
  have hdescent : baseEnd_5381385 < baseStart_5381385 := by decide
  rcases family_descends (prefixWord ++ tailWord_5381385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5381388 : List Nat := [2, 2, 1, 2, 2, 3, 3, 1, 1, 2, 4]
def baseStart_5381388 : Nat := 118140960795 + 5381388 * 2 ^ 59
def prefixEnd_5381388 : Nat := 4983230072969 + 3 ^ 40 * 5381388 * 2
def baseEnd_5381388 : Nat := 2763238632337496528401453

theorem tailTrace_5381388 : CollatzResearch.WordTrace tailWord_5381388 prefixEnd_5381388 2763238632337496528401453 := by
  unfold tailWord_5381388
  simp only [CollatzResearch.WordTrace]
  refine ⟨98137672514078909372388409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130850230018771879163184545 98137672514078909372388409)
  ·
    refine ⟨73603254385559182029291307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98137672514078909372388409 73603254385559182029291307)
    ·
      refine ⟨110404881578338773043936961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73603254385559182029291307 110404881578338773043936961)
      ·
        refine ⟨82803661183754079782952721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110404881578338773043936961 82803661183754079782952721)
        ·
          refine ⟨62102745887815559837214541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82803661183754079782952721 62102745887815559837214541)
          ·
            refine ⟨23288529707930834938955453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62102745887815559837214541 23288529707930834938955453)
            ·
              refine ⟨8733198640474063102108295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23288529707930834938955453 8733198640474063102108295)
              ·
                refine ⟨13099797960711094653162443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8733198640474063102108295 13099797960711094653162443)
                ·
                  refine ⟨19649696941066641979743665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13099797960711094653162443 19649696941066641979743665)
                  ·
                    refine ⟨14737272705799981484807749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19649696941066641979743665 14737272705799981484807749)
                    ·
                      refine ⟨2763238632337496528401453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14737272705799981484807749 2763238632337496528401453)
                      ·
                        rfl

theorem cell23_5381388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3, 1, 1, 2, 4].length) (baseStart_5381388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5381388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5381388 prefixEnd_5381388 := by exact prefixLift 5381388
  have htrace : WordTrace (prefixWord ++ tailWord_5381388) baseStart_5381388 baseEnd_5381388 := by
    simpa [prefixWord, tailWord_5381388, baseEnd_5381388] using wordTrace_append hprefix tailTrace_5381388
  have hstable : (prefixWord ++ tailWord_5381388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5381388).length < 2 ^ (prefixWord ++ tailWord_5381388).sum := by decide
  have hdescent : baseEnd_5381388 < baseStart_5381388 := by decide
  rcases family_descends (prefixWord ++ tailWord_5381388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5381425 : List Nat := [1, 2, 2, 3, 3, 1, 2, 1, 4, 1, 3]
def baseStart_5381425 : Nat := 118140960795 + 5381425 * 2 ^ 59
def prefixEnd_5381425 : Nat := 4983230072969 + 3 ^ 40 * 5381425 * 2
def baseEnd_5381425 : Nat := 2763257631121712883638783

theorem tailTrace_5381425 : CollatzResearch.WordTrace tailWord_5381425 prefixEnd_5381425 2763257631121712883638783 := by
  unfold tailWord_5381425
  simp only [CollatzResearch.WordTrace]
  refine ⟨196276694529023774063873729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130851129686015849375915819 196276694529023774063873729)
  ·
    refine ⟨147207520896767830547905297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196276694529023774063873729 147207520896767830547905297)
    ·
      refine ⟨110405640672575872910928973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147207520896767830547905297 110405640672575872910928973)
      ·
        refine ⟨41402115252215952341598365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110405640672575872910928973 41402115252215952341598365)
        ·
          refine ⟨15525793219580982128099387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41402115252215952341598365 15525793219580982128099387)
          ·
            refine ⟨23288689829371473192149081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15525793219580982128099387 23288689829371473192149081)
            ·
              refine ⟨17466517372028604894111811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23288689829371473192149081 17466517372028604894111811)
              ·
                refine ⟨26199776058042907341167717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17466517372028604894111811 26199776058042907341167717)
                ·
                  refine ⟨4912458010883045126468947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26199776058042907341167717 4912458010883045126468947)
                  ·
                    refine ⟨7368687016324567689703421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4912458010883045126468947 7368687016324567689703421)
                    ·
                      refine ⟨2763257631121712883638783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7368687016324567689703421 2763257631121712883638783)
                      ·
                        rfl

theorem cell23_5381425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 1, 4, 1, 3].length) (baseStart_5381425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5381425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5381425 prefixEnd_5381425 := by exact prefixLift 5381425
  have htrace : WordTrace (prefixWord ++ tailWord_5381425) baseStart_5381425 baseEnd_5381425 := by
    simpa [prefixWord, tailWord_5381425, baseEnd_5381425] using wordTrace_append hprefix tailTrace_5381425
  have hstable : (prefixWord ++ tailWord_5381425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5381425).length < 2 ^ (prefixWord ++ tailWord_5381425).sum := by decide
  have hdescent : baseEnd_5381425 < baseStart_5381425 := by decide
  rcases family_descends (prefixWord ++ tailWord_5381425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5381426 : List Nat := [3, 2, 1, 1, 4, 2, 3, 2, 1, 2, 2]
def baseStart_5381426 : Nat := 118140960795 + 5381426 * 2 ^ 59
def prefixEnd_5381426 : Nat := 4983230072969 + 3 ^ 40 * 5381426 * 2
def baseEnd_5381426 : Nat := 2763258144602367379726279

theorem tailTrace_5381426 : CollatzResearch.WordTrace tailWord_5381426 prefixEnd_5381426 2763258144602367379726279 := by
  unfold tailWord_5381426
  simp only [CollatzResearch.WordTrace]
  refine ⟨49069182750505037808665033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130851154001346767489773421 49069182750505037808665033)
  ·
    refine ⟨36801887062878778356498775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49069182750505037808665033 36801887062878778356498775)
    ·
      refine ⟨55202830594318167534748163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36801887062878778356498775 55202830594318167534748163)
      ·
        refine ⟨82804245891477251302122245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55202830594318167534748163 82804245891477251302122245)
        ·
          refine ⟨15525796104651984619147921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82804245891477251302122245 15525796104651984619147921)
          ·
            refine ⟨11644347078488988464360941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15525796104651984619147921 11644347078488988464360941)
            ·
              refine ⟨4366630154433370674135353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11644347078488988464360941 4366630154433370674135353)
              ·
                refine ⟨3274972615825028005601515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4366630154433370674135353 3274972615825028005601515)
                ·
                  refine ⟨4912458923737542008402273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3274972615825028005601515 4912458923737542008402273)
                  ·
                    refine ⟨3684344192803156506301705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4912458923737542008402273 3684344192803156506301705)
                    ·
                      refine ⟨2763258144602367379726279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3684344192803156506301705 2763258144602367379726279)
                      ·
                        rfl

theorem cell23_5381426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 3, 2, 1, 2, 2].length) (baseStart_5381426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5381426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5381426 prefixEnd_5381426 := by exact prefixLift 5381426
  have htrace : WordTrace (prefixWord ++ tailWord_5381426) baseStart_5381426 baseEnd_5381426 := by
    simpa [prefixWord, tailWord_5381426, baseEnd_5381426] using wordTrace_append hprefix tailTrace_5381426
  have hstable : (prefixWord ++ tailWord_5381426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5381426).length < 2 ^ (prefixWord ++ tailWord_5381426).sum := by decide
  have hdescent : baseEnd_5381426 < baseStart_5381426 := by decide
  rcases family_descends (prefixWord ++ tailWord_5381426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5381428 : List Nat := [2, 5, 1, 1, 1, 1, 2, 1, 2, 7]
def baseStart_5381428 : Nat := 118140960795 + 5381428 * 2 ^ 59
def prefixEnd_5381428 : Nat := 4983230072969 + 3 ^ 40 * 5381428 * 2
def baseEnd_5381428 : Nat := 921086390521225457300423

theorem tailTrace_5381428 : CollatzResearch.WordTrace tailWord_5381428 prefixEnd_5381428 921086390521225457300423 := by
  unfold tailWord_5381428
  simp only [CollatzResearch.WordTrace]
  refine ⟨98138401974006452788116469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130851202632008603717488625 98138401974006452788116469)
  ·
    refine ⟨9200475185063104948885919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 98138401974006452788116469 9200475185063104948885919)
    ·
      refine ⟨13800712777594657423328879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9200475185063104948885919 13800712777594657423328879)
      ·
        refine ⟨20701069166391986134993319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13800712777594657423328879 20701069166391986134993319)
        ·
          refine ⟨31051603749587979202489979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20701069166391986134993319 31051603749587979202489979)
          ·
            refine ⟨46577405624381968803734969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31051603749587979202489979 46577405624381968803734969)
            ·
              refine ⟨34933054218286476602801227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46577405624381968803734969 34933054218286476602801227)
              ·
                refine ⟨52399581327429714904201841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34933054218286476602801227 52399581327429714904201841)
                ·
                  refine ⟨39299685995572286178151381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52399581327429714904201841 39299685995572286178151381)
                  ·
                    refine ⟨921086390521225457300423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39299685995572286178151381 921086390521225457300423)
                    ·
                      rfl

theorem cell23_5381428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_5381428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5381428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5381428 prefixEnd_5381428 := by exact prefixLift 5381428
  have htrace : WordTrace (prefixWord ++ tailWord_5381428) baseStart_5381428 baseEnd_5381428 := by
    simpa [prefixWord, tailWord_5381428, baseEnd_5381428] using wordTrace_append hprefix tailTrace_5381428
  have hstable : (prefixWord ++ tailWord_5381428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5381428).length < 2 ^ (prefixWord ++ tailWord_5381428).sum := by decide
  have hdescent : baseEnd_5381428 < baseStart_5381428 := by decide
  rcases family_descends (prefixWord ++ tailWord_5381428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5381452 : List Nat := [2, 2, 1, 3, 2, 2, 3, 2, 1, 3, 2]
def baseStart_5381452 : Nat := 118140960795 + 5381452 * 2 ^ 59
def prefixEnd_5381452 : Nat := 4983230072969 + 3 ^ 40 * 5381452 * 2
def baseEnd_5381452 : Nat := 2763271495099384278001159

theorem tailTrace_5381452 : CollatzResearch.WordTrace tailWord_5381452 prefixEnd_5381452 2763271495099384278001159 := by
  unfold tailWord_5381452
  simp only [CollatzResearch.WordTrace]
  refine ⟨98138839649962978837553305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130851786199950638450071073 98138839649962978837553305)
  ·
    refine ⟨73604129737472234128164979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98138839649962978837553305 73604129737472234128164979)
    ·
      refine ⟨110406194606208351192247469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73604129737472234128164979 110406194606208351192247469)
      ·
        refine ⟨41402322977328131697092801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110406194606208351192247469 41402322977328131697092801)
        ·
          refine ⟨31051742232996098772819601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41402322977328131697092801 31051742232996098772819601)
          ·
            refine ⟨23288806674747074079614701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31051742232996098772819601 23288806674747074079614701)
            ·
              refine ⟨8733302503030152779855513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23288806674747074079614701 8733302503030152779855513)
              ·
                refine ⟨6549976877272614584891635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8733302503030152779855513 6549976877272614584891635)
                ·
                  refine ⟨9824965315908921877337453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6549976877272614584891635 9824965315908921877337453)
                  ·
                    refine ⟨3684361993465845704001545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9824965315908921877337453 3684361993465845704001545)
                    ·
                      refine ⟨2763271495099384278001159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3684361993465845704001545 2763271495099384278001159)
                      ·
                        rfl

theorem cell23_5381452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3, 2, 1, 3, 2].length) (baseStart_5381452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5381452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5381452 prefixEnd_5381452 := by exact prefixLift 5381452
  have htrace : WordTrace (prefixWord ++ tailWord_5381452) baseStart_5381452 baseEnd_5381452 := by
    simpa [prefixWord, tailWord_5381452, baseEnd_5381452] using wordTrace_append hprefix tailTrace_5381452
  have hstable : (prefixWord ++ tailWord_5381452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5381452).length < 2 ^ (prefixWord ++ tailWord_5381452).sum := by decide
  have hdescent : baseEnd_5381452 < baseStart_5381452 := by decide
  rcases family_descends (prefixWord ++ tailWord_5381452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5381465 : List Nat := [1, 2, 1, 2, 2, 2, 2, 1, 6, 2, 2]
def baseStart_5381465 : Nat := 118140960795 + 5381465 * 2 ^ 59
def prefixEnd_5381465 : Nat := 4983230072969 + 3 ^ 40 * 5381465 * 2
def baseEnd_5381465 : Nat := 2763278170347892727138599

theorem tailTrace_5381465 : CollatzResearch.WordTrace tailWord_5381465 prefixEnd_5381465 2763278170347892727138599 := by
  unfold tailWord_5381465
  simp only [CollatzResearch.WordTrace]
  refine ⟨196278153448878860895329849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130852102299252573930219899 196278153448878860895329849)
  ·
    refine ⟨147208615086659145671497387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196278153448878860895329849 147208615086659145671497387)
    ·
      refine ⟨220812922629988718507246081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147208615086659145671497387 220812922629988718507246081)
      ·
        refine ⟨165609691972491538880434561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 220812922629988718507246081 165609691972491538880434561)
        ·
          refine ⟨124207268979368654160325921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165609691972491538880434561 124207268979368654160325921)
          ·
            refine ⟨93155451734526490620244441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124207268979368654160325921 93155451734526490620244441)
            ·
              refine ⟨69866588800894867965183331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93155451734526490620244441 69866588800894867965183331)
              ·
                refine ⟨104799883201342301947774997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69866588800894867965183331 104799883201342301947774997)
                ·
                  refine ⟨4912494525062920403801953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 104799883201342301947774997 4912494525062920403801953)
                  ·
                    refine ⟨3684370893797190302851465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4912494525062920403801953 3684370893797190302851465)
                    ·
                      refine ⟨2763278170347892727138599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3684370893797190302851465 2763278170347892727138599)
                      ·
                        rfl

theorem cell23_5381465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 6, 2, 2].length) (baseStart_5381465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5381465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5381465 prefixEnd_5381465 := by exact prefixLift 5381465
  have htrace : WordTrace (prefixWord ++ tailWord_5381465) baseStart_5381465 baseEnd_5381465 := by
    simpa [prefixWord, tailWord_5381465, baseEnd_5381465] using wordTrace_append hprefix tailTrace_5381465
  have hstable : (prefixWord ++ tailWord_5381465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5381465).length < 2 ^ (prefixWord ++ tailWord_5381465).sum := by decide
  have hdescent : baseEnd_5381465 < baseStart_5381465 := by decide
  rcases family_descends (prefixWord ++ tailWord_5381465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5381498 : List Nat := [3, 1, 1, 1, 1, 1, 2, 5, 2, 3, 3]
def baseStart_5381498 : Nat := 118140960795 + 5381498 * 2 ^ 59
def prefixEnd_5381498 : Nat := 4983230072969 + 3 ^ 40 * 5381498 * 2
def baseEnd_5381498 : Nat := 2763295115209491098025947

theorem tailTrace_5381498 : CollatzResearch.WordTrace tailWord_5381498 prefixEnd_5381498 2763295115209491098025947 := by
  unfold tailWord_5381498
  simp only [CollatzResearch.WordTrace]
  refine ⟨49069839264439826882820287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130852904705172871687520765 49069839264439826882820287)
  ·
    refine ⟨73604758896659740324230431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49069839264439826882820287 73604758896659740324230431)
    ·
      refine ⟨110407138344989610486345647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73604758896659740324230431 110407138344989610486345647)
      ·
        refine ⟨165610707517484415729518471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110407138344989610486345647 165610707517484415729518471)
        ·
          refine ⟨248416061276226623594277707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165610707517484415729518471 248416061276226623594277707)
          ·
            refine ⟨372624091914339935391416561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 248416061276226623594277707 372624091914339935391416561)
            ·
              refine ⟨279468068935754951543562421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 372624091914339935391416561 279468068935754951543562421)
              ·
                refine ⟨26200131462727026707208977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 279468068935754951543562421 26200131462727026707208977)
                ·
                  refine ⟨19650098597045270030406733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26200131462727026707208977 19650098597045270030406733)
                  ·
                    refine ⟨7368786973891976261402525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19650098597045270030406733 7368786973891976261402525)
                    ·
                      refine ⟨2763295115209491098025947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7368786973891976261402525 2763295115209491098025947)
                      ·
                        rfl

theorem cell23_5381498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 5, 2, 3, 3].length) (baseStart_5381498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5381498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5381498 prefixEnd_5381498 := by exact prefixLift 5381498
  have htrace : WordTrace (prefixWord ++ tailWord_5381498) baseStart_5381498 baseEnd_5381498 := by
    simpa [prefixWord, tailWord_5381498, baseEnd_5381498] using wordTrace_append hprefix tailTrace_5381498
  have hstable : (prefixWord ++ tailWord_5381498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5381498).length < 2 ^ (prefixWord ++ tailWord_5381498).sum := by decide
  have hdescent : baseEnd_5381498 < baseStart_5381498 := by decide
  rcases family_descends (prefixWord ++ tailWord_5381498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5381505 : List Nat := [1, 2, 4, 3, 2, 1, 1, 2, 7]
def baseStart_5381505 : Nat := 118140960795 + 5381505 * 2 ^ 59
def prefixEnd_5381505 : Nat := 4983230072969 + 3 ^ 40 * 5381505 * 2
def baseEnd_5381505 : Nat := 307033189952674730070935

theorem tailTrace_5381505 : CollatzResearch.WordTrace tailWord_5381505 prefixEnd_5381505 307033189952674730070935 := by
  unfold tailWord_5381505
  simp only [CollatzResearch.WordTrace]
  refine ⟨196279612368733947726785969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130853074912489298484523979 196279612368733947726785969)
  ·
    refine ⟨147209709276550460795089477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196279612368733947726785969 147209709276550460795089477)
    ·
      refine ⟨27601820489353211399079277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 147209709276550460795089477 27601820489353211399079277)
      ·
        refine ⟨10350682683507454274654729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27601820489353211399079277 10350682683507454274654729)
        ·
          refine ⟨7763012012630590705991047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10350682683507454274654729 7763012012630590705991047)
          ·
            refine ⟨11644518018945886058986571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7763012012630590705991047 11644518018945886058986571)
            ·
              refine ⟨17466777028418829088479857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11644518018945886058986571 17466777028418829088479857)
              ·
                refine ⟨13100082771314121816359893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17466777028418829088479857 13100082771314121816359893)
                ·
                  refine ⟨307033189952674730070935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13100082771314121816359893 307033189952674730070935)
                  ·
                    rfl

theorem cell23_5381505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 2, 7].length) (baseStart_5381505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5381505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5381505 prefixEnd_5381505 := by exact prefixLift 5381505
  have htrace : WordTrace (prefixWord ++ tailWord_5381505) baseStart_5381505 baseEnd_5381505 := by
    simpa [prefixWord, tailWord_5381505, baseEnd_5381505] using wordTrace_append hprefix tailTrace_5381505
  have hstable : (prefixWord ++ tailWord_5381505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5381505).length < 2 ^ (prefixWord ++ tailWord_5381505).sum := by decide
  have hdescent : baseEnd_5381505 < baseStart_5381505 := by decide
  rcases family_descends (prefixWord ++ tailWord_5381505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5381531 : List Nat := [1, 1, 1, 1, 1, 1, 2, 1, 6, 8]
def baseStart_5381531 : Nat := 118140960795 + 5381531 * 2 ^ 59
def prefixEnd_5381531 : Nat := 4983230072969 + 3 ^ 40 * 5381531 * 2
def baseEnd_5381531 : Nat := 921104020023696489637765

theorem tailTrace_5381531 : CollatzResearch.WordTrace tailWord_5381531 prefixEnd_5381531 921104020023696489637765 := by
  unfold tailWord_5381531
  simp only [CollatzResearch.WordTrace]
  refine ⟨196280560666639754167232447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130853707111093169444821631 196280560666639754167232447)
  ·
    refine ⟨294420840999959631250848671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196280560666639754167232447 294420840999959631250848671)
    ·
      refine ⟨441631261499939446876273007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294420840999959631250848671 441631261499939446876273007)
      ·
        refine ⟨662446892249909170314409511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 441631261499939446876273007 662446892249909170314409511)
        ·
          refine ⟨993670338374863755471614267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 662446892249909170314409511 993670338374863755471614267)
          ·
            refine ⟨1490505507562295633207421401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 993670338374863755471614267 1490505507562295633207421401)
            ·
              refine ⟨1117879130671721724905566051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1490505507562295633207421401 1117879130671721724905566051)
              ·
                refine ⟨1676818696007582587358349077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1117879130671721724905566051 1676818696007582587358349077)
                ·
                  refine ⟨78600876375355433782422613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1676818696007582587358349077 78600876375355433782422613)
                  ·
                    refine ⟨921104020023696489637765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 78600876375355433782422613 921104020023696489637765)
                    ·
                      rfl

theorem cell23_5381531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 6, 8].length) (baseStart_5381531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5381531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5381531 prefixEnd_5381531 := by exact prefixLift 5381531
  have htrace : WordTrace (prefixWord ++ tailWord_5381531) baseStart_5381531 baseEnd_5381531 := by
    simpa [prefixWord, tailWord_5381531, baseEnd_5381531] using wordTrace_append hprefix tailTrace_5381531
  have hstable : (prefixWord ++ tailWord_5381531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5381531).length < 2 ^ (prefixWord ++ tailWord_5381531).sum := by decide
  have hdescent : baseEnd_5381531 < baseStart_5381531 := by decide
  rcases family_descends (prefixWord ++ tailWord_5381531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5381565 : List Nat := [1, 4, 1, 2, 2, 1, 1, 4, 3, 4]
def baseStart_5381565 : Nat := 118140960795 + 5381565 * 2 ^ 59
def prefixEnd_5381565 : Nat := 4983230072969 + 3 ^ 40 * 5381565 * 2
def baseEnd_5381565 : Nat := 921109839471114111962713

theorem tailTrace_5381565 : CollatzResearch.WordTrace tailWord_5381565 prefixEnd_5381565 921109839471114111962713 := by
  unfold tailWord_5381565
  simp only [CollatzResearch.WordTrace]
  refine ⟨196281800748516577973970149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130854533832344385315980099 196281800748516577973970149)
  ·
    refine ⟨36802837640346858370119403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 196281800748516577973970149 36802837640346858370119403)
    ·
      refine ⟨55204256460520287555179105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36802837640346858370119403 55204256460520287555179105)
      ·
        refine ⟨41403192345390215666384329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55204256460520287555179105 41403192345390215666384329)
        ·
          refine ⟨31052394259042661749788247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41403192345390215666384329 31052394259042661749788247)
          ·
            refine ⟨46578591388563992624682371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31052394259042661749788247 46578591388563992624682371)
            ·
              refine ⟨69867887082845988937023557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46578591388563992624682371 69867887082845988937023557)
              ·
                refine ⟨13100228828033622925691917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69867887082845988937023557 13100228828033622925691917)
                ·
                  refine ⟨4912585810512608597134469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13100228828033622925691917 4912585810512608597134469)
                  ·
                    refine ⟨921109839471114111962713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4912585810512608597134469 921109839471114111962713)
                    ·
                      rfl

theorem cell23_5381565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 4, 3, 4].length) (baseStart_5381565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5381565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5381565 prefixEnd_5381565 := by exact prefixLift 5381565
  have htrace : WordTrace (prefixWord ++ tailWord_5381565) baseStart_5381565 baseEnd_5381565 := by
    simpa [prefixWord, tailWord_5381565, baseEnd_5381565] using wordTrace_append hprefix tailTrace_5381565
  have hstable : (prefixWord ++ tailWord_5381565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5381565).length < 2 ^ (prefixWord ++ tailWord_5381565).sum := by decide
  have hdescent : baseEnd_5381565 < baseStart_5381565 := by decide
  rcases family_descends (prefixWord ++ tailWord_5381565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5381575 : List Nat := [1, 1, 4, 1, 1, 3, 2, 3, 2, 2, 3]
def baseStart_5381575 : Nat := 118140960795 + 5381575 * 2 ^ 59
def prefixEnd_5381575 : Nat := 4983230072969 + 3 ^ 40 * 5381575 * 2
def baseEnd_5381575 : Nat := 2763334653219887296763093

theorem tailTrace_5381575 : CollatzResearch.WordTrace tailWord_5381575 prefixEnd_5381575 2763334653219887296763093 := by
  unfold tailWord_5381575
  simp only [CollatzResearch.WordTrace]
  refine ⟨196282165478480349681834179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130854776985653566454556119 196282165478480349681834179)
  ·
    refine ⟨294423248217720524522751269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196282165478480349681834179 294423248217720524522751269)
    ·
      refine ⟨55204359040822598348015863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 294423248217720524522751269 55204359040822598348015863)
      ·
        refine ⟨82806538561233897522023795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55204359040822598348015863 82806538561233897522023795)
        ·
          refine ⟨124209807841850846283035693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82806538561233897522023795 124209807841850846283035693)
          ·
            refine ⟨46578677940694067356138385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 124209807841850846283035693 46578677940694067356138385)
            ·
              refine ⟨34934008455520550517103789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46578677940694067356138385 34934008455520550517103789)
              ·
                refine ⟨13100253170820206443913921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34934008455520550517103789 13100253170820206443913921)
                ·
                  refine ⟨9825189878115154832935441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13100253170820206443913921 9825189878115154832935441)
                  ·
                    refine ⟨7368892408586366124701581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9825189878115154832935441 7368892408586366124701581)
                    ·
                      refine ⟨2763334653219887296763093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7368892408586366124701581 2763334653219887296763093)
                      ·
                        rfl

theorem cell23_5381575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 3, 2, 2, 3].length) (baseStart_5381575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5381575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5381575 prefixEnd_5381575 := by exact prefixLift 5381575
  have htrace : WordTrace (prefixWord ++ tailWord_5381575) baseStart_5381575 baseEnd_5381575 := by
    simpa [prefixWord, tailWord_5381575, baseEnd_5381575] using wordTrace_append hprefix tailTrace_5381575
  have hstable : (prefixWord ++ tailWord_5381575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5381575).length < 2 ^ (prefixWord ++ tailWord_5381575).sum := by decide
  have hdescent : baseEnd_5381575 < baseStart_5381575 := by decide
  rcases family_descends (prefixWord ++ tailWord_5381575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5381578 : List Nat := [3, 1, 2, 1, 2, 3, 1, 2, 8]
def baseStart_5381578 : Nat := 118140960795 + 5381578 * 2 ^ 59
def prefixEnd_5381578 : Nat := 4983230072969 + 3 ^ 40 * 5381578 * 2
def baseEnd_5381578 : Nat := 307037354851316753891731

theorem tailTrace_5381578 : CollatzResearch.WordTrace tailWord_5381578 prefixEnd_5381578 307037354851316753891731 := by
  unfold tailWord_5381578
  simp only [CollatzResearch.WordTrace]
  refine ⟨49070568724367370298548347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130854849931646320796128925 49070568724367370298548347)
  ·
    refine ⟨73605853086551055447822521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49070568724367370298548347 73605853086551055447822521)
    ·
      refine ⟨55204389814913291585866891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73605853086551055447822521 55204389814913291585866891)
      ·
        refine ⟨82806584722369937378800337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55204389814913291585866891 82806584722369937378800337)
        ·
          refine ⟨62104938541777453034100253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82806584722369937378800337 62104938541777453034100253)
          ·
            refine ⟨23289351953166544887787595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62104938541777453034100253 23289351953166544887787595)
            ·
              refine ⟨34934027929749817331681393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23289351953166544887787595 34934027929749817331681393)
              ·
                refine ⟨26200520947312362998761045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34934027929749817331681393 26200520947312362998761045)
                ·
                  refine ⟨307037354851316753891731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26200520947312362998761045 307037354851316753891731)
                  ·
                    rfl

theorem cell23_5381578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 2, 8].length) (baseStart_5381578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5381578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5381578 prefixEnd_5381578 := by exact prefixLift 5381578
  have htrace : WordTrace (prefixWord ++ tailWord_5381578) baseStart_5381578 baseEnd_5381578 := by
    simpa [prefixWord, tailWord_5381578, baseEnd_5381578] using wordTrace_append hprefix tailTrace_5381578
  have hstable : (prefixWord ++ tailWord_5381578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5381578).length < 2 ^ (prefixWord ++ tailWord_5381578).sum := by decide
  have hdescent : baseEnd_5381578 < baseStart_5381578 := by decide
  rcases family_descends (prefixWord ++ tailWord_5381578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5381599 : List Nat := [1, 1, 2, 3, 3, 1, 5, 2, 1, 4]
def baseStart_5381599 : Nat := 118140960795 + 5381599 * 2 ^ 59
def prefixEnd_5381599 : Nat := 4983230072969 + 3 ^ 40 * 5381599 * 2
def baseEnd_5381599 : Nat := 921115658918531734287661

theorem tailTrace_5381599 : CollatzResearch.WordTrace tailWord_5381599 prefixEnd_5381599 921115658918531734287661 := by
  unfold tailWord_5381599
  simp only [CollatzResearch.WordTrace]
  refine ⟨196283040830393401780707851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130855360553595601187138567 196283040830393401780707851)
  ·
    refine ⟨294424561245590102671061777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196283040830393401780707851 294424561245590102671061777)
    ·
      refine ⟨220818420934192577003296333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 294424561245590102671061777 220818420934192577003296333)
      ·
        refine ⟨82806907850322216376236125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 220818420934192577003296333 82806907850322216376236125)
        ·
          refine ⟨31052590443870831141088547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82806907850322216376236125 31052590443870831141088547)
          ·
            refine ⟨46578885665806246711632821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31052590443870831141088547 46578885665806246711632821)
            ·
              refine ⟨4366770531169335629215577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46578885665806246711632821 4366770531169335629215577)
              ·
                refine ⟨3275077898377001721911683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4366770531169335629215577 3275077898377001721911683)
                ·
                  refine ⟨4912616847565502582867525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3275077898377001721911683 4912616847565502582867525)
                  ·
                    refine ⟨921115658918531734287661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4912616847565502582867525 921115658918531734287661)
                    ·
                      rfl

theorem cell23_5381599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 5, 2, 1, 4].length) (baseStart_5381599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5381599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5381599 prefixEnd_5381599 := by exact prefixLift 5381599
  have htrace : WordTrace (prefixWord ++ tailWord_5381599) baseStart_5381599 baseEnd_5381599 := by
    simpa [prefixWord, tailWord_5381599, baseEnd_5381599] using wordTrace_append hprefix tailTrace_5381599
  have hstable : (prefixWord ++ tailWord_5381599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5381599).length < 2 ^ (prefixWord ++ tailWord_5381599).sum := by decide
  have hdescent : baseEnd_5381599 < baseStart_5381599 := by decide
  rcases family_descends (prefixWord ++ tailWord_5381599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5381615 : List Nat := [1, 1, 2, 1, 4, 1, 2, 1, 3, 5, 2]
def baseStart_5381615 : Nat := 118140960795 + 5381615 * 2 ^ 59
def prefixEnd_5381615 : Nat := 4983230072969 + 3 ^ 40 * 5381615 * 2
def baseEnd_5381615 : Nat := 2763355192446067140262909

theorem tailTrace_5381615 : CollatzResearch.WordTrace tailWord_5381615 prefixEnd_5381615 2763355192446067140262909 := by
  unfold tailWord_5381615
  simp only [CollatzResearch.WordTrace]
  refine ⟨196283624398335436513290299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130855749598890291008860199 196283624398335436513290299)
  ·
    refine ⟨294425436597503154769935449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196283624398335436513290299 294425436597503154769935449)
    ·
      refine ⟨220819077448127366077451587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 294425436597503154769935449 220819077448127366077451587)
      ·
        refine ⟨331228616172191049116177381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220819077448127366077451587 331228616172191049116177381)
        ·
          refine ⟨62105365532285821709283259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 331228616172191049116177381 62105365532285821709283259)
          ·
            refine ⟨93158048298428732563924889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62105365532285821709283259 93158048298428732563924889)
            ·
              refine ⟨69868536223821549422943667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93158048298428732563924889 69868536223821549422943667)
              ·
                refine ⟨104802804335732324134415501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69868536223821549422943667 104802804335732324134415501)
                ·
                  refine ⟨39301051625899621550405813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 104802804335732324134415501 39301051625899621550405813)
                  ·
                    refine ⟨3684473589928089520350545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39301051625899621550405813 3684473589928089520350545)
                    ·
                      refine ⟨2763355192446067140262909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3684473589928089520350545 2763355192446067140262909)
                      ·
                        rfl

theorem cell23_5381615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 3, 5, 2].length) (baseStart_5381615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5381615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5381615 prefixEnd_5381615 := by exact prefixLift 5381615
  have htrace : WordTrace (prefixWord ++ tailWord_5381615) baseStart_5381615 baseEnd_5381615 := by
    simpa [prefixWord, tailWord_5381615, baseEnd_5381615] using wordTrace_append hprefix tailTrace_5381615
  have hstable : (prefixWord ++ tailWord_5381615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5381615).length < 2 ^ (prefixWord ++ tailWord_5381615).sum := by decide
  have hdescent : baseEnd_5381615 < baseStart_5381615 := by decide
  rcases family_descends (prefixWord ++ tailWord_5381615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5381656 : List Nat := [2, 1, 2, 3, 4, 1, 1, 4, 1, 1, 3]
def baseStart_5381656 : Nat := 118140960795 + 5381656 * 2 ^ 59
def prefixEnd_5381656 : Nat := 4983230072969 + 3 ^ 40 * 5381656 * 2
def baseEnd_5381656 : Nat := 2763376245152901479850221

theorem tailTrace_5381656 : CollatzResearch.WordTrace tailWord_5381656 prefixEnd_5381656 2763376245152901479850221 := by
  unfold tailWord_5381656
  simp only [CollatzResearch.WordTrace]
  refine ⟨98142559895593450257766411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130856746527457933677021881 98142559895593450257766411)
  ·
    refine ⟨147213839843390175386649617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98142559895593450257766411 147213839843390175386649617)
    ·
      refine ⟨110410379882542631539987213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147213839843390175386649617 110410379882542631539987213)
      ·
        refine ⟨41403892455953486827495205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110410379882542631539987213 41403892455953486827495205)
        ·
          refine ⟨7763229835491278780155351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41403892455953486827495205 7763229835491278780155351)
          ·
            refine ⟨11644844753236918170233027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7763229835491278780155351 11644844753236918170233027)
            ·
              refine ⟨17467267129855377255349541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11644844753236918170233027 17467267129855377255349541)
              ·
                refine ⟨3275112586847883235378039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17467267129855377255349541 3275112586847883235378039)
                ·
                  refine ⟨4912668880271824853067059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3275112586847883235378039 4912668880271824853067059)
                  ·
                    refine ⟨7369003320407737279600589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4912668880271824853067059 7369003320407737279600589)
                    ·
                      refine ⟨2763376245152901479850221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7369003320407737279600589 2763376245152901479850221)
                      ·
                        rfl

theorem cell23_5381656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 4, 1, 1, 3].length) (baseStart_5381656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5381656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5381656 prefixEnd_5381656 := by exact prefixLift 5381656
  have htrace : WordTrace (prefixWord ++ tailWord_5381656) baseStart_5381656 baseEnd_5381656 := by
    simpa [prefixWord, tailWord_5381656, baseEnd_5381656] using wordTrace_append hprefix tailTrace_5381656
  have hstable : (prefixWord ++ tailWord_5381656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5381656).length < 2 ^ (prefixWord ++ tailWord_5381656).sum := by decide
  have hdescent : baseEnd_5381656 < baseStart_5381656 := by decide
  rcases family_descends (prefixWord ++ tailWord_5381656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5381682 : List Nat := [3, 2, 1, 1, 2, 1, 1, 6, 1, 2, 3]
def baseStart_5381682 : Nat := 118140960795 + 5381682 * 2 ^ 59
def prefixEnd_5381682 : Nat := 4983230072969 + 3 ^ 40 * 5381682 * 2
def baseEnd_5381682 : Nat := 2763389595649918378125101

theorem tailTrace_5381682 : CollatzResearch.WordTrace tailWord_5381682 prefixEnd_5381682 2763389595649918378125101 := by
  unfold tailWord_5381682
  simp only [CollatzResearch.WordTrace]
  refine ⟨49071517022273176738994825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130857378726061804637319533 49071517022273176738994825)
  ·
    refine ⟨36803637766704882554246119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49071517022273176738994825 36803637766704882554246119)
    ·
      refine ⟨55205456650057323831369179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36803637766704882554246119 55205456650057323831369179)
      ·
        refine ⟨82808184975085985747053769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55205456650057323831369179 82808184975085985747053769)
        ·
          refine ⟨62106138731314489310290327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82808184975085985747053769 62106138731314489310290327)
          ·
            refine ⟨93159208096971733965435491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62106138731314489310290327 93159208096971733965435491)
            ·
              refine ⟨139738812145457600948153237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93159208096971733965435491 139738812145457600948153237)
              ·
                refine ⟨6550256819318325044444683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 139738812145457600948153237 6550256819318325044444683)
                ·
                  refine ⟨9825385228977487566667025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6550256819318325044444683 9825385228977487566667025)
                  ·
                    refine ⟨7369038921733115675000269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9825385228977487566667025 7369038921733115675000269)
                    ·
                      refine ⟨2763389595649918378125101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7369038921733115675000269 2763389595649918378125101)
                      ·
                        rfl

theorem cell23_5381682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 6, 1, 2, 3].length) (baseStart_5381682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5381682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5381682 prefixEnd_5381682 := by exact prefixLift 5381682
  have htrace : WordTrace (prefixWord ++ tailWord_5381682) baseStart_5381682 baseEnd_5381682 := by
    simpa [prefixWord, tailWord_5381682, baseEnd_5381682] using wordTrace_append hprefix tailTrace_5381682
  have hstable : (prefixWord ++ tailWord_5381682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5381682).length < 2 ^ (prefixWord ++ tailWord_5381682).sum := by decide
  have hdescent : baseEnd_5381682 < baseStart_5381682 := by decide
  rcases family_descends (prefixWord ++ tailWord_5381682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5381712 : List Nat := [2, 1, 1, 1, 1, 3, 5, 1, 4, 1, 3]
def baseStart_5381712 : Nat := 118140960795 + 5381712 * 2 ^ 59
def prefixEnd_5381712 : Nat := 4983230072969 + 3 ^ 40 * 5381712 * 2
def baseEnd_5381712 : Nat := 2763405000069553260749963

theorem tailTrace_5381712 : CollatzResearch.WordTrace tailWord_5381712 prefixEnd_5381712 2763405000069553260749963 := by
  unfold tailWord_5381712
  simp only [CollatzResearch.WordTrace]
  refine ⟨98143581139492011039785695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130858108185989348053047593 98143581139492011039785695)
  ·
    refine ⟨147215371709238016559678543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98143581139492011039785695 147215371709238016559678543)
    ·
      refine ⟨220823057563857024839517815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147215371709238016559678543 220823057563857024839517815)
      ·
        refine ⟨331234586345785537259276723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220823057563857024839517815 331234586345785537259276723)
        ·
          refine ⟨496851879518678305888915085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 331234586345785537259276723 496851879518678305888915085)
          ·
            refine ⟨186319454819504364708343157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 496851879518678305888915085 186319454819504364708343157)
            ·
              refine ⟨17467448889328534191407171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 186319454819504364708343157 17467448889328534191407171)
              ·
                refine ⟨26201173333992801287110757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17467448889328534191407171 26201173333992801287110757)
                ·
                  refine ⟨4912720000123650241333267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26201173333992801287110757 4912720000123650241333267)
                  ·
                    refine ⟨7369080000185475361999901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4912720000123650241333267 7369080000185475361999901)
                    ·
                      refine ⟨2763405000069553260749963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7369080000185475361999901 2763405000069553260749963)
                      ·
                        rfl

theorem cell23_5381712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 1, 4, 1, 3].length) (baseStart_5381712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5381712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5381712 prefixEnd_5381712 := by exact prefixLift 5381712
  have htrace : WordTrace (prefixWord ++ tailWord_5381712) baseStart_5381712 baseEnd_5381712 := by
    simpa [prefixWord, tailWord_5381712, baseEnd_5381712] using wordTrace_append hprefix tailTrace_5381712
  have hstable : (prefixWord ++ tailWord_5381712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5381712).length < 2 ^ (prefixWord ++ tailWord_5381712).sum := by decide
  have hdescent : baseEnd_5381712 < baseStart_5381712 := by decide
  rcases family_descends (prefixWord ++ tailWord_5381712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5381722 : List Nat := [3, 1, 1, 2, 1, 1, 1, 3, 5, 3, 2]
def baseStart_5381722 : Nat := 118140960795 + 5381722 * 2 ^ 59
def prefixEnd_5381722 : Nat := 4983230072969 + 3 ^ 40 * 5381722 * 2
def baseEnd_5381722 : Nat := 2763410134876098221624917

theorem tailTrace_5381722 : CollatzResearch.WordTrace tailWord_5381722 prefixEnd_5381722 2763410134876098221624917 := by
  unfold tailWord_5381722
  simp only [CollatzResearch.WordTrace]
  refine ⟨49071881752236948446858855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130858351339298529191623613 49071881752236948446858855)
  ·
    refine ⟨73607822628355422670288283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49071881752236948446858855 73607822628355422670288283)
    ·
      refine ⟨110411733942533134005432425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73607822628355422670288283 110411733942533134005432425)
      ·
        refine ⟨82808800456899850504074319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110411733942533134005432425 82808800456899850504074319)
        ·
          refine ⟨124213200685349775756111479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82808800456899850504074319 124213200685349775756111479)
          ·
            refine ⟨186319801028024663634167219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124213200685349775756111479 186319801028024663634167219)
            ·
              refine ⟨279479701542036995451250829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 186319801028024663634167219 279479701542036995451250829)
              ·
                refine ⟨104804888078263873294219061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 279479701542036995451250829 104804888078263873294219061)
                ·
                  refine ⟨9825458257337238121333037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 104804888078263873294219061 9825458257337238121333037)
                  ·
                    refine ⟨3684546846501464295499889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9825458257337238121333037 3684546846501464295499889)
                    ·
                      refine ⟨2763410134876098221624917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3684546846501464295499889 2763410134876098221624917)
                      ·
                        rfl

theorem cell23_5381722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 5, 3, 2].length) (baseStart_5381722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5381722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5381722 prefixEnd_5381722 := by exact prefixLift 5381722
  have htrace : WordTrace (prefixWord ++ tailWord_5381722) baseStart_5381722 baseEnd_5381722 := by
    simpa [prefixWord, tailWord_5381722, baseEnd_5381722] using wordTrace_append hprefix tailTrace_5381722
  have hstable : (prefixWord ++ tailWord_5381722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5381722).length < 2 ^ (prefixWord ++ tailWord_5381722).sum := by decide
  have hdescent : baseEnd_5381722 < baseStart_5381722 := by decide
  rcases family_descends (prefixWord ++ tailWord_5381722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5381735 : List Nat := [1, 1, 5, 1, 1, 1, 2, 2, 2, 3, 4]
def baseStart_5381735 : Nat := 118140960795 + 5381735 * 2 ^ 59
def prefixEnd_5381735 : Nat := 4983230072969 + 3 ^ 40 * 5381735 * 2
def baseEnd_5381735 : Nat := 2763416810124606670762357

theorem tailTrace_5381735 : CollatzResearch.WordTrace tailWord_5381735 prefixEnd_5381735 2763416810124606670762357 := by
  unfold tailWord_5381735
  simp only [CollatzResearch.WordTrace]
  refine ⟨196288001157900697007658659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130858667438600464671772439 196288001157900697007658659)
  ·
    refine ⟨294432001736851045511487989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196288001157900697007658659 294432001736851045511487989)
    ·
      refine ⟨27603000162829785516701999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 294432001736851045511487989 27603000162829785516701999)
      ·
        refine ⟨41404500244244678275052999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27603000162829785516701999 41404500244244678275052999)
        ·
          refine ⟨62106750366367017412579499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41404500244244678275052999 62106750366367017412579499)
          ·
            refine ⟨93160125549550526118869249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62106750366367017412579499 93160125549550526118869249)
            ·
              refine ⟨69870094162162894589151937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93160125549550526118869249 69870094162162894589151937)
              ·
                refine ⟨52402570621622170941863953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69870094162162894589151937 52402570621622170941863953)
                ·
                  refine ⟨39301927966216628206397965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52402570621622170941863953 39301927966216628206397965)
                  ·
                    refine ⟨14738222987331235577399237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39301927966216628206397965 14738222987331235577399237)
                    ·
                      refine ⟨2763416810124606670762357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14738222987331235577399237 2763416810124606670762357)
                      ·
                        rfl

theorem cell23_5381735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 2, 2, 3, 4].length) (baseStart_5381735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5381735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5381735 prefixEnd_5381735 := by exact prefixLift 5381735
  have htrace : WordTrace (prefixWord ++ tailWord_5381735) baseStart_5381735 baseEnd_5381735 := by
    simpa [prefixWord, tailWord_5381735, baseEnd_5381735] using wordTrace_append hprefix tailTrace_5381735
  have hstable : (prefixWord ++ tailWord_5381735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5381735).length < 2 ^ (prefixWord ++ tailWord_5381735).sum := by decide
  have hdescent : baseEnd_5381735 < baseStart_5381735 := by decide
  rcases family_descends (prefixWord ++ tailWord_5381735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5381755 : List Nat := [1, 1, 1, 1, 1, 4, 5, 1, 2, 1, 5]
def baseStart_5381755 : Nat := 118140960795 + 5381755 * 2 ^ 59
def prefixEnd_5381755 : Nat := 4983230072969 + 3 ^ 40 * 5381755 * 2
def baseEnd_5381755 : Nat := 2763427079737696592512265

theorem tailTrace_5381755 : CollatzResearch.WordTrace tailWord_5381755 prefixEnd_5381755 2763427079737696592512265 := by
  unfold tailWord_5381755
  simp only [CollatzResearch.WordTrace]
  refine ⟨196288730617828240423386719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130859153745218826948924479 196288730617828240423386719)
  ·
    refine ⟨294433095926742360635080079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196288730617828240423386719 294433095926742360635080079)
    ·
      refine ⟨441649643890113540952620119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294433095926742360635080079 441649643890113540952620119)
      ·
        refine ⟨662474465835170311428930179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 441649643890113540952620119 662474465835170311428930179)
        ·
          refine ⟨993711698752755467143395269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 662474465835170311428930179 993711698752755467143395269)
          ·
            refine ⟨186320943516141650089386613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 993711698752755467143395269 186320943516141650089386613)
            ·
              refine ⟨17467588454638279695879995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 186320943516141650089386613 17467588454638279695879995)
              ·
                refine ⟨26201382681957419543819993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17467588454638279695879995 26201382681957419543819993)
                ·
                  refine ⟨19651037011468064657864995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26201382681957419543819993 19651037011468064657864995)
                  ·
                    refine ⟨29476555517202096986797493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19651037011468064657864995 29476555517202096986797493)
                    ·
                      refine ⟨2763427079737696592512265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29476555517202096986797493 2763427079737696592512265)
                      ·
                        rfl

theorem cell23_5381755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 1, 2, 1, 5].length) (baseStart_5381755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5381755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5381755 prefixEnd_5381755 := by exact prefixLift 5381755
  have htrace : WordTrace (prefixWord ++ tailWord_5381755) baseStart_5381755 baseEnd_5381755 := by
    simpa [prefixWord, tailWord_5381755, baseEnd_5381755] using wordTrace_append hprefix tailTrace_5381755
  have hstable : (prefixWord ++ tailWord_5381755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5381755).length < 2 ^ (prefixWord ++ tailWord_5381755).sum := by decide
  have hdescent : baseEnd_5381755 < baseStart_5381755 := by decide
  rcases family_descends (prefixWord ++ tailWord_5381755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5381769 : List Nat := [1, 2, 1, 1, 4, 1, 4, 1, 4, 2, 2]
def baseStart_5381769 : Nat := 118140960795 + 5381769 * 2 ^ 59
def prefixEnd_5381769 : Nat := 4983230072969 + 3 ^ 40 * 5381769 * 2
def baseEnd_5381769 : Nat := 2763434268466859537737201

theorem tailTrace_5381769 : CollatzResearch.WordTrace tailWord_5381769 prefixEnd_5381769 2763434268466859537737201 := by
  unfold tailWord_5381769
  simp only [CollatzResearch.WordTrace]
  refine ⟨196289241239777520814396361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130859494159851680542930907 196289241239777520814396361)
  ·
    refine ⟨147216930929833140610797271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196289241239777520814396361 147216930929833140610797271)
    ·
      refine ⟨220825396394749710916195907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147216930929833140610797271 220825396394749710916195907)
      ·
        refine ⟨331238094592124566374293861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220825396394749710916195907 331238094592124566374293861)
        ·
          refine ⟨62107142736023356195180099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 331238094592124566374293861 62107142736023356195180099)
          ·
            refine ⟨93160714104035034292770149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62107142736023356195180099 93160714104035034292770149)
            ·
              refine ⟨17467633894506568929894403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 93160714104035034292770149 17467633894506568929894403)
              ·
                refine ⟨26201450841759853394841605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17467633894506568929894403 26201450841759853394841605)
                ·
                  refine ⟨4912772032829972511532801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26201450841759853394841605 4912772032829972511532801)
                  ·
                    refine ⟨3684579024622479383649601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4912772032829972511532801 3684579024622479383649601)
                    ·
                      refine ⟨2763434268466859537737201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3684579024622479383649601 2763434268466859537737201)
                      ·
                        rfl

theorem cell23_5381769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 1, 4, 2, 2].length) (baseStart_5381769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5381769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5381769 prefixEnd_5381769 := by exact prefixLift 5381769
  have htrace : WordTrace (prefixWord ++ tailWord_5381769) baseStart_5381769 baseEnd_5381769 := by
    simpa [prefixWord, tailWord_5381769, baseEnd_5381769] using wordTrace_append hprefix tailTrace_5381769
  have hstable : (prefixWord ++ tailWord_5381769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5381769).length < 2 ^ (prefixWord ++ tailWord_5381769).sum := by decide
  have hdescent : baseEnd_5381769 < baseStart_5381769 := by decide
  rcases family_descends (prefixWord ++ tailWord_5381769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5381780 : List Nat := [2, 4, 2, 2, 2, 2, 2, 1, 2, 1, 3]
def baseStart_5381780 : Nat := 118140960795 + 5381780 * 2 ^ 59
def prefixEnd_5381780 : Nat := 4983230072969 + 3 ^ 40 * 5381780 * 2
def baseEnd_5381780 : Nat := 2763439916754058994699651

theorem tailTrace_5381780 : CollatzResearch.WordTrace tailWord_5381780 prefixEnd_5381780 2763439916754058994699651 := by
  unfold tailWord_5381780
  simp only [CollatzResearch.WordTrace]
  refine ⟨98144821221368834846523397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130859761628491779795364529 98144821221368834846523397)
  ·
    refine ⟨18402153979006656533723137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98144821221368834846523397 18402153979006656533723137)
    ·
      refine ⟨13801615484254992400292353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18402153979006656533723137 13801615484254992400292353)
      ·
        refine ⟨10351211613191244300219265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13801615484254992400292353 10351211613191244300219265)
        ·
          refine ⟨7763408709893433225164449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10351211613191244300219265 7763408709893433225164449)
          ·
            refine ⟨5822556532420074918873337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7763408709893433225164449 5822556532420074918873337)
            ·
              refine ⟨4366917399315056189155003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5822556532420074918873337 4366917399315056189155003)
              ·
                refine ⟨6550376098972584283732505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4366917399315056189155003 6550376098972584283732505)
                ·
                  refine ⟨4912782074229438212799379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6550376098972584283732505 4912782074229438212799379)
                  ·
                    refine ⟨7369173111344157319199069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4912782074229438212799379 7369173111344157319199069)
                    ·
                      refine ⟨2763439916754058994699651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7369173111344157319199069 2763439916754058994699651)
                      ·
                        rfl

theorem cell23_5381780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 2, 1, 2, 1, 3].length) (baseStart_5381780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5381780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5381780 prefixEnd_5381780 := by exact prefixLift 5381780
  have htrace : WordTrace (prefixWord ++ tailWord_5381780) baseStart_5381780 baseEnd_5381780 := by
    simpa [prefixWord, tailWord_5381780, baseEnd_5381780] using wordTrace_append hprefix tailTrace_5381780
  have hstable : (prefixWord ++ tailWord_5381780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5381780).length < 2 ^ (prefixWord ++ tailWord_5381780).sum := by decide
  have hdescent : baseEnd_5381780 < baseStart_5381780 := by decide
  rcases family_descends (prefixWord ++ tailWord_5381780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5381859 : List Nat := [1, 1, 1, 7, 2, 1, 1, 1, 1, 3, 4]
def baseStart_5381859 : Nat := 118140960795 + 5381859 * 2 ^ 59
def prefixEnd_5381859 : Nat := 4983230072969 + 3 ^ 40 * 5381859 * 2
def baseEnd_5381859 : Nat := 2763480481725764185611787

theorem tailTrace_5381859 : CollatzResearch.WordTrace tailWord_5381859 prefixEnd_5381859 2763480481725764185611787 := by
  unfold tailWord_5381859
  simp only [CollatzResearch.WordTrace]
  refine ⟨196292523809451466185172631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130861682539634310790115087 196292523809451466185172631)
  ·
    refine ⟨294438785714177199277758947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196292523809451466185172631 294438785714177199277758947)
    ·
      refine ⟨441658178571265798916638421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294438785714177199277758947 441658178571265798916638421)
      ·
        refine ⟨10351363560264042162108713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 441658178571265798916638421 10351363560264042162108713)
        ·
          refine ⟨7763522670198031621581535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10351363560264042162108713 7763522670198031621581535)
          ·
            refine ⟨11645284005297047432372303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7763522670198031621581535 11645284005297047432372303)
            ·
              refine ⟨17467926007945571148558455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11645284005297047432372303 17467926007945571148558455)
              ·
                refine ⟨26201889011918356722837683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17467926007945571148558455 26201889011918356722837683)
                ·
                  refine ⟨39302833517877535084256525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26201889011918356722837683 39302833517877535084256525)
                  ·
                    refine ⟨14738562569204075656596197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39302833517877535084256525 14738562569204075656596197)
                    ·
                      refine ⟨2763480481725764185611787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14738562569204075656596197 2763480481725764185611787)
                      ·
                        rfl

theorem cell23_5381859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_5381859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5381859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5381859 prefixEnd_5381859 := by exact prefixLift 5381859
  have htrace : WordTrace (prefixWord ++ tailWord_5381859) baseStart_5381859 baseEnd_5381859 := by
    simpa [prefixWord, tailWord_5381859, baseEnd_5381859] using wordTrace_append hprefix tailTrace_5381859
  have hstable : (prefixWord ++ tailWord_5381859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5381859).length < 2 ^ (prefixWord ++ tailWord_5381859).sum := by decide
  have hdescent : baseEnd_5381859 < baseStart_5381859 := by decide
  rcases family_descends (prefixWord ++ tailWord_5381859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5381865 : List Nat := [1, 2, 1, 1, 1, 2, 3, 4, 8]
def baseStart_5381865 : Nat := 118140960795 + 5381865 * 2 ^ 59
def prefixEnd_5381865 : Nat := 4983230072969 + 3 ^ 40 * 5381865 * 2
def baseEnd_5381865 : Nat := 307053729178854573570751

theorem tailTrace_5381865 : CollatzResearch.WordTrace tailWord_5381865 prefixEnd_5381865 307053729178854573570751 := by
  unfold tailWord_5381865
  simp only [CollatzResearch.WordTrace]
  refine ⟨196292742647429729209891049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130861828431619819473260699 196292742647429729209891049)
  ·
    refine ⟨147219556985572296907418287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196292742647429729209891049 147219556985572296907418287)
    ·
      refine ⟨220829335478358445361127431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147219556985572296907418287 220829335478358445361127431)
      ·
        refine ⟨331244003217537668041691147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220829335478358445361127431 331244003217537668041691147)
        ·
          refine ⟨496866004826306502062536721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 331244003217537668041691147 496866004826306502062536721)
          ·
            refine ⟨372649503619729876546902541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 496866004826306502062536721 372649503619729876546902541)
            ·
              refine ⟨139743563857398703705088453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 372649503619729876546902541 139743563857398703705088453)
              ·
                refine ⟨26201918223262256944704085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 139743563857398703705088453 26201918223262256944704085)
                ·
                  refine ⟨307053729178854573570751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26201918223262256944704085 307053729178854573570751)
                  ·
                    rfl

theorem cell23_5381865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 4, 8].length) (baseStart_5381865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5381865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5381865 prefixEnd_5381865 := by exact prefixLift 5381865
  have htrace : WordTrace (prefixWord ++ tailWord_5381865) baseStart_5381865 baseEnd_5381865 := by
    simpa [prefixWord, tailWord_5381865, baseEnd_5381865] using wordTrace_append hprefix tailTrace_5381865
  have hstable : (prefixWord ++ tailWord_5381865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5381865).length < 2 ^ (prefixWord ++ tailWord_5381865).sum := by decide
  have hdescent : baseEnd_5381865 < baseStart_5381865 := by decide
  rcases family_descends (prefixWord ++ tailWord_5381865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5381912 : List Nat := [2, 1, 2, 3, 1, 1, 2, 3, 3, 5]
def baseStart_5381912 : Nat := 118140960795 + 5381912 * 2 ^ 59
def prefixEnd_5381912 : Nat := 4983230072969 + 3 ^ 40 * 5381912 * 2
def baseEnd_5381912 : Nat := 921169232066817492749681

theorem tailTrace_5381912 : CollatzResearch.WordTrace tailWord_5381912 prefixEnd_5381912 921169232066817492749681 := by
  unfold tailWord_5381912
  simp only [CollatzResearch.WordTrace]
  refine ⟨98147228439129728118425995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130862971252172970824567993 98147228439129728118425995)
  ·
    refine ⟨147220842658694592177638993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98147228439129728118425995 147220842658694592177638993)
    ·
      refine ⟨110415631994020944133229245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147220842658694592177638993 110415631994020944133229245)
      ·
        refine ⟨41405861997757854049960967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110415631994020944133229245 41405861997757854049960967)
        ·
          refine ⟨62108792996636781074941451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41405861997757854049960967 62108792996636781074941451)
          ·
            refine ⟨93163189494955171612412177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62108792996636781074941451 93163189494955171612412177)
            ·
              refine ⟨69872392121216378709309133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93163189494955171612412177 69872392121216378709309133)
              ·
                refine ⟨26202147045456142015990925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69872392121216378709309133 26202147045456142015990925)
                ·
                  refine ⟨9825805142046053255996597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26202147045456142015990925 9825805142046053255996597)
                  ·
                    refine ⟨921169232066817492749681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9825805142046053255996597 921169232066817492749681)
                    ·
                      rfl

theorem cell23_5381912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 3, 3, 5].length) (baseStart_5381912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5381912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5381912 prefixEnd_5381912 := by exact prefixLift 5381912
  have htrace : WordTrace (prefixWord ++ tailWord_5381912) baseStart_5381912 baseEnd_5381912 := by
    simpa [prefixWord, tailWord_5381912, baseEnd_5381912] using wordTrace_append hprefix tailTrace_5381912
  have hstable : (prefixWord ++ tailWord_5381912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5381912).length < 2 ^ (prefixWord ++ tailWord_5381912).sum := by decide
  have hdescent : baseEnd_5381912 < baseStart_5381912 := by decide
  rcases family_descends (prefixWord ++ tailWord_5381912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5381919 : List Nat := [1, 1, 2, 4, 2, 1, 1, 3, 1, 5, 2]
def baseStart_5381919 : Nat := 118140960795 + 5381919 * 2 ^ 59
def prefixEnd_5381919 : Nat := 4983230072969 + 3 ^ 40 * 5381919 * 2
def baseEnd_5381919 : Nat := 2763511290565033950861511

theorem tailTrace_5381919 : CollatzResearch.WordTrace tailWord_5381919 prefixEnd_5381919 2763511290565033950861511 := by
  unfold tailWord_5381919
  simp only [CollatzResearch.WordTrace]
  refine ⟨196294712189234096432356811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130863141459489397621571207 196294712189234096432356811)
  ·
    refine ⟨294442068283851144648535217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196294712189234096432356811 294442068283851144648535217)
    ·
      refine ⟨220831551212888358486401413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 294442068283851144648535217 220831551212888358486401413)
      ·
        refine ⟨41405915852416567216200265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 220831551212888358486401413 41405915852416567216200265)
        ·
          refine ⟨31054436889312425412150199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41405915852416567216200265 31054436889312425412150199)
          ·
            refine ⟨46581655333968638118225299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31054436889312425412150199 46581655333968638118225299)
            ·
              refine ⟨69872483000952957177337949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46581655333968638118225299 69872483000952957177337949)
              ·
                refine ⟨26202181125357358941501731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69872483000952957177337949 26202181125357358941501731)
                ·
                  refine ⟨39303271688036038412252597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26202181125357358941501731 39303271688036038412252597)
                  ·
                    refine ⟨3684681720753378601148681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39303271688036038412252597 3684681720753378601148681)
                    ·
                      refine ⟨2763511290565033950861511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3684681720753378601148681 2763511290565033950861511)
                      ·
                        rfl

theorem cell23_5381919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 3, 1, 5, 2].length) (baseStart_5381919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5381919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5381919 prefixEnd_5381919 := by exact prefixLift 5381919
  have htrace : WordTrace (prefixWord ++ tailWord_5381919) baseStart_5381919 baseEnd_5381919 := by
    simpa [prefixWord, tailWord_5381919, baseEnd_5381919] using wordTrace_append hprefix tailTrace_5381919
  have hstable : (prefixWord ++ tailWord_5381919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5381919).length < 2 ^ (prefixWord ++ tailWord_5381919).sum := by decide
  have hdescent : baseEnd_5381919 < baseStart_5381919 := by decide
  rcases family_descends (prefixWord ++ tailWord_5381919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5381952 : List Nat := [2, 1, 1, 2, 2, 1, 1, 1, 1, 8, 3]
def baseStart_5381952 : Nat := 118140960795 + 5381952 * 2 ^ 59
def prefixEnd_5381952 : Nat := 4983230072969 + 3 ^ 40 * 5381952 * 2
def baseEnd_5381952 : Nat := 2763528235426632321748859

theorem tailTrace_5381952 : CollatzResearch.WordTrace tailWord_5381952 prefixEnd_5381952 2763528235426632321748859 := by
  unfold tailWord_5381952
  simp only [CollatzResearch.WordTrace]
  refine ⟨98147957899057271534154055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130863943865409695378872073 98147957899057271534154055)
  ·
    refine ⟨147221936848585907301231083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98147957899057271534154055 147221936848585907301231083)
    ·
      refine ⟨220832905272878860951846625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147221936848585907301231083 220832905272878860951846625)
      ·
        refine ⟨165624678954659145713884969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 220832905272878860951846625 165624678954659145713884969)
        ·
          refine ⟨124218509215994359285413727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165624678954659145713884969 124218509215994359285413727)
          ·
            refine ⟨186327763823991538928120591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124218509215994359285413727 186327763823991538928120591)
            ·
              refine ⟨279491645735987308392180887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 186327763823991538928120591 279491645735987308392180887)
              ·
                refine ⟨419237468603980962588271331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 279491645735987308392180887 419237468603980962588271331)
                ·
                  refine ⟨628856202905971443882406997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 419237468603980962588271331 628856202905971443882406997)
                  ·
                    refine ⟨7369408627804352857996957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 628856202905971443882406997 7369408627804352857996957)
                    ·
                      refine ⟨2763528235426632321748859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7369408627804352857996957 2763528235426632321748859)
                      ·
                        rfl

theorem cell23_5381952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 1, 8, 3].length) (baseStart_5381952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5381952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5381952 prefixEnd_5381952 := by exact prefixLift 5381952
  have htrace : WordTrace (prefixWord ++ tailWord_5381952) baseStart_5381952 baseEnd_5381952 := by
    simpa [prefixWord, tailWord_5381952, baseEnd_5381952] using wordTrace_append hprefix tailTrace_5381952
  have hstable : (prefixWord ++ tailWord_5381952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5381952).length < 2 ^ (prefixWord ++ tailWord_5381952).sum := by decide
  have hdescent : baseEnd_5381952 < baseStart_5381952 := by decide
  rcases family_descends (prefixWord ++ tailWord_5381952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5381962 : List Nat := [3, 1, 2, 1, 1, 1, 3, 3, 1, 1, 6]
def baseStart_5381962 : Nat := 118140960795 + 5381962 * 2 ^ 59
def prefixEnd_5381962 : Nat := 4983230072969 + 3 ^ 40 * 5381962 * 2
def baseEnd_5381962 : Nat := 2763533370233177282623813

theorem tailTrace_5381962 : CollatzResearch.WordTrace tailWord_5381962 prefixEnd_5381962 2763533370233177282623813 := by
  unfold tailWord_5381962
  simp only [CollatzResearch.WordTrace]
  refine ⟨49074070132019578694043035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130864187018718876517448093 49074070132019578694043035)
  ·
    refine ⟨73611105198029368041064553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49074070132019578694043035 73611105198029368041064553)
    ·
      refine ⟨55208328898522026030798415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73611105198029368041064553 55208328898522026030798415)
      ·
        refine ⟨82812493347783039046197623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55208328898522026030798415 82812493347783039046197623)
        ·
          refine ⟨124218740021674558569296435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82812493347783039046197623 124218740021674558569296435)
          ·
            refine ⟨186328110032511837853944653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124218740021674558569296435 186328110032511837853944653)
            ·
              refine ⟨69873041262191939195229245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 186328110032511837853944653 69873041262191939195229245)
              ·
                refine ⟨26202390473321977198210967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69873041262191939195229245 26202390473321977198210967)
                ·
                  refine ⟨39303585709982965797316451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26202390473321977198210967 39303585709982965797316451)
                  ·
                    refine ⟨58955378564974448695974677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39303585709982965797316451 58955378564974448695974677)
                    ·
                      refine ⟨2763533370233177282623813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58955378564974448695974677 2763533370233177282623813)
                      ·
                        rfl

theorem cell23_5381962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 3, 1, 1, 6].length) (baseStart_5381962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5381962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5381962 prefixEnd_5381962 := by exact prefixLift 5381962
  have htrace : WordTrace (prefixWord ++ tailWord_5381962) baseStart_5381962 baseEnd_5381962 := by
    simpa [prefixWord, tailWord_5381962, baseEnd_5381962] using wordTrace_append hprefix tailTrace_5381962
  have hstable : (prefixWord ++ tailWord_5381962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5381962).length < 2 ^ (prefixWord ++ tailWord_5381962).sum := by decide
  have hdescent : baseEnd_5381962 < baseStart_5381962 := by decide
  rcases family_descends (prefixWord ++ tailWord_5381962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5381986 : List Nat := [3, 3, 2, 1, 2, 1, 3, 1, 1, 1, 5]
def baseStart_5381986 : Nat := 118140960795 + 5381986 * 2 ^ 59
def prefixEnd_5381986 : Nat := 4983230072969 + 3 ^ 40 * 5381986 * 2
def baseEnd_5381986 : Nat := 2763545693768885188723703

theorem tailTrace_5381986 : CollatzResearch.WordTrace tailWord_5381986 prefixEnd_5381986 2763545693768885188723703 := by
  unfold tailWord_5381986
  simp only [CollatzResearch.WordTrace]
  refine ⟨49074288969997841718761453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130864770586660911250030541 49074288969997841718761453)
  ·
    refine ⟨18402858363749190644535545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49074288969997841718761453 18402858363749190644535545)
    ·
      refine ⟨13802143772811892983401659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18402858363749190644535545 13802143772811892983401659)
      ·
        refine ⟨20703215659217839475102489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13802143772811892983401659 20703215659217839475102489)
        ·
          refine ⟨15527411744413379606326867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20703215659217839475102489 15527411744413379606326867)
          ·
            refine ⟨23291117616620069409490301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15527411744413379606326867 23291117616620069409490301)
            ·
              refine ⟨8734169106232526028558863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23291117616620069409490301 8734169106232526028558863)
              ·
                refine ⟨13101253659348789042838295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8734169106232526028558863 13101253659348789042838295)
                ·
                  refine ⟨19651880489023183564257443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13101253659348789042838295 19651880489023183564257443)
                  ·
                    refine ⟨29477820733534775346386165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19651880489023183564257443 29477820733534775346386165)
                    ·
                      refine ⟨2763545693768885188723703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29477820733534775346386165 2763545693768885188723703)
                      ·
                        rfl

theorem cell23_5381986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3, 1, 1, 1, 5].length) (baseStart_5381986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5381986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5381986 prefixEnd_5381986 := by exact prefixLift 5381986
  have htrace : WordTrace (prefixWord ++ tailWord_5381986) baseStart_5381986 baseEnd_5381986 := by
    simpa [prefixWord, tailWord_5381986, baseEnd_5381986] using wordTrace_append hprefix tailTrace_5381986
  have hstable : (prefixWord ++ tailWord_5381986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5381986).length < 2 ^ (prefixWord ++ tailWord_5381986).sum := by decide
  have hdescent : baseEnd_5381986 < baseStart_5381986 := by decide
  rcases family_descends (prefixWord ++ tailWord_5381986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5381994 : List Nat := [3, 1, 3, 4, 1, 2, 2, 2, 1, 1, 3]
def baseStart_5381994 : Nat := 118140960795 + 5381994 * 2 ^ 59
def prefixEnd_5381994 : Nat := 4983230072969 + 3 ^ 40 * 5381994 * 2
def baseEnd_5381994 : Nat := 2763549801614121157423667

theorem tailTrace_5381994 : CollatzResearch.WordTrace tailWord_5381994 prefixEnd_5381994 2763549801614121157423667 := by
  unfold tailWord_5381994
  simp only [CollatzResearch.WordTrace]
  refine ⟨49074361915990596060334259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130864965109308256160891357 49074361915990596060334259)
  ·
    refine ⟨73611542873985894090501389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49074361915990596060334259 73611542873985894090501389)
    ·
      refine ⟨27604328577744710283938021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73611542873985894090501389 27604328577744710283938021)
      ·
        refine ⟨5175811608327133178238379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27604328577744710283938021 5175811608327133178238379)
        ·
          refine ⟨7763717412490699767357569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5175811608327133178238379 7763717412490699767357569)
          ·
            refine ⟨5822788059368024825518177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7763717412490699767357569 5822788059368024825518177)
            ·
              refine ⟨4367091044526018619138633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5822788059368024825518177 4367091044526018619138633)
              ·
                refine ⟨3275318283394513964353975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4367091044526018619138633 3275318283394513964353975)
                ·
                  refine ⟨4912977425091770946530963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3275318283394513964353975 4912977425091770946530963)
                  ·
                    refine ⟨7369466137637656419796445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4912977425091770946530963 7369466137637656419796445)
                    ·
                      refine ⟨2763549801614121157423667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7369466137637656419796445 2763549801614121157423667)
                      ·
                        rfl

theorem cell23_5381994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_5381994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5381994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5381994 prefixEnd_5381994 := by exact prefixLift 5381994
  have htrace : WordTrace (prefixWord ++ tailWord_5381994) baseStart_5381994 baseEnd_5381994 := by
    simpa [prefixWord, tailWord_5381994, baseEnd_5381994] using wordTrace_append hprefix tailTrace_5381994
  have hstable : (prefixWord ++ tailWord_5381994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5381994).length < 2 ^ (prefixWord ++ tailWord_5381994).sum := by decide
  have hdescent : baseEnd_5381994 < baseStart_5381994 := by decide
  rcases family_descends (prefixWord ++ tailWord_5381994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5382012 : List Nat := [2, 2, 2, 1, 1, 1, 1, 1, 3, 4, 5]
def baseStart_5382012 : Nat := 118140960795 + 5382012 * 2 ^ 59
def prefixEnd_5382012 : Nat := 4983230072969 + 3 ^ 40 * 5382012 * 2
def baseEnd_5382012 : Nat := 2763559044265902086998583

theorem tailTrace_5382012 : CollatzResearch.WordTrace tailWord_5382012 prefixEnd_5382012 2763559044265902086998583 := by
  unfold tailWord_5382012
  simp only [CollatzResearch.WordTrace]
  refine ⟨98149052088948586657746145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130865402785264782210328193 98149052088948586657746145)
  ·
    refine ⟨73611789066711439993309609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98149052088948586657746145 73611789066711439993309609)
    ·
      refine ⟨55208841800033579994982207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73611789066711439993309609 55208841800033579994982207)
      ·
        refine ⟨82813262700050369992473311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55208841800033579994982207 82813262700050369992473311)
        ·
          refine ⟨124219894050075554988709967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82813262700050369992473311 124219894050075554988709967)
          ·
            refine ⟨186329841075113332483064951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124219894050075554988709967 186329841075113332483064951)
            ·
              refine ⟨279494761612669998724597427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 186329841075113332483064951 279494761612669998724597427)
              ·
                refine ⟨419242142419004998086896141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 279494761612669998724597427 419242142419004998086896141)
                ·
                  refine ⟨157215803407126874282586053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 419242142419004998086896141 157215803407126874282586053)
                  ·
                    refine ⟨29477963138836288927984885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 157215803407126874282586053 29477963138836288927984885)
                    ·
                      refine ⟨2763559044265902086998583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29477963138836288927984885 2763559044265902086998583)
                      ·
                        rfl

theorem cell23_5382012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 3, 4, 5].length) (baseStart_5382012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5382012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5382012 prefixEnd_5382012 := by exact prefixLift 5382012
  have htrace : WordTrace (prefixWord ++ tailWord_5382012) baseStart_5382012 baseEnd_5382012 := by
    simpa [prefixWord, tailWord_5382012, baseEnd_5382012] using wordTrace_append hprefix tailTrace_5382012
  have hstable : (prefixWord ++ tailWord_5382012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5382012).length < 2 ^ (prefixWord ++ tailWord_5382012).sum := by decide
  have hdescent : baseEnd_5382012 < baseStart_5382012 := by decide
  rcases family_descends (prefixWord ++ tailWord_5382012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5382016 : List Nat := [2, 1, 1, 2, 1, 2, 3, 5, 2, 1, 3]
def baseStart_5382016 : Nat := 118140960795 + 5382016 * 2 ^ 59
def prefixEnd_5382016 : Nat := 4983230072969 + 3 ^ 40 * 5382016 * 2
def baseEnd_5382016 : Nat := 2763561098188520071348565

theorem tailTrace_5382016 : CollatzResearch.WordTrace tailWord_5382016 prefixEnd_5382016 2763561098188520071348565 := by
  unfold tailWord_5382016
  simp only [CollatzResearch.WordTrace]
  refine ⟨98149125034941340999318951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130865500046588454665758601 98149125034941340999318951)
  ·
    refine ⟨147223687552412011498978427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98149125034941340999318951 147223687552412011498978427)
    ·
      refine ⟨220835531328618017248467641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147223687552412011498978427 220835531328618017248467641)
      ·
        refine ⟨165626648496463512936350731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 220835531328618017248467641 165626648496463512936350731)
        ·
          refine ⟨248439972744695269404526097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165626648496463512936350731 248439972744695269404526097)
          ·
            refine ⟨186329979558521452053394573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 248439972744695269404526097 186329979558521452053394573)
            ·
              refine ⟨69873742334445544520022965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 186329979558521452053394573 69873742334445544520022965)
              ·
                refine ⟨6550663343854269798752153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 69873742334445544520022965 6550663343854269798752153)
                ·
                  refine ⟨4912997507890702349064115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6550663343854269798752153 4912997507890702349064115)
                  ·
                    refine ⟨7369496261836053523596173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4912997507890702349064115 7369496261836053523596173)
                    ·
                      refine ⟨2763561098188520071348565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7369496261836053523596173 2763561098188520071348565)
                      ·
                        rfl

theorem cell23_5382016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 5, 2, 1, 3].length) (baseStart_5382016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5382016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5382016 prefixEnd_5382016 := by exact prefixLift 5382016
  have htrace : WordTrace (prefixWord ++ tailWord_5382016) baseStart_5382016 baseEnd_5382016 := by
    simpa [prefixWord, tailWord_5382016, baseEnd_5382016] using wordTrace_append hprefix tailTrace_5382016
  have hstable : (prefixWord ++ tailWord_5382016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5382016).length < 2 ^ (prefixWord ++ tailWord_5382016).sum := by decide
  have hdescent : baseEnd_5382016 < baseStart_5382016 := by decide
  rcases family_descends (prefixWord ++ tailWord_5382016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5382032 : List Nat := [2, 1, 1, 1, 1, 1, 2, 4, 4, 6]
def baseStart_5382032 : Nat := 118140960795 + 5382032 * 2 ^ 59
def prefixEnd_5382032 : Nat := 4983230072969 + 3 ^ 40 * 5382032 * 2
def baseEnd_5382032 : Nat := 921189771292997336249497

theorem tailTrace_5382032 : CollatzResearch.WordTrace tailWord_5382032 prefixEnd_5382032 921189771292997336249497 := by
  unfold tailWord_5382032
  simp only [CollatzResearch.WordTrace]
  refine ⟨98149416818912358365610175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130865889091883144487480233 98149416818912358365610175)
  ·
    refine ⟨147224125228368537548415263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98149416818912358365610175 147224125228368537548415263)
    ·
      refine ⟨220836187842552806322622895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147224125228368537548415263 220836187842552806322622895)
      ·
        refine ⟨331254281763829209483934343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220836187842552806322622895 331254281763829209483934343)
        ·
          refine ⟨496881422645743814225901515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 331254281763829209483934343 496881422645743814225901515)
          ·
            refine ⟨745322133968615721338852273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 496881422645743814225901515 745322133968615721338852273)
            ·
              refine ⟨558991600476461791004139205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 745322133968615721338852273 558991600476461791004139205)
              ·
                refine ⟨104810925089336585813276101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 558991600476461791004139205 104810925089336585813276101)
                ·
                  refine ⟨19652048454250609839989269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 104810925089336585813276101 19652048454250609839989269)
                  ·
                    refine ⟨921189771292997336249497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19652048454250609839989269 921189771292997336249497)
                    ·
                      rfl

theorem cell23_5382032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 4, 6].length) (baseStart_5382032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5382032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5382032 prefixEnd_5382032 := by exact prefixLift 5382032
  have htrace : WordTrace (prefixWord ++ tailWord_5382032) baseStart_5382032 baseEnd_5382032 := by
    simpa [prefixWord, tailWord_5382032, baseEnd_5382032] using wordTrace_append hprefix tailTrace_5382032
  have hstable : (prefixWord ++ tailWord_5382032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5382032).length < 2 ^ (prefixWord ++ tailWord_5382032).sum := by decide
  have hdescent : baseEnd_5382032 < baseStart_5382032 := by decide
  rcases family_descends (prefixWord ++ tailWord_5382032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5382096 : List Nat := [2, 1, 1, 1, 1, 2, 7, 3, 5]
def baseStart_5382096 : Nat := 118140960795 + 5382096 * 2 ^ 59
def prefixEnd_5382096 : Nat := 4983230072969 + 3 ^ 40 * 5382096 * 2
def baseEnd_5382096 : Nat := 307066908515653306483133

theorem tailTrace_5382096 : CollatzResearch.WordTrace tailWord_5382096 prefixEnd_5382096 307066908515653306483133 := by
  unfold tailWord_5382096
  simp only [CollatzResearch.WordTrace]
  refine ⟨98150583954796427830775071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130867445273061903774366761 98150583954796427830775071)
  ·
    refine ⟨147225875932194641746162607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98150583954796427830775071 147225875932194641746162607)
    ·
      refine ⟨220838813898291962619243911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147225875932194641746162607 220838813898291962619243911)
      ·
        refine ⟨331258220847437943928865867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220838813898291962619243911 331258220847437943928865867)
        ·
          refine ⟨496887331271156915893298801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 331258220847437943928865867 496887331271156915893298801)
          ·
            refine ⟨372665498453367686919974101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 496887331271156915893298801 372665498453367686919974101)
            ·
              refine ⟨8734347620000805162186893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 372665498453367686919974101 8734347620000805162186893)
              ·
                refine ⟨3275380357500301935820085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8734347620000805162186893 3275380357500301935820085)
                ·
                  refine ⟨307066908515653306483133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3275380357500301935820085 307066908515653306483133)
                  ·
                    rfl

theorem cell23_5382096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7, 3, 5].length) (baseStart_5382096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5382096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5382096 prefixEnd_5382096 := by exact prefixLift 5382096
  have htrace : WordTrace (prefixWord ++ tailWord_5382096) baseStart_5382096 baseEnd_5382096 := by
    simpa [prefixWord, tailWord_5382096, baseEnd_5382096] using wordTrace_append hprefix tailTrace_5382096
  have hstable : (prefixWord ++ tailWord_5382096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5382096).length < 2 ^ (prefixWord ++ tailWord_5382096).sum := by decide
  have hdescent : baseEnd_5382096 < baseStart_5382096 := by decide
  rcases family_descends (prefixWord ++ tailWord_5382096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5382116 : List Nat := [2, 3, 1, 1, 1, 1, 4, 1, 2, 5, 2]
def baseStart_5382116 : Nat := 118140960795 + 5382116 * 2 ^ 59
def prefixEnd_5382116 : Nat := 4983230072969 + 3 ^ 40 * 5382116 * 2
def baseEnd_5382116 : Nat := 2763612446253969680098105

theorem tailTrace_5382116 : CollatzResearch.WordTrace tailWord_5382116 prefixEnd_5382116 2763612446253969680098105 := by
  unfold tailWord_5382116
  simp only [CollatzResearch.WordTrace]
  refine ⟨98150948684760199538639101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130867931579680266051518801 98150948684760199538639101)
  ·
    refine ⟨36806605756785074826989663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98150948684760199538639101 36806605756785074826989663)
    ·
      refine ⟨55209908635177612240484495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36806605756785074826989663 55209908635177612240484495)
      ·
        refine ⟨82814862952766418360726743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55209908635177612240484495 82814862952766418360726743)
        ·
          refine ⟨124222294429149627541090115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82814862952766418360726743 124222294429149627541090115)
          ·
            refine ⟨186333441643724441311635173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124222294429149627541090115 186333441643724441311635173)
            ·
              refine ⟨34937520308198332745931595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 186333441643724441311635173 34937520308198332745931595)
              ·
                refine ⟨52406280462297499118897393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34937520308198332745931595 52406280462297499118897393)
                ·
                  refine ⟨39304710346723124339173045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52406280462297499118897393 39304710346723124339173045)
                  ·
                    refine ⟨3684816595005292906797473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39304710346723124339173045 3684816595005292906797473)
                    ·
                      refine ⟨2763612446253969680098105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3684816595005292906797473 2763612446253969680098105)
                      ·
                        rfl

theorem cell23_5382116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 1, 2, 5, 2].length) (baseStart_5382116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5382116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5382116 prefixEnd_5382116 := by exact prefixLift 5382116
  have htrace : WordTrace (prefixWord ++ tailWord_5382116) baseStart_5382116 baseEnd_5382116 := by
    simpa [prefixWord, tailWord_5382116, baseEnd_5382116] using wordTrace_append hprefix tailTrace_5382116
  have hstable : (prefixWord ++ tailWord_5382116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5382116).length < 2 ^ (prefixWord ++ tailWord_5382116).sum := by decide
  have hdescent : baseEnd_5382116 < baseStart_5382116 := by decide
  rcases family_descends (prefixWord ++ tailWord_5382116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5382164 : List Nat := [2, 4, 3, 2, 1, 2, 2, 2, 5]
def baseStart_5382164 : Nat := 118140960795 + 5382164 * 2 ^ 59
def prefixEnd_5382164 : Nat := 4983230072969 + 3 ^ 40 * 5382164 * 2
def baseEnd_5382164 : Nat := 307070788147265054699765

theorem tailTrace_5382164 : CollatzResearch.WordTrace tailWord_5382164 prefixEnd_5382164 307070788147265054699765 := by
  unfold tailWord_5382164
  simp only [CollatzResearch.WordTrace]
  refine ⟨98151824036673251637512773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130869098715564335516683697 98151824036673251637512773)
  ·
    refine ⟨18403467006876234682033645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98151824036673251637512773 18403467006876234682033645)
    ·
      refine ⟨6901300127578588005762617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18403467006876234682033645 6901300127578588005762617)
      ·
        refine ⟨5175975095683941004321963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6901300127578588005762617 5175975095683941004321963)
        ·
          refine ⟨7763962643525911506482945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5175975095683941004321963 7763962643525911506482945)
          ·
            refine ⟨5822971982644433629862209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7763962643525911506482945 5822971982644433629862209)
            ·
              refine ⟨4367228986983325222396657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5822971982644433629862209 4367228986983325222396657)
              ·
                refine ⟨3275421740237493916797493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4367228986983325222396657 3275421740237493916797493)
                ·
                  refine ⟨307070788147265054699765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3275421740237493916797493 307070788147265054699765)
                  ·
                    rfl

theorem cell23_5382164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 2, 2, 5].length) (baseStart_5382164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5382164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5382164 prefixEnd_5382164 := by exact prefixLift 5382164
  have htrace : WordTrace (prefixWord ++ tailWord_5382164) baseStart_5382164 baseEnd_5382164 := by
    simpa [prefixWord, tailWord_5382164, baseEnd_5382164] using wordTrace_append hprefix tailTrace_5382164
  have hstable : (prefixWord ++ tailWord_5382164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5382164).length < 2 ^ (prefixWord ++ tailWord_5382164).sum := by decide
  have hdescent : baseEnd_5382164 < baseStart_5382164 := by decide
  rcases family_descends (prefixWord ++ tailWord_5382164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5382180 : List Nat := [2, 3, 1, 4, 2, 1, 1, 1, 2, 4, 2]
def baseStart_5382180 : Nat := 118140960795 + 5382180 * 2 ^ 59
def prefixEnd_5382180 : Nat := 4983230072969 + 3 ^ 40 * 5382180 * 2
def baseEnd_5382180 : Nat := 2763645309015857429697811

theorem tailTrace_5382180 : CollatzResearch.WordTrace tailWord_5382180 prefixEnd_5382180 2763645309015857429697811 := by
  unfold tailWord_5382180
  simp only [CollatzResearch.WordTrace]
  refine ⟨98152115820644269003803997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130869487760859025338405329 98152115820644269003803997)
  ·
    refine ⟨36807043432741600876426499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98152115820644269003803997 36807043432741600876426499)
    ·
      refine ⟨55210565149112401314639749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36807043432741600876426499 55210565149112401314639749)
      ·
        refine ⟨10351980965458575246494953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55210565149112401314639749 10351980965458575246494953)
        ·
          refine ⟨7763985724093931434871215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10351980965458575246494953 7763985724093931434871215)
          ·
            refine ⟨11645978586140897152306823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7763985724093931434871215 11645978586140897152306823)
            ·
              refine ⟨17468967879211345728460235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11645978586140897152306823 17468967879211345728460235)
              ·
                refine ⟨26203451818817018592690353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17468967879211345728460235 26203451818817018592690353)
                ·
                  refine ⟨19652588864112763944517765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26203451818817018592690353 19652588864112763944517765)
                  ·
                    refine ⟨3684860412021143239597081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19652588864112763944517765 3684860412021143239597081)
                    ·
                      refine ⟨2763645309015857429697811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3684860412021143239597081 2763645309015857429697811)
                      ·
                        rfl

theorem cell23_5382180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 1, 2, 4, 2].length) (baseStart_5382180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5382180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5382180 prefixEnd_5382180 := by exact prefixLift 5382180
  have htrace : WordTrace (prefixWord ++ tailWord_5382180) baseStart_5382180 baseEnd_5382180 := by
    simpa [prefixWord, tailWord_5382180, baseEnd_5382180] using wordTrace_append hprefix tailTrace_5382180
  have hstable : (prefixWord ++ tailWord_5382180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5382180).length < 2 ^ (prefixWord ++ tailWord_5382180).sum := by decide
  have hdescent : baseEnd_5382180 < baseStart_5382180 := by decide
  rcases family_descends (prefixWord ++ tailWord_5382180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5382200 : List Nat := [2, 1, 2, 1, 6, 2, 1, 1, 2, 2, 3]
def baseStart_5382200 : Nat := 118140960795 + 5382200 * 2 ^ 59
def prefixEnd_5382200 : Nat := 4983230072969 + 3 ^ 40 * 5382200 * 2
def baseEnd_5382200 : Nat := 2763655578628947351447719

theorem tailTrace_5382200 : CollatzResearch.WordTrace tailWord_5382200 prefixEnd_5382200 2763655578628947351447719 := by
  unfold tailWord_5382200
  simp only [CollatzResearch.WordTrace]
  refine ⟨98152480550608040711668027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130869974067477387615557369 98152480550608040711668027)
  ·
    refine ⟨147228720825912061067502041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98152480550608040711668027 147228720825912061067502041)
    ·
      refine ⟨110421540619434045800626531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147228720825912061067502041 110421540619434045800626531)
      ·
        refine ⟨165632310929151068700939797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110421540619434045800626531 165632310929151068700939797)
        ·
          refine ⟨7764014574803956345356553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 165632310929151068700939797 7764014574803956345356553)
          ·
            refine ⟨5823010931102967259017415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7764014574803956345356553 5823010931102967259017415)
            ·
              refine ⟨8734516396654450888526123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5823010931102967259017415 8734516396654450888526123)
              ·
                refine ⟨13101774594981676332789185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8734516396654450888526123 13101774594981676332789185)
                ·
                  refine ⟨9826330946236257249591889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13101774594981676332789185 9826330946236257249591889)
                  ·
                    refine ⟨7369748209677192937193917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9826330946236257249591889 7369748209677192937193917)
                    ·
                      refine ⟨2763655578628947351447719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7369748209677192937193917 2763655578628947351447719)
                      ·
                        rfl

theorem cell23_5382200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 1, 1, 2, 2, 3].length) (baseStart_5382200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5382200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5382200 prefixEnd_5382200 := by exact prefixLift 5382200
  have htrace : WordTrace (prefixWord ++ tailWord_5382200) baseStart_5382200 baseEnd_5382200 := by
    simpa [prefixWord, tailWord_5382200, baseEnd_5382200] using wordTrace_append hprefix tailTrace_5382200
  have hstable : (prefixWord ++ tailWord_5382200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5382200).length < 2 ^ (prefixWord ++ tailWord_5382200).sum := by decide
  have hdescent : baseEnd_5382200 < baseStart_5382200 := by decide
  rcases family_descends (prefixWord ++ tailWord_5382200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5382250 : List Nat := [3, 1, 3, 2, 3, 1, 2, 2, 1, 5]
def baseStart_5382250 : Nat := 118140960795 + 5382250 * 2 ^ 59
def prefixEnd_5382250 : Nat := 4983230072969 + 3 ^ 40 * 5382250 * 2
def baseEnd_5382250 : Nat := 921227084220557385274163

theorem tailTrace_5382250 : CollatzResearch.WordTrace tailWord_5382250 prefixEnd_5382250 921227084220557385274163 := by
  unfold tailWord_5382250
  simp only [CollatzResearch.WordTrace]
  refine ⟨49076696187758734990664051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130871189834023293308437469 49076696187758734990664051)
  ·
    refine ⟨73615044281638102485996077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49076696187758734990664051 73615044281638102485996077)
    ·
      refine ⟨27605641605614288432248529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73615044281638102485996077 27605641605614288432248529)
      ·
        refine ⟨20704231204210716324186397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27605641605614288432248529 20704231204210716324186397)
        ·
          refine ⟨7764086701579018621569899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20704231204210716324186397 7764086701579018621569899)
          ·
            refine ⟨11646130052368527932354849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7764086701579018621569899 11646130052368527932354849)
            ·
              refine ⟨8734597539276395949266137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11646130052368527932354849 8734597539276395949266137)
              ·
                refine ⟨6550948154457296961949603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8734597539276395949266137 6550948154457296961949603)
                ·
                  refine ⟨9826422231685945442924405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6550948154457296961949603 9826422231685945442924405)
                  ·
                    refine ⟨921227084220557385274163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9826422231685945442924405 921227084220557385274163)
                    ·
                      rfl

theorem cell23_5382250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 2, 2, 1, 5].length) (baseStart_5382250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5382250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5382250 prefixEnd_5382250 := by exact prefixLift 5382250
  have htrace : WordTrace (prefixWord ++ tailWord_5382250) baseStart_5382250 baseEnd_5382250 := by
    simpa [prefixWord, tailWord_5382250, baseEnd_5382250] using wordTrace_append hprefix tailTrace_5382250
  have hstable : (prefixWord ++ tailWord_5382250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5382250).length < 2 ^ (prefixWord ++ tailWord_5382250).sum := by decide
  have hdescent : baseEnd_5382250 < baseStart_5382250 := by decide
  rcases family_descends (prefixWord ++ tailWord_5382250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5382253 : List Nat := [1, 5, 1, 1, 2, 1, 1, 1, 2, 6, 2]
def baseStart_5382253 : Nat := 118140960795 + 5382253 * 2 ^ 59
def prefixEnd_5382253 : Nat := 4983230072969 + 3 ^ 40 * 5382253 * 2
def baseEnd_5382253 : Nat := 2763682793103635644084975

theorem tailTrace_5382253 : CollatzResearch.WordTrace tailWord_5382253 prefixEnd_5382253 2763682793103635644084975 := by
  unfold tailWord_5382253
  simp only [CollatzResearch.WordTrace]
  refine ⟨196306894170024071475015413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130871262780016047650010275 196306894170024071475015413)
  ·
    refine ⟨18403771328439756700782695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 196306894170024071475015413 18403771328439756700782695)
    ·
      refine ⟨27605656992659635051174043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18403771328439756700782695 27605656992659635051174043)
      ·
        refine ⟨41408485488989452576761065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27605656992659635051174043 41408485488989452576761065)
        ·
          refine ⟨31056364116742089432570799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41408485488989452576761065 31056364116742089432570799)
          ·
            refine ⟨46584546175113134148856199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31056364116742089432570799 46584546175113134148856199)
            ·
              refine ⟨69876819262669701223284299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46584546175113134148856199 69876819262669701223284299)
              ·
                refine ⟨104815228894004551834926449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69876819262669701223284299 104815228894004551834926449)
                ·
                  refine ⟨78611421670503413876194837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 104815228894004551834926449 78611421670503413876194837)
                  ·
                    refine ⟨3684910390804847525446633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 78611421670503413876194837 3684910390804847525446633)
                    ·
                      refine ⟨2763682793103635644084975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3684910390804847525446633 2763682793103635644084975)
                      ·
                        rfl

theorem cell23_5382253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 2, 6, 2].length) (baseStart_5382253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5382253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5382253 prefixEnd_5382253 := by exact prefixLift 5382253
  have htrace : WordTrace (prefixWord ++ tailWord_5382253) baseStart_5382253 baseEnd_5382253 := by
    simpa [prefixWord, tailWord_5382253, baseEnd_5382253] using wordTrace_append hprefix tailTrace_5382253
  have hstable : (prefixWord ++ tailWord_5382253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5382253).length < 2 ^ (prefixWord ++ tailWord_5382253).sum := by decide
  have hdescent : baseEnd_5382253 < baseStart_5382253 := by decide
  rcases family_descends (prefixWord ++ tailWord_5382253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5382330 : List Nat := [3, 1, 1, 1, 2, 2, 2, 5, 1, 3, 2]
def baseStart_5382330 : Nat := 118140960795 + 5382330 * 2 ^ 59
def prefixEnd_5382330 : Nat := 4983230072969 + 3 ^ 40 * 5382330 * 2
def baseEnd_5382330 : Nat := 2763722331114031842822121

theorem tailTrace_5382330 : CollatzResearch.WordTrace tailWord_5382330 prefixEnd_5382330 2763722331114031842822121 := by
  unfold tailWord_5382330
  simp only [CollatzResearch.WordTrace]
  refine ⟨49077425647686278406392111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130873135060496742417045629 49077425647686278406392111)
  ·
    refine ⟨73616138471529417609588167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49077425647686278406392111 73616138471529417609588167)
    ·
      refine ⟨110424207707294126414382251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73616138471529417609588167 110424207707294126414382251)
      ·
        refine ⟨165636311560941189621573377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110424207707294126414382251 165636311560941189621573377)
        ·
          refine ⟨124227233670705892216180033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165636311560941189621573377 124227233670705892216180033)
          ·
            refine ⟨93170425253029419162135025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124227233670705892216180033 93170425253029419162135025)
            ·
              refine ⟨69877818939772064371601269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93170425253029419162135025 69877818939772064371601269)
              ·
                refine ⟨6551045525603631034837619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 69877818939772064371601269 6551045525603631034837619)
                ·
                  refine ⟨9826568288405446552256429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6551045525603631034837619 9826568288405446552256429)
                  ·
                    refine ⟨3684963108152042457096161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9826568288405446552256429 3684963108152042457096161)
                    ·
                      refine ⟨2763722331114031842822121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3684963108152042457096161 2763722331114031842822121)
                      ·
                        rfl

theorem cell23_5382330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 5, 1, 3, 2].length) (baseStart_5382330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5382330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5382330 prefixEnd_5382330 := by exact prefixLift 5382330
  have htrace : WordTrace (prefixWord ++ tailWord_5382330) baseStart_5382330 baseEnd_5382330 := by
    simpa [prefixWord, tailWord_5382330, baseEnd_5382330] using wordTrace_append hprefix tailTrace_5382330
  have hstable : (prefixWord ++ tailWord_5382330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5382330).length < 2 ^ (prefixWord ++ tailWord_5382330).sum := by decide
  have hdescent : baseEnd_5382330 < baseStart_5382330 := by decide
  rcases family_descends (prefixWord ++ tailWord_5382330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5382338 : List Nat := [3, 5, 1, 1, 1, 2, 1, 4, 1, 2, 2]
def baseStart_5382338 : Nat := 118140960795 + 5382338 * 2 ^ 59
def prefixEnd_5382338 : Nat := 4983230072969 + 3 ^ 40 * 5382338 * 2
def baseEnd_5382338 : Nat := 2763726438959267811522085

theorem tailTrace_5382338 : CollatzResearch.WordTrace tailWord_5382338 prefixEnd_5382338 2763726438959267811522085 := by
  unfold tailWord_5382338
  simp only [CollatzResearch.WordTrace]
  refine ⟨49077498593679032747964917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130873329583144087327906445 49077498593679032747964917)
  ·
    refine ⟨4601015493157409320121711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 49077498593679032747964917 4601015493157409320121711)
    ·
      refine ⟨6901523239736113980182567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4601015493157409320121711 6901523239736113980182567)
      ·
        refine ⟨10352284859604170970273851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6901523239736113980182567 10352284859604170970273851)
        ·
          refine ⟨15528427289406256455410777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10352284859604170970273851 15528427289406256455410777)
          ·
            refine ⟨11646320467054692341558083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15528427289406256455410777 11646320467054692341558083)
            ·
              refine ⟨17469480700582038512337125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11646320467054692341558083 17469480700582038512337125)
              ·
                refine ⟨3275527631359132221063211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17469480700582038512337125 3275527631359132221063211)
                ·
                  refine ⟨4913291447038698331594817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3275527631359132221063211 4913291447038698331594817)
                  ·
                    refine ⟨3684968585279023748696113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4913291447038698331594817 3684968585279023748696113)
                    ·
                      refine ⟨2763726438959267811522085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3684968585279023748696113 2763726438959267811522085)
                      ·
                        rfl

theorem cell23_5382338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 4, 1, 2, 2].length) (baseStart_5382338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5382338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5382338 prefixEnd_5382338 := by exact prefixLift 5382338
  have htrace : WordTrace (prefixWord ++ tailWord_5382338) baseStart_5382338 baseEnd_5382338 := by
    simpa [prefixWord, tailWord_5382338, baseEnd_5382338] using wordTrace_append hprefix tailTrace_5382338
  have hstable : (prefixWord ++ tailWord_5382338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5382338).length < 2 ^ (prefixWord ++ tailWord_5382338).sum := by decide
  have hdescent : baseEnd_5382338 < baseStart_5382338 := by decide
  rcases family_descends (prefixWord ++ tailWord_5382338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5382360 : List Nat := [2, 1, 2, 2, 4, 1, 1, 3, 1, 4, 2]
def baseStart_5382360 : Nat := 118140960795 + 5382360 * 2 ^ 59
def prefixEnd_5382360 : Nat := 4983230072969 + 3 ^ 40 * 5382360 * 2
def baseEnd_5382360 : Nat := 2763737735533666725446983

theorem tailTrace_5382360 : CollatzResearch.WordTrace tailWord_5382360 prefixEnd_5382360 2763737735533666725446983 := by
  unfold tailWord_5382360
  simp only [CollatzResearch.WordTrace]
  refine ⟨98155398390318214374580267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130873864520424285832773689 98155398390318214374580267)
  ·
    refine ⟨147233097585477321561870401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98155398390318214374580267 147233097585477321561870401)
    ·
      refine ⟨110424823189107991171402801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147233097585477321561870401 110424823189107991171402801)
      ·
        refine ⟨82818617391830993378552101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110424823189107991171402801 82818617391830993378552101)
        ·
          refine ⟨15528490760968311258478519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82818617391830993378552101 15528490760968311258478519)
          ·
            refine ⟨23292736141452466887717779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15528490760968311258478519 23292736141452466887717779)
            ·
              refine ⟨34939104212178700331576669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23292736141452466887717779 34939104212178700331576669)
              ·
                refine ⟨13102164079567012624341251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34939104212178700331576669 13102164079567012624341251)
                ·
                  refine ⟨19653246119350518936511877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13102164079567012624341251 19653246119350518936511877)
                  ·
                    refine ⟨3684983647378222300595977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19653246119350518936511877 3684983647378222300595977)
                    ·
                      refine ⟨2763737735533666725446983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3684983647378222300595977 2763737735533666725446983)
                      ·
                        rfl

theorem cell23_5382360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 3, 1, 4, 2].length) (baseStart_5382360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5382360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5382360 prefixEnd_5382360 := by exact prefixLift 5382360
  have htrace : WordTrace (prefixWord ++ tailWord_5382360) baseStart_5382360 baseEnd_5382360 := by
    simpa [prefixWord, tailWord_5382360, baseEnd_5382360] using wordTrace_append hprefix tailTrace_5382360
  have hstable : (prefixWord ++ tailWord_5382360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5382360).length < 2 ^ (prefixWord ++ tailWord_5382360).sum := by decide
  have hdescent : baseEnd_5382360 < baseStart_5382360 := by decide
  rcases family_descends (prefixWord ++ tailWord_5382360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5382381 : List Nat := [1, 5, 1, 2, 3, 2, 2, 1, 1, 3, 2]
def baseStart_5382381 : Nat := 118140960795 + 5382381 * 2 ^ 59
def prefixEnd_5382381 : Nat := 4983230072969 + 3 ^ 40 * 5382381 * 2
def baseEnd_5382381 : Nat := 2763748518627411143284387

theorem tailTrace_5382381 : CollatzResearch.WordTrace tailWord_5382381 prefixEnd_5382381 2763748518627411143284387 := by
  unfold tailWord_5382381
  simp only [CollatzResearch.WordTrace]
  refine ⟨196311562713560349335674997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130874375142373566223783331 196311562713560349335674997)
  ·
    refine ⟨18404209004396282750219531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 196311562713560349335674997 18404209004396282750219531)
    ·
      refine ⟨27606313506594424125329297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18404209004396282750219531 27606313506594424125329297)
      ·
        refine ⟨20704735129945818093996973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27606313506594424125329297 20704735129945818093996973)
        ·
          refine ⟨7764275673729681785248865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20704735129945818093996973 7764275673729681785248865)
          ·
            refine ⟨5823206755297261338936649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7764275673729681785248865 5823206755297261338936649)
            ·
              refine ⟨4367405066472946004202487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5823206755297261338936649 4367405066472946004202487)
              ·
                refine ⟨6551107599709419006303731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4367405066472946004202487 6551107599709419006303731)
                ·
                  refine ⟨9826661399564128509455597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6551107599709419006303731 9826661399564128509455597)
                  ·
                    refine ⟨3684998024836548191045849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9826661399564128509455597 3684998024836548191045849)
                    ·
                      refine ⟨2763748518627411143284387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3684998024836548191045849 2763748518627411143284387)
                      ·
                        rfl

theorem cell23_5382381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 2, 1, 1, 3, 2].length) (baseStart_5382381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5382381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5382381 prefixEnd_5382381 := by exact prefixLift 5382381
  have htrace : WordTrace (prefixWord ++ tailWord_5382381) baseStart_5382381 baseEnd_5382381 := by
    simpa [prefixWord, tailWord_5382381, baseEnd_5382381] using wordTrace_append hprefix tailTrace_5382381
  have hstable : (prefixWord ++ tailWord_5382381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5382381).length < 2 ^ (prefixWord ++ tailWord_5382381).sum := by decide
  have hdescent : baseEnd_5382381 < baseStart_5382381 := by decide
  rcases family_descends (prefixWord ++ tailWord_5382381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5382394 : List Nat := [3, 1, 1, 1, 1, 7, 1, 2, 2, 2, 2]
def baseStart_5382394 : Nat := 118140960795 + 5382394 * 2 ^ 59
def prefixEnd_5382394 : Nat := 4983230072969 + 3 ^ 40 * 5382394 * 2
def baseEnd_5382394 : Nat := 2763755193875919592421827

theorem tailTrace_5382394 : CollatzResearch.WordTrace tailWord_5382394 prefixEnd_5382394 2763755193875919592421827 := by
  unfold tailWord_5382394
  simp only [CollatzResearch.WordTrace]
  refine ⟨49078009215628313138974559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130874691241675501703932157 49078009215628313138974559)
  ·
    refine ⟨73617013823442469708461839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49078009215628313138974559 73617013823442469708461839)
    ·
      refine ⟨110425520735163704562692759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73617013823442469708461839 110425520735163704562692759)
      ·
        refine ⟨165638281102745556844039139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110425520735163704562692759 165638281102745556844039139)
        ·
          refine ⟨248457421654118335266058709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165638281102745556844039139 248457421654118335266058709)
          ·
            refine ⟨5823220820018398482798251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 248457421654118335266058709 5823220820018398482798251)
            ·
              refine ⟨8734831230027597724197377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5823220820018398482798251 8734831230027597724197377)
              ·
                refine ⟨6551123422520698293148033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8734831230027597724197377 6551123422520698293148033)
                ·
                  refine ⟨4913342566890523719861025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6551123422520698293148033 4913342566890523719861025)
                  ·
                    refine ⟨3685006925167892789895769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4913342566890523719861025 3685006925167892789895769)
                    ·
                      refine ⟨2763755193875919592421827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3685006925167892789895769 2763755193875919592421827)
                      ·
                        rfl

theorem cell23_5382394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 1, 2, 2, 2, 2].length) (baseStart_5382394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5382394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5382394 prefixEnd_5382394 := by exact prefixLift 5382394
  have htrace : WordTrace (prefixWord ++ tailWord_5382394) baseStart_5382394 baseEnd_5382394 := by
    simpa [prefixWord, tailWord_5382394, baseEnd_5382394] using wordTrace_append hprefix tailTrace_5382394
  have hstable : (prefixWord ++ tailWord_5382394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5382394).length < 2 ^ (prefixWord ++ tailWord_5382394).sum := by decide
  have hdescent : baseEnd_5382394 < baseStart_5382394 := by decide
  rcases family_descends (prefixWord ++ tailWord_5382394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5382433 : List Nat := [1, 2, 3, 2, 1, 1, 4, 1, 1, 3, 4]
def baseStart_5382433 : Nat := 118140960795 + 5382433 * 2 ^ 59
def prefixEnd_5382433 : Nat := 4983230072969 + 3 ^ 40 * 5382433 * 2
def baseEnd_5382433 : Nat := 2763775219621444939834147

theorem tailTrace_5382433 : CollatzResearch.WordTrace tailWord_5382433 prefixEnd_5382433 2763775219621444939834147 := by
  unfold tailWord_5382433
  simp only [CollatzResearch.WordTrace]
  refine ⟨196313459309371962216567953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130875639539581308144378635 196313459309371962216567953)
  ·
    refine ⟨147235094482028971662425965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196313459309371962216567953 147235094482028971662425965)
    ·
      refine ⟨55213160430760864373409737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147235094482028971662425965 55213160430760864373409737)
      ·
        refine ⟨41409870323070648280057303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55213160430760864373409737 41409870323070648280057303)
        ·
          refine ⟨62114805484605972420085955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41409870323070648280057303 62114805484605972420085955)
          ·
            refine ⟨93172208226908958630128933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62114805484605972420085955 93172208226908958630128933)
            ·
              refine ⟨17469789042545429743149175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 93172208226908958630128933 17469789042545429743149175)
              ·
                refine ⟨26204683563818144614723763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17469789042545429743149175 26204683563818144614723763)
                ·
                  refine ⟨39307025345727216922085645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26204683563818144614723763 39307025345727216922085645)
                  ·
                    refine ⟨14740134504647706345782117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39307025345727216922085645 14740134504647706345782117)
                    ·
                      refine ⟨2763775219621444939834147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14740134504647706345782117 2763775219621444939834147)
                      ·
                        rfl

theorem cell23_5382433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 1, 1, 3, 4].length) (baseStart_5382433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5382433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5382433 prefixEnd_5382433 := by exact prefixLift 5382433
  have htrace : WordTrace (prefixWord ++ tailWord_5382433) baseStart_5382433 baseEnd_5382433 := by
    simpa [prefixWord, tailWord_5382433, baseEnd_5382433] using wordTrace_append hprefix tailTrace_5382433
  have hstable : (prefixWord ++ tailWord_5382433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5382433).length < 2 ^ (prefixWord ++ tailWord_5382433).sum := by decide
  have hdescent : baseEnd_5382433 < baseStart_5382433 := by decide
  rcases family_descends (prefixWord ++ tailWord_5382433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5382540 : List Nat := [2, 2, 1, 2, 1, 4, 2, 1, 3, 1, 4]
def baseStart_5382540 : Nat := 118140960795 + 5382540 * 2 ^ 59
def prefixEnd_5382540 : Nat := 4983230072969 + 3 ^ 40 * 5382540 * 2
def baseEnd_5382540 : Nat := 2763830162051476021196155

theorem tailTrace_5382540 : CollatzResearch.WordTrace tailWord_5382540 prefixEnd_5382540 2763830162051476021196155 := by
  unfold tailWord_5382540
  simp only [CollatzResearch.WordTrace]
  refine ⟨98158680959992159745356537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130878241279989546327142049 98158680959992159745356537)
  ·
    refine ⟨73619010719994119809017403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98158680959992159745356537 73619010719994119809017403)
    ·
      refine ⟨110428516079991179713526105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73619010719994119809017403 110428516079991179713526105)
      ·
        refine ⟨82821387059993384785144579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110428516079991179713526105 82821387059993384785144579)
        ·
          refine ⟨124232080589990077177716869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82821387059993384785144579 124232080589990077177716869)
          ·
            refine ⟨23293515110623139470821913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 124232080589990077177716869 23293515110623139470821913)
            ·
              refine ⟨17470136332967354603116435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23293515110623139470821913 17470136332967354603116435)
              ·
                refine ⟨26205204499451031904674653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17470136332967354603116435 26205204499451031904674653)
                ·
                  refine ⟨9826951687294136964252995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26205204499451031904674653 9826951687294136964252995)
                  ·
                    refine ⟨14740427530941205446379493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9826951687294136964252995 14740427530941205446379493)
                    ·
                      refine ⟨2763830162051476021196155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14740427530941205446379493 2763830162051476021196155)
                      ·
                        rfl

theorem cell23_5382540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 1, 3, 1, 4].length) (baseStart_5382540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5382540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5382540 prefixEnd_5382540 := by exact prefixLift 5382540
  have htrace : WordTrace (prefixWord ++ tailWord_5382540) baseStart_5382540 baseEnd_5382540 := by
    simpa [prefixWord, tailWord_5382540, baseEnd_5382540] using wordTrace_append hprefix tailTrace_5382540
  have hstable : (prefixWord ++ tailWord_5382540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5382540).length < 2 ^ (prefixWord ++ tailWord_5382540).sum := by decide
  have hdescent : baseEnd_5382540 < baseStart_5382540 := by decide
  rcases family_descends (prefixWord ++ tailWord_5382540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5382554 : List Nat := [3, 1, 1, 4, 1, 4, 2, 1, 1, 5]
def baseStart_5382554 : Nat := 118140960795 + 5382554 * 2 ^ 59
def prefixEnd_5382554 : Nat := 4983230072969 + 3 ^ 40 * 5382554 * 2
def baseEnd_5382554 : Nat := 921279116926879655473697

theorem tailTrace_5382554 : CollatzResearch.WordTrace tailWord_5382554 prefixEnd_5382554 921279116926879655473697 := by
  unfold tailWord_5382554
  simp only [CollatzResearch.WordTrace]
  refine ⟨49079468135483399970430679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130878581694622399921148477 49079468135483399970430679)
  ·
    refine ⟨73619202203225099955646019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49079468135483399970430679 73619202203225099955646019)
    ·
      refine ⟨110428803304837649933469029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73619202203225099955646019 110428803304837649933469029)
      ·
        refine ⟨20705400619657059362525443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 110428803304837649933469029 20705400619657059362525443)
        ·
          refine ⟨31058100929485589043788165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20705400619657059362525443 31058100929485589043788165)
          ·
            refine ⟨5823393924278547945710281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31058100929485589043788165 5823393924278547945710281)
            ·
              refine ⟨4367545443208910959282711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5823393924278547945710281 4367545443208910959282711)
              ·
                refine ⟨6551318164813366438924067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4367545443208910959282711 6551318164813366438924067)
                ·
                  refine ⟨9826977247220049658386101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6551318164813366438924067 9826977247220049658386101)
                  ·
                    refine ⟨921279116926879655473697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9826977247220049658386101 921279116926879655473697)
                    ·
                      rfl

theorem cell23_5382554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 2, 1, 1, 5].length) (baseStart_5382554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5382554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5382554 prefixEnd_5382554 := by exact prefixLift 5382554
  have htrace : WordTrace (prefixWord ++ tailWord_5382554) baseStart_5382554 baseEnd_5382554 := by
    simpa [prefixWord, tailWord_5382554, baseEnd_5382554] using wordTrace_append hprefix tailTrace_5382554
  have hstable : (prefixWord ++ tailWord_5382554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5382554).length < 2 ^ (prefixWord ++ tailWord_5382554).sum := by decide
  have hdescent : baseEnd_5382554 < baseStart_5382554 := by decide
  rcases family_descends (prefixWord ++ tailWord_5382554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5382563 : List Nat := [1, 1, 1, 4, 1, 5, 10]
def baseStart_5382563 : Nat := 118140960795 + 5382563 * 2 ^ 59
def prefixEnd_5382563 : Nat := 4983230072969 + 3 ^ 40 * 5382563 * 2
def baseEnd_5382563 : Nat := 34121505828475671990229

theorem tailTrace_5382563 : CollatzResearch.WordTrace tailWord_5382563 prefixEnd_5382563 34121505828475671990229 := by
  unfold tailWord_5382563
  simp only [CollatzResearch.WordTrace]
  refine ⟨196318200798900994418800343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130878800532600662945866895 196318200798900994418800343)
  ·
    refine ⟨294477301198351491628200515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196318200798900994418800343 294477301198351491628200515)
    ·
      refine ⟨441715951797527237442300773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294477301198351491628200515 441715951797527237442300773)
      ·
        refine ⟨82821740962036357020431395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 441715951797527237442300773 82821740962036357020431395)
        ·
          refine ⟨124232611443054535530647093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82821740962036357020431395 124232611443054535530647093)
          ·
            refine ⟨11646807322786362705998165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 124232611443054535530647093 11646807322786362705998165)
            ·
              refine ⟨34121505828475671990229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 11646807322786362705998165 34121505828475671990229)
              ·
                rfl

theorem cell23_5382563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 10].length) (baseStart_5382563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5382563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5382563 prefixEnd_5382563 := by exact prefixLift 5382563
  have htrace : WordTrace (prefixWord ++ tailWord_5382563) baseStart_5382563 baseEnd_5382563 := by
    simpa [prefixWord, tailWord_5382563, baseEnd_5382563] using wordTrace_append hprefix tailTrace_5382563
  have hstable : (prefixWord ++ tailWord_5382563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5382563).length < 2 ^ (prefixWord ++ tailWord_5382563).sum := by decide
  have hdescent : baseEnd_5382563 < baseStart_5382563 := by decide
  rcases family_descends (prefixWord ++ tailWord_5382563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5382567 : List Nat := [1, 1, 6, 1, 1, 3, 1, 1, 4, 4]
def baseStart_5382567 : Nat := 118140960795 + 5382567 * 2 ^ 59
def prefixEnd_5382567 : Nat := 4983230072969 + 3 ^ 40 * 5382567 * 2
def baseEnd_5382567 : Nat := 921281342009715805186177

theorem tailTrace_5382567 : CollatzResearch.WordTrace tailWord_5382567 prefixEnd_5382567 921281342009715805186177 := by
  unfold tailWord_5382567
  simp only [CollatzResearch.WordTrace]
  refine ⟨196318346690886503101945955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130878897793924335401297303 196318346690886503101945955)
  ·
    refine ⟨294477520036329754652918933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196318346690886503101945955 294477520036329754652918933)
    ·
      refine ⟨13803633751702957249355575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 294477520036329754652918933 13803633751702957249355575)
      ·
        refine ⟨20705450627554435874033363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13803633751702957249355575 20705450627554435874033363)
        ·
          refine ⟨31058175941331653811050045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20705450627554435874033363 31058175941331653811050045)
          ·
            refine ⟨11646815977999370179143767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31058175941331653811050045 11646815977999370179143767)
            ·
              refine ⟨17470223966999055268715651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11646815977999370179143767 17470223966999055268715651)
              ·
                refine ⟨26205335950498582903073477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17470223966999055268715651 26205335950498582903073477)
                ·
                  refine ⟨4913500490718484294326277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26205335950498582903073477 4913500490718484294326277)
                  ·
                    refine ⟨921281342009715805186177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4913500490718484294326277 921281342009715805186177)
                    ·
                      rfl

theorem cell23_5382567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 1, 4, 4].length) (baseStart_5382567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5382567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5382567 prefixEnd_5382567 := by exact prefixLift 5382567
  have htrace : WordTrace (prefixWord ++ tailWord_5382567) baseStart_5382567 baseEnd_5382567 := by
    simpa [prefixWord, tailWord_5382567, baseEnd_5382567] using wordTrace_append hprefix tailTrace_5382567
  have hstable : (prefixWord ++ tailWord_5382567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5382567).length < 2 ^ (prefixWord ++ tailWord_5382567).sum := by decide
  have hdescent : baseEnd_5382567 < baseStart_5382567 := by decide
  rcases family_descends (prefixWord ++ tailWord_5382567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5382650 : List Nat := [3, 1, 1, 1, 1, 2, 2, 1, 4, 4, 3]
def baseStart_5382650 : Nat := 118140960795 + 5382650 * 2 ^ 59
def prefixEnd_5382650 : Nat := 4983230072969 + 3 ^ 40 * 5382650 * 2
def baseEnd_5382650 : Nat := 2763886644923470590820649

theorem tailTrace_5382650 : CollatzResearch.WordTrace tailWord_5382650 prefixEnd_5382650 2763886644923470590820649 := by
  unfold tailWord_5382650
  simp only [CollatzResearch.WordTrace]
  refine ⟨49080343487396452069304351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130880915966390538851478269 49080343487396452069304351)
  ·
    refine ⟨73620515231094678103956527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49080343487396452069304351 73620515231094678103956527)
    ·
      refine ⟨110430772846642017155934791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73620515231094678103956527 110430772846642017155934791)
      ·
        refine ⟨165646159269963025733902187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110430772846642017155934791 165646159269963025733902187)
        ·
          refine ⟨248469238904944538600853281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165646159269963025733902187 248469238904944538600853281)
          ·
            refine ⟨186351929178708403950639961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 248469238904944538600853281 186351929178708403950639961)
            ·
              refine ⟨139763946884031302962979971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 186351929178708403950639961 139763946884031302962979971)
              ·
                refine ⟨209645920326046954444469957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 139763946884031302962979971 209645920326046954444469957)
                ·
                  refine ⟨39308610061133803958338117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 209645920326046954444469957 39308610061133803958338117)
                  ·
                    refine ⟨7370364386462588242188397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39308610061133803958338117 7370364386462588242188397)
                    ·
                      refine ⟨2763886644923470590820649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7370364386462588242188397 2763886644923470590820649)
                      ·
                        rfl

theorem cell23_5382650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 4, 4, 3].length) (baseStart_5382650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5382650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5382650 prefixEnd_5382650 := by exact prefixLift 5382650
  have htrace : WordTrace (prefixWord ++ tailWord_5382650) baseStart_5382650 baseEnd_5382650 := by
    simpa [prefixWord, tailWord_5382650, baseEnd_5382650] using wordTrace_append hprefix tailTrace_5382650
  have hstable : (prefixWord ++ tailWord_5382650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5382650).length < 2 ^ (prefixWord ++ tailWord_5382650).sum := by decide
  have hdescent : baseEnd_5382650 < baseStart_5382650 := by decide
  rcases family_descends (prefixWord ++ tailWord_5382650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5382690 : List Nat := [3, 3, 1, 1, 1, 1, 1, 1, 2, 1, 8]
def baseStart_5382690 : Nat := 118140960795 + 5382690 * 2 ^ 59
def prefixEnd_5382690 : Nat := 4983230072969 + 3 ^ 40 * 5382690 * 2
def baseEnd_5382690 : Nat := 2763907184149650434320465

theorem tailTrace_5382690 : CollatzResearch.WordTrace tailWord_5382690 prefixEnd_5382690 2763907184149650434320465 := by
  unfold tailWord_5382690
  simp only [CollatzResearch.WordTrace]
  refine ⟨49080708217360223777168381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130881888579627263405782349 49080708217360223777168381)
  ·
    refine ⟨18405265581510083916438143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49080708217360223777168381 18405265581510083916438143)
    ·
      refine ⟨27607898372265125874657215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18405265581510083916438143 27607898372265125874657215)
      ·
        refine ⟨41411847558397688811985823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27607898372265125874657215 41411847558397688811985823)
        ·
          refine ⟨62117771337596533217978735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41411847558397688811985823 62117771337596533217978735)
          ·
            refine ⟨93176657006394799826968103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62117771337596533217978735 93176657006394799826968103)
            ·
              refine ⟨139764985509592199740452155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93176657006394799826968103 139764985509592199740452155)
              ·
                refine ⟨209647478264388299610678233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 139764985509592199740452155 209647478264388299610678233)
                ·
                  refine ⟨157235608698291224708008675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 209647478264388299610678233 157235608698291224708008675)
                  ·
                    refine ⟨235853413047436837062013013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 157235608698291224708008675 235853413047436837062013013)
                    ·
                      refine ⟨2763907184149650434320465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 235853413047436837062013013 2763907184149650434320465)
                      ·
                        rfl

theorem cell23_5382690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_5382690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5382690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5382690 prefixEnd_5382690 := by exact prefixLift 5382690
  have htrace : WordTrace (prefixWord ++ tailWord_5382690) baseStart_5382690 baseEnd_5382690 := by
    simpa [prefixWord, tailWord_5382690, baseEnd_5382690] using wordTrace_append hprefix tailTrace_5382690
  have hstable : (prefixWord ++ tailWord_5382690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5382690).length < 2 ^ (prefixWord ++ tailWord_5382690).sum := by decide
  have hdescent : baseEnd_5382690 < baseStart_5382690 := by decide
  rcases family_descends (prefixWord ++ tailWord_5382690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5382700 : List Nat := [2, 2, 1, 1, 1, 2, 1, 4, 4, 5]
def baseStart_5382700 : Nat := 118140960795 + 5382700 * 2 ^ 59
def prefixEnd_5382700 : Nat := 4983230072969 + 3 ^ 40 * 5382700 * 2
def baseEnd_5382700 : Nat := 921304106318731798398473

theorem tailTrace_5382700 : CollatzResearch.WordTrace tailWord_5382700 prefixEnd_5382700 921304106318731798398473 := by
  unfold tailWord_5382700
  simp only [CollatzResearch.WordTrace]
  refine ⟨98161598799702333408268777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130882131732936444544358369 98161598799702333408268777)
  ·
    refine ⟨73621199099776750056201583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98161598799702333408268777 73621199099776750056201583)
    ·
      refine ⟨110431798649665125084302375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73621199099776750056201583 110431798649665125084302375)
      ·
        refine ⟨165647697974497687626453563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110431798649665125084302375 165647697974497687626453563)
        ·
          refine ⟨248471546961746531439680345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165647697974497687626453563 248471546961746531439680345)
          ·
            refine ⟨186353660221309898579760259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 248471546961746531439680345 186353660221309898579760259)
            ·
              refine ⟨279530490331964847869640389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 186353660221309898579760259 279530490331964847869640389)
              ·
                refine ⟨52411966937243408975557573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 279530490331964847869640389 52411966937243408975557573)
                ·
                  refine ⟨9827243800733139182917045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52411966937243408975557573 9827243800733139182917045)
                  ·
                    refine ⟨921304106318731798398473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9827243800733139182917045 921304106318731798398473)
                    ·
                      rfl

theorem cell23_5382700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 5].length) (baseStart_5382700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5382700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5382700 prefixEnd_5382700 := by exact prefixLift 5382700
  have htrace : WordTrace (prefixWord ++ tailWord_5382700) baseStart_5382700 baseEnd_5382700 := by
    simpa [prefixWord, tailWord_5382700, baseEnd_5382700] using wordTrace_append hprefix tailTrace_5382700
  have hstable : (prefixWord ++ tailWord_5382700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5382700).length < 2 ^ (prefixWord ++ tailWord_5382700).sum := by decide
  have hdescent : baseEnd_5382700 < baseStart_5382700 := by decide
  rcases family_descends (prefixWord ++ tailWord_5382700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5382707 : List Nat := [1, 1, 1, 2, 4, 2, 1, 2, 2, 5, 2]
def baseStart_5382707 : Nat := 118140960795 + 5382707 * 2 ^ 59
def prefixEnd_5382707 : Nat := 4983230072969 + 3 ^ 40 * 5382707 * 2
def baseEnd_5382707 : Nat := 2763915913320776867807887

theorem tailTrace_5382707 : CollatzResearch.WordTrace tailWord_5382707 prefixEnd_5382707 2763915913320776867807887 := by
  unfold tailWord_5382707
  simp only [CollatzResearch.WordTrace]
  refine ⟨196323452910379307012042375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130882301940252871341361583 196323452910379307012042375)
  ·
    refine ⟨294485179365568960518063563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196323452910379307012042375 294485179365568960518063563)
    ·
      refine ⟨441727769048353440777095345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294485179365568960518063563 441727769048353440777095345)
      ·
        refine ⟨331295826786265080582821509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 441727769048353440777095345 331295826786265080582821509)
        ·
          refine ⟨62117967522424702609279033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 331295826786265080582821509 62117967522424702609279033)
          ·
            refine ⟨46588475641818526956959275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62117967522424702609279033 46588475641818526956959275)
            ·
              refine ⟨69882713462727790435438913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46588475641818526956959275 69882713462727790435438913)
              ·
                refine ⟨52412035097045842826579185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69882713462727790435438913 52412035097045842826579185)
                ·
                  refine ⟨39309026322784382119934389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52412035097045842826579185 39309026322784382119934389)
                  ·
                    refine ⟨3685221217761035823743849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39309026322784382119934389 3685221217761035823743849)
                    ·
                      refine ⟨2763915913320776867807887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3685221217761035823743849 2763915913320776867807887)
                      ·
                        rfl

theorem cell23_5382707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 2, 2, 5, 2].length) (baseStart_5382707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5382707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5382707 prefixEnd_5382707 := by exact prefixLift 5382707
  have htrace : WordTrace (prefixWord ++ tailWord_5382707) baseStart_5382707 baseEnd_5382707 := by
    simpa [prefixWord, tailWord_5382707, baseEnd_5382707] using wordTrace_append hprefix tailTrace_5382707
  have hstable : (prefixWord ++ tailWord_5382707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5382707).length < 2 ^ (prefixWord ++ tailWord_5382707).sum := by decide
  have hdescent : baseEnd_5382707 < baseStart_5382707 := by decide
  rcases family_descends (prefixWord ++ tailWord_5382707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5382717 : List Nat := [1, 4, 1, 3, 2, 2, 1, 1, 1, 7]
def baseStart_5382717 : Nat := 118140960795 + 5382717 * 2 ^ 59
def prefixEnd_5382717 : Nat := 4983230072969 + 3 ^ 40 * 5382717 * 2
def baseEnd_5382717 : Nat := 921307016042440609560947

theorem tailTrace_5382717 : CollatzResearch.WordTrace tailWord_5382717 prefixEnd_5382717 921307016042440609560947 := by
  unfold tailWord_5382717
  simp only [CollatzResearch.WordTrace]
  refine ⟨196323817640343078719906405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130882545093562052479937603 196323817640343078719906405)
  ·
    refine ⟨36810715807564327259982451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 196323817640343078719906405 36810715807564327259982451)
    ·
      refine ⟨55216073711346490889973677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36810715807564327259982451 55216073711346490889973677)
      ·
        refine ⟨20706027641754934083740129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55216073711346490889973677 20706027641754934083740129)
        ·
          refine ⟨15529520731316200562805097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20706027641754934083740129 15529520731316200562805097)
          ·
            refine ⟨11647140548487150422103823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15529520731316200562805097 11647140548487150422103823)
            ·
              refine ⟨17470710822730725633155735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11647140548487150422103823 17470710822730725633155735)
              ·
                refine ⟨26206066234096088449733603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17470710822730725633155735 26206066234096088449733603)
                ·
                  refine ⟨39309099351144132674600405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26206066234096088449733603 39309099351144132674600405)
                  ·
                    refine ⟨921307016042440609560947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39309099351144132674600405 921307016042440609560947)
                    ·
                      rfl

theorem cell23_5382717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 1, 1, 7].length) (baseStart_5382717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5382717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5382717 prefixEnd_5382717 := by exact prefixLift 5382717
  have htrace : WordTrace (prefixWord ++ tailWord_5382717) baseStart_5382717 baseEnd_5382717 := by
    simpa [prefixWord, tailWord_5382717, baseEnd_5382717] using wordTrace_append hprefix tailTrace_5382717
  have hstable : (prefixWord ++ tailWord_5382717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5382717).length < 2 ^ (prefixWord ++ tailWord_5382717).sum := by decide
  have hdescent : baseEnd_5382717 < baseStart_5382717 := by decide
  rcases family_descends (prefixWord ++ tailWord_5382717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5382798 : List Nat := [4, 1, 1, 3, 1, 1, 5, 2, 1, 4]
def baseStart_5382798 : Nat := 118140960795 + 5382798 * 2 ^ 59
def prefixEnd_5382798 : Nat := 4983230072969 + 3 ^ 40 * 5382798 * 2
def baseEnd_5382798 : Nat := 921320880020112003923323

theorem tailTrace_5382798 : CollatzResearch.WordTrace tailWord_5382798 prefixEnd_5382798 921320880020112003923323 := by
  unfold tailWord_5382798
  simp only [CollatzResearch.WordTrace]
  refine ⟨24540846494131203694200631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130884514635366419702403365 24540846494131203694200631)
  ·
    refine ⟨36811269741196805541300947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24540846494131203694200631 36811269741196805541300947)
    ·
      refine ⟨55216904611795208311951421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36811269741196805541300947 55216904611795208311951421)
      ·
        refine ⟨20706339229423203116981783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55216904611795208311951421 20706339229423203116981783)
        ·
          refine ⟨31059508844134804675472675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20706339229423203116981783 31059508844134804675472675)
          ·
            refine ⟨46589263266202207013209013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31059508844134804675472675 46589263266202207013209013)
            ·
              refine ⟨4367743431206456907488345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46589263266202207013209013 4367743431206456907488345)
              ·
                refine ⟨3275807573404842680616259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4367743431206456907488345 3275807573404842680616259)
                ·
                  refine ⟨4913711360107264020924389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3275807573404842680616259 4913711360107264020924389)
                  ·
                    refine ⟨921320880020112003923323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4913711360107264020924389 921320880020112003923323)
                    ·
                      rfl

theorem cell23_5382798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 5, 2, 1, 4].length) (baseStart_5382798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5382798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5382798 prefixEnd_5382798 := by exact prefixLift 5382798
  have htrace : WordTrace (prefixWord ++ tailWord_5382798) baseStart_5382798 baseEnd_5382798 := by
    simpa [prefixWord, tailWord_5382798, baseEnd_5382798] using wordTrace_append hprefix tailTrace_5382798
  have hstable : (prefixWord ++ tailWord_5382798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5382798).length < 2 ^ (prefixWord ++ tailWord_5382798).sum := by decide
  have hdescent : baseEnd_5382798 < baseStart_5382798 := by decide
  rcases family_descends (prefixWord ++ tailWord_5382798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5382800 : List Nat := [2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 7]
def baseStart_5382800 : Nat := 118140960795 + 5382800 * 2 ^ 59
def prefixEnd_5382800 : Nat := 4983230072969 + 3 ^ 40 * 5382800 * 2
def baseEnd_5382800 : Nat := 2763963667021645003944959

theorem tailTrace_5382800 : CollatzResearch.WordTrace tailWord_5382800 prefixEnd_5382800 2763963667021645003944959 := by
  unfold tailWord_5382800
  simp only [CollatzResearch.WordTrace]
  refine ⟨98163422449521191947588927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130884563266028255930118569 98163422449521191947588927)
  ·
    refine ⟨147245133674281787921383391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98163422449521191947588927 147245133674281787921383391)
    ·
      refine ⟨220867700511422681882075087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147245133674281787921383391 220867700511422681882075087)
      ·
        refine ⟨331301550767134022823112631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220867700511422681882075087 331301550767134022823112631)
        ·
          refine ⟨496952326150701034234668947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 331301550767134022823112631 496952326150701034234668947)
          ·
            refine ⟨745428489226051551352003421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 496952326150701034234668947 745428489226051551352003421)
            ·
              refine ⟨279535683459769331757001283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 745428489226051551352003421 279535683459769331757001283)
              ·
                refine ⟨419303525189653997635501925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 279535683459769331757001283 419303525189653997635501925)
                ·
                  refine ⟨78619410973060124556656611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 419303525189653997635501925 78619410973060124556656611)
                  ·
                    refine ⟨117929116459590186834984917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 78619410973060124556656611 117929116459590186834984917)
                    ·
                      refine ⟨2763963667021645003944959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 117929116459590186834984917 2763963667021645003944959)
                      ·
                        rfl

theorem cell23_5382800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 7].length) (baseStart_5382800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5382800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5382800 prefixEnd_5382800 := by exact prefixLift 5382800
  have htrace : WordTrace (prefixWord ++ tailWord_5382800) baseStart_5382800 baseEnd_5382800 := by
    simpa [prefixWord, tailWord_5382800, baseEnd_5382800] using wordTrace_append hprefix tailTrace_5382800
  have hstable : (prefixWord ++ tailWord_5382800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5382800).length < 2 ^ (prefixWord ++ tailWord_5382800).sum := by decide
  have hdescent : baseEnd_5382800 < baseStart_5382800 := by decide
  rcases family_descends (prefixWord ++ tailWord_5382800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5382807 : List Nat := [1, 1, 3, 3, 2, 1, 2, 2, 3, 5]
def baseStart_5382807 : Nat := 118140960795 + 5382807 * 2 ^ 59
def prefixEnd_5382807 : Nat := 4983230072969 + 3 ^ 40 * 5382807 * 2
def baseEnd_5382807 : Nat := 921322420462075492185809

theorem tailTrace_5382807 : CollatzResearch.WordTrace tailWord_5382807 prefixEnd_5382807 921322420462075492185809 := by
  unfold tailWord_5382807
  simp only [CollatzResearch.WordTrace]
  refine ⟨196327100210017024090682675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130884733473344682727121783 196327100210017024090682675)
  ·
    refine ⟨294490650315025536136024013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196327100210017024090682675 294490650315025536136024013)
    ·
      refine ⟨110433993868134576051009005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 294490650315025536136024013 110433993868134576051009005)
      ·
        refine ⟨41412747700550466019128377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110433993868134576051009005 41412747700550466019128377)
        ·
          refine ⟨31059560775412849514346283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41412747700550466019128377 31059560775412849514346283)
          ·
            refine ⟨46589341163119274271519425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31059560775412849514346283 46589341163119274271519425)
            ·
              refine ⟨34942005872339455703639569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46589341163119274271519425 34942005872339455703639569)
              ·
                refine ⟨26206504404254591777729677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34942005872339455703639569 26206504404254591777729677)
                ·
                  refine ⟨9827439151595471916648629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26206504404254591777729677 9827439151595471916648629)
                  ·
                    refine ⟨921322420462075492185809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9827439151595471916648629 921322420462075492185809)
                    ·
                      rfl

theorem cell23_5382807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 2, 3, 5].length) (baseStart_5382807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5382807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5382807 prefixEnd_5382807 := by exact prefixLift 5382807
  have htrace : WordTrace (prefixWord ++ tailWord_5382807) baseStart_5382807 baseEnd_5382807 := by
    simpa [prefixWord, tailWord_5382807, baseEnd_5382807] using wordTrace_append hprefix tailTrace_5382807
  have hstable : (prefixWord ++ tailWord_5382807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5382807).length < 2 ^ (prefixWord ++ tailWord_5382807).sum := by decide
  have hdescent : baseEnd_5382807 < baseStart_5382807 := by decide
  rcases family_descends (prefixWord ++ tailWord_5382807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5382831 : List Nat := [1, 1, 2, 1, 2, 6, 2, 1, 2, 3, 2]
def baseStart_5382831 : Nat := 118140960795 + 5382831 * 2 ^ 59
def prefixEnd_5382831 : Nat := 4983230072969 + 3 ^ 40 * 5382831 * 2
def baseEnd_5382831 : Nat := 2763979584921934382657317

theorem tailTrace_5382831 : CollatzResearch.WordTrace tailWord_5382831 prefixEnd_5382831 2763979584921934382657317 := by
  unfold tailWord_5382831
  simp only [CollatzResearch.WordTrace]
  refine ⟨196327975561930076189556347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130885317041286717459704231 196327975561930076189556347)
  ·
    refine ⟨294491963342895114284334521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196327975561930076189556347 294491963342895114284334521)
    ·
      refine ⟨220868972507171335713250891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 294491963342895114284334521 220868972507171335713250891)
      ·
        refine ⟨331303458760757003569876337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220868972507171335713250891 331303458760757003569876337)
        ·
          refine ⟨248477594070567752677407253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 331303458760757003569876337 248477594070567752677407253)
          ·
            refine ⟨11647387222057863406753465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 248477594070567752677407253 11647387222057863406753465)
            ·
              refine ⟨8735540416543397555065099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11647387222057863406753465 8735540416543397555065099)
              ·
                refine ⟨13103310624815096332597649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8735540416543397555065099 13103310624815096332597649)
                ·
                  refine ⟨9827482968611322249448237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13103310624815096332597649 9827482968611322249448237)
                  ·
                    refine ⟨3685306113229245843543089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9827482968611322249448237 3685306113229245843543089)
                    ·
                      refine ⟨2763979584921934382657317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3685306113229245843543089 2763979584921934382657317)
                      ·
                        rfl

theorem cell23_5382831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2, 1, 2, 3, 2].length) (baseStart_5382831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5382831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5382831 prefixEnd_5382831 := by exact prefixLift 5382831
  have htrace : WordTrace (prefixWord ++ tailWord_5382831) baseStart_5382831 baseEnd_5382831 := by
    simpa [prefixWord, tailWord_5382831, baseEnd_5382831] using wordTrace_append hprefix tailTrace_5382831
  have hstable : (prefixWord ++ tailWord_5382831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5382831).length < 2 ^ (prefixWord ++ tailWord_5382831).sum := by decide
  have hdescent : baseEnd_5382831 < baseStart_5382831 := by decide
  rcases family_descends (prefixWord ++ tailWord_5382831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5382849 : List Nat := [1, 2, 6, 2, 2, 1, 2, 2, 1, 4]
def baseStart_5382849 : Nat := 118140960795 + 5382849 * 2 ^ 59
def prefixEnd_5382849 : Nat := 4983230072969 + 3 ^ 40 * 5382849 * 2
def baseEnd_5382849 : Nat := 921329609191238437410745

theorem tailTrace_5382849 : CollatzResearch.WordTrace tailWord_5382849 prefixEnd_5382849 921329609191238437410745 := by
  unfold tailWord_5382849
  simp only [CollatzResearch.WordTrace]
  refine ⟨196328632075864865263711601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130885754717243243509141067 196328632075864865263711601)
  ·
    refine ⟨147246474056898648947783701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196328632075864865263711601 147246474056898648947783701)
    ·
      refine ⟨6902178471417124169427361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 147246474056898648947783701 6902178471417124169427361)
      ·
        refine ⟨5176633853562843127070521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6902178471417124169427361 5176633853562843127070521)
        ·
          refine ⟨3882475390172132345302891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5176633853562843127070521 3882475390172132345302891)
          ·
            refine ⟨5823713085258198517954337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3882475390172132345302891 5823713085258198517954337)
            ·
              refine ⟨4367784813943648888465753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5823713085258198517954337 4367784813943648888465753)
              ·
                refine ⟨3275838610457736666349315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4367784813943648888465753 3275838610457736666349315)
                ·
                  refine ⟨4913757915686604999523973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3275838610457736666349315 4913757915686604999523973)
                  ·
                    refine ⟨921329609191238437410745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4913757915686604999523973 921329609191238437410745)
                    ·
                      rfl

theorem cell23_5382849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_5382849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5382849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5382849 prefixEnd_5382849 := by exact prefixLift 5382849
  have htrace : WordTrace (prefixWord ++ tailWord_5382849) baseStart_5382849 baseEnd_5382849 := by
    simpa [prefixWord, tailWord_5382849, baseEnd_5382849] using wordTrace_append hprefix tailTrace_5382849
  have hstable : (prefixWord ++ tailWord_5382849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5382849).length < 2 ^ (prefixWord ++ tailWord_5382849).sum := by decide
  have hdescent : baseEnd_5382849 < baseStart_5382849 := by decide
  rcases family_descends (prefixWord ++ tailWord_5382849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5382874 : List Nat := [3, 1, 1, 2, 2, 2, 4, 1, 1, 2, 4]
def baseStart_5382874 : Nat := 118140960795 + 5382874 * 2 ^ 59
def prefixEnd_5382874 : Nat := 4983230072969 + 3 ^ 40 * 5382874 * 2
def baseEnd_5382874 : Nat := 2764001664590077714419619

theorem tailTrace_5382874 : CollatzResearch.WordTrace tailWord_5382874 prefixEnd_5382874 2764001664590077714419619 := by
  unfold tailWord_5382874
  simp only [CollatzResearch.WordTrace]
  refine ⟨49082385975193573633342919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130886362600516196355581117 49082385975193573633342919)
  ·
    refine ⟨73623578962790360450014379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49082385975193573633342919 73623578962790360450014379)
    ·
      refine ⟨110435368444185540675021569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73623578962790360450014379 110435368444185540675021569)
      ·
        refine ⟨82826526333139155506266177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110435368444185540675021569 82826526333139155506266177)
        ·
          refine ⟨62119894749854366629699633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82826526333139155506266177 62119894749854366629699633)
          ·
            refine ⟨46589921062390774972274725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62119894749854366629699633 46589921062390774972274725)
            ·
              refine ⟨8735610199198270307301511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46589921062390774972274725 8735610199198270307301511)
              ·
                refine ⟨13103415298797405460952267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8735610199198270307301511 13103415298797405460952267)
                ·
                  refine ⟨19655122948196108191428401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13103415298797405460952267 19655122948196108191428401)
                  ·
                    refine ⟨14741342211147081143571301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19655122948196108191428401 14741342211147081143571301)
                    ·
                      refine ⟨2764001664590077714419619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14741342211147081143571301 2764001664590077714419619)
                      ·
                        rfl

theorem cell23_5382874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4, 1, 1, 2, 4].length) (baseStart_5382874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5382874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5382874 prefixEnd_5382874 := by exact prefixLift 5382874
  have htrace : WordTrace (prefixWord ++ tailWord_5382874) baseStart_5382874 baseEnd_5382874 := by
    simpa [prefixWord, tailWord_5382874, baseEnd_5382874] using wordTrace_append hprefix tailTrace_5382874
  have hstable : (prefixWord ++ tailWord_5382874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5382874).length < 2 ^ (prefixWord ++ tailWord_5382874).sum := by decide
  have hdescent : baseEnd_5382874 < baseStart_5382874 := by decide
  rcases family_descends (prefixWord ++ tailWord_5382874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5382884 : List Nat := [2, 3, 1, 1, 1, 5, 3, 7]
def baseStart_5382884 : Nat := 118140960795 + 5382884 * 2 ^ 59
def prefixEnd_5382884 : Nat := 4983230072969 + 3 ^ 40 * 5382884 * 2
def baseEnd_5382884 : Nat := 102370622199874913899799

theorem tailTrace_5382884 : CollatzResearch.WordTrace tailWord_5382884 prefixEnd_5382884 102370622199874913899799 := by
  unfold tailWord_5382884
  simp only [CollatzResearch.WordTrace]
  refine ⟨98164954315369033120617853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130886605753825377494157137 98164954315369033120617853)
  ·
    refine ⟨36811857868263387420231695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98164954315369033120617853 36811857868263387420231695)
    ·
      refine ⟨55217786802395081130347543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36811857868263387420231695 55217786802395081130347543)
      ·
        refine ⟨82826680203592621695521315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55217786802395081130347543 82826680203592621695521315)
        ·
          refine ⟨124240020305388932543281973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82826680203592621695521315 124240020305388932543281973)
          ·
            refine ⟨11647501903630212425932685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 124240020305388932543281973 11647501903630212425932685)
            ·
              refine ⟨4367813213861329659724757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11647501903630212425932685 4367813213861329659724757)
              ·
                refine ⟨102370622199874913899799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4367813213861329659724757 102370622199874913899799)
                ·
                  rfl

theorem cell23_5382884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 3, 7].length) (baseStart_5382884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5382884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5382884 prefixEnd_5382884 := by exact prefixLift 5382884
  have htrace : WordTrace (prefixWord ++ tailWord_5382884) baseStart_5382884 baseEnd_5382884 := by
    simpa [prefixWord, tailWord_5382884, baseEnd_5382884] using wordTrace_append hprefix tailTrace_5382884
  have hstable : (prefixWord ++ tailWord_5382884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5382884).length < 2 ^ (prefixWord ++ tailWord_5382884).sum := by decide
  have hdescent : baseEnd_5382884 < baseStart_5382884 := by decide
  rcases family_descends (prefixWord ++ tailWord_5382884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5382895 : List Nat := [1, 1, 2, 1, 5, 3, 2, 3, 1, 2, 2]
def baseStart_5382895 : Nat := 118140960795 + 5382895 * 2 ^ 59
def prefixEnd_5382895 : Nat := 4983230072969 + 3 ^ 40 * 5382895 * 2
def baseEnd_5382895 : Nat := 2764012447683822132257023

theorem tailTrace_5382895 : CollatzResearch.WordTrace tailWord_5382895 prefixEnd_5382895 2764012447683822132257023 := by
  unfold tailWord_5382895
  simp only [CollatzResearch.WordTrace]
  refine ⟨196330309833698215119886139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130886873222465476746590759 196330309833698215119886139)
  ·
    refine ⟨294495464750547322679829209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196330309833698215119886139 294495464750547322679829209)
    ·
      refine ⟨220871598562910492009871907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 294495464750547322679829209 220871598562910492009871907)
      ·
        refine ⟨331307397844365738014807861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220871598562910492009871907 331307397844365738014807861)
        ·
          refine ⟨31060068547909287938888237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 331307397844365738014807861 31060068547909287938888237)
          ·
            refine ⟨11647525705465982977083089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31060068547909287938888237 11647525705465982977083089)
            ·
              refine ⟨8735644279099487232812317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11647525705465982977083089 8735644279099487232812317)
              ·
                refine ⟨3275866604662307712304619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8735644279099487232812317 3275866604662307712304619)
                ·
                  refine ⟨4913799906993461568456929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3275866604662307712304619 4913799906993461568456929)
                  ·
                    refine ⟨3685349930245096176342697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4913799906993461568456929 3685349930245096176342697)
                    ·
                      refine ⟨2764012447683822132257023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3685349930245096176342697 2764012447683822132257023)
                      ·
                        rfl

theorem cell23_5382895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2, 3, 1, 2, 2].length) (baseStart_5382895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5382895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5382895 prefixEnd_5382895 := by exact prefixLift 5382895
  have htrace : WordTrace (prefixWord ++ tailWord_5382895) baseStart_5382895 baseEnd_5382895 := by
    simpa [prefixWord, tailWord_5382895, baseEnd_5382895] using wordTrace_append hprefix tailTrace_5382895
  have hstable : (prefixWord ++ tailWord_5382895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5382895).length < 2 ^ (prefixWord ++ tailWord_5382895).sum := by decide
  have hdescent : baseEnd_5382895 < baseStart_5382895 := by decide
  rcases family_descends (prefixWord ++ tailWord_5382895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5382898 : List Nat := [3, 2, 1, 3, 1, 2, 4, 1, 1, 2, 3]
def baseStart_5382898 : Nat := 118140960795 + 5382898 * 2 ^ 59
def prefixEnd_5382898 : Nat := 4983230072969 + 3 ^ 40 * 5382898 * 2
def baseEnd_5382898 : Nat := 2764013988125785620519509

theorem tailTrace_5382898 : CollatzResearch.WordTrace tailWord_5382898 prefixEnd_5382898 2764013988125785620519509 := by
  unfold tailWord_5382898
  simp only [CollatzResearch.WordTrace]
  refine ⟨49082604813171836658061337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130886946168458231088163565 49082604813171836658061337)
  ·
    refine ⟨36811953609878877493546003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49082604813171836658061337 36811953609878877493546003)
    ·
      refine ⟨55217930414818316240319005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36811953609878877493546003 55217930414818316240319005)
      ·
        refine ⟨20706723905556868590119627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55217930414818316240319005 20706723905556868590119627)
        ·
          refine ⟨31060085858335302885179441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20706723905556868590119627 31060085858335302885179441)
          ·
            refine ⟨23295064393751477163884581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31060085858335302885179441 23295064393751477163884581)
            ·
              refine ⟨4367824573828401968228359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23295064393751477163884581 4367824573828401968228359)
              ·
                refine ⟨6551736860742602952342539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4367824573828401968228359 6551736860742602952342539)
                ·
                  refine ⟨9827605291113904428513809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6551736860742602952342539 9827605291113904428513809)
                  ·
                    refine ⟨7370703968335428321385357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9827605291113904428513809 7370703968335428321385357)
                    ·
                      refine ⟨2764013988125785620519509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7370703968335428321385357 2764013988125785620519509)
                      ·
                        rfl

theorem cell23_5382898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 4, 1, 1, 2, 3].length) (baseStart_5382898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5382898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5382898 prefixEnd_5382898 := by exact prefixLift 5382898
  have htrace : WordTrace (prefixWord ++ tailWord_5382898) baseStart_5382898 baseEnd_5382898 := by
    simpa [prefixWord, tailWord_5382898, baseEnd_5382898] using wordTrace_append hprefix tailTrace_5382898
  have hstable : (prefixWord ++ tailWord_5382898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5382898).length < 2 ^ (prefixWord ++ tailWord_5382898).sum := by decide
  have hdescent : baseEnd_5382898 < baseStart_5382898 := by decide
  rcases family_descends (prefixWord ++ tailWord_5382898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5382917 : List Nat := [1, 3, 1, 1, 2, 1, 1, 3, 1, 5, 4]
def baseStart_5382917 : Nat := 118140960795 + 5382917 * 2 ^ 59
def prefixEnd_5382917 : Nat := 4983230072969 + 3 ^ 40 * 5382917 * 2
def baseEnd_5382917 : Nat := 2764023744258221046181921

theorem tailTrace_5382917 : CollatzResearch.WordTrace tailWord_5382917 prefixEnd_5382917 2764023744258221046181921 := by
  unfold tailWord_5382917
  simp only [CollatzResearch.WordTrace]
  refine ⟨196331112239618512877187005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130887408159745675251458003 196331112239618512877187005)
  ·
    refine ⟨73624167089856942328945127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 196331112239618512877187005 73624167089856942328945127)
    ·
      refine ⟨110436250634785413493417691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73624167089856942328945127 110436250634785413493417691)
      ·
        refine ⟨165654375952178120240126537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110436250634785413493417691 165654375952178120240126537)
        ·
          refine ⟨124240781964133590180094903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165654375952178120240126537 124240781964133590180094903)
          ·
            refine ⟨186361172946200385270142355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124240781964133590180094903 186361172946200385270142355)
            ·
              refine ⟨279541759419300577905213533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 186361172946200385270142355 279541759419300577905213533)
              ·
                refine ⟨104828159782237716714455075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 279541759419300577905213533 104828159782237716714455075)
                ·
                  refine ⟨157242239673356575071682613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 104828159782237716714455075 157242239673356575071682613)
                  ·
                    refine ⟨14741459969377178912970245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 157242239673356575071682613 14741459969377178912970245)
                    ·
                      refine ⟨2764023744258221046181921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14741459969377178912970245 2764023744258221046181921)
                      ·
                        rfl

theorem cell23_5382917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 5, 4].length) (baseStart_5382917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5382917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5382917 prefixEnd_5382917 := by exact prefixLift 5382917
  have htrace : WordTrace (prefixWord ++ tailWord_5382917) baseStart_5382917 baseEnd_5382917 := by
    simpa [prefixWord, tailWord_5382917, baseEnd_5382917] using wordTrace_append hprefix tailTrace_5382917
  have hstable : (prefixWord ++ tailWord_5382917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5382917).length < 2 ^ (prefixWord ++ tailWord_5382917).sum := by decide
  have hdescent : baseEnd_5382917 < baseStart_5382917 := by decide
  rcases family_descends (prefixWord ++ tailWord_5382917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5382927 : List Nat := [1, 1, 2, 1, 1, 1, 5, 3, 2, 6]
def baseStart_5382927 : Nat := 118140960795 + 5382927 * 2 ^ 59
def prefixEnd_5382927 : Nat := 4983230072969 + 3 ^ 40 * 5382927 * 2
def baseEnd_5382927 : Nat := 921342959688255335685625

theorem tailTrace_5382927 : CollatzResearch.WordTrace tailWord_5382927 prefixEnd_5382927 921342959688255335685625 := by
  unfold tailWord_5382927
  simp only [CollatzResearch.WordTrace]
  refine ⟨196331476969582284585051035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130887651313054856390034023 196331476969582284585051035)
  ·
    refine ⟨294497215454373426877576553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196331476969582284585051035 294497215454373426877576553)
    ·
      refine ⟨220872911590780070158182415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 294497215454373426877576553 220872911590780070158182415)
      ·
        refine ⟨331309367386170105237273623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220872911590780070158182415 331309367386170105237273623)
        ·
          refine ⟨496964051079255157855910435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 331309367386170105237273623 496964051079255157855910435)
          ·
            refine ⟨745446076618882736783865653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 496964051079255157855910435 745446076618882736783865653)
            ·
              refine ⟨69885569683020256573487405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 745446076618882736783865653 69885569683020256573487405)
              ·
                refine ⟨26207088631132596215057777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69885569683020256573487405 26207088631132596215057777)
                ·
                  refine ⟨19655316473349447161293333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26207088631132596215057777 19655316473349447161293333)
                  ·
                    refine ⟨921342959688255335685625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19655316473349447161293333 921342959688255335685625)
                    ·
                      rfl

theorem cell23_5382927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 3, 2, 6].length) (baseStart_5382927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5382927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5382927 prefixEnd_5382927 := by exact prefixLift 5382927
  have htrace : WordTrace (prefixWord ++ tailWord_5382927) baseStart_5382927 baseEnd_5382927 := by
    simpa [prefixWord, tailWord_5382927, baseEnd_5382927] using wordTrace_append hprefix tailTrace_5382927
  have hstable : (prefixWord ++ tailWord_5382927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5382927).length < 2 ^ (prefixWord ++ tailWord_5382927).sum := by decide
  have hdescent : baseEnd_5382927 < baseStart_5382927 := by decide
  rcases family_descends (prefixWord ++ tailWord_5382927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5382938 : List Nat := [3, 1, 1, 3, 2, 1, 4, 2, 1, 3, 2]
def baseStart_5382938 : Nat := 118140960795 + 5382938 * 2 ^ 59
def prefixEnd_5382938 : Nat := 4983230072969 + 3 ^ 40 * 5382938 * 2
def baseEnd_5382938 : Nat := 2764034527351965464019325

theorem tailTrace_5382938 : CollatzResearch.WordTrace tailWord_5382938 prefixEnd_5382938 2764034527351965464019325 := by
  unfold tailWord_5382938
  simp only [CollatzResearch.WordTrace]
  refine ⟨49082969543135608365925367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130887918781694955642467645 49082969543135608365925367)
  ·
    refine ⟨73624454314703412548888051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49082969543135608365925367 73624454314703412548888051)
    ·
      refine ⟨110436681472055118823332077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73624454314703412548888051 110436681472055118823332077)
      ·
        refine ⟨41413755552020669558749529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110436681472055118823332077 41413755552020669558749529)
        ·
          refine ⟨31060316664015502169062147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41413755552020669558749529 31060316664015502169062147)
          ·
            refine ⟨46590474996023253253593221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31060316664015502169062147 46590474996023253253593221)
            ·
              refine ⟨8735714061754359985048729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46590474996023253253593221 8735714061754359985048729)
              ·
                refine ⟨6551785546315769988786547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8735714061754359985048729 6551785546315769988786547)
                ·
                  refine ⟨9827678319473654983179821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6551785546315769988786547 9827678319473654983179821)
                  ·
                    refine ⟨3685379369802620618692433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9827678319473654983179821 3685379369802620618692433)
                    ·
                      refine ⟨2764034527351965464019325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3685379369802620618692433 2764034527351965464019325)
                      ·
                        rfl

theorem cell23_5382938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4, 2, 1, 3, 2].length) (baseStart_5382938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5382938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5382938 prefixEnd_5382938 := by exact prefixLift 5382938
  have htrace : WordTrace (prefixWord ++ tailWord_5382938) baseStart_5382938 baseEnd_5382938 := by
    simpa [prefixWord, tailWord_5382938, baseEnd_5382938] using wordTrace_append hprefix tailTrace_5382938
  have hstable : (prefixWord ++ tailWord_5382938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5382938).length < 2 ^ (prefixWord ++ tailWord_5382938).sum := by decide
  have hdescent : baseEnd_5382938 < baseStart_5382938 := by decide
  rcases family_descends (prefixWord ++ tailWord_5382938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5382967 : List Nat := [1, 1, 3, 1, 2, 1, 3, 1, 1, 2, 7]
def baseStart_5382967 : Nat := 118140960795 + 5382967 * 2 ^ 59
def prefixEnd_5382967 : Nat := 4983230072969 + 3 ^ 40 * 5382967 * 2
def baseEnd_5382967 : Nat := 2764049418290945850556691

theorem tailTrace_5382967 : CollatzResearch.WordTrace tailWord_5382967 prefixEnd_5382967 2764049418290945850556691 := by
  unfold tailWord_5382967
  simp only [CollatzResearch.WordTrace]
  refine ⟨196332935889437371416507155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130888623926291580944338103 196332935889437371416507155)
  ·
    refine ⟨294499403834156057124760733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196332935889437371416507155 294499403834156057124760733)
    ·
      refine ⟨110437276437808521421785275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 294499403834156057124760733 110437276437808521421785275)
      ·
        refine ⟨165655914656712782132677913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110437276437808521421785275 165655914656712782132677913)
        ·
          refine ⟨124241935992534586599508435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165655914656712782132677913 124241935992534586599508435)
          ·
            refine ⟨186362903988801879899262653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124241935992534586599508435 186362903988801879899262653)
            ·
              refine ⟨69886088995800704962223495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 186362903988801879899262653 69886088995800704962223495)
              ·
                refine ⟨104829133493701057443335243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69886088995800704962223495 104829133493701057443335243)
                ·
                  refine ⟨157243700240551586165002865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 104829133493701057443335243 157243700240551586165002865)
                  ·
                    refine ⟨117932775180413689623752149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 157243700240551586165002865 117932775180413689623752149)
                    ·
                      refine ⟨2764049418290945850556691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 117932775180413689623752149 2764049418290945850556691)
                      ·
                        rfl

theorem cell23_5382967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 2, 7].length) (baseStart_5382967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5382967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5382967 prefixEnd_5382967 := by exact prefixLift 5382967
  have htrace : WordTrace (prefixWord ++ tailWord_5382967) baseStart_5382967 baseEnd_5382967 := by
    simpa [prefixWord, tailWord_5382967, baseEnd_5382967] using wordTrace_append hprefix tailTrace_5382967
  have hstable : (prefixWord ++ tailWord_5382967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5382967).length < 2 ^ (prefixWord ++ tailWord_5382967).sum := by decide
  have hdescent : baseEnd_5382967 < baseStart_5382967 := by decide
  rcases family_descends (prefixWord ++ tailWord_5382967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5382968 : List Nat := [2, 1, 2, 1, 3, 2, 2, 4, 2, 2, 2]
def baseStart_5382968 : Nat := 118140960795 + 5382968 * 2 ^ 59
def prefixEnd_5382968 : Nat := 4983230072969 + 3 ^ 40 * 5382968 * 2
def baseEnd_5382968 : Nat := 2764049931771600346644187

theorem tailTrace_5382968 : CollatzResearch.WordTrace tailWord_5382968 prefixEnd_5382968 2764049931771600346644187 := by
  unfold tailWord_5382968
  simp only [CollatzResearch.WordTrace]
  refine ⟨98166486181216874293646779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130888648241622499058195705 98166486181216874293646779)
  ·
    refine ⟨147249729271825311440470169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98166486181216874293646779 147249729271825311440470169)
    ·
      refine ⟨110437296953868983580352627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147249729271825311440470169 110437296953868983580352627)
      ·
        refine ⟨165655945430803475370528941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110437296953868983580352627 165655945430803475370528941)
        ·
          refine ⟨62120979536551303263948353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 165655945430803475370528941 62120979536551303263948353)
          ·
            refine ⟨46590734652413477447961265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62120979536551303263948353 46590734652413477447961265)
            ·
              refine ⟨34943050989310108085970949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46590734652413477447961265 34943050989310108085970949)
              ·
                refine ⟨6551822060495645266119553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34943050989310108085970949 6551822060495645266119553)
                ·
                  refine ⟨4913866545371733949589665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6551822060495645266119553 4913866545371733949589665)
                  ·
                    refine ⟨3685399909028800462192249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4913866545371733949589665 3685399909028800462192249)
                    ·
                      refine ⟨2764049931771600346644187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3685399909028800462192249 2764049931771600346644187)
                      ·
                        rfl

theorem cell23_5382968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 4, 2, 2, 2].length) (baseStart_5382968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5382968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5382968 prefixEnd_5382968 := by exact prefixLift 5382968
  have htrace : WordTrace (prefixWord ++ tailWord_5382968) baseStart_5382968 baseEnd_5382968 := by
    simpa [prefixWord, tailWord_5382968, baseEnd_5382968] using wordTrace_append hprefix tailTrace_5382968
  have hstable : (prefixWord ++ tailWord_5382968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5382968).length < 2 ^ (prefixWord ++ tailWord_5382968).sum := by decide
  have hdescent : baseEnd_5382968 < baseStart_5382968 := by decide
  rcases family_descends (prefixWord ++ tailWord_5382968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5382984 : List Nat := [2, 1, 3, 1, 1, 3, 2, 1, 1, 5, 3]
def baseStart_5382984 : Nat := 118140960795 + 5382984 * 2 ^ 59
def prefixEnd_5382984 : Nat := 4983230072969 + 3 ^ 40 * 5382984 * 2
def baseEnd_5382984 : Nat := 2764058147462072284044113

theorem tailTrace_5382984 : CollatzResearch.WordTrace tailWord_5382984 prefixEnd_5382984 2764058147462072284044113 := by
  unfold tailWord_5382984
  simp only [CollatzResearch.WordTrace]
  refine ⟨98166777965187891659938003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130889037286917188879917337 98166777965187891659938003)
  ·
    refine ⟨147250166947781837489907005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98166777965187891659938003 147250166947781837489907005)
    ·
      refine ⟨55218812605418189058715127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147250166947781837489907005 55218812605418189058715127)
      ·
        refine ⟨82828218908127283588072691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55218812605418189058715127 82828218908127283588072691)
        ·
          refine ⟨124242328362190925382109037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82828218908127283588072691 124242328362190925382109037)
          ·
            refine ⟨46590873135821597018290889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 124242328362190925382109037 46590873135821597018290889)
            ·
              refine ⟨34943154851866197763718167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46590873135821597018290889 34943154851866197763718167)
              ·
                refine ⟨52414732277799296645577251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34943154851866197763718167 52414732277799296645577251)
                ·
                  refine ⟨78622098416698944968365877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52414732277799296645577251 78622098416698944968365877)
                  ·
                    refine ⟨7370821726565526090784301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 78622098416698944968365877 7370821726565526090784301)
                    ·
                      refine ⟨2764058147462072284044113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7370821726565526090784301 2764058147462072284044113)
                      ·
                        rfl

theorem cell23_5382984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 1, 1, 5, 3].length) (baseStart_5382984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5382984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5382984 prefixEnd_5382984 := by exact prefixLift 5382984
  have htrace : WordTrace (prefixWord ++ tailWord_5382984) baseStart_5382984 baseEnd_5382984 := by
    simpa [prefixWord, tailWord_5382984, baseEnd_5382984] using wordTrace_append hprefix tailTrace_5382984
  have hstable : (prefixWord ++ tailWord_5382984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5382984).length < 2 ^ (prefixWord ++ tailWord_5382984).sum := by decide
  have hdescent : baseEnd_5382984 < baseStart_5382984 := by decide
  rcases family_descends (prefixWord ++ tailWord_5382984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5382985 : List Nat := [1, 2, 1, 1, 2, 5, 4, 1, 2, 2, 2]
def baseStart_5382985 : Nat := 118140960795 + 5382985 * 2 ^ 59
def prefixEnd_5382985 : Nat := 4983230072969 + 3 ^ 40 * 5382985 * 2
def baseEnd_5382985 : Nat := 2764058660942726780131609

theorem tailTrace_5382985 : CollatzResearch.WordTrace tailWord_5382985 prefixEnd_5382985 2764058660942726780131609 := by
  unfold tailWord_5382985
  simp only [CollatzResearch.WordTrace]
  refine ⟨196333592403372160490662409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130889061602248106993774939 196333592403372160490662409)
  ·
    refine ⟨147250194302529120367996807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196333592403372160490662409 147250194302529120367996807)
    ·
      refine ⟨220875291453793680551995211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147250194302529120367996807 220875291453793680551995211)
      ·
        refine ⟨331312937180690520827992817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220875291453793680551995211 331312937180690520827992817)
        ·
          refine ⟨248484702885517890620994613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 331312937180690520827992817 248484702885517890620994613)
          ·
            refine ⟨23295440895517302245718245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 248484702885517890620994613 23295440895517302245718245)
            ·
              refine ⟨4367895167909494171072171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23295440895517302245718245 4367895167909494171072171)
              ·
                refine ⟨6551842751864241256608257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4367895167909494171072171 6551842751864241256608257)
                ·
                  refine ⟨4913882063898180942456193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6551842751864241256608257 4913882063898180942456193)
                  ·
                    refine ⟨3685411547923635706842145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4913882063898180942456193 3685411547923635706842145)
                    ·
                      refine ⟨2764058660942726780131609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3685411547923635706842145 2764058660942726780131609)
                      ·
                        rfl

theorem cell23_5382985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 4, 1, 2, 2, 2].length) (baseStart_5382985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5382985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5382985 prefixEnd_5382985 := by exact prefixLift 5382985
  have htrace : WordTrace (prefixWord ++ tailWord_5382985) baseStart_5382985 baseEnd_5382985 := by
    simpa [prefixWord, tailWord_5382985, baseEnd_5382985] using wordTrace_append hprefix tailTrace_5382985
  have hstable : (prefixWord ++ tailWord_5382985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5382985).length < 2 ^ (prefixWord ++ tailWord_5382985).sum := by decide
  have hdescent : baseEnd_5382985 < baseStart_5382985 := by decide
  rcases family_descends (prefixWord ++ tailWord_5382985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5382989 : List Nat := [1, 6, 1, 2, 3, 1, 1, 2, 1, 3, 2]
def baseStart_5382989 : Nat := 118140960795 + 5382989 * 2 ^ 59
def prefixEnd_5382989 : Nat := 4983230072969 + 3 ^ 40 * 5382989 * 2
def baseEnd_5382989 : Nat := 2764060714865344764481591

theorem tailTrace_5382989 : CollatzResearch.WordTrace tailWord_5382989 prefixEnd_5382989 2764060714865344764481591 := by
  unfold tailWord_5382989
  simp only [CollatzResearch.WordTrace]
  refine ⟨196333738295357669173808021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130889158863571779449205347 196333738295357669173808021)
  ·
    refine ⟨9203143982594890742522251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 196333738295357669173808021 9203143982594890742522251)
    ·
      refine ⟨13804715973892336113783377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9203143982594890742522251 13804715973892336113783377)
      ·
        refine ⟨10353536980419252085337533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13804715973892336113783377 10353536980419252085337533)
        ·
          refine ⟨3882576367657219532001575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10353536980419252085337533 3882576367657219532001575)
          ·
            refine ⟨5823864551485829298002363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3882576367657219532001575 5823864551485829298002363)
            ·
              refine ⟨8735796827228743947003545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5823864551485829298002363 8735796827228743947003545)
              ·
                refine ⟨6551847620421557960252659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8735796827228743947003545 6551847620421557960252659)
                ·
                  refine ⟨9827771430632336940378989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6551847620421557960252659 9827771430632336940378989)
                  ·
                    refine ⟨3685414286487126352642121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9827771430632336940378989 3685414286487126352642121)
                    ·
                      refine ⟨2764060714865344764481591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3685414286487126352642121 2764060714865344764481591)
                      ·
                        rfl

theorem cell23_5382989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 1, 2, 1, 3, 2].length) (baseStart_5382989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5382989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5382989 prefixEnd_5382989 := by exact prefixLift 5382989
  have htrace : WordTrace (prefixWord ++ tailWord_5382989) baseStart_5382989 baseEnd_5382989 := by
    simpa [prefixWord, tailWord_5382989, baseEnd_5382989] using wordTrace_append hprefix tailTrace_5382989
  have hstable : (prefixWord ++ tailWord_5382989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5382989).length < 2 ^ (prefixWord ++ tailWord_5382989).sum := by decide
  have hdescent : baseEnd_5382989 < baseStart_5382989 := by decide
  rcases family_descends (prefixWord ++ tailWord_5382989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5383058 : List Nat := [3, 2, 3, 2, 2, 1, 1, 1, 1, 3, 4]
def baseStart_5383058 : Nat := 118140960795 + 5383058 * 2 ^ 59
def prefixEnd_5383058 : Nat := 4983230072969 + 3 ^ 40 * 5383058 * 2
def baseEnd_5383058 : Nat := 2764096145030504994518773

theorem tailTrace_5383058 : CollatzResearch.WordTrace tailWord_5383058 prefixEnd_5383058 2764096145030504994518773 := by
  unfold tailWord_5383058
  simp only [CollatzResearch.WordTrace]
  refine ⟨49084063733026923489517457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130890836621405129305379885 49084063733026923489517457)
  ·
    refine ⟨36813047799770192617138093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49084063733026923489517457 36813047799770192617138093)
    ·
      refine ⟨13804892924913822231426785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36813047799770192617138093 13804892924913822231426785)
      ·
        refine ⟨10353669693685366673570089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13804892924913822231426785 10353669693685366673570089)
        ·
          refine ⟨7765252270264025005177567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10353669693685366673570089 7765252270264025005177567)
          ·
            refine ⟨11647878405396037507766351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7765252270264025005177567 11647878405396037507766351)
            ·
              refine ⟨17471817608094056261649527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11647878405396037507766351 17471817608094056261649527)
              ·
                refine ⟨26207726412141084392474291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17471817608094056261649527 26207726412141084392474291)
                ·
                  refine ⟨39311589618211626588711437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26207726412141084392474291 39311589618211626588711437)
                  ·
                    refine ⟨14741846106829359970766789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39311589618211626588711437 14741846106829359970766789)
                    ·
                      refine ⟨2764096145030504994518773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14741846106829359970766789 2764096145030504994518773)
                      ·
                        rfl

theorem cell23_5383058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_5383058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5383058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5383058 prefixEnd_5383058 := by exact prefixLift 5383058
  have htrace : WordTrace (prefixWord ++ tailWord_5383058) baseStart_5383058 baseEnd_5383058 := by
    simpa [prefixWord, tailWord_5383058, baseEnd_5383058] using wordTrace_append hprefix tailTrace_5383058
  have hstable : (prefixWord ++ tailWord_5383058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5383058).length < 2 ^ (prefixWord ++ tailWord_5383058).sum := by decide
  have hdescent : baseEnd_5383058 < baseStart_5383058 := by decide
  rcases family_descends (prefixWord ++ tailWord_5383058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5383061 : List Nat := [1, 3, 2, 1, 1, 5, 1, 1, 1, 4, 3]
def baseStart_5383061 : Nat := 118140960795 + 5383061 * 2 ^ 59
def prefixEnd_5383061 : Nat := 4983230072969 + 3 ^ 40 * 5383061 * 2
def baseEnd_5383061 : Nat := 2764097685472468482781259

theorem tailTrace_5383061 : CollatzResearch.WordTrace tailWord_5383061 prefixEnd_5383061 2764097685472468482781259 := by
  unfold tailWord_5383061
  simp only [CollatzResearch.WordTrace]
  refine ⟨196336364351096825470429037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130890909567397883646952691 196336364351096825470429037)
  ·
    refine ⟨73626136631661309551410889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 196336364351096825470429037 73626136631661309551410889)
    ·
      refine ⟨55219602473745982163558167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73626136631661309551410889 55219602473745982163558167)
      ·
        refine ⟨82829403710618973245337251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55219602473745982163558167 82829403710618973245337251)
        ·
          refine ⟨124244105565928459868005877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82829403710618973245337251 124244105565928459868005877)
          ·
            refine ⟨11647884896805793112625551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 124244105565928459868005877 11647884896805793112625551)
            ·
              refine ⟨17471827345208689668938327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11647884896805793112625551 17471827345208689668938327)
              ·
                refine ⟨26207741017813034503407491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17471827345208689668938327 26207741017813034503407491)
                ·
                  refine ⟨39311611526719551755111237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26207741017813034503407491 39311611526719551755111237)
                  ·
                    refine ⟨7370927161259915954083357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39311611526719551755111237 7370927161259915954083357)
                    ·
                      refine ⟨2764097685472468482781259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7370927161259915954083357 2764097685472468482781259)
                      ·
                        rfl

theorem cell23_5383061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 1, 1, 4, 3].length) (baseStart_5383061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5383061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5383061 prefixEnd_5383061 := by exact prefixLift 5383061
  have htrace : WordTrace (prefixWord ++ tailWord_5383061) baseStart_5383061 baseEnd_5383061 := by
    simpa [prefixWord, tailWord_5383061, baseEnd_5383061] using wordTrace_append hprefix tailTrace_5383061
  have hstable : (prefixWord ++ tailWord_5383061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5383061).length < 2 ^ (prefixWord ++ tailWord_5383061).sum := by decide
  have hdescent : baseEnd_5383061 < baseStart_5383061 := by decide
  rcases family_descends (prefixWord ++ tailWord_5383061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5383111 : List Nat := [1, 1, 4, 1, 1, 2, 3, 4, 1, 5]
def baseStart_5383111 : Nat := 118140960795 + 5383111 * 2 ^ 59
def prefixEnd_5383111 : Nat := 4983230072969 + 3 ^ 40 * 5383111 * 2
def baseEnd_5383111 : Nat := 921374453168397762385343

theorem tailTrace_5383111 : CollatzResearch.WordTrace tailWord_5383111 prefixEnd_5383111 921374453168397762385343 := by
  unfold tailWord_5383111
  simp only [CollatzResearch.WordTrace]
  refine ⟨196338188000915684009749187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130892125333943789339832791 196338188000915684009749187)
  ·
    refine ⟨294507282001373526014623781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196338188000915684009749187 294507282001373526014623781)
    ·
      refine ⟨55220115375257536127741959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 294507282001373526014623781 55220115375257536127741959)
      ·
        refine ⟨82830173062886304191612939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55220115375257536127741959 82830173062886304191612939)
        ·
          refine ⟨124245259594329456287419409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82830173062886304191612939 124245259594329456287419409)
          ·
            refine ⟨93183944695747092215564557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124245259594329456287419409 93183944695747092215564557)
            ·
              refine ⟨34943979260905159580836709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93183944695747092215564557 34943979260905159580836709)
              ·
                refine ⟨6551996111419717421406883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34943979260905159580836709 6551996111419717421406883)
                ·
                  refine ⟨9827994167129576132110325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6551996111419717421406883 9827994167129576132110325)
                  ·
                    refine ⟨921374453168397762385343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9827994167129576132110325 921374453168397762385343)
                    ·
                      rfl

theorem cell23_5383111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 4, 1, 5].length) (baseStart_5383111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5383111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5383111 prefixEnd_5383111 := by exact prefixLift 5383111
  have htrace : WordTrace (prefixWord ++ tailWord_5383111) baseStart_5383111 baseEnd_5383111 := by
    simpa [prefixWord, tailWord_5383111, baseEnd_5383111] using wordTrace_append hprefix tailTrace_5383111
  have hstable : (prefixWord ++ tailWord_5383111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5383111).length < 2 ^ (prefixWord ++ tailWord_5383111).sum := by decide
  have hdescent : baseEnd_5383111 < baseStart_5383111 := by decide
  rcases family_descends (prefixWord ++ tailWord_5383111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5383118 : List Nat := [4, 1, 1, 1, 2, 3, 2, 1, 1, 5, 2]
def baseStart_5383118 : Nat := 118140960795 + 5383118 * 2 ^ 59
def prefixEnd_5383118 : Nat := 4983230072969 + 3 ^ 40 * 5383118 * 2
def baseEnd_5383118 : Nat := 2764126953869774759768497

theorem tailTrace_5383118 : CollatzResearch.WordTrace tailWord_5383118 prefixEnd_5383118 2764126953869774759768497 := by
  unfold tailWord_5383118
  simp only [CollatzResearch.WordTrace]
  refine ⟨24542305413986290525656751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130892295541260216136836005 24542305413986290525656751)
  ·
    refine ⟨36813458120979435788485127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24542305413986290525656751 36813458120979435788485127)
    ·
      refine ⟨55220187181469153682727691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36813458120979435788485127 55220187181469153682727691)
      ·
        refine ⟨82830280772203730524091537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55220187181469153682727691 82830280772203730524091537)
        ·
          refine ⟨62122710579152797893068653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82830280772203730524091537 62122710579152797893068653)
          ·
            refine ⟨23296016467182299209900745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62122710579152797893068653 23296016467182299209900745)
            ·
              refine ⟨17472012350386724407425559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23296016467182299209900745 17472012350386724407425559)
              ·
                refine ⟨26208018525580086611138339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17472012350386724407425559 26208018525580086611138339)
                ·
                  refine ⟨39312027788370129916707509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26208018525580086611138339 39312027788370129916707509)
                  ·
                    refine ⟨3685502605159699679691329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39312027788370129916707509 3685502605159699679691329)
                    ·
                      refine ⟨2764126953869774759768497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3685502605159699679691329 2764126953869774759768497)
                      ·
                        rfl

theorem cell23_5383118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 1, 1, 5, 2].length) (baseStart_5383118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5383118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5383118 prefixEnd_5383118 := by exact prefixLift 5383118
  have htrace : WordTrace (prefixWord ++ tailWord_5383118) baseStart_5383118 baseEnd_5383118 := by
    simpa [prefixWord, tailWord_5383118, baseEnd_5383118] using wordTrace_append hprefix tailTrace_5383118
  have hstable : (prefixWord ++ tailWord_5383118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5383118).length < 2 ^ (prefixWord ++ tailWord_5383118).sum := by decide
  have hdescent : baseEnd_5383118 < baseStart_5383118 := by decide
  rcases family_descends (prefixWord ++ tailWord_5383118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5383135 : List Nat := [1, 1, 2, 3, 5, 1, 1, 2, 2, 3, 2]
def baseStart_5383135 : Nat := 118140960795 + 5383135 * 2 ^ 59
def prefixEnd_5383135 : Nat := 4983230072969 + 3 ^ 40 * 5383135 * 2
def baseEnd_5383135 : Nat := 2764135683040901193255919

theorem tailTrace_5383135 : CollatzResearch.WordTrace tailWord_5383135 prefixEnd_5383135 2764135683040901193255919 := by
  unfold tailWord_5383135
  simp only [CollatzResearch.WordTrace]
  refine ⟨196339063352828736108622859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130892708901885824072415239 196339063352828736108622859)
  ·
    refine ⟨294508595029243104162934289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196339063352828736108622859 294508595029243104162934289)
    ·
      refine ⟨220881446271932328122200717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 294508595029243104162934289 220881446271932328122200717)
      ·
        refine ⟨82830542351974623045825269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 220881446271932328122200717 82830542351974623045825269)
        ·
          refine ⟨7765363345497620910546119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 82830542351974623045825269 7765363345497620910546119)
          ·
            refine ⟨11648045018246431365819179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7765363345497620910546119 11648045018246431365819179)
            ·
              refine ⟨17472067527369647048728769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11648045018246431365819179 17472067527369647048728769)
              ·
                refine ⟨13104050645527235286546577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17472067527369647048728769 13104050645527235286546577)
                ·
                  refine ⟨9828037984145426464909933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13104050645527235286546577 9828037984145426464909933)
                  ·
                    refine ⟨3685514244054534924341225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9828037984145426464909933 3685514244054534924341225)
                    ·
                      refine ⟨2764135683040901193255919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3685514244054534924341225 2764135683040901193255919)
                      ·
                        rfl

theorem cell23_5383135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 2, 2, 3, 2].length) (baseStart_5383135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5383135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5383135 prefixEnd_5383135 := by exact prefixLift 5383135
  have htrace : WordTrace (prefixWord ++ tailWord_5383135) baseStart_5383135 baseEnd_5383135 := by
    simpa [prefixWord, tailWord_5383135, baseEnd_5383135] using wordTrace_append hprefix tailTrace_5383135
  have hstable : (prefixWord ++ tailWord_5383135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5383135).length < 2 ^ (prefixWord ++ tailWord_5383135).sum := by decide
  have hdescent : baseEnd_5383135 < baseStart_5383135 := by decide
  rcases family_descends (prefixWord ++ tailWord_5383135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5383151 : List Nat := [1, 1, 2, 1, 4, 3, 2, 2, 1, 1, 5]
def baseStart_5383151 : Nat := 118140960795 + 5383151 * 2 ^ 59
def prefixEnd_5383151 : Nat := 4983230072969 + 3 ^ 40 * 5383151 * 2
def baseEnd_5383151 : Nat := 2764143898731373130655845

theorem tailTrace_5383151 : CollatzResearch.WordTrace tailWord_5383151 prefixEnd_5383151 2764143898731373130655845 := by
  unfold tailWord_5383151
  simp only [CollatzResearch.WordTrace]
  refine ⟨196339646920770770841205307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130893097947180513894136871 196339646920770770841205307)
  ·
    refine ⟨294509470381156156261807961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196339646920770770841205307 294509470381156156261807961)
    ·
      refine ⟨220882102785867117196355971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 294509470381156156261807961 220882102785867117196355971)
      ·
        refine ⟨331323154178800675794533957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220882102785867117196355971 331323154178800675794533957)
        ·
          refine ⟨62123091408525126711475117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 331323154178800675794533957 62123091408525126711475117)
          ·
            refine ⟨23296159278196922516803169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62123091408525126711475117 23296159278196922516803169)
            ·
              refine ⟨17472119458647691887602377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23296159278196922516803169 17472119458647691887602377)
              ·
                refine ⟨13104089593985768915701783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17472119458647691887602377 13104089593985768915701783)
                ·
                  refine ⟨19656134390978653373552675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13104089593985768915701783 19656134390978653373552675)
                  ·
                    refine ⟨29484201586467980060329013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19656134390978653373552675 29484201586467980060329013)
                    ·
                      refine ⟨2764143898731373130655845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29484201586467980060329013 2764143898731373130655845)
                      ·
                        rfl

theorem cell23_5383151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 2, 1, 1, 5].length) (baseStart_5383151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5383151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5383151 prefixEnd_5383151 := by exact prefixLift 5383151
  have htrace : WordTrace (prefixWord ++ tailWord_5383151) baseStart_5383151 baseEnd_5383151 := by
    simpa [prefixWord, tailWord_5383151, baseEnd_5383151] using wordTrace_append hprefix tailTrace_5383151
  have hstable : (prefixWord ++ tailWord_5383151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5383151).length < 2 ^ (prefixWord ++ tailWord_5383151).sum := by decide
  have hdescent : baseEnd_5383151 < baseStart_5383151 := by decide
  rcases family_descends (prefixWord ++ tailWord_5383151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5383161 : List Nat := [1, 2, 1, 3, 1, 3, 2, 3, 1, 2, 4]
def baseStart_5383161 : Nat := 118140960795 + 5383161 * 2 ^ 59
def prefixEnd_5383161 : Nat := 4983230072969 + 3 ^ 40 * 5383161 * 2
def baseEnd_5383161 : Nat := 2764149033537918091530799

theorem tailTrace_5383161 : CollatzResearch.WordTrace tailWord_5383161 prefixEnd_5383161 2764149033537918091530799 := by
  unfold tailWord_5383161
  simp only [CollatzResearch.WordTrace]
  refine ⟨196340011650734542549069337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130893341100489695032712891 196340011650734542549069337)
  ·
    refine ⟨147255008738050906911802003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196340011650734542549069337 147255008738050906911802003)
    ·
      refine ⟨220882513107076360367703005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147255008738050906911802003 220882513107076360367703005)
      ·
        refine ⟨82830942415153635137888627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 220882513107076360367703005 82830942415153635137888627)
        ·
          refine ⟨124246413622730452706832941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82830942415153635137888627 124246413622730452706832941)
          ·
            refine ⟨46592405108523919765062353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 124246413622730452706832941 46592405108523919765062353)
            ·
              refine ⟨34944303831392939823796765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46592405108523919765062353 34944303831392939823796765)
              ·
                refine ⟨13104113936772352433923787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34944303831392939823796765 13104113936772352433923787)
                ·
                  refine ⟨19656170905158528650885681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13104113936772352433923787 19656170905158528650885681)
                  ·
                    refine ⟨14742128178868896488164261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19656170905158528650885681 14742128178868896488164261)
                    ·
                      refine ⟨2764149033537918091530799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14742128178868896488164261 2764149033537918091530799)
                      ·
                        rfl

theorem cell23_5383161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 3, 1, 2, 4].length) (baseStart_5383161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5383161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5383161 prefixEnd_5383161 := by exact prefixLift 5383161
  have htrace : WordTrace (prefixWord ++ tailWord_5383161) baseStart_5383161 baseEnd_5383161 := by
    simpa [prefixWord, tailWord_5383161, baseEnd_5383161] using wordTrace_append hprefix tailTrace_5383161
  have hstable : (prefixWord ++ tailWord_5383161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5383161).length < 2 ^ (prefixWord ++ tailWord_5383161).sum := by decide
  have hdescent : baseEnd_5383161 < baseStart_5383161 := by decide
  rcases family_descends (prefixWord ++ tailWord_5383161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5383178 : List Nat := [3, 1, 2, 2, 3, 2, 1, 2, 1, 2, 4]
def baseStart_5383178 : Nat := 118140960795 + 5383178 * 2 ^ 59
def prefixEnd_5383178 : Nat := 4983230072969 + 3 ^ 40 * 5383178 * 2
def baseEnd_5383178 : Nat := 2764157762709044525018221

theorem tailTrace_5383178 : CollatzResearch.WordTrace tailWord_5383178 prefixEnd_5383178 2764157762709044525018221 := by
  unfold tailWord_5383178
  simp only [CollatzResearch.WordTrace]
  refine ⟨49085157922918238613109547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130893754461115302968292125 49085157922918238613109547)
  ·
    refine ⟨73627736884377357919664321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49085157922918238613109547 73627736884377357919664321)
    ·
      refine ⟨55220802663283018439748241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73627736884377357919664321 55220802663283018439748241)
      ·
        refine ⟨41415601997462263829811181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55220802663283018439748241 41415601997462263829811181)
        ·
          refine ⟨15530850749048348936179193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41415601997462263829811181 15530850749048348936179193)
          ·
            refine ⟨11648138061786261702134395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15530850749048348936179193 11648138061786261702134395)
            ·
              refine ⟨17472207092679392553201593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11648138061786261702134395 17472207092679392553201593)
              ·
                refine ⟨13104155319509544414901195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17472207092679392553201593 13104155319509544414901195)
                ·
                  refine ⟨19656232979264316622351793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13104155319509544414901195 19656232979264316622351793)
                  ·
                    refine ⟨14742174734448237466763845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19656232979264316622351793 14742174734448237466763845)
                    ·
                      refine ⟨2764157762709044525018221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14742174734448237466763845 2764157762709044525018221)
                      ·
                        rfl

theorem cell23_5383178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 2, 1, 2, 4].length) (baseStart_5383178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5383178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5383178 prefixEnd_5383178 := by exact prefixLift 5383178
  have htrace : WordTrace (prefixWord ++ tailWord_5383178) baseStart_5383178 baseEnd_5383178 := by
    simpa [prefixWord, tailWord_5383178, baseEnd_5383178] using wordTrace_append hprefix tailTrace_5383178
  have hstable : (prefixWord ++ tailWord_5383178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5383178).length < 2 ^ (prefixWord ++ tailWord_5383178).sum := by decide
  have hdescent : baseEnd_5383178 < baseStart_5383178 := by decide
  rcases family_descends (prefixWord ++ tailWord_5383178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5383184 : List Nat := [2, 1, 1, 1, 1, 1, 1, 3, 3, 9]
def baseStart_5383184 : Nat := 118140960795 + 5383184 * 2 ^ 59
def prefixEnd_5383184 : Nat := 4983230072969 + 3 ^ 40 * 5383184 * 2
def baseEnd_5383184 : Nat := 921386947864323833847731

theorem tailTrace_5383184 : CollatzResearch.WordTrace tailWord_5383184 prefixEnd_5383184 921386947864323833847731 := by
  unfold tailWord_5383184
  simp only [CollatzResearch.WordTrace]
  refine ⟨98170425264825608738578303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130893900353100811651437737 98170425264825608738578303)
  ·
    refine ⟨147255637897238413107867455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98170425264825608738578303 147255637897238413107867455)
    ·
      refine ⟨220883456845857619661801183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147255637897238413107867455 220883456845857619661801183)
      ·
        refine ⟨331325185268786429492701775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220883456845857619661801183 331325185268786429492701775)
        ·
          refine ⟨496987777903179644239052663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 331325185268786429492701775 496987777903179644239052663)
          ·
            refine ⟨745481666854769466358578995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 496987777903179644239052663 745481666854769466358578995)
            ·
              refine ⟨1118222500282154199537868493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 745481666854769466358578995 1118222500282154199537868493)
              ·
                refine ⟨419333437605807824826700685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1118222500282154199537868493 419333437605807824826700685)
                ·
                  refine ⟨157250039102177934310012757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 419333437605807824826700685 157250039102177934310012757)
                  ·
                    refine ⟨921386947864323833847731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 157250039102177934310012757 921386947864323833847731)
                    ·
                      rfl

theorem cell23_5383184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 3, 9].length) (baseStart_5383184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5383184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5383184 prefixEnd_5383184 := by exact prefixLift 5383184
  have htrace : WordTrace (prefixWord ++ tailWord_5383184) baseStart_5383184 baseEnd_5383184 := by
    simpa [prefixWord, tailWord_5383184, baseEnd_5383184] using wordTrace_append hprefix tailTrace_5383184
  have hstable : (prefixWord ++ tailWord_5383184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5383184).length < 2 ^ (prefixWord ++ tailWord_5383184).sum := by decide
  have hdescent : baseEnd_5383184 < baseStart_5383184 := by decide
  rcases family_descends (prefixWord ++ tailWord_5383184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5383199 : List Nat := [1, 1, 2, 4, 1, 3, 4, 2, 1, 2, 2]
def baseStart_5383199 : Nat := 118140960795 + 5383199 * 2 ^ 59
def prefixEnd_5383199 : Nat := 4983230072969 + 3 ^ 40 * 5383199 * 2
def baseEnd_5383199 : Nat := 2764168545802788942855625

theorem tailTrace_5383199 : CollatzResearch.WordTrace tailWord_5383199 prefixEnd_5383199 2764168545802788942855625 := by
  unfold tailWord_5383199
  simp only [CollatzResearch.WordTrace]
  refine ⟨196341397624596875038952651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130894265083064583359301767 196341397624596875038952651)
  ·
    refine ⟨294512096436895312558428977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196341397624596875038952651 294512096436895312558428977)
    ·
      refine ⟨220884072327671484418821733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 294512096436895312558428977 220884072327671484418821733)
      ·
        refine ⟨41415763561438403328529075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 220884072327671484418821733 41415763561438403328529075)
        ·
          refine ⟨62123645342157604992793613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41415763561438403328529075 62123645342157604992793613)
          ·
            refine ⟨23296367003309101872297605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62123645342157604992793613 23296367003309101872297605)
            ·
              refine ⟨4368068813120456601055801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23296367003309101872297605 4368068813120456601055801)
              ·
                refine ⟨3276051609840342450791851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4368068813120456601055801 3276051609840342450791851)
                ·
                  refine ⟨4914077414760513676187777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3276051609840342450791851 4914077414760513676187777)
                  ·
                    refine ⟨3685558061070385257140833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4914077414760513676187777 3685558061070385257140833)
                    ·
                      refine ⟨2764168545802788942855625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3685558061070385257140833 2764168545802788942855625)
                      ·
                        rfl

theorem cell23_5383199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 4, 2, 1, 2, 2].length) (baseStart_5383199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5383199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5383199 prefixEnd_5383199 := by exact prefixLift 5383199
  have htrace : WordTrace (prefixWord ++ tailWord_5383199) baseStart_5383199 baseEnd_5383199 := by
    simpa [prefixWord, tailWord_5383199, baseEnd_5383199] using wordTrace_append hprefix tailTrace_5383199
  have hstable : (prefixWord ++ tailWord_5383199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5383199).length < 2 ^ (prefixWord ++ tailWord_5383199).sum := by decide
  have hdescent : baseEnd_5383199 < baseStart_5383199 := by decide
  rcases family_descends (prefixWord ++ tailWord_5383199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5383201 : List Nat := [1, 2, 3, 2, 3, 1, 1, 1, 2, 7]
def baseStart_5383201 : Nat := 118140960795 + 5383201 * 2 ^ 59
def prefixEnd_5383201 : Nat := 4983230072969 + 3 ^ 40 * 5383201 * 2
def baseEnd_5383201 : Nat := 921389857588032645010205

theorem tailTrace_5383201 : CollatzResearch.WordTrace tailWord_5383201 prefixEnd_5383201 921389857588032645010205 := by
  unfold tailWord_5383201
  simp only [CollatzResearch.WordTrace]
  refine ⟨196341470570589629380525457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130894313713726419587016971 196341470570589629380525457)
  ·
    refine ⟨147256102927942222035394093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196341470570589629380525457 147256102927942222035394093)
    ·
      refine ⟨55221038597978333263272785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147256102927942222035394093 55221038597978333263272785)
      ·
        refine ⟨41415778948483749947454589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55221038597978333263272785 41415778948483749947454589)
        ·
          refine ⟨15530917105681406230295471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41415778948483749947454589 15530917105681406230295471)
          ·
            refine ⟨23296375658522109345443207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15530917105681406230295471 23296375658522109345443207)
            ·
              refine ⟨34944563487783164018164811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23296375658522109345443207 34944563487783164018164811)
              ·
                refine ⟨52416845231674746027247217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34944563487783164018164811 52416845231674746027247217)
                ·
                  refine ⟨39312633923756059520435413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52416845231674746027247217 39312633923756059520435413)
                  ·
                    refine ⟨921389857588032645010205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39312633923756059520435413 921389857588032645010205)
                    ·
                      rfl

theorem cell23_5383201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 1, 2, 7].length) (baseStart_5383201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5383201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5383201 prefixEnd_5383201 := by exact prefixLift 5383201
  have htrace : WordTrace (prefixWord ++ tailWord_5383201) baseStart_5383201 baseEnd_5383201 := by
    simpa [prefixWord, tailWord_5383201, baseEnd_5383201] using wordTrace_append hprefix tailTrace_5383201
  have hstable : (prefixWord ++ tailWord_5383201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5383201).length < 2 ^ (prefixWord ++ tailWord_5383201).sum := by decide
  have hdescent : baseEnd_5383201 < baseStart_5383201 := by decide
  rcases family_descends (prefixWord ++ tailWord_5383201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5383221 : List Nat := [1, 3, 3, 1, 1, 1, 1, 1, 4, 3, 4]
def baseStart_5383221 : Nat := 118140960795 + 5383221 * 2 ^ 59
def prefixEnd_5383221 : Nat := 4983230072969 + 3 ^ 40 * 5383221 * 2
def baseEnd_5383221 : Nat := 2764179842377187856780523

theorem tailTrace_5383221 : CollatzResearch.WordTrace tailWord_5383221 prefixEnd_5383221 2764179842377187856780523 := by
  unfold tailWord_5383221
  simp only [CollatzResearch.WordTrace]
  refine ⟨196342200030517172796253517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130894800020344781864169011 196342200030517172796253517)
  ·
    refine ⟨73628325011443939798595069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 196342200030517172796253517 73628325011443939798595069)
    ·
      refine ⟨27610621879291477424473151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73628325011443939798595069 27610621879291477424473151)
      ·
        refine ⟨41415932818937216136709727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27610621879291477424473151 41415932818937216136709727)
        ·
          refine ⟨62123899228405824205064591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41415932818937216136709727 62123899228405824205064591)
          ·
            refine ⟨93185848842608736307596887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62123899228405824205064591 93185848842608736307596887)
            ·
              refine ⟨139778773263913104461395331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93185848842608736307596887 139778773263913104461395331)
              ·
                refine ⟨209668159895869656692092997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 139778773263913104461395331 209668159895869656692092997)
                ·
                  refine ⟨39312779980475560629767437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 209668159895869656692092997 39312779980475560629767437)
                  ·
                    refine ⟨14742292492678335236162789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39312779980475560629767437 14742292492678335236162789)
                    ·
                      refine ⟨2764179842377187856780523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14742292492678335236162789 2764179842377187856780523)
                      ·
                        rfl

theorem cell23_5383221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 4, 3, 4].length) (baseStart_5383221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5383221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5383221 prefixEnd_5383221 := by exact prefixLift 5383221
  have htrace : WordTrace (prefixWord ++ tailWord_5383221) baseStart_5383221 baseEnd_5383221 := by
    simpa [prefixWord, tailWord_5383221, baseEnd_5383221] using wordTrace_append hprefix tailTrace_5383221
  have hstable : (prefixWord ++ tailWord_5383221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5383221).length < 2 ^ (prefixWord ++ tailWord_5383221).sum := by decide
  have hdescent : baseEnd_5383221 < baseStart_5383221 := by decide
  rcases family_descends (prefixWord ++ tailWord_5383221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5383225 : List Nat := [1, 2, 1, 5, 2, 1, 2, 1, 3, 3, 2]
def baseStart_5383225 : Nat := 118140960795 + 5383225 * 2 ^ 59
def prefixEnd_5383225 : Nat := 4983230072969 + 3 ^ 40 * 5383225 * 2
def baseEnd_5383225 : Nat := 2764181896299805841130505

theorem tailTrace_5383225 : CollatzResearch.WordTrace tailWord_5383225 prefixEnd_5383225 2764181896299805841130505 := by
  unfold tailWord_5383225
  simp only [CollatzResearch.WordTrace]
  refine ⟨196342345922502681479399129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130894897281668454319599419 196342345922502681479399129)
  ·
    refine ⟨147256759441877011109549347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196342345922502681479399129 147256759441877011109549347)
    ·
      refine ⟨220885139162815516664324021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147256759441877011109549347 220885139162815516664324021)
      ·
        refine ⟨20707981796513954687280377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 220885139162815516664324021 20707981796513954687280377)
        ·
          refine ⟨15530986347385466015460283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20707981796513954687280377 15530986347385466015460283)
          ·
            refine ⟨23296479521078199023190425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15530986347385466015460283 23296479521078199023190425)
            ·
              refine ⟨17472359640808649267392819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23296479521078199023190425 17472359640808649267392819)
              ·
                refine ⟨26208539461212973901089229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17472359640808649267392819 26208539461212973901089229)
                ·
                  refine ⟨9828202297954865212908461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26208539461212973901089229 9828202297954865212908461)
                  ·
                    refine ⟨3685575861733074454840673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9828202297954865212908461 3685575861733074454840673)
                    ·
                      refine ⟨2764181896299805841130505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3685575861733074454840673 2764181896299805841130505)
                      ·
                        rfl

theorem cell23_5383225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 1, 3, 3, 2].length) (baseStart_5383225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5383225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5383225 prefixEnd_5383225 := by exact prefixLift 5383225
  have htrace : WordTrace (prefixWord ++ tailWord_5383225) baseStart_5383225 baseEnd_5383225 := by
    simpa [prefixWord, tailWord_5383225, baseEnd_5383225] using wordTrace_append hprefix tailTrace_5383225
  have hstable : (prefixWord ++ tailWord_5383225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5383225).length < 2 ^ (prefixWord ++ tailWord_5383225).sum := by decide
  have hdescent : baseEnd_5383225 < baseStart_5383225 := by decide
  rcases family_descends (prefixWord ++ tailWord_5383225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5383241 : List Nat := [1, 2, 1, 1, 2, 2, 2, 2, 1, 6, 3]
def baseStart_5383241 : Nat := 118140960795 + 5383241 * 2 ^ 59
def prefixEnd_5383241 : Nat := 4983230072969 + 3 ^ 40 * 5383241 * 2
def baseEnd_5383241 : Nat := 2764190111990277778530431

theorem tailTrace_5383241 : CollatzResearch.WordTrace tailWord_5383241 prefixEnd_5383241 2764190111990277778530431 := by
  unfold tailWord_5383241
  simp only [CollatzResearch.WordTrace]
  refine ⟨196342929490444716211981577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130895286326963144141321051 196342929490444716211981577)
  ·
    refine ⟨147257197117833537158986183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196342929490444716211981577 147257197117833537158986183)
    ·
      refine ⟨220885795676750305738479275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147257197117833537158986183 220885795676750305738479275)
      ·
        refine ⟨331328693515125458607718913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220885795676750305738479275 331328693515125458607718913)
        ·
          refine ⟨248496520136344093955789185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 331328693515125458607718913 248496520136344093955789185)
          ·
            refine ⟨186372390102258070466841889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 248496520136344093955789185 186372390102258070466841889)
            ·
              refine ⟨139779292576693552850131417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 186372390102258070466841889 139779292576693552850131417)
              ·
                refine ⟨104834469432520164637598563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 139779292576693552850131417 104834469432520164637598563)
                ·
                  refine ⟨157251704148780246956397845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 104834469432520164637598563 157251704148780246956397845)
                  ·
                    refine ⟨7371173631974074076081149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 157251704148780246956397845 7371173631974074076081149)
                    ·
                      refine ⟨2764190111990277778530431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7371173631974074076081149 2764190111990277778530431)
                      ·
                        rfl

theorem cell23_5383241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 6, 3].length) (baseStart_5383241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5383241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5383241 prefixEnd_5383241 := by exact prefixLift 5383241
  have htrace : WordTrace (prefixWord ++ tailWord_5383241) baseStart_5383241 baseEnd_5383241 := by
    simpa [prefixWord, tailWord_5383241, baseEnd_5383241] using wordTrace_append hprefix tailTrace_5383241
  have hstable : (prefixWord ++ tailWord_5383241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5383241).length < 2 ^ (prefixWord ++ tailWord_5383241).sum := by decide
  have hdescent : baseEnd_5383241 < baseStart_5383241 := by decide
  rcases family_descends (prefixWord ++ tailWord_5383241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5383242 : List Nat := [3, 1, 2, 1, 1, 2, 6, 1, 1, 3, 2]
def baseStart_5383242 : Nat := 118140960795 + 5383242 * 2 ^ 59
def prefixEnd_5383242 : Nat := 4983230072969 + 3 ^ 40 * 5383242 * 2
def baseEnd_5383242 : Nat := 2764190625470932274617927

theorem tailTrace_5383242 : CollatzResearch.WordTrace tailWord_5383242 prefixEnd_5383242 2764190625470932274617927 := by
  unfold tailWord_5383242
  simp only [CollatzResearch.WordTrace]
  refine ⟨49085741490860273345691995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130895310642294062255178653 49085741490860273345691995)
  ·
    refine ⟨73628612236290410018537993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49085741490860273345691995 73628612236290410018537993)
    ·
      refine ⟨55221459177217807513903495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73628612236290410018537993 55221459177217807513903495)
      ·
        refine ⟨82832188765826711270855243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55221459177217807513903495 82832188765826711270855243)
        ·
          refine ⟨124248283148740066906282865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82832188765826711270855243 124248283148740066906282865)
          ·
            refine ⟨93186212361555050179712149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124248283148740066906282865 93186212361555050179712149)
            ·
              refine ⟨4368103704447892977174007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 93186212361555050179712149 4368103704447892977174007)
              ·
                refine ⟨6552155556671839465761011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4368103704447892977174007 6552155556671839465761011)
                ·
                  refine ⟨9828233335007759198641517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6552155556671839465761011 9828233335007759198641517)
                  ·
                    refine ⟨3685587500627909699490569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9828233335007759198641517 3685587500627909699490569)
                    ·
                      refine ⟨2764190625470932274617927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3685587500627909699490569 2764190625470932274617927)
                      ·
                        rfl

theorem cell23_5383242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 6, 1, 1, 3, 2].length) (baseStart_5383242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5383242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5383242 prefixEnd_5383242 := by exact prefixLift 5383242
  have htrace : WordTrace (prefixWord ++ tailWord_5383242) baseStart_5383242 baseEnd_5383242 := by
    simpa [prefixWord, tailWord_5383242, baseEnd_5383242] using wordTrace_append hprefix tailTrace_5383242
  have hstable : (prefixWord ++ tailWord_5383242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5383242).length < 2 ^ (prefixWord ++ tailWord_5383242).sum := by decide
  have hdescent : baseEnd_5383242 < baseStart_5383242 := by decide
  rcases family_descends (prefixWord ++ tailWord_5383242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5383251 : List Nat := [1, 1, 1, 2, 1, 1, 2, 6, 2, 2, 4]
def baseStart_5383251 : Nat := 118140960795 + 5383251 * 2 ^ 59
def prefixEnd_5383251 : Nat := 4983230072969 + 3 ^ 40 * 5383251 * 2
def baseEnd_5383251 : Nat := 2764195246796822739405385

theorem tailTrace_5383251 : CollatzResearch.WordTrace tailWord_5383251 prefixEnd_5383251 2764195246796822739405385 := by
  unfold tailWord_5383251
  simp only [CollatzResearch.WordTrace]
  refine ⟨196343294220408487919845607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130895529480272325279897071 196343294220408487919845607)
  ·
    refine ⟨294514941330612731879768411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196343294220408487919845607 294514941330612731879768411)
    ·
      refine ⟨441772411995919097819652617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294514941330612731879768411 441772411995919097819652617)
      ·
        refine ⟨331329308996939323364739463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 441772411995919097819652617 331329308996939323364739463)
        ·
          refine ⟨496993963495408985047109195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 331329308996939323364739463 496993963495408985047109195)
          ·
            refine ⟨745490945243113477570663793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 496993963495408985047109195 745490945243113477570663793)
            ·
              refine ⟨559118208932335108177997845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 745490945243113477570663793 559118208932335108177997845)
              ·
                refine ⟨26208666043703208195843649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 559118208932335108177997845 26208666043703208195843649)
                ·
                  refine ⟨19656499532777406146882737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26208666043703208195843649 19656499532777406146882737)
                  ·
                    refine ⟨14742374649583054610162053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19656499532777406146882737 14742374649583054610162053)
                    ·
                      refine ⟨2764195246796822739405385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14742374649583054610162053 2764195246796822739405385)
                      ·
                        rfl

theorem cell23_5383251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 6, 2, 2, 4].length) (baseStart_5383251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5383251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5383251 prefixEnd_5383251 := by exact prefixLift 5383251
  have htrace : WordTrace (prefixWord ++ tailWord_5383251) baseStart_5383251 baseEnd_5383251 := by
    simpa [prefixWord, tailWord_5383251, baseEnd_5383251] using wordTrace_append hprefix tailTrace_5383251
  have hstable : (prefixWord ++ tailWord_5383251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5383251).length < 2 ^ (prefixWord ++ tailWord_5383251).sum := by decide
  have hdescent : baseEnd_5383251 < baseStart_5383251 := by decide
  rcases family_descends (prefixWord ++ tailWord_5383251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5383278 : List Nat := [4, 1, 2, 2, 1, 2, 2, 2, 7]
def baseStart_5383278 : Nat := 118140960795 + 5383278 * 2 ^ 59
def prefixEnd_5383278 : Nat := 4983230072969 + 3 ^ 40 * 5383278 * 2
def baseEnd_5383278 : Nat := 307134345641610459307529

theorem tailTrace_5383278 : CollatzResearch.WordTrace tailWord_5383278 prefixEnd_5383278 307134345641610459307529 := by
  unfold tailWord_5383278
  simp only [CollatzResearch.WordTrace]
  refine ⟨24543034873913833941384811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130896185994207114354052325 24543034873913833941384811)
  ·
    refine ⟨36814552310870750912077217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24543034873913833941384811 36814552310870750912077217)
    ·
      refine ⟨27610914233153063184057913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36814552310870750912077217 27610914233153063184057913)
      ·
        refine ⟨20708185674864797388043435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27610914233153063184057913 20708185674864797388043435)
        ·
          refine ⟨31062278512297196082065153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20708185674864797388043435 31062278512297196082065153)
          ·
            refine ⟨23296708884222897061548865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31062278512297196082065153 23296708884222897061548865)
            ·
              refine ⟨17472531663167172796161649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23296708884222897061548865 17472531663167172796161649)
              ·
                refine ⟨13104398747375379597121237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17472531663167172796161649 13104398747375379597121237)
                ·
                  refine ⟨307134345641610459307529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13104398747375379597121237 307134345641610459307529)
                  ·
                    rfl

theorem cell23_5383278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 2, 7].length) (baseStart_5383278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5383278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5383278 prefixEnd_5383278 := by exact prefixLift 5383278
  have htrace : WordTrace (prefixWord ++ tailWord_5383278) baseStart_5383278 baseEnd_5383278 := by
    simpa [prefixWord, tailWord_5383278, baseEnd_5383278] using wordTrace_append hprefix tailTrace_5383278
  have hstable : (prefixWord ++ tailWord_5383278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5383278).length < 2 ^ (prefixWord ++ tailWord_5383278).sum := by decide
  have hdescent : baseEnd_5383278 < baseStart_5383278 := by decide
  rcases family_descends (prefixWord ++ tailWord_5383278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5383291 : List Nat := [1, 1, 1, 1, 1, 4, 1, 2, 6, 5]
def baseStart_5383291 : Nat := 118140960795 + 5383291 * 2 ^ 59
def prefixEnd_5383291 : Nat := 4983230072969 + 3 ^ 40 * 5383291 * 2
def baseEnd_5383291 : Nat := 921405262007667527635067

theorem tailTrace_5383291 : CollatzResearch.WordTrace tailWord_5383291 prefixEnd_5383291 921405262007667527635067 := by
  unfold tailWord_5383291
  simp only [CollatzResearch.WordTrace]
  refine ⟨196344753140263574751301727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130896502093509049834201151 196344753140263574751301727)
  ·
    refine ⟨294517129710395362126952591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196344753140263574751301727 294517129710395362126952591)
    ·
      refine ⟨441775694565593043190428887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294517129710395362126952591 441775694565593043190428887)
      ·
        refine ⟨662663541848389564785643331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 441775694565593043190428887 662663541848389564785643331)
        ·
          refine ⟨993995312772584347178464997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 662663541848389564785643331 993995312772584347178464997)
          ·
            refine ⟨186374121144859565095962187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 993995312772584347178464997 186374121144859565095962187)
            ·
              refine ⟨279561181717289347643943281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 186374121144859565095962187 279561181717289347643943281)
              ·
                refine ⟨209670886287967010732957461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 279561181717289347643943281 209670886287967010732957461)
                ·
                  refine ⟨9828322794748453628107381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 209670886287967010732957461 9828322794748453628107381)
                  ·
                    refine ⟨921405262007667527635067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9828322794748453628107381 921405262007667527635067)
                    ·
                      rfl

theorem cell23_5383291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 6, 5].length) (baseStart_5383291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5383291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5383291 prefixEnd_5383291 := by exact prefixLift 5383291
  have htrace : WordTrace (prefixWord ++ tailWord_5383291) baseStart_5383291 baseEnd_5383291 := by
    simpa [prefixWord, tailWord_5383291, baseEnd_5383291] using wordTrace_append hprefix tailTrace_5383291
  have hstable : (prefixWord ++ tailWord_5383291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5383291).length < 2 ^ (prefixWord ++ tailWord_5383291).sum := by decide
  have hdescent : baseEnd_5383291 < baseStart_5383291 := by decide
  rcases family_descends (prefixWord ++ tailWord_5383291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5383328 : List Nat := [2, 1, 1, 4, 2, 1, 1, 2, 4, 1, 4]
def baseStart_5383328 : Nat := 118140960795 + 5383328 * 2 ^ 59
def prefixEnd_5383328 : Nat := 4983230072969 + 3 ^ 40 * 5383328 * 2
def baseEnd_5383328 : Nat := 2764234784807218938142531

theorem tailTrace_5383328 : CollatzResearch.WordTrace tailWord_5383328 prefixEnd_5383328 2764234784807218938142531 := by
  unfold tailWord_5383328
  simp only [CollatzResearch.WordTrace]
  refine ⟨98173051320564765035199319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130897401760753020046932425 98173051320564765035199319)
  ·
    refine ⟨147259576980847147552798979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98173051320564765035199319 147259576980847147552798979)
    ·
      refine ⟨220889365471270721329198469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147259576980847147552798979 220889365471270721329198469)
      ·
        refine ⟨41416756025863260249224713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 220889365471270721329198469 41416756025863260249224713)
        ·
          refine ⟨31062567019397445186918535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41416756025863260249224713 31062567019397445186918535)
          ·
            refine ⟨46593850529096167780377803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31062567019397445186918535 46593850529096167780377803)
            ·
              refine ⟨69890775793644251670566705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46593850529096167780377803 69890775793644251670566705)
              ·
                refine ⟨52418081845233188752925029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69890775793644251670566705 52418081845233188752925029)
                ·
                  refine ⟨9828390345981222891173443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52418081845233188752925029 9828390345981222891173443)
                  ·
                    refine ⟨14742585518971834336760165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9828390345981222891173443 14742585518971834336760165)
                    ·
                      refine ⟨2764234784807218938142531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14742585518971834336760165 2764234784807218938142531)
                      ·
                        rfl

theorem cell23_5383328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 4, 1, 4].length) (baseStart_5383328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5383328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5383328 prefixEnd_5383328 := by exact prefixLift 5383328
  have htrace : WordTrace (prefixWord ++ tailWord_5383328) baseStart_5383328 baseEnd_5383328 := by
    simpa [prefixWord, tailWord_5383328, baseEnd_5383328] using wordTrace_append hprefix tailTrace_5383328
  have hstable : (prefixWord ++ tailWord_5383328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5383328).length < 2 ^ (prefixWord ++ tailWord_5383328).sum := by decide
  have hdescent : baseEnd_5383328 < baseStart_5383328 := by decide
  rcases family_descends (prefixWord ++ tailWord_5383328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5383331 : List Nat := [1, 1, 1, 4, 1, 1, 1, 2, 1, 5, 5]
def baseStart_5383331 : Nat := 118140960795 + 5383331 * 2 ^ 59
def prefixEnd_5383331 : Nat := 4983230072969 + 3 ^ 40 * 5383331 * 2
def baseEnd_5383331 : Nat := 2764236325249182426405017

theorem tailTrace_5383331 : CollatzResearch.WordTrace tailWord_5383331 prefixEnd_5383331 2764236325249182426405017 := by
  unfold tailWord_5383331
  simp only [CollatzResearch.WordTrace]
  refine ⟨196346212060118661582757847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130897474706745774388505231 196346212060118661582757847)
  ·
    refine ⟨294519318090177992374136771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196346212060118661582757847 294519318090177992374136771)
    ·
      refine ⟨441778977135266988561205157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294519318090177992374136771 441778977135266988561205157)
      ·
        refine ⟨82833558212862560355225967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 441778977135266988561205157 82833558212862560355225967)
        ·
          refine ⟨124250337319293840532838951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82833558212862560355225967 124250337319293840532838951)
          ·
            refine ⟨186375505978940760799258427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124250337319293840532838951 186375505978940760799258427)
            ·
              refine ⟨279563258968411141198887641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 186375505978940760799258427 279563258968411141198887641)
              ·
                refine ⟨209672444226308355899165731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 279563258968411141198887641 209672444226308355899165731)
                ·
                  refine ⟨314508666339462533848748597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 209672444226308355899165731 314508666339462533848748597)
                  ·
                    refine ⟨29485187469324612548320181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 314508666339462533848748597 29485187469324612548320181)
                    ·
                      refine ⟨2764236325249182426405017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29485187469324612548320181 2764236325249182426405017)
                      ·
                        rfl

theorem cell23_5383331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 5, 5].length) (baseStart_5383331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5383331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5383331 prefixEnd_5383331 := by exact prefixLift 5383331
  have htrace : WordTrace (prefixWord ++ tailWord_5383331) baseStart_5383331 baseEnd_5383331 := by
    simpa [prefixWord, tailWord_5383331, baseEnd_5383331] using wordTrace_append hprefix tailTrace_5383331
  have hstable : (prefixWord ++ tailWord_5383331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5383331).length < 2 ^ (prefixWord ++ tailWord_5383331).sum := by decide
  have hdescent : baseEnd_5383331 < baseStart_5383331 := by decide
  rcases family_descends (prefixWord ++ tailWord_5383331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5383345 : List Nat := [1, 2, 2, 5, 1, 1, 1, 3, 2, 1, 4]
def baseStart_5383345 : Nat := 118140960795 + 5383345 * 2 ^ 59
def prefixEnd_5383345 : Nat := 4983230072969 + 3 ^ 40 * 5383345 * 2
def baseEnd_5383345 : Nat := 2764243513978345371629953

theorem tailTrace_5383345 : CollatzResearch.WordTrace tailWord_5383345 prefixEnd_5383345 2764243513978345371629953 := by
  unfold tailWord_5383345
  simp only [CollatzResearch.WordTrace]
  refine ⟨196346722682067941973767489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130897815121378627982511659 196346722682067941973767489)
  ·
    refine ⟨147260042011550956480325617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196346722682067941973767489 147260042011550956480325617)
    ·
      refine ⟨110445031508663217360244213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147260042011550956480325617 110445031508663217360244213)
      ·
        refine ⟨10354221703937176627522895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 110445031508663217360244213 10354221703937176627522895)
        ·
          refine ⟨15531332555905764941284343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10354221703937176627522895 15531332555905764941284343)
          ·
            refine ⟨23296998833858647411926515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15531332555905764941284343 23296998833858647411926515)
            ·
              refine ⟨34945498250787971117889773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23296998833858647411926515 34945498250787971117889773)
              ·
                refine ⟨13104561844045489169208665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34945498250787971117889773 13104561844045489169208665)
                ·
                  refine ⟨9828421383034116876906499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13104561844045489169208665 9828421383034116876906499)
                  ·
                    refine ⟨14742632074551175315359749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9828421383034116876906499 14742632074551175315359749)
                    ·
                      refine ⟨2764243513978345371629953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14742632074551175315359749 2764243513978345371629953)
                      ·
                        rfl

theorem cell23_5383345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_5383345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5383345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5383345 prefixEnd_5383345 := by exact prefixLift 5383345
  have htrace : WordTrace (prefixWord ++ tailWord_5383345) baseStart_5383345 baseEnd_5383345 := by
    simpa [prefixWord, tailWord_5383345, baseEnd_5383345] using wordTrace_append hprefix tailTrace_5383345
  have hstable : (prefixWord ++ tailWord_5383345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5383345).length < 2 ^ (prefixWord ++ tailWord_5383345).sum := by decide
  have hdescent : baseEnd_5383345 < baseStart_5383345 := by decide
  rcases family_descends (prefixWord ++ tailWord_5383345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5383368 : List Nat := [2, 1, 3, 1, 2, 1, 3, 4, 6]
def baseStart_5383368 : Nat := 118140960795 + 5383368 * 2 ^ 59
def prefixEnd_5383368 : Nat := 4983230072969 + 3 ^ 40 * 5383368 * 2
def baseEnd_5383368 : Nat := 307139480448155420182483

theorem tailTrace_5383368 : CollatzResearch.WordTrace tailWord_5383368 prefixEnd_5383368 307139480448155420182483 := by
  unfold tailWord_5383368
  simp only [CollatzResearch.WordTrace]
  refine ⟨98173780780492308450927379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130898374373989744601236505 98173780780492308450927379)
  ·
    refine ⟨147260671170738462676391069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98173780780492308450927379 147260671170738462676391069)
    ·
      refine ⟨55222751689026923503646651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147260671170738462676391069 55222751689026923503646651)
      ·
        refine ⟨82834127533540385255469977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55222751689026923503646651 82834127533540385255469977)
        ·
          refine ⟨62125595650155288941602483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82834127533540385255469977 62125595650155288941602483)
          ·
            refine ⟨93188393475232933412403725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62125595650155288941602483 93188393475232933412403725)
            ·
              refine ⟨34945647553212350029651397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93188393475232933412403725 34945647553212350029651397)
              ·
                refine ⟨6552308916227315630559637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34945647553212350029651397 6552308916227315630559637)
                ·
                  refine ⟨307139480448155420182483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6552308916227315630559637 307139480448155420182483)
                  ·
                    rfl

theorem cell23_5383368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 4, 6].length) (baseStart_5383368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5383368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5383368 prefixEnd_5383368 := by exact prefixLift 5383368
  have htrace : WordTrace (prefixWord ++ tailWord_5383368) baseStart_5383368 baseEnd_5383368 := by
    simpa [prefixWord, tailWord_5383368, baseEnd_5383368] using wordTrace_append hprefix tailTrace_5383368
  have hstable : (prefixWord ++ tailWord_5383368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5383368).length < 2 ^ (prefixWord ++ tailWord_5383368).sum := by decide
  have hdescent : baseEnd_5383368 < baseStart_5383368 := by decide
  rcases family_descends (prefixWord ++ tailWord_5383368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5383399 : List Nat := [1, 1, 5, 3, 2, 2, 1, 1, 2, 2, 3]
def baseStart_5383399 : Nat := 118140960795 + 5383399 * 2 ^ 59
def prefixEnd_5383399 : Nat := 4983230072969 + 3 ^ 40 * 5383399 * 2
def baseEnd_5383399 : Nat := 2764271241933688160354705

theorem tailTrace_5383399 : CollatzResearch.WordTrace tailWord_5383399 prefixEnd_5383399 2764271241933688160354705 := by
  unfold tailWord_5383399
  simp only [CollatzResearch.WordTrace]
  refine ⟨196348692223872309196233251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130899128149248206130822167 196348692223872309196233251)
  ·
    refine ⟨294523038335808463794349877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196348692223872309196233251 294523038335808463794349877)
    ·
      refine ⟨27611534843982043480720301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 294523038335808463794349877 27611534843982043480720301)
      ·
        refine ⟨10354325566493266305270113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27611534843982043480720301 10354325566493266305270113)
        ·
          refine ⟨7765744174869949728952585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10354325566493266305270113 7765744174869949728952585)
          ·
            refine ⟨5824308131152462296714439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7765744174869949728952585 5824308131152462296714439)
            ·
              refine ⟨8736462196728693445071659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5824308131152462296714439 8736462196728693445071659)
              ·
                refine ⟨13104693295093040167607489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8736462196728693445071659 13104693295093040167607489)
                ·
                  refine ⟨9828519971319780125705617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13104693295093040167607489 9828519971319780125705617)
                  ·
                    refine ⟨7371389978489835094279213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9828519971319780125705617 7371389978489835094279213)
                    ·
                      refine ⟨2764271241933688160354705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7371389978489835094279213 2764271241933688160354705)
                      ·
                        rfl

theorem cell23_5383399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_5383399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5383399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5383399 prefixEnd_5383399 := by exact prefixLift 5383399
  have htrace : WordTrace (prefixWord ++ tailWord_5383399) baseStart_5383399 baseEnd_5383399 := by
    simpa [prefixWord, tailWord_5383399, baseEnd_5383399] using wordTrace_append hprefix tailTrace_5383399
  have hstable : (prefixWord ++ tailWord_5383399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5383399).length < 2 ^ (prefixWord ++ tailWord_5383399).sum := by decide
  have hdescent : baseEnd_5383399 < baseStart_5383399 := by decide
  rcases family_descends (prefixWord ++ tailWord_5383399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5383469 : List Nat := [1, 5, 3, 1, 1, 1, 2, 3, 1, 1, 4]
def baseStart_5383469 : Nat := 118140960795 + 5383469 * 2 ^ 59
def prefixEnd_5383469 : Nat := 4983230072969 + 3 ^ 40 * 5383469 * 2
def baseEnd_5383469 : Nat := 2764307185579502886479383

theorem tailTrace_5383469 : CollatzResearch.WordTrace tailWord_5383469 prefixEnd_5383469 2764307185579502886479383 := by
  unfold tailWord_5383469
  simp only [CollatzResearch.WordTrace]
  refine ⟨196351245333618711151281461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130900830222412474100854307 196351245333618711151281461)
  ·
    refine ⟨18407929250026754170432637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 196351245333618711151281461 18407929250026754170432637)
    ·
      refine ⟨6902973468760032813912239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18407929250026754170432637 6902973468760032813912239)
      ·
        refine ⟨10354460203140049220868359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6902973468760032813912239 10354460203140049220868359)
        ·
          refine ⟨15531690304710073831302539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10354460203140049220868359 15531690304710073831302539)
          ·
            refine ⟨23297535457065110746953809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15531690304710073831302539 23297535457065110746953809)
            ·
              refine ⟨17473151592798833060215357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23297535457065110746953809 17473151592798833060215357)
              ·
                refine ⟨6552431847299562397580759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17473151592798833060215357 6552431847299562397580759)
                ·
                  refine ⟨9828647770949343596371139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6552431847299562397580759 9828647770949343596371139)
                  ·
                    refine ⟨14742971656424015394556709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9828647770949343596371139 14742971656424015394556709)
                    ·
                      refine ⟨2764307185579502886479383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14742971656424015394556709 2764307185579502886479383)
                      ·
                        rfl

theorem cell23_5383469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_5383469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5383469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5383469 prefixEnd_5383469 := by exact prefixLift 5383469
  have htrace : WordTrace (prefixWord ++ tailWord_5383469) baseStart_5383469 baseEnd_5383469 := by
    simpa [prefixWord, tailWord_5383469, baseEnd_5383469] using wordTrace_append hprefix tailTrace_5383469
  have hstable : (prefixWord ++ tailWord_5383469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5383469).length < 2 ^ (prefixWord ++ tailWord_5383469).sum := by decide
  have hdescent : baseEnd_5383469 < baseStart_5383469 := by decide
  rcases family_descends (prefixWord ++ tailWord_5383469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5383488 : List Nat := [2, 1, 1, 2, 2, 1, 4, 1, 2, 7]
def baseStart_5383488 : Nat := 118140960795 + 5383488 * 2 ^ 59
def prefixEnd_5383488 : Nat := 4983230072969 + 3 ^ 40 * 5383488 * 2
def baseEnd_5383488 : Nat := 921438980570646104047265

theorem tailTrace_5383488 : CollatzResearch.WordTrace tailWord_5383488 prefixEnd_5383488 921438980570646104047265 := by
  unfold tailWord_5383488
  simp only [CollatzResearch.WordTrace]
  refine ⟨98175969160274938698111559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130901292213699918264148745 98175969160274938698111559)
  ·
    refine ⟨147263953740412408047167339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98175969160274938698111559 147263953740412408047167339)
    ·
      refine ⟨220895930610618612070751009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147263953740412408047167339 220895930610618612070751009)
      ·
        refine ⟨165671947957963959053063257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 220895930610618612070751009 165671947957963959053063257)
        ·
          refine ⟨124253960968472969289797443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165671947957963959053063257 124253960968472969289797443)
          ·
            refine ⟨186380941452709453934696165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124253960968472969289797443 186380941452709453934696165)
            ·
              refine ⟨34946426522383022612755531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 186380941452709453934696165 34946426522383022612755531)
              ·
                refine ⟨52419639783574533919133297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34946426522383022612755531 52419639783574533919133297)
                ·
                  refine ⟨39314729837680900439349973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52419639783574533919133297 39314729837680900439349973)
                  ·
                    refine ⟨921438980570646104047265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39314729837680900439349973 921438980570646104047265)
                    ·
                      rfl

theorem cell23_5383488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 1, 2, 7].length) (baseStart_5383488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5383488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5383488 prefixEnd_5383488 := by exact prefixLift 5383488
  have htrace : WordTrace (prefixWord ++ tailWord_5383488) baseStart_5383488 baseEnd_5383488 := by
    simpa [prefixWord, tailWord_5383488, baseEnd_5383488] using wordTrace_append hprefix tailTrace_5383488
  have hstable : (prefixWord ++ tailWord_5383488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5383488).length < 2 ^ (prefixWord ++ tailWord_5383488).sum := by decide
  have hdescent : baseEnd_5383488 < baseStart_5383488 := by decide
  rcases family_descends (prefixWord ++ tailWord_5383488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5383492 : List Nat := [2, 3, 4, 1, 1, 2, 2, 8]
def baseStart_5383492 : Nat := 118140960795 + 5383492 * 2 ^ 59
def prefixEnd_5383492 : Nat := 4983230072969 + 3 ^ 40 * 5383492 * 2
def baseEnd_5383492 : Nat := 102382185023502085055251

theorem tailTrace_5383492 : CollatzResearch.WordTrace tailWord_5383492 prefixEnd_5383492 102382185023502085055251 := by
  unfold tailWord_5383492
  simp only [CollatzResearch.WordTrace]
  refine ⟨98176042106267693039684365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130901389475023590719579153 98176042106267693039684365)
  ·
    refine ⟨36816015789850384889881637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98176042106267693039684365 36816015789850384889881637)
    ·
      refine ⟨6903002960596947166852807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36816015789850384889881637 6903002960596947166852807)
      ·
        refine ⟨10354504440895420750279211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6903002960596947166852807 10354504440895420750279211)
        ·
          refine ⟨15531756661343131125418817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10354504440895420750279211 15531756661343131125418817)
          ·
            refine ⟨11648817496007348344064113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15531756661343131125418817 11648817496007348344064113)
            ·
              refine ⟨8736613122005511258048085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11648817496007348344064113 8736613122005511258048085)
              ·
                refine ⟨102382185023502085055251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8736613122005511258048085 102382185023502085055251)
                ·
                  rfl

theorem cell23_5383492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 2, 8].length) (baseStart_5383492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5383492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5383492 prefixEnd_5383492 := by exact prefixLift 5383492
  have htrace : WordTrace (prefixWord ++ tailWord_5383492) baseStart_5383492 baseEnd_5383492 := by
    simpa [prefixWord, tailWord_5383492, baseEnd_5383492] using wordTrace_append hprefix tailTrace_5383492
  have hstable : (prefixWord ++ tailWord_5383492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5383492).length < 2 ^ (prefixWord ++ tailWord_5383492).sum := by decide
  have hdescent : baseEnd_5383492 < baseStart_5383492 := by decide
  rcases family_descends (prefixWord ++ tailWord_5383492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5383512 : List Nat := [2, 1, 2, 2, 1, 1, 5, 1, 3, 3, 2]
def baseStart_5383512 : Nat := 118140960795 + 5383512 * 2 ^ 59
def prefixEnd_5383512 : Nat := 4983230072969 + 3 ^ 40 * 5383512 * 2
def baseEnd_5383512 : Nat := 2764329265247646218241685

theorem tailTrace_5383512 : CollatzResearch.WordTrace tailWord_5383512 prefixEnd_5383512 2764329265247646218241685 := by
  unfold tailWord_5383512
  simp only [CollatzResearch.WordTrace]
  refine ⟨98176406836231464747548395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130901875781641952996731193 98176406836231464747548395)
  ·
    refine ⟨147264610254347197121322593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98176406836231464747548395 147264610254347197121322593)
    ·
      refine ⟨110448457690760397840991945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147264610254347197121322593 110448457690760397840991945)
      ·
        refine ⟨82836343268070298380743959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110448457690760397840991945 82836343268070298380743959)
        ·
          refine ⟨124254514902105447571115939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82836343268070298380743959 124254514902105447571115939)
          ·
            refine ⟨186381772353158171356673909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124254514902105447571115939 186381772353158171356673909)
            ·
              refine ⟨17473291158108578564688179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 186381772353158171356673909 17473291158108578564688179)
              ·
                refine ⟨26209936737162867847032269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17473291158108578564688179 26209936737162867847032269)
                ·
                  refine ⟨9828726276436075442637101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26209936737162867847032269 9828726276436075442637101)
                  ·
                    refine ⟨3685772353663528290988913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9828726276436075442637101 3685772353663528290988913)
                    ·
                      refine ⟨2764329265247646218241685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3685772353663528290988913 2764329265247646218241685)
                      ·
                        rfl

theorem cell23_5383512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 1, 3, 3, 2].length) (baseStart_5383512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5383512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5383512 prefixEnd_5383512 := by exact prefixLift 5383512
  have htrace : WordTrace (prefixWord ++ tailWord_5383512) baseStart_5383512 baseEnd_5383512 := by
    simpa [prefixWord, tailWord_5383512, baseEnd_5383512] using wordTrace_append hprefix tailTrace_5383512
  have hstable : (prefixWord ++ tailWord_5383512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5383512).length < 2 ^ (prefixWord ++ tailWord_5383512).sum := by decide
  have hdescent : baseEnd_5383512 < baseStart_5383512 := by decide
  rcases family_descends (prefixWord ++ tailWord_5383512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5383545 : List Nat := [1, 2, 1, 3, 2, 1, 3, 1, 2, 4, 3]
def baseStart_5383545 : Nat := 118140960795 + 5383545 * 2 ^ 59
def prefixEnd_5383545 : Nat := 4983230072969 + 3 ^ 40 * 5383545 * 2
def baseEnd_5383545 : Nat := 2764346210109244589129033

theorem tailTrace_5383545 : CollatzResearch.WordTrace tailWord_5383545 prefixEnd_5383545 2764346210109244589129033 := by
  unfold tailWord_5383545
  simp only [CollatzResearch.WordTrace]
  refine ⟨196354017281343376131048089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130902678187562250754032059 196354017281343376131048089)
  ·
    refine ⟨147265512961007532098286067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196354017281343376131048089 147265512961007532098286067)
    ·
      refine ⟨220898269441511298147429101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147265512961007532098286067 220898269441511298147429101)
      ·
        refine ⟨82836851040566736805285913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 220898269441511298147429101 82836851040566736805285913)
        ·
          refine ⟨62127638280425052603964435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82836851040566736805285913 62127638280425052603964435)
          ·
            refine ⟨93191457420637578905946653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62127638280425052603964435 93191457420637578905946653)
            ·
              refine ⟨34946796532739092089729995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93191457420637578905946653 34946796532739092089729995)
              ·
                refine ⟨52420194799108638134594993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34946796532739092089729995 52420194799108638134594993)
                ·
                  refine ⟨39315146099331478600946245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52420194799108638134594993 39315146099331478600946245)
                  ·
                    refine ⟨7371589893624652237677421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39315146099331478600946245 7371589893624652237677421)
                    ·
                      refine ⟨2764346210109244589129033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7371589893624652237677421 2764346210109244589129033)
                      ·
                        rfl

theorem cell23_5383545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 1, 2, 4, 3].length) (baseStart_5383545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5383545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5383545 prefixEnd_5383545 := by exact prefixLift 5383545
  have htrace : WordTrace (prefixWord ++ tailWord_5383545) baseStart_5383545 baseEnd_5383545 := by
    simpa [prefixWord, tailWord_5383545, baseEnd_5383545] using wordTrace_append hprefix tailTrace_5383545
  have hstable : (prefixWord ++ tailWord_5383545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5383545).length < 2 ^ (prefixWord ++ tailWord_5383545).sum := by decide
  have hdescent : baseEnd_5383545 < baseStart_5383545 := by decide
  rcases family_descends (prefixWord ++ tailWord_5383545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5383555 : List Nat := [1, 1, 1, 3, 5, 1, 1, 1, 1, 4, 4]
def baseStart_5383555 : Nat := 118140960795 + 5383555 * 2 ^ 59
def prefixEnd_5383555 : Nat := 4983230072969 + 3 ^ 40 * 5383555 * 2
def baseEnd_5383555 : Nat := 2764351344915789550003987

theorem tailTrace_5383555 : CollatzResearch.WordTrace tailWord_5383555 prefixEnd_5383555 2764351344915789550003987 := by
  unfold tailWord_5383555
  simp only [CollatzResearch.WordTrace]
  refine ⟨196354382011307147838912119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130902921340871431892608079 196354382011307147838912119)
  ·
    refine ⟨294531573016960721758368179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196354382011307147838912119 294531573016960721758368179)
    ·
      refine ⟨441797359525441082637552269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294531573016960721758368179 441797359525441082637552269)
      ·
        refine ⟨165674009822040405989082101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 441797359525441082637552269 165674009822040405989082101)
        ·
          refine ⟨15531938420816288061476447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 165674009822040405989082101 15531938420816288061476447)
          ·
            refine ⟨23297907631224432092214671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15531938420816288061476447 23297907631224432092214671)
            ·
              refine ⟨34946861446836648138322007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23297907631224432092214671 34946861446836648138322007)
              ·
                refine ⟨52420292170254972207483011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34946861446836648138322007 52420292170254972207483011)
                ·
                  refine ⟨78630438255382458311224517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52420292170254972207483011 78630438255382458311224517)
                  ·
                    refine ⟨14743207172884210933354597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 78630438255382458311224517 14743207172884210933354597)
                    ·
                      refine ⟨2764351344915789550003987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14743207172884210933354597 2764351344915789550003987)
                      ·
                        rfl

theorem cell23_5383555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 1, 1, 4, 4].length) (baseStart_5383555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5383555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5383555 prefixEnd_5383555 := by exact prefixLift 5383555
  have htrace : WordTrace (prefixWord ++ tailWord_5383555) baseStart_5383555 baseEnd_5383555 := by
    simpa [prefixWord, tailWord_5383555, baseEnd_5383555] using wordTrace_append hprefix tailTrace_5383555
  have hstable : (prefixWord ++ tailWord_5383555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5383555).length < 2 ^ (prefixWord ++ tailWord_5383555).sum := by decide
  have hdescent : baseEnd_5383555 < baseStart_5383555 := by decide
  rcases family_descends (prefixWord ++ tailWord_5383555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5383559 : List Nat := [1, 1, 4, 2, 2, 3, 2, 1, 1, 4, 2]
def baseStart_5383559 : Nat := 118140960795 + 5383559 * 2 ^ 59
def prefixEnd_5383559 : Nat := 4983230072969 + 3 ^ 40 * 5383559 * 2
def baseEnd_5383559 : Nat := 2764353398838407534353969

theorem tailTrace_5383559 : CollatzResearch.WordTrace tailWord_5383559 prefixEnd_5383559 2764353398838407534353969 := by
  unfold tailWord_5383559
  simp only [CollatzResearch.WordTrace]
  refine ⟨196354527903292656522057731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130903018602195104348038487 196354527903292656522057731)
  ·
    refine ⟨294531791854938984783086597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196354527903292656522057731 294531791854938984783086597)
    ·
      refine ⟨55224710972801059646828737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 294531791854938984783086597 55224710972801059646828737)
      ·
        refine ⟨41418533229600794735121553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55224710972801059646828737 41418533229600794735121553)
        ·
          refine ⟨31063899922200596051341165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41418533229600794735121553 31063899922200596051341165)
          ·
            refine ⟨11648962470825223519252937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31063899922200596051341165 11648962470825223519252937)
            ·
              refine ⟨8736721853118917639439703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11648962470825223519252937 8736721853118917639439703)
              ·
                refine ⟨13105082779678376459159555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8736721853118917639439703 13105082779678376459159555)
                ·
                  refine ⟨19657624169517564688739333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13105082779678376459159555 19657624169517564688739333)
                  ·
                    refine ⟨3685804531784543379138625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19657624169517564688739333 3685804531784543379138625)
                    ·
                      refine ⟨2764353398838407534353969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3685804531784543379138625 2764353398838407534353969)
                      ·
                        rfl

theorem cell23_5383559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2, 1, 1, 4, 2].length) (baseStart_5383559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5383559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5383559 prefixEnd_5383559 := by exact prefixLift 5383559
  have htrace : WordTrace (prefixWord ++ tailWord_5383559) baseStart_5383559 baseEnd_5383559 := by
    simpa [prefixWord, tailWord_5383559, baseEnd_5383559] using wordTrace_append hprefix tailTrace_5383559
  have hstable : (prefixWord ++ tailWord_5383559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5383559).length < 2 ^ (prefixWord ++ tailWord_5383559).sum := by decide
  have hdescent : baseEnd_5383559 < baseStart_5383559 := by decide
  rcases family_descends (prefixWord ++ tailWord_5383559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5383575 : List Nat := [1, 1, 3, 3, 1, 1, 1, 1, 3, 5, 3]
def baseStart_5383575 : Nat := 118140960795 + 5383575 * 2 ^ 59
def prefixEnd_5383575 : Nat := 4983230072969 + 3 ^ 40 * 5383575 * 2
def baseEnd_5383575 : Nat := 2764361614528879471753895

theorem tailTrace_5383575 : CollatzResearch.WordTrace tailWord_5383575 prefixEnd_5383575 2764361614528879471753895 := by
  unfold tailWord_5383575
  simp only [CollatzResearch.WordTrace]
  refine ⟨196355111471234691254640179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130903407647489794169760119 196355111471234691254640179)
  ·
    refine ⟨294532667206852036881960269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196355111471234691254640179 294532667206852036881960269)
    ·
      refine ⟨110449750202569513830735101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 294532667206852036881960269 110449750202569513830735101)
      ·
        refine ⟨41418656325963567686525663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110449750202569513830735101 41418656325963567686525663)
        ·
          refine ⟨62127984488945351529788495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41418656325963567686525663 62127984488945351529788495)
          ·
            refine ⟨93191976733418027294682743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62127984488945351529788495 93191976733418027294682743)
            ·
              refine ⟨139787965100127040942024115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93191976733418027294682743 139787965100127040942024115)
              ·
                refine ⟨209681947650190561413036173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 139787965100127040942024115 209681947650190561413036173)
                ·
                  refine ⟨78630730368821460529888565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 209681947650190561413036173 78630730368821460529888565)
                  ·
                    refine ⟨7371630972077011924677053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 78630730368821460529888565 7371630972077011924677053)
                    ·
                      refine ⟨2764361614528879471753895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7371630972077011924677053 2764361614528879471753895)
                      ·
                        rfl

theorem cell23_5383575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 3, 5, 3].length) (baseStart_5383575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5383575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5383575 prefixEnd_5383575 := by exact prefixLift 5383575
  have htrace : WordTrace (prefixWord ++ tailWord_5383575) baseStart_5383575 baseEnd_5383575 := by
    simpa [prefixWord, tailWord_5383575, baseEnd_5383575] using wordTrace_append hprefix tailTrace_5383575
  have hstable : (prefixWord ++ tailWord_5383575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5383575).length < 2 ^ (prefixWord ++ tailWord_5383575).sum := by decide
  have hdescent : baseEnd_5383575 < baseStart_5383575 := by decide
  rcases family_descends (prefixWord ++ tailWord_5383575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5383580 : List Nat := [2, 2, 3, 4, 1, 2, 2, 1, 1, 3, 2]
def baseStart_5383580 : Nat := 118140960795 + 5383580 * 2 ^ 59
def prefixEnd_5383580 : Nat := 4983230072969 + 3 ^ 40 * 5383580 * 2
def baseEnd_5383580 : Nat := 2764364181932151952191373

theorem tailTrace_5383580 : CollatzResearch.WordTrace tailWord_5383580 prefixEnd_5383580 2764364181932151952191373 := by
  unfold tailWord_5383580
  simp only [CollatzResearch.WordTrace]
  refine ⟨98177646918108288554286097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130903529224144384739048129 98177646918108288554286097)
  ·
    refine ⟨73633235188581216415714573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98177646918108288554286097 73633235188581216415714573)
    ·
      refine ⟨27612463195717956155892965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73633235188581216415714573 27612463195717956155892965)
      ·
        refine ⟨5177336849197116779229931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27612463195717956155892965 5177336849197116779229931)
        ·
          refine ⟨7766005273795675168844897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5177336849197116779229931 7766005273795675168844897)
          ·
            refine ⟨5824503955346756376633673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7766005273795675168844897 5824503955346756376633673)
            ·
              refine ⟨4368377966510067282475255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5824503955346756376633673 4368377966510067282475255)
              ·
                refine ⟨6552566949765100923712883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4368377966510067282475255 6552566949765100923712883)
                ·
                  refine ⟨9828850424647651385569325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6552566949765100923712883 9828850424647651385569325)
                  ·
                    refine ⟨3685818909242869269588497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9828850424647651385569325 3685818909242869269588497)
                    ·
                      refine ⟨2764364181932151952191373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3685818909242869269588497 2764364181932151952191373)
                      ·
                        rfl

theorem cell23_5383580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_5383580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5383580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5383580 prefixEnd_5383580 := by exact prefixLift 5383580
  have htrace : WordTrace (prefixWord ++ tailWord_5383580) baseStart_5383580 baseEnd_5383580 := by
    simpa [prefixWord, tailWord_5383580, baseEnd_5383580] using wordTrace_append hprefix tailTrace_5383580
  have hstable : (prefixWord ++ tailWord_5383580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5383580).length < 2 ^ (prefixWord ++ tailWord_5383580).sum := by decide
  have hdescent : baseEnd_5383580 < baseStart_5383580 := by decide
  rcases family_descends (prefixWord ++ tailWord_5383580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5383602 : List Nat := [3, 2, 1, 1, 1, 1, 2, 3, 2, 5, 2]
def baseStart_5383602 : Nat := 118140960795 + 5383602 * 2 ^ 59
def prefixEnd_5383602 : Nat := 4983230072969 + 3 ^ 40 * 5383602 * 2
def baseEnd_5383602 : Nat := 2764375478506550866116271

theorem tailTrace_5383602 : CollatzResearch.WordTrace tailWord_5383602 prefixEnd_5383602 2764375478506550866116271 := by
  unfold tailWord_5383602
  simp only [CollatzResearch.WordTrace]
  refine ⟨49089024060534218716468265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130904064161424583243915373 49089024060534218716468265)
  ·
    refine ⟨36816768045400664037351199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49089024060534218716468265 36816768045400664037351199)
    ·
      refine ⟨55225152068100996056026799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36816768045400664037351199 55225152068100996056026799)
      ·
        refine ⟨82837728102151494084040199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55225152068100996056026799 82837728102151494084040199)
        ·
          refine ⟨124256592153227241126060299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82837728102151494084040199 124256592153227241126060299)
          ·
            refine ⟨186384888229840861689090449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124256592153227241126060299 186384888229840861689090449)
            ·
              refine ⟨139788666172380646266817837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 186384888229840861689090449 139788666172380646266817837)
              ·
                refine ⟨52420749814642742350056689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 139788666172380646266817837 52420749814642742350056689)
                ·
                  refine ⟨39315562360982056762542517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52420749814642742350056689 39315562360982056762542517)
                  ·
                    refine ⟨3685833971342067821488361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39315562360982056762542517 3685833971342067821488361)
                    ·
                      refine ⟨2764375478506550866116271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3685833971342067821488361 2764375478506550866116271)
                      ·
                        rfl

theorem cell23_5383602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 3, 2, 5, 2].length) (baseStart_5383602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5383602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5383602 prefixEnd_5383602 := by exact prefixLift 5383602
  have htrace : WordTrace (prefixWord ++ tailWord_5383602) baseStart_5383602 baseEnd_5383602 := by
    simpa [prefixWord, tailWord_5383602, baseEnd_5383602] using wordTrace_append hprefix tailTrace_5383602
  have hstable : (prefixWord ++ tailWord_5383602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5383602).length < 2 ^ (prefixWord ++ tailWord_5383602).sum := by decide
  have hdescent : baseEnd_5383602 < baseStart_5383602 := by decide
  rcases family_descends (prefixWord ++ tailWord_5383602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5383672 : List Nat := [2, 1, 2, 1, 1, 6, 1, 3, 6]
def baseStart_5383672 : Nat := 118140960795 + 5383672 * 2 ^ 59
def prefixEnd_5383672 : Nat := 4983230072969 + 3 ^ 40 * 5383672 * 2
def baseEnd_5383672 : Nat := 307156824683596176915661

theorem tailTrace_5383672 : CollatzResearch.WordTrace tailWord_5383672 prefixEnd_5383672 307156824683596176915661 := by
  unfold tailWord_5383672
  simp only [CollatzResearch.WordTrace]
  refine ⟨98179324675941638410460635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130905766234588851213947513 98179324675941638410460635)
  ·
    refine ⟨147268987013912457615690953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98179324675941638410460635 147268987013912457615690953)
    ·
      refine ⟨110451740260434343211768215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147268987013912457615690953 110451740260434343211768215)
      ·
        refine ⟨165677610390651514817652323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110451740260434343211768215 165677610390651514817652323)
        ·
          refine ⟨248516415585977272226478485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165677610390651514817652323 248516415585977272226478485)
          ·
            refine ⟨11649206980592684635616179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 248516415585977272226478485 11649206980592684635616179)
            ·
              refine ⟨17473810470889026953424269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11649206980592684635616179 17473810470889026953424269)
              ·
                refine ⟨6552678926583385107534101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17473810470889026953424269 6552678926583385107534101)
                ·
                  refine ⟨307156824683596176915661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6552678926583385107534101 307156824683596176915661)
                  ·
                    rfl

theorem cell23_5383672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 3, 6].length) (baseStart_5383672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5383672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5383672 prefixEnd_5383672 := by exact prefixLift 5383672
  have htrace : WordTrace (prefixWord ++ tailWord_5383672) baseStart_5383672 baseEnd_5383672 := by
    simpa [prefixWord, tailWord_5383672, baseEnd_5383672] using wordTrace_append hprefix tailTrace_5383672
  have hstable : (prefixWord ++ tailWord_5383672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5383672).length < 2 ^ (prefixWord ++ tailWord_5383672).sum := by decide
  have hdescent : baseEnd_5383672 < baseStart_5383672 := by decide
  rcases family_descends (prefixWord ++ tailWord_5383672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5383756 : List Nat := [2, 2, 1, 3, 1, 3, 4, 1, 1, 1, 4]
def baseStart_5383756 : Nat := 118140960795 + 5383756 * 2 ^ 59
def prefixEnd_5383756 : Nat := 4983230072969 + 3 ^ 40 * 5383756 * 2
def baseEnd_5383756 : Nat := 2764454554527343263590563

theorem tailTrace_5383756 : CollatzResearch.WordTrace tailWord_5383756 prefixEnd_5383756 2764454554527343263590563 := by
  unfold tailWord_5383756
  simp only [CollatzResearch.WordTrace]
  refine ⟨98180856541789479583489561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130907808722385972777986081 98180856541789479583489561)
  ·
    refine ⟨73635642406342109687617171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98180856541789479583489561 73635642406342109687617171)
    ·
      refine ⟨110453463609513164531425757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73635642406342109687617171 110453463609513164531425757)
      ·
        refine ⟨41420048853567436699284659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110453463609513164531425757 41420048853567436699284659)
        ·
          refine ⟨62130073280351155048926989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41420048853567436699284659 62130073280351155048926989)
          ·
            refine ⟨23298777480131683143347621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62130073280351155048926989 23298777480131683143347621)
            ·
              refine ⟨4368520777524690589377679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23298777480131683143347621 4368520777524690589377679)
              ·
                refine ⟨6552781166287035884066519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4368520777524690589377679 6552781166287035884066519)
                ·
                  refine ⟨9829171749430553826099779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6552781166287035884066519 9829171749430553826099779)
                  ·
                    refine ⟨14743757624145830739149669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9829171749430553826099779 14743757624145830739149669)
                    ·
                      refine ⟨2764454554527343263590563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14743757624145830739149669 2764454554527343263590563)
                      ·
                        rfl

theorem cell23_5383756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 4, 1, 1, 1, 4].length) (baseStart_5383756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5383756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5383756 prefixEnd_5383756 := by exact prefixLift 5383756
  have htrace : WordTrace (prefixWord ++ tailWord_5383756) baseStart_5383756 baseEnd_5383756 := by
    simpa [prefixWord, tailWord_5383756, baseEnd_5383756] using wordTrace_append hprefix tailTrace_5383756
  have hstable : (prefixWord ++ tailWord_5383756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5383756).length < 2 ^ (prefixWord ++ tailWord_5383756).sum := by decide
  have hdescent : baseEnd_5383756 < baseStart_5383756 := by decide
  rcases family_descends (prefixWord ++ tailWord_5383756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5383762 : List Nat := [3, 2, 2, 1, 2, 3, 10]
def baseStart_5383762 : Nat := 118140960795 + 5383762 * 2 ^ 59
def prefixEnd_5383762 : Nat := 4983230072969 + 3 ^ 40 * 5383762 * 2
def baseEnd_5383762 : Nat := 34129106610015681976735

theorem tailTrace_5383762 : CollatzResearch.WordTrace tailWord_5383762 prefixEnd_5383762 34129106610015681976735 := by
  unfold tailWord_5383762
  simp only [CollatzResearch.WordTrace]
  refine ⟨49090482980389305547924385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130907954614371481461131693 49090482980389305547924385)
  ·
    refine ⟨36817862235291979160943289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49090482980389305547924385 36817862235291979160943289)
    ·
      refine ⟨27613396676468984370707467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36817862235291979160943289 27613396676468984370707467)
      ·
        refine ⟨41420095014703476556061201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27613396676468984370707467 41420095014703476556061201)
        ·
          refine ⟨31065071261027607417045901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41420095014703476556061201 31065071261027607417045901)
          ·
            refine ⟨11649401722885352781392213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31065071261027607417045901 11649401722885352781392213)
            ·
              refine ⟨34129106610015681976735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 11649401722885352781392213 34129106610015681976735)
              ·
                rfl

theorem cell23_5383762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 10].length) (baseStart_5383762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5383762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5383762 prefixEnd_5383762 := by exact prefixLift 5383762
  have htrace : WordTrace (prefixWord ++ tailWord_5383762) baseStart_5383762 baseEnd_5383762 := by
    simpa [prefixWord, tailWord_5383762, baseEnd_5383762] using wordTrace_append hprefix tailTrace_5383762
  have hstable : (prefixWord ++ tailWord_5383762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5383762).length < 2 ^ (prefixWord ++ tailWord_5383762).sum := by decide
  have hdescent : baseEnd_5383762 < baseStart_5383762 := by decide
  rcases family_descends (prefixWord ++ tailWord_5383762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5383786 : List Nat := [3, 1, 3, 2, 1, 4, 1, 1, 1, 2, 4]
def baseStart_5383786 : Nat := 118140960795 + 5383786 * 2 ^ 59
def prefixEnd_5383786 : Nat := 4983230072969 + 3 ^ 40 * 5383786 * 2
def baseEnd_5383786 : Nat := 2764469958946978146215425

theorem tailTrace_5383786 : CollatzResearch.WordTrace tailWord_5383786 prefixEnd_5383786 2764469958946978146215425 := by
  unfold tailWord_5383786
  simp only [CollatzResearch.WordTrace]
  refine ⟨49090701818367568572642803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130908538182313516193714141 49090701818367568572642803)
  ·
    refine ⟨73636052727551352858964205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49090701818367568572642803 73636052727551352858964205)
    ·
      refine ⟨27613519772831757322111577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73636052727551352858964205 27613519772831757322111577)
      ·
        refine ⟨20710139829623817991583683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27613519772831757322111577 20710139829623817991583683)
        ·
          refine ⟨31065209744435726987375525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20710139829623817991583683 31065209744435726987375525)
          ·
            refine ⟨5824726827081698810132911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31065209744435726987375525 5824726827081698810132911)
            ·
              refine ⟨8737090240622548215199367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5824726827081698810132911 8737090240622548215199367)
              ·
                refine ⟨13105635360933822322799051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8737090240622548215199367 13105635360933822322799051)
                ·
                  refine ⟨19658453041400733484198577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13105635360933822322799051 19658453041400733484198577)
                  ·
                    refine ⟨14743839781050550113148933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19658453041400733484198577 14743839781050550113148933)
                    ·
                      refine ⟨2764469958946978146215425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14743839781050550113148933 2764469958946978146215425)
                      ·
                        rfl

theorem cell23_5383786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 1, 1, 1, 2, 4].length) (baseStart_5383786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5383786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5383786 prefixEnd_5383786 := by exact prefixLift 5383786
  have htrace : WordTrace (prefixWord ++ tailWord_5383786) baseStart_5383786 baseEnd_5383786 := by
    simpa [prefixWord, tailWord_5383786, baseEnd_5383786] using wordTrace_append hprefix tailTrace_5383786
  have hstable : (prefixWord ++ tailWord_5383786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5383786).length < 2 ^ (prefixWord ++ tailWord_5383786).sum := by decide
  have hdescent : baseEnd_5383786 < baseStart_5383786 := by decide
  rcases family_descends (prefixWord ++ tailWord_5383786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5383840 : List Nat := [2, 1, 1, 4, 3, 3, 2, 1, 2, 1, 3]
def baseStart_5383840 : Nat := 118140960795 + 5383840 * 2 ^ 59
def prefixEnd_5383840 : Nat := 4983230072969 + 3 ^ 40 * 5383840 * 2
def baseEnd_5383840 : Nat := 2764497686902320934940177

theorem tailTrace_5383840 : CollatzResearch.WordTrace tailWord_5383840 prefixEnd_5383840 2764497686902320934940177 := by
  unfold tailWord_5383840
  simp only [CollatzResearch.WordTrace]
  refine ⟨98182388407637320756518487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130909851210183094342024649 98182388407637320756518487)
  ·
    refine ⟨147273582611455981134777731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98182388407637320756518487 147273582611455981134777731)
    ·
      refine ⟨220910373917183971702166597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147273582611455981134777731 220910373917183971702166597)
      ·
        refine ⟨41420695109471994694156237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 220910373917183971702166597 41420695109471994694156237)
        ·
          refine ⟨15532760666051998010308589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41420695109471994694156237 15532760666051998010308589)
          ·
            refine ⟨5824785249769499253865721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15532760666051998010308589 5824785249769499253865721)
            ·
              refine ⟨4368588937327124440399291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5824785249769499253865721 4368588937327124440399291)
              ·
                refine ⟨6552883405990686660598937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4368588937327124440399291 6552883405990686660598937)
                ·
                  refine ⟨4914662554493014995449203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6552883405990686660598937 4914662554493014995449203)
                  ·
                    refine ⟨7371993831739522493173805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4914662554493014995449203 7371993831739522493173805)
                    ·
                      refine ⟨2764497686902320934940177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7371993831739522493173805 2764497686902320934940177)
                      ·
                        rfl

theorem cell23_5383840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 2, 1, 2, 1, 3].length) (baseStart_5383840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5383840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5383840 prefixEnd_5383840 := by exact prefixLift 5383840
  have htrace : WordTrace (prefixWord ++ tailWord_5383840) baseStart_5383840 baseEnd_5383840 := by
    simpa [prefixWord, tailWord_5383840, baseEnd_5383840] using wordTrace_append hprefix tailTrace_5383840
  have hstable : (prefixWord ++ tailWord_5383840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5383840).length < 2 ^ (prefixWord ++ tailWord_5383840).sum := by decide
  have hdescent : baseEnd_5383840 < baseStart_5383840 := by decide
  rcases family_descends (prefixWord ++ tailWord_5383840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5383874 : List Nat := [3, 5, 1, 2, 1, 1, 2, 2, 2, 1, 3]
def baseStart_5383874 : Nat := 118140960795 + 5383874 * 2 ^ 59
def prefixEnd_5383874 : Nat := 4983230072969 + 3 ^ 40 * 5383874 * 2
def baseEnd_5383874 : Nat := 2764515145244573801915021

theorem tailTrace_5383874 : CollatzResearch.WordTrace tailWord_5383874 prefixEnd_5383874 2764515145244573801915021 := by
  unfold tailWord_5383874
  simp only [CollatzResearch.WordTrace]
  refine ⟨49091504224287866329943669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130910677931434310213183117 49091504224287866329943669)
  ·
    refine ⟨4602328521026987468432219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 49091504224287866329943669 4602328521026987468432219)
    ·
      refine ⟨6903492781540481202648329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4602328521026987468432219 6903492781540481202648329)
      ·
        refine ⟨5177619586155360901986247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6903492781540481202648329 5177619586155360901986247)
        ·
          refine ⟨7766429379233041352979371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5177619586155360901986247 7766429379233041352979371)
          ·
            refine ⟨11649644068849562029469057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7766429379233041352979371 11649644068849562029469057)
            ·
              refine ⟨8737233051637171522101793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11649644068849562029469057 8737233051637171522101793)
              ·
                refine ⟨6552924788727878641576345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8737233051637171522101793 6552924788727878641576345)
                ·
                  refine ⟨4914693591545908981182259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6552924788727878641576345 4914693591545908981182259)
                  ·
                    refine ⟨7372040387318863471773389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4914693591545908981182259 7372040387318863471773389)
                    ·
                      refine ⟨2764515145244573801915021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7372040387318863471773389 2764515145244573801915021)
                      ·
                        rfl

theorem cell23_5383874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_5383874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5383874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5383874 prefixEnd_5383874 := by exact prefixLift 5383874
  have htrace : WordTrace (prefixWord ++ tailWord_5383874) baseStart_5383874 baseEnd_5383874 := by
    simpa [prefixWord, tailWord_5383874, baseEnd_5383874] using wordTrace_append hprefix tailTrace_5383874
  have hstable : (prefixWord ++ tailWord_5383874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5383874).length < 2 ^ (prefixWord ++ tailWord_5383874).sum := by decide
  have hdescent : baseEnd_5383874 < baseStart_5383874 := by decide
  rcases family_descends (prefixWord ++ tailWord_5383874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5383879 : List Nat := [1, 1, 4, 1, 1, 1, 4, 2, 2, 3, 3]
def baseStart_5383879 : Nat := 118140960795 + 5383879 * 2 ^ 59
def prefixEnd_5383879 : Nat := 4983230072969 + 3 ^ 40 * 5383879 * 2
def baseEnd_5383879 : Nat := 2764517712647846282352497

theorem tailTrace_5383879 : CollatzResearch.WordTrace tailWord_5383879 prefixEnd_5383879 2764517712647846282352497 := by
  unfold tailWord_5383879
  simp only [CollatzResearch.WordTrace]
  refine ⟨196366199262133351173706691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130910799508088900782471127 196366199262133351173706691)
  ·
    refine ⟨294549298893200026760560037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196366199262133351173706691 294549298893200026760560037)
    ·
      refine ⟨55227993542475005017605007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 294549298893200026760560037 55227993542475005017605007)
      ·
        refine ⟨82841990313712507526407511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55227993542475005017605007 82841990313712507526407511)
        ·
          refine ⟨124262985470568761289611267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82841990313712507526407511 124262985470568761289611267)
          ·
            refine ⟨186394478205853141934416901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124262985470568761289611267 186394478205853141934416901)
            ·
              refine ⟨34948964663597464112703169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 186394478205853141934416901 34948964663597464112703169)
              ·
                refine ⟨26211723497698098084527377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34948964663597464112703169 26211723497698098084527377)
                ·
                  refine ⟨19658792623273573563395533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26211723497698098084527377 19658792623273573563395533)
                  ·
                    refine ⟨7372047233727590086273325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19658792623273573563395533 7372047233727590086273325)
                    ·
                      refine ⟨2764517712647846282352497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7372047233727590086273325 2764517712647846282352497)
                      ·
                        rfl

theorem cell23_5383879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 2, 2, 3, 3].length) (baseStart_5383879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5383879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5383879 prefixEnd_5383879 := by exact prefixLift 5383879
  have htrace : WordTrace (prefixWord ++ tailWord_5383879) baseStart_5383879 baseEnd_5383879 := by
    simpa [prefixWord, tailWord_5383879, baseEnd_5383879] using wordTrace_append hprefix tailTrace_5383879
  have hstable : (prefixWord ++ tailWord_5383879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5383879).length < 2 ^ (prefixWord ++ tailWord_5383879).sum := by decide
  have hdescent : baseEnd_5383879 < baseStart_5383879 := by decide
  rcases family_descends (prefixWord ++ tailWord_5383879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5383886 : List Nat := [4, 1, 1, 1, 3, 1, 3, 4, 5]
def baseStart_5383886 : Nat := 118140960795 + 5383886 * 2 ^ 59
def prefixEnd_5383886 : Nat := 4983230072969 + 3 ^ 40 * 5383886 * 2
def baseEnd_5383886 : Nat := 307169034112491972773885

theorem tailTrace_5383886 : CollatzResearch.WordTrace tailWord_5383886 prefixEnd_5383886 307169034112491972773885 := by
  unfold tailWord_5383886
  simp only [CollatzResearch.WordTrace]
  refine ⟨24545806821638498921151439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130910969715405327579474341 24545806821638498921151439)
  ·
    refine ⟨36818710232457748381727159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24545806821638498921151439 36818710232457748381727159)
    ·
      refine ⟨55228065348686622572590739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36818710232457748381727159 55228065348686622572590739)
      ·
        refine ⟨82842098023029933858886109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55228065348686622572590739 82842098023029933858886109)
        ·
          refine ⟨31065786758636225197082291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82842098023029933858886109 31065786758636225197082291)
          ·
            refine ⟨46598680137954337795623437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31065786758636225197082291 46598680137954337795623437)
            ·
              refine ⟨17474505051732876673358789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46598680137954337795623437 17474505051732876673358789)
              ·
                refine ⟨3276469697199914376254773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17474505051732876673358789 3276469697199914376254773)
                ·
                  refine ⟨307169034112491972773885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3276469697199914376254773 307169034112491972773885)
                  ·
                    rfl

theorem cell23_5383886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 4, 5].length) (baseStart_5383886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5383886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5383886 prefixEnd_5383886 := by exact prefixLift 5383886
  have htrace : WordTrace (prefixWord ++ tailWord_5383886) baseStart_5383886 baseEnd_5383886 := by
    simpa [prefixWord, tailWord_5383886, baseEnd_5383886] using wordTrace_append hprefix tailTrace_5383886
  have hstable : (prefixWord ++ tailWord_5383886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5383886).length < 2 ^ (prefixWord ++ tailWord_5383886).sum := by decide
  have hdescent : baseEnd_5383886 < baseStart_5383886 := by decide
  rcases family_descends (prefixWord ++ tailWord_5383886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5383919 : List Nat := [1, 1, 2, 1, 5, 1, 3, 1, 1, 3, 4]
def baseStart_5383919 : Nat := 118140960795 + 5383919 * 2 ^ 59
def prefixEnd_5383919 : Nat := 4983230072969 + 3 ^ 40 * 5383919 * 2
def baseEnd_5383919 : Nat := 2764538251874026125852313

theorem tailTrace_5383919 : CollatzResearch.WordTrace tailWord_5383919 prefixEnd_5383919 2764538251874026125852313 := by
  unfold tailWord_5383919
  simp only [CollatzResearch.WordTrace]
  refine ⟨196367658181988438005162811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130911772121325625336775207 196367658181988438005162811)
  ·
    refine ⟨294551487272982657007744217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196367658181988438005162811 294551487272982657007744217)
    ·
      refine ⟨220913615454736992755808163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 294551487272982657007744217 220913615454736992755808163)
      ·
        refine ⟨331370423182105489133712245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220913615454736992755808163 331370423182105489133712245)
        ·
          refine ⟨31065977173322389606285523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 331370423182105489133712245 31065977173322389606285523)
          ·
            refine ⟨46598965759983584409428285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31065977173322389606285523 46598965759983584409428285)
            ·
              refine ⟨17474612159993844153535607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46598965759983584409428285 17474612159993844153535607)
              ·
                refine ⟨26211918239990766230303411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17474612159993844153535607 26211918239990766230303411)
                ·
                  refine ⟨39317877359986149345455117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26211918239990766230303411 39317877359986149345455117)
                  ·
                    refine ⟨14744204009994806004545669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39317877359986149345455117 14744204009994806004545669)
                    ·
                      refine ⟨2764538251874026125852313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14744204009994806004545669 2764538251874026125852313)
                      ·
                        rfl

theorem cell23_5383919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 1, 1, 3, 4].length) (baseStart_5383919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5383919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5383919 prefixEnd_5383919 := by exact prefixLift 5383919
  have htrace : WordTrace (prefixWord ++ tailWord_5383919) baseStart_5383919 baseEnd_5383919 := by
    simpa [prefixWord, tailWord_5383919, baseEnd_5383919] using wordTrace_append hprefix tailTrace_5383919
  have hstable : (prefixWord ++ tailWord_5383919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5383919).length < 2 ^ (prefixWord ++ tailWord_5383919).sum := by decide
  have hdescent : baseEnd_5383919 < baseStart_5383919 := by decide
  rcases family_descends (prefixWord ++ tailWord_5383919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5383946 : List Nat := [3, 1, 2, 2, 1, 3, 1, 3, 3, 4]
def baseStart_5383946 : Nat := 118140960795 + 5383946 * 2 ^ 59
def prefixEnd_5383946 : Nat := 4983230072969 + 3 ^ 40 * 5383946 * 2
def baseEnd_5383946 : Nat := 921517371950565840071563

theorem tailTrace_5383946 : CollatzResearch.WordTrace tailWord_5383946 prefixEnd_5383946 921517371950565840071563 := by
  unfold tailWord_5383946
  simp only [CollatzResearch.WordTrace]
  refine ⟨49092160738222655404098923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130912428635260414410930461 49092160738222655404098923)
  ·
    refine ⟨73638241107333983106148385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49092160738222655404098923 73638241107333983106148385)
    ·
      refine ⟨55228680830500487329611289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73638241107333983106148385 55228680830500487329611289)
      ·
        refine ⟨41421510622875365497208467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55228680830500487329611289 41421510622875365497208467)
        ·
          refine ⟨62132265934313048245812701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41421510622875365497208467 62132265934313048245812701)
          ·
            refine ⟨23299599725367393092179763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62132265934313048245812701 23299599725367393092179763)
            ·
              refine ⟨34949399588051089638269645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23299599725367393092179763 34949399588051089638269645)
              ·
                refine ⟨13106024845519158614351117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34949399588051089638269645 13106024845519158614351117)
                ·
                  refine ⟨4914759317069684480381669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13106024845519158614351117 4914759317069684480381669)
                  ·
                    refine ⟨921517371950565840071563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4914759317069684480381669 921517371950565840071563)
                    ·
                      rfl

theorem cell23_5383946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 3, 3, 4].length) (baseStart_5383946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5383946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5383946 prefixEnd_5383946 := by exact prefixLift 5383946
  have htrace : WordTrace (prefixWord ++ tailWord_5383946) baseStart_5383946 baseEnd_5383946 := by
    simpa [prefixWord, tailWord_5383946, baseEnd_5383946] using wordTrace_append hprefix tailTrace_5383946
  have hstable : (prefixWord ++ tailWord_5383946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5383946).length < 2 ^ (prefixWord ++ tailWord_5383946).sum := by decide
  have hdescent : baseEnd_5383946 < baseStart_5383946 := by decide
  rcases family_descends (prefixWord ++ tailWord_5383946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5383980 : List Nat := [2, 2, 1, 1, 1, 7, 1, 3, 1, 4]
def baseStart_5383980 : Nat := 118140960795 + 5383980 * 2 ^ 59
def prefixEnd_5383980 : Nat := 4983230072969 + 3 ^ 40 * 5383980 * 2
def baseEnd_5383980 : Nat := 921523191397983462396511

theorem tailTrace_5383980 : CollatzResearch.WordTrace tailWord_5383980 prefixEnd_5383980 921523191397983462396511 := by
  unfold tailWord_5383980
  simp only [CollatzResearch.WordTrace]
  refine ⟨98184941517383722711566697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130913255356511630282088929 98184941517383722711566697)
  ·
    refine ⟨73638706138037792033675023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98184941517383722711566697 73638706138037792033675023)
    ·
      refine ⟨110458059207056688050512535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73638706138037792033675023 110458059207056688050512535)
      ·
        refine ⟨165687088810585032075768803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110458059207056688050512535 165687088810585032075768803)
        ·
          refine ⟨248530633215877548113653205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165687088810585032075768803 248530633215877548113653205)
          ·
            refine ⟨5824936715997130033913747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 248530633215877548113653205 5824936715997130033913747)
            ·
              refine ⟨8737405073995695050870621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5824936715997130033913747 8737405073995695050870621)
              ·
                refine ⟨3276526902748385644076483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8737405073995695050870621 3276526902748385644076483)
                ·
                  refine ⟨4914790354122578466114725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3276526902748385644076483 4914790354122578466114725)
                  ·
                    refine ⟨921523191397983462396511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4914790354122578466114725 921523191397983462396511)
                    ·
                      rfl

theorem cell23_5383980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 1, 3, 1, 4].length) (baseStart_5383980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5383980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5383980 prefixEnd_5383980 := by exact prefixLift 5383980
  have htrace : WordTrace (prefixWord ++ tailWord_5383980) baseStart_5383980 baseEnd_5383980 := by
    simpa [prefixWord, tailWord_5383980, baseEnd_5383980] using wordTrace_append hprefix tailTrace_5383980
  have hstable : (prefixWord ++ tailWord_5383980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5383980).length < 2 ^ (prefixWord ++ tailWord_5383980).sum := by decide
  have hdescent : baseEnd_5383980 < baseStart_5383980 := by decide
  rcases family_descends (prefixWord ++ tailWord_5383980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5383990 : List Nat := [5, 1, 2, 2, 1, 2, 1, 2, 2, 2, 3]
def baseStart_5383990 : Nat := 118140960795 + 5383990 * 2 ^ 59
def prefixEnd_5383990 : Nat := 4983230072969 + 3 ^ 40 * 5383990 * 2
def baseEnd_5383990 : Nat := 2764574709000495348064487

theorem tailTrace_5383990 : CollatzResearch.WordTrace tailWord_5383990 prefixEnd_5383990 2764574709000495348064487 := by
  unfold tailWord_5383990
  simp only [CollatzResearch.WordTrace]
  refine ⟨12273140485295701070687339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 130913498509820811420664949 12273140485295701070687339)
  ·
    refine ⟨18409710727943551606031009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12273140485295701070687339 18409710727943551606031009)
    ·
      refine ⟨13807283045957663704523257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18409710727943551606031009 13807283045957663704523257)
      ·
        refine ⟨10355462284468247778392443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13807283045957663704523257 10355462284468247778392443)
        ·
          refine ⟨15533193426702371667588665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10355462284468247778392443 15533193426702371667588665)
          ·
            refine ⟨11649895070026778750691499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15533193426702371667588665 11649895070026778750691499)
            ·
              refine ⟨17474842605040168126037249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11649895070026778750691499 17474842605040168126037249)
              ·
                refine ⟨13106131953780126094527937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17474842605040168126037249 13106131953780126094527937)
                ·
                  refine ⟨9829598965335094570895953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13106131953780126094527937 9829598965335094570895953)
                  ·
                    refine ⟨7372199224001320928171965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9829598965335094570895953 7372199224001320928171965)
                    ·
                      refine ⟨2764574709000495348064487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7372199224001320928171965 2764574709000495348064487)
                      ·
                        rfl

theorem cell23_5383990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_5383990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5383990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5383990 prefixEnd_5383990 := by exact prefixLift 5383990
  have htrace : WordTrace (prefixWord ++ tailWord_5383990) baseStart_5383990 baseEnd_5383990 := by
    simpa [prefixWord, tailWord_5383990, baseEnd_5383990] using wordTrace_append hprefix tailTrace_5383990
  have hstable : (prefixWord ++ tailWord_5383990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5383990).length < 2 ^ (prefixWord ++ tailWord_5383990).sum := by decide
  have hdescent : baseEnd_5383990 < baseStart_5383990 := by decide
  rcases family_descends (prefixWord ++ tailWord_5383990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5383997 : List Nat := [1, 4, 1, 4, 1, 2, 3, 2, 1, 4]
def baseStart_5383997 : Nat := 118140960795 + 5383997 * 2 ^ 59
def prefixEnd_5383997 : Nat := 4983230072969 + 3 ^ 40 * 5383997 * 2
def baseEnd_5383997 : Nat := 921526101121692273558985

theorem tailTrace_5383997 : CollatzResearch.WordTrace tailWord_5383997 prefixEnd_5383997 921526101121692273558985 := by
  unfold tailWord_5383997
  simp only [CollatzResearch.WordTrace]
  refine ⟨196370503075705857326502245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130913668717137238217668163 196370503075705857326502245)
  ·
    refine ⟨36819469326694848248719171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 196370503075705857326502245 36819469326694848248719171)
    ·
      refine ⟨55229203990042272373078757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36819469326694848248719171 55229203990042272373078757)
      ·
        refine ⟨10355475748132926069952267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55229203990042272373078757 10355475748132926069952267)
        ·
          refine ⟨15533213622199389104928401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10355475748132926069952267 15533213622199389104928401)
          ·
            refine ⟨11649910216649541828696301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15533213622199389104928401 11649910216649541828696301)
            ·
              refine ⟨4368716331243578185761113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11649910216649541828696301 4368716331243578185761113)
              ·
                refine ⟨3276537248432683639320835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4368716331243578185761113 3276537248432683639320835)
                ·
                  refine ⟨4914805872649025458981253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3276537248432683639320835 4914805872649025458981253)
                  ·
                    refine ⟨921526101121692273558985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4914805872649025458981253 921526101121692273558985)
                    ·
                      rfl

theorem cell23_5383997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 3, 2, 1, 4].length) (baseStart_5383997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5383997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5383997 prefixEnd_5383997 := by exact prefixLift 5383997
  have htrace : WordTrace (prefixWord ++ tailWord_5383997) baseStart_5383997 baseEnd_5383997 := by
    simpa [prefixWord, tailWord_5383997, baseEnd_5383997] using wordTrace_append hprefix tailTrace_5383997
  have hstable : (prefixWord ++ tailWord_5383997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5383997).length < 2 ^ (prefixWord ++ tailWord_5383997).sum := by decide
  have hdescent : baseEnd_5383997 < baseStart_5383997 := by decide
  rcases family_descends (prefixWord ++ tailWord_5383997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5384003 : List Nat := [1, 1, 1, 3, 1, 5, 3, 1, 3, 1, 3]
def baseStart_5384003 : Nat := 118140960795 + 5384003 * 2 ^ 59
def prefixEnd_5384003 : Nat := 4983230072969 + 3 ^ 40 * 5384003 * 2
def baseEnd_5384003 : Nat := 2764581384249003797201927

theorem tailTrace_5384003 : CollatzResearch.WordTrace tailWord_5384003 prefixEnd_5384003 2764581384249003797201927 := by
  unfold tailWord_5384003
  simp only [CollatzResearch.WordTrace]
  refine ⟨196370721913684120351220663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130913814609122746900813775 196370721913684120351220663)
  ·
    refine ⟨294556082870526180526830995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196370721913684120351220663 294556082870526180526830995)
    ·
      refine ⟨441834124305789270790246493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294556082870526180526830995 441834124305789270790246493)
      ·
        refine ⟨165687796614670976546342435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 441834124305789270790246493 165687796614670976546342435)
        ·
          refine ⟨248531694922006464819513653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165687796614670976546342435 248531694922006464819513653)
          ·
            refine ⟨23299846398938106076829405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 248531694922006464819513653 23299846398938106076829405)
            ·
              refine ⟨8737442399601789778811027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23299846398938106076829405 8737442399601789778811027)
              ·
                refine ⟨13106163599402684668216541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8737442399601789778811027 13106163599402684668216541)
                ·
                  refine ⟨4914811349776006750581203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13106163599402684668216541 4914811349776006750581203)
                  ·
                    refine ⟨7372217024664010125871805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4914811349776006750581203 7372217024664010125871805)
                    ·
                      refine ⟨2764581384249003797201927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7372217024664010125871805 2764581384249003797201927)
                      ·
                        rfl

theorem cell23_5384003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3, 1, 3, 1, 3].length) (baseStart_5384003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5384003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5384003 prefixEnd_5384003 := by exact prefixLift 5384003
  have htrace : WordTrace (prefixWord ++ tailWord_5384003) baseStart_5384003 baseEnd_5384003 := by
    simpa [prefixWord, tailWord_5384003, baseEnd_5384003] using wordTrace_append hprefix tailTrace_5384003
  have hstable : (prefixWord ++ tailWord_5384003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5384003).length < 2 ^ (prefixWord ++ tailWord_5384003).sum := by decide
  have hdescent : baseEnd_5384003 < baseStart_5384003 := by decide
  rcases family_descends (prefixWord ++ tailWord_5384003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5384026 : List Nat := [3, 1, 1, 2, 1, 3, 3, 1, 3, 1, 4]
def baseStart_5384026 : Nat := 118140960795 + 5384026 * 2 ^ 59
def prefixEnd_5384026 : Nat := 4983230072969 + 3 ^ 40 * 5384026 * 2
def baseEnd_5384026 : Nat := 2764593194304057207214321

theorem tailTrace_5384026 : CollatzResearch.WordTrace tailWord_5384026 prefixEnd_5384026 2764593194304057207214321 := by
  unfold tailWord_5384026
  simp only [CollatzResearch.WordTrace]
  refine ⟨49092890198150198819826983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130914373861733863519538621 49092890198150198819826983)
  ·
    refine ⟨73639335297225298229740475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49092890198150198819826983 73639335297225298229740475)
    ·
      refine ⟨110459002945837947344610713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73639335297225298229740475 110459002945837947344610713)
      ·
        refine ⟨82844252209378460508458035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110459002945837947344610713 82844252209378460508458035)
        ·
          refine ⟨124266378314067690762687053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82844252209378460508458035 124266378314067690762687053)
          ·
            refine ⟨46599891867775384036007645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 124266378314067690762687053 46599891867775384036007645)
            ·
              refine ⟨17474959450415769013502867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46599891867775384036007645 17474959450415769013502867)
              ·
                refine ⟨26212439175623653520254301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17474959450415769013502867 26212439175623653520254301)
                ·
                  refine ⟨9829664690858870070095363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26212439175623653520254301 9829664690858870070095363)
                  ·
                    refine ⟨14744497036288305105143045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9829664690858870070095363 14744497036288305105143045)
                    ·
                      refine ⟨2764593194304057207214321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14744497036288305105143045 2764593194304057207214321)
                      ·
                        rfl

theorem cell23_5384026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 1, 3, 1, 4].length) (baseStart_5384026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5384026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5384026 prefixEnd_5384026 := by exact prefixLift 5384026
  have htrace : WordTrace (prefixWord ++ tailWord_5384026) baseStart_5384026 baseEnd_5384026 := by
    simpa [prefixWord, tailWord_5384026, baseEnd_5384026] using wordTrace_append hprefix tailTrace_5384026
  have hstable : (prefixWord ++ tailWord_5384026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5384026).length < 2 ^ (prefixWord ++ tailWord_5384026).sum := by decide
  have hdescent : baseEnd_5384026 < baseStart_5384026 := by decide
  rcases family_descends (prefixWord ++ tailWord_5384026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5384054 : List Nat := [5, 1, 1, 3, 2, 1, 1, 4, 1, 1, 3]
def baseStart_5384054 : Nat := 118140960795 + 5384054 * 2 ^ 59
def prefixEnd_5384054 : Nat := 4983230072969 + 3 ^ 40 * 5384054 * 2
def baseEnd_5384054 : Nat := 2764607571762383097664193

theorem tailTrace_5384054 : CollatzResearch.WordTrace tailWord_5384054 prefixEnd_5384054 2764607571762383097664193 := by
  unfold tailWord_5384054
  simp only [CollatzResearch.WordTrace]
  refine ⟨12273286377281209753832951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 130915054690999570707551477 12273286377281209753832951)
  ·
    refine ⟨18409929565921814630749427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12273286377281209753832951 18409929565921814630749427)
    ·
      refine ⟨27614894348882721946124141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18409929565921814630749427 27614894348882721946124141)
      ·
        refine ⟨10355585380831020729796553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27614894348882721946124141 10355585380831020729796553)
        ·
          refine ⟨7766689035623265547347415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10355585380831020729796553 7766689035623265547347415)
          ·
            refine ⟨11650033553434898321021123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7766689035623265547347415 11650033553434898321021123)
            ·
              refine ⟨17475050330152347481531685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11650033553434898321021123 17475050330152347481531685)
              ·
                refine ⟨3276571936903565152787191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17475050330152347481531685 3276571936903565152787191)
                ·
                  refine ⟨4914857905355347729180787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3276571936903565152787191 4914857905355347729180787)
                  ·
                    refine ⟨7372286858033021593771181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4914857905355347729180787 7372286858033021593771181)
                    ·
                      refine ⟨2764607571762383097664193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7372286858033021593771181 2764607571762383097664193)
                      ·
                        rfl

theorem cell23_5384054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 4, 1, 1, 3].length) (baseStart_5384054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5384054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5384054 prefixEnd_5384054 := by exact prefixLift 5384054
  have htrace : WordTrace (prefixWord ++ tailWord_5384054) baseStart_5384054 baseEnd_5384054 := by
    simpa [prefixWord, tailWord_5384054, baseEnd_5384054] using wordTrace_append hprefix tailTrace_5384054
  have hstable : (prefixWord ++ tailWord_5384054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5384054).length < 2 ^ (prefixWord ++ tailWord_5384054).sum := by decide
  have hdescent : baseEnd_5384054 < baseStart_5384054 := by decide
  rcases family_descends (prefixWord ++ tailWord_5384054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5384093 : List Nat := [1, 4, 2, 1, 2, 2, 2, 2, 1, 3, 3]
def baseStart_5384093 : Nat := 118140960795 + 5384093 * 2 ^ 59
def prefixEnd_5384093 : Nat := 4983230072969 + 3 ^ 40 * 5384093 * 2
def baseEnd_5384093 : Nat := 2764627597507908445076513

theorem tailTrace_5384093 : CollatzResearch.WordTrace tailWord_5384093 prefixEnd_5384093 2764627597507908445076513 := by
  unfold tailWord_5384093
  simp only [CollatzResearch.WordTrace]
  refine ⟨196374004483358065721996933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130916002988905377147997955 196374004483358065721996933)
  ·
    refine ⟨36820125840629637322874425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 196374004483358065721996933 36820125840629637322874425)
    ·
      refine ⟨27615094380472227992155819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36820125840629637322874425 27615094380472227992155819)
      ·
        refine ⟨41422641570708341988233729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27615094380472227992155819 41422641570708341988233729)
        ·
          refine ⟨31066981178031256491175297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41422641570708341988233729 31066981178031256491175297)
          ·
            refine ⟨23300235883523442368381473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31066981178031256491175297 23300235883523442368381473)
            ·
              refine ⟨17475176912642581776286105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23300235883523442368381473 17475176912642581776286105)
              ·
                refine ⟨13106382684481936332214579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17475176912642581776286105 13106382684481936332214579)
                ·
                  refine ⟨19659574026722904498321869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13106382684481936332214579 19659574026722904498321869)
                  ·
                    refine ⟨7372340260021089186870701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19659574026722904498321869 7372340260021089186870701)
                    ·
                      refine ⟨2764627597507908445076513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7372340260021089186870701 2764627597507908445076513)
                      ·
                        rfl

theorem cell23_5384093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 2, 1, 3, 3].length) (baseStart_5384093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5384093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5384093 prefixEnd_5384093 := by exact prefixLift 5384093
  have htrace : WordTrace (prefixWord ++ tailWord_5384093) baseStart_5384093 baseEnd_5384093 := by
    simpa [prefixWord, tailWord_5384093, baseEnd_5384093] using wordTrace_append hprefix tailTrace_5384093
  have hstable : (prefixWord ++ tailWord_5384093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5384093).length < 2 ^ (prefixWord ++ tailWord_5384093).sum := by decide
  have hdescent : baseEnd_5384093 < baseStart_5384093 := by decide
  rcases family_descends (prefixWord ++ tailWord_5384093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5384104 : List Nat := [2, 1, 6, 2, 1, 2, 1, 2, 2, 4]
def baseStart_5384104 : Nat := 118140960795 + 5384104 * 2 ^ 59
def prefixEnd_5384104 : Nat := 4983230072969 + 3 ^ 40 * 5384104 * 2
def baseEnd_5384104 : Nat := 921544415265035967346321

theorem tailTrace_5384104 : CollatzResearch.WordTrace tailWord_5384104 prefixEnd_5384104 921544415265035967346321 := by
  unfold tailWord_5384104
  simp only [CollatzResearch.WordTrace]
  refine ⟨98187202843159107300323683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130916270457545476400431577 98187202843159107300323683)
  ·
    refine ⟨147280804264738660950485525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98187202843159107300323683 147280804264738660950485525)
    ·
      refine ⟨6903787699909624732054009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 147280804264738660950485525 6903787699909624732054009)
      ·
        refine ⟨5177840774932218549040507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6903787699909624732054009 5177840774932218549040507)
        ·
          refine ⟨7766761162398327823560761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5177840774932218549040507 7766761162398327823560761)
          ·
            refine ⟨5825070871798745867670571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7766761162398327823560761 5825070871798745867670571)
            ·
              refine ⟨8737606307698118801505857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5825070871798745867670571 8737606307698118801505857)
              ·
                refine ⟨6553204730773589101129393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8737606307698118801505857 6553204730773589101129393)
                ·
                  refine ⟨4914903548080191825847045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6553204730773589101129393 4914903548080191825847045)
                  ·
                    refine ⟨921544415265035967346321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4914903548080191825847045 921544415265035967346321)
                    ·
                      rfl

theorem cell23_5384104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_5384104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5384104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5384104 prefixEnd_5384104 := by exact prefixLift 5384104
  have htrace : WordTrace (prefixWord ++ tailWord_5384104) baseStart_5384104 baseEnd_5384104 := by
    simpa [prefixWord, tailWord_5384104, baseEnd_5384104] using wordTrace_append hprefix tailTrace_5384104
  have hstable : (prefixWord ++ tailWord_5384104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5384104).length < 2 ^ (prefixWord ++ tailWord_5384104).sum := by decide
  have hdescent : baseEnd_5384104 < baseStart_5384104 := by decide
  rcases family_descends (prefixWord ++ tailWord_5384104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5384133 : List Nat := [1, 3, 1, 1, 1, 1, 1, 7, 1, 4, 2]
def baseStart_5384133 : Nat := 118140960795 + 5384133 * 2 ^ 59
def prefixEnd_5384133 : Nat := 4983230072969 + 3 ^ 40 * 5384133 * 2
def baseEnd_5384133 : Nat := 2764648136734088288576329

theorem tailTrace_5384133 : CollatzResearch.WordTrace tailWord_5384133 prefixEnd_5384133 2764648136734088288576329 := by
  unfold tailWord_5384133
  simp only [CollatzResearch.WordTrace]
  refine ⟨196375463403213152553453053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130916975602142101702302035 196375463403213152553453053)
  ·
    refine ⟨73640798776204932207544895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 196375463403213152553453053 73640798776204932207544895)
    ·
      refine ⟨110461198164307398311317343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73640798776204932207544895 110461198164307398311317343)
      ·
        refine ⟨165691797246461097466976015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110461198164307398311317343 165691797246461097466976015)
        ·
          refine ⟨248537695869691646200464023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165691797246461097466976015 248537695869691646200464023)
          ·
            refine ⟨372806543804537469300696035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 248537695869691646200464023 372806543804537469300696035)
            ·
              refine ⟨559209815706806203951044053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 372806543804537469300696035 559209815706806203951044053)
              ·
                refine ⟨13106480055628270405102595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 559209815706806203951044053 13106480055628270405102595)
                ·
                  refine ⟨19659720083442405607653893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13106480055628270405102595 19659720083442405607653893)
                  ·
                    refine ⟨3686197515645451051435105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19659720083442405607653893 3686197515645451051435105)
                    ·
                      refine ⟨2764648136734088288576329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3686197515645451051435105 2764648136734088288576329)
                      ·
                        rfl

theorem cell23_5384133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 7, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 7, 1, 4, 2].length) (baseStart_5384133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5384133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5384133 prefixEnd_5384133 := by exact prefixLift 5384133
  have htrace : WordTrace (prefixWord ++ tailWord_5384133) baseStart_5384133 baseEnd_5384133 := by
    simpa [prefixWord, tailWord_5384133, baseEnd_5384133] using wordTrace_append hprefix tailTrace_5384133
  have hstable : (prefixWord ++ tailWord_5384133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5384133).length < 2 ^ (prefixWord ++ tailWord_5384133).sum := by decide
  have hdescent : baseEnd_5384133 < baseStart_5384133 := by decide
  rcases family_descends (prefixWord ++ tailWord_5384133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5384153 : List Nat := [1, 2, 1, 2, 6, 1, 1, 1, 2, 1, 5]
def baseStart_5384153 : Nat := 118140960795 + 5384153 * 2 ^ 59
def prefixEnd_5384153 : Nat := 4983230072969 + 3 ^ 40 * 5384153 * 2
def baseEnd_5384153 : Nat := 2764658406347178210326237

theorem tailTrace_5384153 : CollatzResearch.WordTrace tailWord_5384153 prefixEnd_5384153 2764658406347178210326237 := by
  unfold tailWord_5384153
  simp only [CollatzResearch.WordTrace]
  refine ⟨196376192863140695969181113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130917461908760463979454075 196376192863140695969181113)
  ·
    refine ⟨147282144647355521976885835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196376192863140695969181113 147282144647355521976885835)
    ·
      refine ⟨220923216971033282965328753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147282144647355521976885835 220923216971033282965328753)
      ·
        refine ⟨165692412728274962223996565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 220923216971033282965328753 165692412728274962223996565)
        ·
          refine ⟨7766831846637888854249839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 165692412728274962223996565 7766831846637888854249839)
          ·
            refine ⟨11650247769956833281374759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7766831846637888854249839 11650247769956833281374759)
            ·
              refine ⟨17475371654935249922062139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11650247769956833281374759 17475371654935249922062139)
              ·
                refine ⟨26213057482402874883093209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17475371654935249922062139 26213057482402874883093209)
                ·
                  refine ⟨19659793111802156162319907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26213057482402874883093209 19659793111802156162319907)
                  ·
                    refine ⟨29489689667703234243479861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19659793111802156162319907 29489689667703234243479861)
                    ·
                      refine ⟨2764658406347178210326237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29489689667703234243479861 2764658406347178210326237)
                      ·
                        rfl

theorem cell23_5384153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 1, 2, 1, 5].length) (baseStart_5384153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5384153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5384153 prefixEnd_5384153 := by exact prefixLift 5384153
  have htrace : WordTrace (prefixWord ++ tailWord_5384153) baseStart_5384153 baseEnd_5384153 := by
    simpa [prefixWord, tailWord_5384153, baseEnd_5384153] using wordTrace_append hprefix tailTrace_5384153
  have hstable : (prefixWord ++ tailWord_5384153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5384153).length < 2 ^ (prefixWord ++ tailWord_5384153).sum := by decide
  have hdescent : baseEnd_5384153 < baseStart_5384153 := by decide
  rcases family_descends (prefixWord ++ tailWord_5384153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5384203 : List Nat := [1, 1, 1, 1, 6, 1, 4, 1, 2, 5]
def baseStart_5384203 : Nat := 118140960795 + 5384203 * 2 ^ 59
def prefixEnd_5384203 : Nat := 4983230072969 + 3 ^ 40 * 5384203 * 2
def baseEnd_5384203 : Nat := 921561360126634338233669

theorem tailTrace_5384203 : CollatzResearch.WordTrace tailWord_5384203 prefixEnd_5384203 921561360126634338233669 := by
  unfold tailWord_5384203
  simp only [CollatzResearch.WordTrace]
  refine ⟨196378016512959554508501263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130918677675306369672334175 196378016512959554508501263)
  ·
    refine ⟨294567024769439331762751895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196378016512959554508501263 294567024769439331762751895)
    ·
      refine ⟨441850537154158997644127843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294567024769439331762751895 441850537154158997644127843)
      ·
        refine ⟨662775805731238496466191765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 441850537154158997644127843 662775805731238496466191765)
        ·
          refine ⟨31067615893651804521852739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 662775805731238496466191765 31067615893651804521852739)
          ·
            refine ⟨46601423840477706782779109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31067615893651804521852739 46601423840477706782779109)
            ·
              refine ⟨8737766970089570021771083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46601423840477706782779109 8737766970089570021771083)
              ·
                refine ⟨13106650455134355032656625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8737766970089570021771083 13106650455134355032656625)
                ·
                  refine ⟨9829987841350766274492469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13106650455134355032656625 9829987841350766274492469)
                  ·
                    refine ⟨921561360126634338233669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9829987841350766274492469 921561360126634338233669)
                    ·
                      rfl

theorem cell23_5384203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4, 1, 2, 5].length) (baseStart_5384203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5384203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5384203 prefixEnd_5384203 := by exact prefixLift 5384203
  have htrace : WordTrace (prefixWord ++ tailWord_5384203) baseStart_5384203 baseEnd_5384203 := by
    simpa [prefixWord, tailWord_5384203, baseEnd_5384203] using wordTrace_append hprefix tailTrace_5384203
  have hstable : (prefixWord ++ tailWord_5384203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5384203).length < 2 ^ (prefixWord ++ tailWord_5384203).sum := by decide
  have hdescent : baseEnd_5384203 < baseStart_5384203 := by decide
  rcases family_descends (prefixWord ++ tailWord_5384203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5384223 : List Nat := [1, 1, 2, 4, 1, 2, 1, 4, 2, 1, 4]
def baseStart_5384223 : Nat := 118140960795 + 5384223 * 2 ^ 59
def prefixEnd_5384223 : Nat := 4983230072969 + 3 ^ 40 * 5384223 * 2
def baseEnd_5384223 : Nat := 2764694349992992936450915

theorem tailTrace_5384223 : CollatzResearch.WordTrace tailWord_5384223 prefixEnd_5384223 2764694349992992936450915 := by
  unfold tailWord_5384223
  simp only [CollatzResearch.WordTrace]
  refine ⟨196378745972887097924229323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130919163981924731949486215 196378745972887097924229323)
  ·
    refine ⟨294568118959330646886343985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196378745972887097924229323 294568118959330646886343985)
    ·
      refine ⟨220926089219497985164757989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 294568118959330646886343985 220926089219497985164757989)
      ·
        refine ⟨41423641728655872218392123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 220926089219497985164757989 41423641728655872218392123)
        ·
          refine ⟨62135462592983808327588185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41423641728655872218392123 62135462592983808327588185)
          ·
            refine ⟨46601596944737856245691139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62135462592983808327588185 46601596944737856245691139)
            ·
              refine ⟨69902395417106784368536709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46601596944737856245691139 69902395417106784368536709)
              ·
                refine ⟨13106699140707522069100633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69902395417106784368536709 13106699140707522069100633)
                ·
                  refine ⟨9830024355530641551825475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13106699140707522069100633 9830024355530641551825475)
                  ·
                    refine ⟨14745036533295962327738213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9830024355530641551825475 14745036533295962327738213)
                    ·
                      refine ⟨2764694349992992936450915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14745036533295962327738213 2764694349992992936450915)
                      ·
                        rfl

theorem cell23_5384223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 4, 2, 1, 4].length) (baseStart_5384223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5384223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5384223 prefixEnd_5384223 := by exact prefixLift 5384223
  have htrace : WordTrace (prefixWord ++ tailWord_5384223) baseStart_5384223 baseEnd_5384223 := by
    simpa [prefixWord, tailWord_5384223, baseEnd_5384223] using wordTrace_append hprefix tailTrace_5384223
  have hstable : (prefixWord ++ tailWord_5384223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5384223).length < 2 ^ (prefixWord ++ tailWord_5384223).sum := by decide
  have hdescent : baseEnd_5384223 < baseStart_5384223 := by decide
  rcases family_descends (prefixWord ++ tailWord_5384223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5384236 : List Nat := [2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 6]
def baseStart_5384236 : Nat := 118140960795 + 5384236 * 2 ^ 59
def prefixEnd_5384236 : Nat := 4983230072969 + 3 ^ 40 * 5384236 * 2
def baseEnd_5384236 : Nat := 2764701025241501385588355

theorem tailTrace_5384236 : CollatzResearch.WordTrace tailWord_5384236 prefixEnd_5384236 2764701025241501385588355 := by
  unfold tailWord_5384236
  simp only [CollatzResearch.WordTrace]
  refine ⟨98189610060920000572226281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130919480081226667429635041 98189610060920000572226281)
  ·
    refine ⟨73642207545690000429169711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98189610060920000572226281 73642207545690000429169711)
    ·
      refine ⟨110463311318535000643754567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73642207545690000429169711 110463311318535000643754567)
      ·
        refine ⟨165694966977802500965631851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110463311318535000643754567 165694966977802500965631851)
        ·
          refine ⟨248542450466703751448447777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165694966977802500965631851 248542450466703751448447777)
          ·
            refine ⟨186406837850027813586335833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 248542450466703751448447777 186406837850027813586335833)
            ·
              refine ⟨139805128387520860189751875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 186406837850027813586335833 139805128387520860189751875)
              ·
                refine ⟨209707692581281290284627813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 139805128387520860189751875 209707692581281290284627813)
                ·
                  refine ⟨39320192358990241928367715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 209707692581281290284627813 39320192358990241928367715)
                  ·
                    refine ⟨58980288538485362892551573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39320192358990241928367715 58980288538485362892551573)
                    ·
                      refine ⟨2764701025241501385588355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58980288538485362892551573 2764701025241501385588355)
                      ·
                        rfl

theorem cell23_5384236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 6].length) (baseStart_5384236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5384236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5384236 prefixEnd_5384236 := by exact prefixLift 5384236
  have htrace : WordTrace (prefixWord ++ tailWord_5384236) baseStart_5384236 baseEnd_5384236 := by
    simpa [prefixWord, tailWord_5384236, baseEnd_5384236] using wordTrace_append hprefix tailTrace_5384236
  have hstable : (prefixWord ++ tailWord_5384236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5384236).length < 2 ^ (prefixWord ++ tailWord_5384236).sum := by decide
  have hdescent : baseEnd_5384236 < baseStart_5384236 := by decide
  rcases family_descends (prefixWord ++ tailWord_5384236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5384240 : List Nat := [2, 1, 1, 1, 2, 6, 1, 1, 2, 4, 2]
def baseStart_5384240 : Nat := 118140960795 + 5384240 * 2 ^ 59
def prefixEnd_5384240 : Nat := 4983230072969 + 3 ^ 40 * 5384240 * 2
def baseEnd_5384240 : Nat := 2764703079164119369938337

theorem tailTrace_5384240 : CollatzResearch.WordTrace tailWord_5384240 prefixEnd_5384240 2764703079164119369938337 := by
  unfold tailWord_5384240
  simp only [CollatzResearch.WordTrace]
  refine ⟨98189683006912754913799087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130919577342550339885065449 98189683006912754913799087)
  ·
    refine ⟨147284524510369132370698631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98189683006912754913799087 147284524510369132370698631)
    ·
      refine ⟨220926786765553698556047947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147284524510369132370698631 220926786765553698556047947)
      ·
        refine ⟨331390180148330547834071921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220926786765553698556047947 331390180148330547834071921)
        ·
          refine ⟨248542635111247910875553941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 331390180148330547834071921 248542635111247910875553941)
          ·
            refine ⟨11650436020839745822291591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 248542635111247910875553941 11650436020839745822291591)
            ·
              refine ⟨17475654031259618733437387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11650436020839745822291591 17475654031259618733437387)
              ·
                refine ⟨26213481046889428100156081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17475654031259618733437387 26213481046889428100156081)
                ·
                  refine ⟨19660110785167071075117061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26213481046889428100156081 19660110785167071075117061)
                  ·
                    refine ⟨3686270772218825826584449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19660110785167071075117061 3686270772218825826584449)
                    ·
                      refine ⟨2764703079164119369938337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3686270772218825826584449 2764703079164119369938337)
                      ·
                        rfl

theorem cell23_5384240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 1, 2, 4, 2].length) (baseStart_5384240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5384240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5384240 prefixEnd_5384240 := by exact prefixLift 5384240
  have htrace : WordTrace (prefixWord ++ tailWord_5384240) baseStart_5384240 baseEnd_5384240 := by
    simpa [prefixWord, tailWord_5384240, baseEnd_5384240] using wordTrace_append hprefix tailTrace_5384240
  have hstable : (prefixWord ++ tailWord_5384240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5384240).length < 2 ^ (prefixWord ++ tailWord_5384240).sum := by decide
  have hdescent : baseEnd_5384240 < baseStart_5384240 := by decide
  rcases family_descends (prefixWord ++ tailWord_5384240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5384243 : List Nat := [1, 1, 1, 2, 4, 1, 2, 2, 4, 2, 3]
def baseStart_5384243 : Nat := 118140960795 + 5384243 * 2 ^ 59
def prefixEnd_5384243 : Nat := 4983230072969 + 3 ^ 40 * 5384243 * 2
def baseEnd_5384243 : Nat := 2764704619606082858200823

theorem tailTrace_5384243 : CollatzResearch.WordTrace tailWord_5384243 prefixEnd_5384243 2764704619606082858200823 := by
  unfold tailWord_5384243
  simp only [CollatzResearch.WordTrace]
  refine ⟨196379475432814641339957383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130919650288543094226638255 196379475432814641339957383)
  ·
    refine ⟨294569213149221962009936075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196379475432814641339957383 294569213149221962009936075)
    ·
      refine ⟨441853819723832943014904113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294569213149221962009936075 441853819723832943014904113)
      ·
        refine ⟨331390364792874707261178085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 441853819723832943014904113 331390364792874707261178085)
        ·
          refine ⟨62135693398664007611470891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 331390364792874707261178085 62135693398664007611470891)
          ·
            refine ⟨93203540097996011417206337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62135693398664007611470891 93203540097996011417206337)
            ·
              refine ⟨69902655073497008562904753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93203540097996011417206337 69902655073497008562904753)
              ·
                refine ⟨52426991305122756422178565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69902655073497008562904753 52426991305122756422178565)
                ·
                  refine ⟨9830060869710516829158481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52426991305122756422178565 9830060869710516829158481)
                  ·
                    refine ⟨7372545652282887621868861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9830060869710516829158481 7372545652282887621868861)
                    ·
                      refine ⟨2764704619606082858200823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7372545652282887621868861 2764704619606082858200823)
                      ·
                        rfl

theorem cell23_5384243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 2, 4, 2, 3].length) (baseStart_5384243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5384243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5384243 prefixEnd_5384243 := by exact prefixLift 5384243
  have htrace : WordTrace (prefixWord ++ tailWord_5384243) baseStart_5384243 baseEnd_5384243 := by
    simpa [prefixWord, tailWord_5384243, baseEnd_5384243] using wordTrace_append hprefix tailTrace_5384243
  have hstable : (prefixWord ++ tailWord_5384243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5384243).length < 2 ^ (prefixWord ++ tailWord_5384243).sum := by decide
  have hdescent : baseEnd_5384243 < baseStart_5384243 := by decide
  rcases family_descends (prefixWord ++ tailWord_5384243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5384254 : List Nat := [4, 2, 1, 3, 3, 1, 1, 1, 2, 5]
def baseStart_5384254 : Nat := 118140960795 + 5384254 * 2 ^ 59
def prefixEnd_5384254 : Nat := 4983230072969 + 3 ^ 40 * 5384254 * 2
def baseEnd_5384254 : Nat := 921570089297760771721091

theorem tailTrace_5384254 : CollatzResearch.WordTrace tailWord_5384254 prefixEnd_5384254 921570089297760771721091 := by
  unfold tailWord_5384254
  simp only [CollatzResearch.WordTrace]
  refine ⟨24547484579471848777325977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130919917757183193479071877 24547484579471848777325977)
  ·
    refine ⟨18410613434603886582994483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24547484579471848777325977 18410613434603886582994483)
    ·
      refine ⟨27615920151905829874491725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18410613434603886582994483 27615920151905829874491725)
      ·
        refine ⟨10355970056964686202934397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27615920151905829874491725 10355970056964686202934397)
        ·
          refine ⟨3883488771361757326100399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10355970056964686202934397 3883488771361757326100399)
          ·
            refine ⟨5825233157042635989150599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3883488771361757326100399 5825233157042635989150599)
            ·
              refine ⟨8737849735563953983725899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5825233157042635989150599 8737849735563953983725899)
              ·
                refine ⟨13106774603345930975588849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8737849735563953983725899 13106774603345930975588849)
                ·
                  refine ⟨9830080952509448231691637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13106774603345930975588849 9830080952509448231691637)
                  ·
                    refine ⟨921570089297760771721091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9830080952509448231691637 921570089297760771721091)
                    ·
                      rfl

theorem cell23_5384254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 1, 1, 2, 5].length) (baseStart_5384254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5384254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5384254 prefixEnd_5384254 := by exact prefixLift 5384254
  have htrace : WordTrace (prefixWord ++ tailWord_5384254) baseStart_5384254 baseEnd_5384254 := by
    simpa [prefixWord, tailWord_5384254, baseEnd_5384254] using wordTrace_append hprefix tailTrace_5384254
  have hstable : (prefixWord ++ tailWord_5384254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5384254).length < 2 ^ (prefixWord ++ tailWord_5384254).sum := by decide
  have hdescent : baseEnd_5384254 < baseStart_5384254 := by decide
  rcases family_descends (prefixWord ++ tailWord_5384254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5384257 : List Nat := [1, 2, 5, 1, 2, 3, 1, 1, 2, 1, 4]
def baseStart_5384257 : Nat := 118140960795 + 5384257 * 2 ^ 59
def prefixEnd_5384257 : Nat := 4983230072969 + 3 ^ 40 * 5384257 * 2
def baseEnd_5384257 : Nat := 2764711808335245803425759

theorem tailTrace_5384257 : CollatzResearch.WordTrace tailWord_5384257 prefixEnd_5384257 2764711808335245803425759 := by
  unfold tailWord_5384257
  simp only [CollatzResearch.WordTrace]
  refine ⟨196379986054763921730967025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130919990703175947820644683 196379986054763921730967025)
  ·
    refine ⟨147284989541072941298225269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196379986054763921730967025 147284989541072941298225269)
    ·
      refine ⟨13807967769475588246708619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 147284989541072941298225269 13807967769475588246708619)
      ·
        refine ⟨20711951654213382370062929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13807967769475588246708619 20711951654213382370062929)
        ·
          refine ⟨15533963740660036777547197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20711951654213382370062929 15533963740660036777547197)
          ·
            refine ⟨5825236402747513791580199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15533963740660036777547197 5825236402747513791580199)
            ·
              refine ⟨8737854604121270687370299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5825236402747513791580199 8737854604121270687370299)
              ·
                refine ⟨13106781906181906031055449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8737854604121270687370299 13106781906181906031055449)
                ·
                  refine ⟨9830086429636429523291587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13106781906181906031055449 9830086429636429523291587)
                  ·
                    refine ⟨14745129644454644284937381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9830086429636429523291587 14745129644454644284937381)
                    ·
                      refine ⟨2764711808335245803425759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14745129644454644284937381 2764711808335245803425759)
                      ·
                        rfl

theorem cell23_5384257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 1, 1, 2, 1, 4].length) (baseStart_5384257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5384257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5384257 prefixEnd_5384257 := by exact prefixLift 5384257
  have htrace : WordTrace (prefixWord ++ tailWord_5384257) baseStart_5384257 baseEnd_5384257 := by
    simpa [prefixWord, tailWord_5384257, baseEnd_5384257] using wordTrace_append hprefix tailTrace_5384257
  have hstable : (prefixWord ++ tailWord_5384257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5384257).length < 2 ^ (prefixWord ++ tailWord_5384257).sum := by decide
  have hdescent : baseEnd_5384257 < baseStart_5384257 := by decide
  rcases family_descends (prefixWord ++ tailWord_5384257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5384280 : List Nat := [2, 1, 2, 2, 1, 6, 1, 2, 6]
def baseStart_5384280 : Nat := 118140960795 + 5384280 * 2 ^ 59
def prefixEnd_5384280 : Nat := 4983230072969 + 3 ^ 40 * 5384280 * 2
def baseEnd_5384280 : Nat := 307191513154477690382017

theorem tailTrace_5384280 : CollatzResearch.WordTrace tailWord_5384280 prefixEnd_5384280 307191513154477690382017 := by
  unfold tailWord_5384280
  simp only [CollatzResearch.WordTrace]
  refine ⟨98190412466840298329527147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130920549955787064439369529 98190412466840298329527147)
  ·
    refine ⟨147285618700260447494290721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98190412466840298329527147 147285618700260447494290721)
    ·
      refine ⟨110464214025195335620718041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147285618700260447494290721 110464214025195335620718041)
      ·
        refine ⟨82848160518896501715538531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110464214025195335620718041 82848160518896501715538531)
        ·
          refine ⟨124272240778344752573307797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82848160518896501715538531 124272240778344752573307797)
          ·
            refine ⟨5825261286484910276873803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 124272240778344752573307797 5825261286484910276873803)
            ·
              refine ⟨8737891929727365415310705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5825261286484910276873803 8737891929727365415310705)
              ·
                refine ⟨6553418947295524061483029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8737891929727365415310705 6553418947295524061483029)
                ·
                  refine ⟨307191513154477690382017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6553418947295524061483029 307191513154477690382017)
                  ·
                    rfl

theorem cell23_5384280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 1, 2, 6].length) (baseStart_5384280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5384280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5384280 prefixEnd_5384280 := by exact prefixLift 5384280
  have htrace : WordTrace (prefixWord ++ tailWord_5384280) baseStart_5384280 baseEnd_5384280 := by
    simpa [prefixWord, tailWord_5384280, baseEnd_5384280] using wordTrace_append hprefix tailTrace_5384280
  have hstable : (prefixWord ++ tailWord_5384280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5384280).length < 2 ^ (prefixWord ++ tailWord_5384280).sum := by decide
  have hdescent : baseEnd_5384280 < baseStart_5384280 := by decide
  rcases family_descends (prefixWord ++ tailWord_5384280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5384300 : List Nat := [2, 2, 1, 1, 3, 3, 1, 2, 1, 5, 2]
def baseStart_5384300 : Nat := 118140960795 + 5384300 * 2 ^ 59
def prefixEnd_5384300 : Nat := 4983230072969 + 3 ^ 40 * 5384300 * 2
def baseEnd_5384300 : Nat := 2764733888003389135188061

theorem tailTrace_5384300 : CollatzResearch.WordTrace tailWord_5384300 prefixEnd_5384300 2764733888003389135188061 := by
  unfold tailWord_5384300
  simp only [CollatzResearch.WordTrace]
  refine ⟨98190777196804070037391177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130921036262405426716521569 98190777196804070037391177)
  ·
    refine ⟨73643082897603052528043383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98190777196804070037391177 73643082897603052528043383)
    ·
      refine ⟨110464624346404578792065075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73643082897603052528043383 110464624346404578792065075)
      ·
        refine ⟨165696936519606868188097613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110464624346404578792065075 165696936519606868188097613)
        ·
          refine ⟨62136351194852575570536605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 165696936519606868188097613 62136351194852575570536605)
          ·
            refine ⟨23301131698069715838951227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62136351194852575570536605 23301131698069715838951227)
            ·
              refine ⟨34951697547104573758426841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23301131698069715838951227 34951697547104573758426841)
              ·
                refine ⟨26213773160328430318820131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34951697547104573758426841 26213773160328430318820131)
                ·
                  refine ⟨39320659740492645478230197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26213773160328430318820131 39320659740492645478230197)
                  ·
                    refine ⟨3686311850671185513584081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39320659740492645478230197 3686311850671185513584081)
                    ·
                      refine ⟨2764733888003389135188061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3686311850671185513584081 2764733888003389135188061)
                      ·
                        rfl

theorem cell23_5384300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 5, 2].length) (baseStart_5384300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5384300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5384300 prefixEnd_5384300 := by exact prefixLift 5384300
  have htrace : WordTrace (prefixWord ++ tailWord_5384300) baseStart_5384300 baseEnd_5384300 := by
    simpa [prefixWord, tailWord_5384300, baseEnd_5384300] using wordTrace_append hprefix tailTrace_5384300
  have hstable : (prefixWord ++ tailWord_5384300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5384300).length < 2 ^ (prefixWord ++ tailWord_5384300).sum := by decide
  have hdescent : baseEnd_5384300 < baseStart_5384300 := by decide
  rcases family_descends (prefixWord ++ tailWord_5384300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5384334 : List Nat := [4, 1, 1, 3, 3, 1, 1, 2, 2, 3, 2]
def baseStart_5384334 : Nat := 118140960795 + 5384334 * 2 ^ 59
def prefixEnd_5384334 : Nat := 4983230072969 + 3 ^ 40 * 5384334 * 2
def baseEnd_5384334 : Nat := 2764751346345642002162905

theorem tailTrace_5384334 : CollatzResearch.WordTrace tailWord_5384334 prefixEnd_5384334 2764751346345642002162905 := by
  unfold tailWord_5384334
  simp only [CollatzResearch.WordTrace]
  refine ⟨24547849309435620485190007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130921862983656642587680037 24547849309435620485190007)
  ·
    refine ⟨36821773964153430727785011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24547849309435620485190007 36821773964153430727785011)
    ·
      refine ⟨55232660946230146091677517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36821773964153430727785011 55232660946230146091677517)
      ·
        refine ⟨20712247854836304784379069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55232660946230146091677517 20712247854836304784379069)
        ·
          refine ⟨7767092945563614294142151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20712247854836304784379069 7767092945563614294142151)
          ·
            refine ⟨11650639418345421441213227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7767092945563614294142151 11650639418345421441213227)
            ·
              refine ⟨17475959127518132161819841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11650639418345421441213227 17475959127518132161819841)
              ·
                refine ⟨13106969345638599121364881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17475959127518132161819841 13106969345638599121364881)
                ·
                  refine ⟨9830227009228949341023661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13106969345638599121364881 9830227009228949341023661)
                  ·
                    refine ⟨3686335128460856002883873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9830227009228949341023661 3686335128460856002883873)
                    ·
                      refine ⟨2764751346345642002162905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3686335128460856002883873 2764751346345642002162905)
                      ·
                        rfl

theorem cell23_5384334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 2, 2, 3, 2].length) (baseStart_5384334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5384334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5384334 prefixEnd_5384334 := by exact prefixLift 5384334
  have htrace : WordTrace (prefixWord ++ tailWord_5384334) baseStart_5384334 baseEnd_5384334 := by
    simpa [prefixWord, tailWord_5384334, baseEnd_5384334] using wordTrace_append hprefix tailTrace_5384334
  have hstable : (prefixWord ++ tailWord_5384334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5384334).length < 2 ^ (prefixWord ++ tailWord_5384334).sum := by decide
  have hdescent : baseEnd_5384334 < baseStart_5384334 := by decide
  rcases family_descends (prefixWord ++ tailWord_5384334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5384353 : List Nat := [1, 2, 3, 3, 1, 2, 1, 10]
def baseStart_5384353 : Nat := 118140960795 + 5384353 * 2 ^ 59
def prefixEnd_5384353 : Nat := 4983230072969 + 3 ^ 40 * 5384353 * 2
def baseEnd_5384353 : Nat := 102398559351039904734271

theorem tailTrace_5384353 : CollatzResearch.WordTrace tailWord_5384353 prefixEnd_5384353 102398559351039904734271 := by
  unfold tailWord_5384353
  simp only [CollatzResearch.WordTrace]
  refine ⟨196383487462416130126461713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130922324974944086750974475 196383487462416130126461713)
  ·
    refine ⟨147287615596812097594846285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196383487462416130126461713 147287615596812097594846285)
    ·
      refine ⟨55232855848804536598067357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147287615596812097594846285 55232855848804536598067357)
      ·
        refine ⟨20712320943301701224275259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55232855848804536598067357 20712320943301701224275259)
        ·
          refine ⟨31068481414952551836412889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20712320943301701224275259 31068481414952551836412889)
          ·
            refine ⟨23301361061214413877309667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31068481414952551836412889 23301361061214413877309667)
            ·
              refine ⟨34952041591821620815964501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23301361061214413877309667 34952041591821620815964501)
              ·
                refine ⟨102398559351039904734271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 34952041591821620815964501 102398559351039904734271)
                ·
                  rfl

theorem cell23_5384353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 10].length) (baseStart_5384353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5384353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5384353 prefixEnd_5384353 := by exact prefixLift 5384353
  have htrace : WordTrace (prefixWord ++ tailWord_5384353) baseStart_5384353 baseEnd_5384353 := by
    simpa [prefixWord, tailWord_5384353, baseEnd_5384353] using wordTrace_append hprefix tailTrace_5384353
  have hstable : (prefixWord ++ tailWord_5384353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5384353).length < 2 ^ (prefixWord ++ tailWord_5384353).sum := by decide
  have hdescent : baseEnd_5384353 < baseStart_5384353 := by decide
  rcases family_descends (prefixWord ++ tailWord_5384353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5384384 : List Nat := [2, 1, 1, 2, 5, 2, 3, 1, 1, 2, 3]
def baseStart_5384384 : Nat := 118140960795 + 5384384 * 2 ^ 59
def prefixEnd_5384384 : Nat := 4983230072969 + 3 ^ 40 * 5384384 * 2
def baseEnd_5384384 : Nat := 2764777020378366806537675

theorem tailTrace_5384384 : CollatzResearch.WordTrace tailWord_5384384 prefixEnd_5384384 2764777020378366806537675 := by
  unfold tailWord_5384384
  simp only [CollatzResearch.WordTrace]
  refine ⟨98192309062651911210420103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130923078750202548280560137 98192309062651911210420103)
  ·
    refine ⟨147288463593977866815630155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98192309062651911210420103 147288463593977866815630155)
    ·
      refine ⟨220932695390966800223445233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147288463593977866815630155 220932695390966800223445233)
      ·
        refine ⟨165699521543225100167583925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 220932695390966800223445233 165699521543225100167583925)
        ·
          refine ⟨15534330144677353140710993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 165699521543225100167583925 15534330144677353140710993)
          ·
            refine ⟨11650747608508014855533245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15534330144677353140710993 11650747608508014855533245)
            ·
              refine ⟨4369030353190505570824967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11650747608508014855533245 4369030353190505570824967)
              ·
                refine ⟨6553545529785758356237451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4369030353190505570824967 6553545529785758356237451)
                ·
                  refine ⟨9830318294678637534356177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6553545529785758356237451 9830318294678637534356177)
                  ·
                    refine ⟨7372738721008978150767133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9830318294678637534356177 7372738721008978150767133)
                    ·
                      refine ⟨2764777020378366806537675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7372738721008978150767133 2764777020378366806537675)
                      ·
                        rfl

theorem cell23_5384384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 3, 1, 1, 2, 3].length) (baseStart_5384384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5384384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5384384 prefixEnd_5384384 := by exact prefixLift 5384384
  have htrace : WordTrace (prefixWord ++ tailWord_5384384) baseStart_5384384 baseEnd_5384384 := by
    simpa [prefixWord, tailWord_5384384, baseEnd_5384384] using wordTrace_append hprefix tailTrace_5384384
  have hstable : (prefixWord ++ tailWord_5384384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5384384).length < 2 ^ (prefixWord ++ tailWord_5384384).sum := by decide
  have hdescent : baseEnd_5384384 < baseStart_5384384 := by decide
  rcases family_descends (prefixWord ++ tailWord_5384384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5384398 : List Nat := [4, 1, 1, 1, 4, 1, 4, 2, 1, 2, 2]
def baseStart_5384398 : Nat := 118140960795 + 5384398 * 2 ^ 59
def prefixEnd_5384398 : Nat := 4983230072969 + 3 ^ 40 * 5384398 * 2
def baseEnd_5384398 : Nat := 2764784209107529751762611

theorem tailTrace_5384398 : CollatzResearch.WordTrace tailWord_5384398 prefixEnd_5384398 2764784209107529751762611 := by
  unfold tailWord_5384398
  simp only [CollatzResearch.WordTrace]
  refine ⟨24548141093406637851481231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130923419164835401874566565 24548141093406637851481231)
  ·
    refine ⟨36822211640109956777221847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24548141093406637851481231 36822211640109956777221847)
    ·
      refine ⟨55233317460164935165832771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36822211640109956777221847 55233317460164935165832771)
      ·
        refine ⟨82849976190247402748749157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55233317460164935165832771 82849976190247402748749157)
        ·
          refine ⟨15534370535671388015390467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82849976190247402748749157 15534370535671388015390467)
          ·
            refine ⟨23301555803507082023085701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15534370535671388015390467 23301555803507082023085701)
            ·
              refine ⟨4369041713157577879328569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23301555803507082023085701 4369041713157577879328569)
              ·
                refine ⟨3276781284868183409496427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4369041713157577879328569 3276781284868183409496427)
                ·
                  refine ⟨4915171927302275114244641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3276781284868183409496427 4915171927302275114244641)
                  ·
                    refine ⟨3686378945476706335683481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4915171927302275114244641 3686378945476706335683481)
                    ·
                      refine ⟨2764784209107529751762611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3686378945476706335683481 2764784209107529751762611)
                      ·
                        rfl

theorem cell23_5384398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 4, 2, 1, 2, 2].length) (baseStart_5384398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5384398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5384398 prefixEnd_5384398 := by exact prefixLift 5384398
  have htrace : WordTrace (prefixWord ++ tailWord_5384398) baseStart_5384398 baseEnd_5384398 := by
    simpa [prefixWord, tailWord_5384398, baseEnd_5384398] using wordTrace_append hprefix tailTrace_5384398
  have hstable : (prefixWord ++ tailWord_5384398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5384398).length < 2 ^ (prefixWord ++ tailWord_5384398).sum := by decide
  have hdescent : baseEnd_5384398 < baseStart_5384398 := by decide
  rcases family_descends (prefixWord ++ tailWord_5384398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5384453 : List Nat := [1, 3, 1, 1, 2, 1, 2, 1, 1, 1, 9]
def baseStart_5384453 : Nat := 118140960795 + 5384453 * 2 ^ 59
def prefixEnd_5384453 : Nat := 4983230072969 + 3 ^ 40 * 5384453 * 2
def baseEnd_5384453 : Nat := 2764812450543527036574857

theorem tailTrace_5384453 : CollatzResearch.WordTrace tailWord_5384453 prefixEnd_5384453 2764812450543527036574857 := by
  unfold tailWord_5384453
  simp only [CollatzResearch.WordTrace]
  refine ⟨196387134762053847205102013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130924756508035898136734675 196387134762053847205102013)
  ·
    refine ⟨73645175535770192701913255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 196387134762053847205102013 73645175535770192701913255)
    ·
      refine ⟨110467763303655289052869883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73645175535770192701913255 110467763303655289052869883)
      ·
        refine ⟨165701644955482933579304825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110467763303655289052869883 165701644955482933579304825)
        ·
          refine ⟨124276233716612200184478619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165701644955482933579304825 124276233716612200184478619)
          ·
            refine ⟨186414350574918300276717929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124276233716612200184478619 186414350574918300276717929)
            ·
              refine ⟨139810762931188725207538447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 186414350574918300276717929 139810762931188725207538447)
              ·
                refine ⟨209716144396783087811307671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 139810762931188725207538447 209716144396783087811307671)
                ·
                  refine ⟨314574216595174631716961507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 209716144396783087811307671 314574216595174631716961507)
                  ·
                    refine ⟨471861324892761947575442261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 314574216595174631716961507 471861324892761947575442261)
                    ·
                      refine ⟨2764812450543527036574857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 471861324892761947575442261 2764812450543527036574857)
                      ·
                        rfl

theorem cell23_5384453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 1, 9].length) (baseStart_5384453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5384453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5384453 prefixEnd_5384453 := by exact prefixLift 5384453
  have htrace : WordTrace (prefixWord ++ tailWord_5384453) baseStart_5384453 baseEnd_5384453 := by
    simpa [prefixWord, tailWord_5384453, baseEnd_5384453] using wordTrace_append hprefix tailTrace_5384453
  have hstable : (prefixWord ++ tailWord_5384453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5384453).length < 2 ^ (prefixWord ++ tailWord_5384453).sum := by decide
  have hdescent : baseEnd_5384453 < baseStart_5384453 := by decide
  rcases family_descends (prefixWord ++ tailWord_5384453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5384460 : List Nat := [2, 2, 1, 2, 2, 2, 4, 1, 7]
def baseStart_5384460 : Nat := 118140960795 + 5384460 * 2 ^ 59
def prefixEnd_5384460 : Nat := 4983230072969 + 3 ^ 40 * 5384460 * 2
def baseEnd_5384460 : Nat := 307201782767567612131925

theorem tailTrace_5384460 : CollatzResearch.WordTrace tailWord_5384460 prefixEnd_5384460 307201782767567612131925 := by
  unfold tailWord_5384460
  simp only [CollatzResearch.WordTrace]
  refine ⟨98193695036514243700303417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130924926715352324933737889 98193695036514243700303417)
  ·
    refine ⟨73645271277385682775227563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98193695036514243700303417 73645271277385682775227563)
    ·
      refine ⟨110467906916078524162841345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73645271277385682775227563 110467906916078524162841345)
      ·
        refine ⟨82850930187058893122131009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110467906916078524162841345 82850930187058893122131009)
        ·
          refine ⟨62138197640294169841598257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82850930187058893122131009 62138197640294169841598257)
          ·
            refine ⟨46603648230220627381198693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62138197640294169841598257 46603648230220627381198693)
            ·
              refine ⟨8738184043166367633974755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46603648230220627381198693 8738184043166367633974755)
              ·
                refine ⟨13107276064749551450962133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8738184043166367633974755 13107276064749551450962133)
                ·
                  refine ⟨307201782767567612131925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13107276064749551450962133 307201782767567612131925)
                  ·
                    rfl

theorem cell23_5384460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4, 1, 7].length) (baseStart_5384460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5384460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5384460 prefixEnd_5384460 := by exact prefixLift 5384460
  have htrace : WordTrace (prefixWord ++ tailWord_5384460) baseStart_5384460 baseEnd_5384460 := by
    simpa [prefixWord, tailWord_5384460, baseEnd_5384460] using wordTrace_append hprefix tailTrace_5384460
  have hstable : (prefixWord ++ tailWord_5384460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5384460).length < 2 ^ (prefixWord ++ tailWord_5384460).sum := by decide
  have hdescent : baseEnd_5384460 < baseStart_5384460 := by decide
  rcases family_descends (prefixWord ++ tailWord_5384460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5384544 : List Nat := [2, 1, 1, 3, 5, 1, 2, 1, 2, 1, 4]
def baseStart_5384544 : Nat := 118140960795 + 5384544 * 2 ^ 59
def prefixEnd_5384544 : Nat := 4983230072969 + 3 ^ 40 * 5384544 * 2
def baseEnd_5384544 : Nat := 2764859177283086180536939

theorem tailTrace_5384544 : CollatzResearch.WordTrace tailWord_5384544 prefixEnd_5384544 2764859177283086180536939 := by
  unfold tailWord_5384544
  simp only [CollatzResearch.WordTrace]
  refine ⟨98195226902362084873332343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130926969203149446497776457 98195226902362084873332343)
  ·
    refine ⟨147292840353543127309998515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98195226902362084873332343 147292840353543127309998515)
    ·
      refine ⟨220939260530314690964997773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147292840353543127309998515 220939260530314690964997773)
      ·
        refine ⟨82852222698868009111874165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 220939260530314690964997773 82852222698868009111874165)
        ·
          refine ⟨7767395878018875854238203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 82852222698868009111874165 7767395878018875854238203)
          ·
            refine ⟨11651093817028313781357305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7767395878018875854238203 11651093817028313781357305)
            ·
              refine ⟨8738320362771235336017979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11651093817028313781357305 8738320362771235336017979)
              ·
                refine ⟨13107480544156853004026969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8738320362771235336017979 13107480544156853004026969)
                ·
                  refine ⟨9830610408117639753020227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13107480544156853004026969 9830610408117639753020227)
                  ·
                    refine ⟨14745915612176459629530341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9830610408117639753020227 14745915612176459629530341)
                    ·
                      refine ⟨2764859177283086180536939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14745915612176459629530341 2764859177283086180536939)
                      ·
                        rfl

theorem cell23_5384544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 2, 1, 2, 1, 4].length) (baseStart_5384544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5384544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5384544 prefixEnd_5384544 := by exact prefixLift 5384544
  have htrace : WordTrace (prefixWord ++ tailWord_5384544) baseStart_5384544 baseEnd_5384544 := by
    simpa [prefixWord, tailWord_5384544, baseEnd_5384544] using wordTrace_append hprefix tailTrace_5384544
  have hstable : (prefixWord ++ tailWord_5384544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5384544).length < 2 ^ (prefixWord ++ tailWord_5384544).sum := by decide
  have hdescent : baseEnd_5384544 < baseStart_5384544 := by decide
  rcases family_descends (prefixWord ++ tailWord_5384544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5384571 : List Nat := [1, 1, 1, 1, 1, 7, 4, 2, 1, 4]
def baseStart_5384571 : Nat := 118140960795 + 5384571 * 2 ^ 59
def prefixEnd_5384571 : Nat := 4983230072969 + 3 ^ 40 * 5384571 * 2
def baseEnd_5384571 : Nat := 921624347086919191633105

theorem tailTrace_5384571 : CollatzResearch.WordTrace tailWord_5384571 prefixEnd_5384571 921624347086919191633105 := by
  unfold tailWord_5384571
  simp only [CollatzResearch.WordTrace]
  refine ⟨196391438575626353357897567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130927625717084235571931711 196391438575626353357897567)
  ·
    refine ⟨294587157863439530036846351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196391438575626353357897567 294587157863439530036846351)
    ·
      refine ⟨441880736795159295055269527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294587157863439530036846351 441880736795159295055269527)
      ·
        refine ⟨662821105192738942582904291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 441880736795159295055269527 662821105192738942582904291)
        ·
          refine ⟨994231657789108413874356437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 662821105192738942582904291 994231657789108413874356437)
          ·
            refine ⟨23302304479432228450180229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 994231657789108413874356437 23302304479432228450180229)
            ·
              refine ⟨4369182089893542834408793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23302304479432228450180229 4369182089893542834408793)
              ·
                refine ⟨3276886567420157125806595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4369182089893542834408793 3276886567420157125806595)
                ·
                  refine ⟨4915329851130235688709893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3276886567420157125806595 4915329851130235688709893)
                  ·
                    refine ⟨921624347086919191633105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4915329851130235688709893 921624347086919191633105)
                    ·
                      rfl

theorem cell23_5384571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 4, 2, 1, 4].length) (baseStart_5384571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5384571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5384571 prefixEnd_5384571 := by exact prefixLift 5384571
  have htrace : WordTrace (prefixWord ++ tailWord_5384571) baseStart_5384571 baseEnd_5384571 := by
    simpa [prefixWord, tailWord_5384571, baseEnd_5384571] using wordTrace_append hprefix tailTrace_5384571
  have hstable : (prefixWord ++ tailWord_5384571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5384571).length < 2 ^ (prefixWord ++ tailWord_5384571).sum := by decide
  have hdescent : baseEnd_5384571 < baseStart_5384571 := by decide
  rcases family_descends (prefixWord ++ tailWord_5384571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5384578 : List Nat := [3, 4, 2, 1, 2, 1, 1, 1, 2, 4, 2]
def baseStart_5384578 : Nat := 118140960795 + 5384578 * 2 ^ 59
def prefixEnd_5384578 : Nat := 4983230072969 + 3 ^ 40 * 5384578 * 2
def baseEnd_5384578 : Nat := 2764876635625339047511783

theorem tailTrace_5384578 : CollatzResearch.WordTrace tailWord_5384578 prefixEnd_5384578 2764876635625339047511783 := by
  unfold tailWord_5384578
  simp only [CollatzResearch.WordTrace]
  refine ⟨49097923471650248388350597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130927795924400662368934925 49097923471650248388350597)
  ·
    refine ⟨9205860650934421572815737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49097923471650248388350597 9205860650934421572815737)
    ·
      refine ⟨6904395488200816179611803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9205860650934421572815737 6904395488200816179611803)
      ·
        refine ⟨10356593232301224269417705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6904395488200816179611803 10356593232301224269417705)
        ·
          refine ⟨7767444924225918202063279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10356593232301224269417705 7767444924225918202063279)
          ·
            refine ⟨11651167386338877303094919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7767444924225918202063279 11651167386338877303094919)
            ·
              refine ⟨17476751079508315954642379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11651167386338877303094919 17476751079508315954642379)
              ·
                refine ⟨26215126619262473931963569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17476751079508315954642379 26215126619262473931963569)
                ·
                  refine ⟨19661344964446855448972677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26215126619262473931963569 19661344964446855448972677)
                  ·
                    refine ⟨3686502180833785396682377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19661344964446855448972677 3686502180833785396682377)
                    ·
                      refine ⟨2764876635625339047511783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3686502180833785396682377 2764876635625339047511783)
                      ·
                        rfl

theorem cell23_5384578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 1, 2, 4, 2].length) (baseStart_5384578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5384578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5384578 prefixEnd_5384578 := by exact prefixLift 5384578
  have htrace : WordTrace (prefixWord ++ tailWord_5384578) baseStart_5384578 baseEnd_5384578 := by
    simpa [prefixWord, tailWord_5384578, baseEnd_5384578] using wordTrace_append hprefix tailTrace_5384578
  have hstable : (prefixWord ++ tailWord_5384578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5384578).length < 2 ^ (prefixWord ++ tailWord_5384578).sum := by decide
  have hdescent : baseEnd_5384578 < baseStart_5384578 := by decide
  rcases family_descends (prefixWord ++ tailWord_5384578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5384597 : List Nat := [1, 3, 2, 1, 1, 2, 1, 6, 1, 5]
def baseStart_5384597 : Nat := 118140960795 + 5384597 * 2 ^ 59
def prefixEnd_5384597 : Nat := 4983230072969 + 3 ^ 40 * 5384597 * 2
def baseEnd_5384597 : Nat := 921628797252591491058065

theorem tailTrace_5384597 : CollatzResearch.WordTrace tailWord_5384597 prefixEnd_5384597 921628797252591491058065 := by
  unfold tailWord_5384597
  simp only [CollatzResearch.WordTrace]
  refine ⟨196392386873532159798344045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130928257915688106532229363 196392386873532159798344045)
  ·
    refine ⟨73647145077574559924379017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 196392386873532159798344045 73647145077574559924379017)
    ·
      refine ⟨55235358808180919943284263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73647145077574559924379017 55235358808180919943284263)
      ·
        refine ⟨82853038212271379914926395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55235358808180919943284263 82853038212271379914926395)
        ·
          refine ⟨124279557318407069872389593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82853038212271379914926395 124279557318407069872389593)
          ·
            refine ⟨93209667988805302404292195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124279557318407069872389593 93209667988805302404292195)
            ·
              refine ⟨139814501983207953606438293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93209667988805302404292195 139814501983207953606438293)
              ·
                refine ⟨6553804780462872825301795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 139814501983207953606438293 6553804780462872825301795)
                ·
                  refine ⟨9830707170694309237952693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6553804780462872825301795 9830707170694309237952693)
                  ·
                    refine ⟨921628797252591491058065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9830707170694309237952693 921628797252591491058065)
                    ·
                      rfl

theorem cell23_5384597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 6, 1, 5].length) (baseStart_5384597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5384597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5384597 prefixEnd_5384597 := by exact prefixLift 5384597
  have htrace : WordTrace (prefixWord ++ tailWord_5384597) baseStart_5384597 baseEnd_5384597 := by
    simpa [prefixWord, tailWord_5384597, baseEnd_5384597] using wordTrace_append hprefix tailTrace_5384597
  have hstable : (prefixWord ++ tailWord_5384597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5384597).length < 2 ^ (prefixWord ++ tailWord_5384597).sum := by decide
  have hdescent : baseEnd_5384597 < baseStart_5384597 := by decide
  rcases family_descends (prefixWord ++ tailWord_5384597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5384611 : List Nat := [1, 1, 1, 4, 1, 4, 1, 5, 1, 1, 3]
def baseStart_5384611 : Nat := 118140960795 + 5384611 * 2 ^ 59
def prefixEnd_5384611 : Nat := 4983230072969 + 3 ^ 40 * 5384611 * 2
def baseEnd_5384611 : Nat := 2764893580486937418399131

theorem tailTrace_5384611 : CollatzResearch.WordTrace tailWord_5384611 prefixEnd_5384611 2764893580486937418399131 := by
  unfold tailWord_5384611
  simp only [CollatzResearch.WordTrace]
  refine ⟨196392897495481440189353687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130928598330320960126235791 196392897495481440189353687)
  ·
    refine ⟨294589346243222160284030531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196392897495481440189353687 294589346243222160284030531)
    ·
      refine ⟨441884019364833240426045797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294589346243222160284030531 441884019364833240426045797)
      ·
        refine ⟨82853253630906232579883587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 441884019364833240426045797 82853253630906232579883587)
        ·
          refine ⟨124279880446359348869825381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82853253630906232579883587 124279880446359348869825381)
          ·
            refine ⟨23302477583692377913092259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 124279880446359348869825381 23302477583692377913092259)
            ·
              refine ⟨34953716375538566869638389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23302477583692377913092259 34953716375538566869638389)
              ·
                refine ⟨3276910910206740644028599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34953716375538566869638389 3276910910206740644028599)
                ·
                  refine ⟨4915366365310110966042899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3276910910206740644028599 4915366365310110966042899)
                  ·
                    refine ⟨7373049547965166449064349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4915366365310110966042899 7373049547965166449064349)
                    ·
                      refine ⟨2764893580486937418399131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7373049547965166449064349 2764893580486937418399131)
                      ·
                        rfl

theorem cell23_5384611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 5, 1, 1, 3].length) (baseStart_5384611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5384611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5384611 prefixEnd_5384611 := by exact prefixLift 5384611
  have htrace : WordTrace (prefixWord ++ tailWord_5384611) baseStart_5384611 baseEnd_5384611 := by
    simpa [prefixWord, tailWord_5384611, baseEnd_5384611] using wordTrace_append hprefix tailTrace_5384611
  have hstable : (prefixWord ++ tailWord_5384611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5384611).length < 2 ^ (prefixWord ++ tailWord_5384611).sum := by decide
  have hdescent : baseEnd_5384611 < baseStart_5384611 := by decide
  rcases family_descends (prefixWord ++ tailWord_5384611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5384617 : List Nat := [1, 2, 1, 1, 1, 1, 3, 2, 1, 8, 2]
def baseStart_5384617 : Nat := 118140960795 + 5384617 * 2 ^ 59
def prefixEnd_5384617 : Nat := 4983230072969 + 3 ^ 40 * 5384617 * 2
def baseEnd_5384617 : Nat := 2764896661370864394924103

theorem tailTrace_5384617 : CollatzResearch.WordTrace tailWord_5384617 prefixEnd_5384617 2764896661370864394924103 := by
  unfold tailWord_5384617
  simp only [CollatzResearch.WordTrace]
  refine ⟨196393116333459703214072105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130928744222306468809381403 196393116333459703214072105)
  ·
    refine ⟨147294837250094777410554079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196393116333459703214072105 147294837250094777410554079)
    ·
      refine ⟨220942255875142166115831119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147294837250094777410554079 220942255875142166115831119)
      ·
        refine ⟨331413383812713249173746679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220942255875142166115831119 331413383812713249173746679)
        ·
          refine ⟨497120075719069873760620019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 331413383812713249173746679 497120075719069873760620019)
          ·
            refine ⟨745680113578604810640930029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 497120075719069873760620019 745680113578604810640930029)
            ·
              refine ⟨279630042591976803990348761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 745680113578604810640930029 279630042591976803990348761)
              ·
                refine ⟨209722531943982602992761571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 279630042591976803990348761 209722531943982602992761571)
                ·
                  refine ⟨314583797915973904489142357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 209722531943982602992761571 314583797915973904489142357)
                  ·
                    refine ⟨3686528881827819193232137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 314583797915973904489142357 3686528881827819193232137)
                    ·
                      refine ⟨2764896661370864394924103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3686528881827819193232137 2764896661370864394924103)
                      ·
                        rfl

theorem cell23_5384617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 8, 2].length) (baseStart_5384617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5384617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5384617 prefixEnd_5384617 := by exact prefixLift 5384617
  have htrace : WordTrace (prefixWord ++ tailWord_5384617) baseStart_5384617 baseEnd_5384617 := by
    simpa [prefixWord, tailWord_5384617, baseEnd_5384617] using wordTrace_append hprefix tailTrace_5384617
  have hstable : (prefixWord ++ tailWord_5384617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5384617).length < 2 ^ (prefixWord ++ tailWord_5384617).sum := by decide
  have hdescent : baseEnd_5384617 < baseStart_5384617 := by decide
  rcases family_descends (prefixWord ++ tailWord_5384617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5384637 : List Nat := [1, 4, 1, 2, 2, 2, 1, 1, 3, 1, 5]
def baseStart_5384637 : Nat := 118140960795 + 5384637 * 2 ^ 59
def prefixEnd_5384637 : Nat := 4983230072969 + 3 ^ 40 * 5384637 * 2
def baseEnd_5384637 : Nat := 2764906930983954316674011

theorem tailTrace_5384637 : CollatzResearch.WordTrace tailWord_5384637 prefixEnd_5384637 2764906930983954316674011 := by
  unfold tailWord_5384637
  simp only [CollatzResearch.WordTrace]
  refine ⟨196393845793387246629800165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130929230528924831086533443 196393845793387246629800165)
  ·
    refine ⟨36823846086260108743087531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 196393845793387246629800165 36823846086260108743087531)
    ·
      refine ⟨55235769129390163114631297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36823846086260108743087531 55235769129390163114631297)
      ·
        refine ⟨41426826847042622335973473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55235769129390163114631297 41426826847042622335973473)
        ·
          refine ⟨31070120135281966751980105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41426826847042622335973473 31070120135281966751980105)
          ·
            refine ⟨23302590101461475063985079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31070120135281966751980105 23302590101461475063985079)
            ·
              refine ⟨34953885152192212595977619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23302590101461475063985079 34953885152192212595977619)
              ·
                refine ⟨52430827728288318893966429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34953885152192212595977619 52430827728288318893966429)
                ·
                  refine ⟨19661560398108119585237411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52430827728288318893966429 19661560398108119585237411)
                  ·
                    refine ⟨29492340597162179377856117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19661560398108119585237411 29492340597162179377856117)
                    ·
                      refine ⟨2764906930983954316674011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29492340597162179377856117 2764906930983954316674011)
                      ·
                        rfl

theorem cell23_5384637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 1, 3, 1, 5].length) (baseStart_5384637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5384637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5384637 prefixEnd_5384637 := by exact prefixLift 5384637
  have htrace : WordTrace (prefixWord ++ tailWord_5384637) baseStart_5384637 baseEnd_5384637 := by
    simpa [prefixWord, tailWord_5384637, baseEnd_5384637] using wordTrace_append hprefix tailTrace_5384637
  have hstable : (prefixWord ++ tailWord_5384637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5384637).length < 2 ^ (prefixWord ++ tailWord_5384637).sum := by decide
  have hdescent : baseEnd_5384637 < baseStart_5384637 := by decide
  rcases family_descends (prefixWord ++ tailWord_5384637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5384640 : List Nat := [2, 1, 1, 2, 3, 1, 1, 12]
def baseStart_5384640 : Nat := 118140960795 + 5384640 * 2 ^ 59
def prefixEnd_5384640 : Nat := 4983230072969 + 3 ^ 40 * 5384640 * 2
def baseEnd_5384640 : Nat := 102404017460219177960611

theorem tailTrace_5384640 : CollatzResearch.WordTrace tailWord_5384640 prefixEnd_5384640 102404017460219177960611 := by
  unfold tailWord_5384640
  simp only [CollatzResearch.WordTrace]
  refine ⟨98196977606188189071079687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130929303474917585428106249 98196977606188189071079687)
  ·
    refine ⟨147295466409282283606619531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98196977606188189071079687 147295466409282283606619531)
    ·
      refine ⟨220943199613923425409929297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147295466409282283606619531 220943199613923425409929297)
      ·
        refine ⟨165707399710442569057446973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 220943199613923425409929297 165707399710442569057446973)
        ·
          refine ⟨62140274891415963396542615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 165707399710442569057446973 62140274891415963396542615)
          ·
            refine ⟨93210412337123945094813923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62140274891415963396542615 93210412337123945094813923)
            ·
              refine ⟨139815618505685917642220885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93210412337123945094813923 139815618505685917642220885)
              ·
                refine ⟨102404017460219177960611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 139815618505685917642220885 102404017460219177960611)
                ·
                  rfl

theorem cell23_5384640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 12].length) (baseStart_5384640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5384640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5384640 prefixEnd_5384640 := by exact prefixLift 5384640
  have htrace : WordTrace (prefixWord ++ tailWord_5384640) baseStart_5384640 baseEnd_5384640 := by
    simpa [prefixWord, tailWord_5384640, baseEnd_5384640] using wordTrace_append hprefix tailTrace_5384640
  have hstable : (prefixWord ++ tailWord_5384640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5384640).length < 2 ^ (prefixWord ++ tailWord_5384640).sum := by decide
  have hdescent : baseEnd_5384640 < baseStart_5384640 := by decide
  rcases family_descends (prefixWord ++ tailWord_5384640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5384647 : List Nat := [1, 1, 4, 1, 1, 5, 1, 1, 1, 1, 6]
def baseStart_5384647 : Nat := 118140960795 + 5384647 * 2 ^ 59
def prefixEnd_5384647 : Nat := 4983230072969 + 3 ^ 40 * 5384647 * 2
def baseEnd_5384647 : Nat := 2764912065790499277548965

theorem tailTrace_5384647 : CollatzResearch.WordTrace tailWord_5384647 prefixEnd_5384647 2764912065790499277548965 := by
  unfold tailWord_5384647
  simp only [CollatzResearch.WordTrace]
  refine ⟨196394210523351018337664195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130929473682234012225109463 196394210523351018337664195)
  ·
    refine ⟨294591315785026527506496293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196394210523351018337664195 294591315785026527506496293)
    ·
      refine ⟨55235871709692473907468055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 294591315785026527506496293 55235871709692473907468055)
      ·
        refine ⟨82853807564538710861202083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55235871709692473907468055 82853807564538710861202083)
        ·
          refine ⟨124280711346808066291803125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82853807564538710861202083 124280711346808066291803125)
          ·
            refine ⟨11651316688763256214856543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 124280711346808066291803125 11651316688763256214856543)
            ·
              refine ⟨17476975033144884322284815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11651316688763256214856543 17476975033144884322284815)
              ·
                refine ⟨26215462549717326483427223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17476975033144884322284815 26215462549717326483427223)
                ·
                  refine ⟨39323193824575989725140835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26215462549717326483427223 39323193824575989725140835)
                  ·
                    refine ⟨58984790736863984587711253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39323193824575989725140835 58984790736863984587711253)
                    ·
                      refine ⟨2764912065790499277548965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58984790736863984587711253 2764912065790499277548965)
                      ·
                        rfl

theorem cell23_5384647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 1, 1, 1, 6].length) (baseStart_5384647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5384647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5384647 prefixEnd_5384647 := by exact prefixLift 5384647
  have htrace : WordTrace (prefixWord ++ tailWord_5384647) baseStart_5384647 baseEnd_5384647 := by
    simpa [prefixWord, tailWord_5384647, baseEnd_5384647] using wordTrace_append hprefix tailTrace_5384647
  have hstable : (prefixWord ++ tailWord_5384647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5384647).length < 2 ^ (prefixWord ++ tailWord_5384647).sum := by decide
  have hdescent : baseEnd_5384647 < baseStart_5384647 := by decide
  rcases family_descends (prefixWord ++ tailWord_5384647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5384684 : List Nat := [2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 3]
def baseStart_5384684 : Nat := 118140960795 + 5384684 * 2 ^ 59
def prefixEnd_5384684 : Nat := 4983230072969 + 3 ^ 40 * 5384684 * 2
def baseEnd_5384684 : Nat := 2764931064574715632786295

theorem tailTrace_5384684 : CollatzResearch.WordTrace tailWord_5384684 prefixEnd_5384684 2764931064574715632786295 := by
  unfold tailWord_5384684
  simp only [CollatzResearch.WordTrace]
  refine ⟨98197780012108486828380553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130930373349477982437840737 98197780012108486828380553)
  ·
    refine ⟨73648335009081365121285415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98197780012108486828380553 73648335009081365121285415)
    ·
      refine ⟨110472502513622047681928123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73648335009081365121285415 110472502513622047681928123)
      ·
        refine ⟨165708753770433071522892185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110472502513622047681928123 165708753770433071522892185)
        ·
          refine ⟨124281565327824803642169139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165708753770433071522892185 124281565327824803642169139)
          ·
            refine ⟨186422347991737205463253709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124281565327824803642169139 186422347991737205463253709)
            ·
              refine ⟨69908380496901452048720141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 186422347991737205463253709 69908380496901452048720141)
              ·
                refine ⟨26215642686338044518270053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69908380496901452048720141 26215642686338044518270053)
                ·
                  refine ⟨4915433003688383347175635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26215642686338044518270053 4915433003688383347175635)
                  ·
                    refine ⟨7373149505532575020763453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4915433003688383347175635 7373149505532575020763453)
                    ·
                      refine ⟨2764931064574715632786295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7373149505532575020763453 2764931064574715632786295)
                      ·
                        rfl

theorem cell23_5384684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 3].length) (baseStart_5384684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5384684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5384684 prefixEnd_5384684 := by exact prefixLift 5384684
  have htrace : WordTrace (prefixWord ++ tailWord_5384684) baseStart_5384684 baseEnd_5384684 := by
    simpa [prefixWord, tailWord_5384684, baseEnd_5384684] using wordTrace_append hprefix tailTrace_5384684
  have hstable : (prefixWord ++ tailWord_5384684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5384684).length < 2 ^ (prefixWord ++ tailWord_5384684).sum := by decide
  have hdescent : baseEnd_5384684 < baseStart_5384684 := by decide
  rcases family_descends (prefixWord ++ tailWord_5384684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5384685 : List Nat := [1, 5, 1, 3, 1, 3, 1, 1, 3, 2, 2]
def baseStart_5384685 : Nat := 118140960795 + 5384685 * 2 ^ 59
def prefixEnd_5384685 : Nat := 4983230072969 + 3 ^ 40 * 5384685 * 2
def baseEnd_5384685 : Nat := 2764931578055370128873791

theorem tailTrace_5384685 : CollatzResearch.WordTrace tailWord_5384685 prefixEnd_5384685 2764931578055370128873791 := by
  unfold tailWord_5384685
  simp only [CollatzResearch.WordTrace]
  refine ⟨196395596497213350827547509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130930397664808900551698339 196395596497213350827547509)
  ·
    refine ⟨18412087171613751640082579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 196395596497213350827547509 18412087171613751640082579)
    ·
      refine ⟨27618130757420627460123869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18412087171613751640082579 27618130757420627460123869)
      ·
        refine ⟨10356799034032735297546451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27618130757420627460123869 10356799034032735297546451)
        ·
          refine ⟨15535198551049102946319677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10356799034032735297546451 15535198551049102946319677)
          ·
            refine ⟨5825699456643413604869879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15535198551049102946319677 5825699456643413604869879)
            ·
              refine ⟨8738549184965120407304819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5825699456643413604869879 8738549184965120407304819)
              ·
                refine ⟨13107823777447680610957229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8738549184965120407304819 13107823777447680610957229)
                ·
                  refine ⟨4915433916542880229108961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13107823777447680610957229 4915433916542880229108961)
                  ·
                    refine ⟨3686575437407160171831721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4915433916542880229108961 3686575437407160171831721)
                    ·
                      refine ⟨2764931578055370128873791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3686575437407160171831721 2764931578055370128873791)
                      ·
                        rfl

theorem cell23_5384685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 1, 1, 3, 2, 2].length) (baseStart_5384685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5384685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5384685 prefixEnd_5384685 := by exact prefixLift 5384685
  have htrace : WordTrace (prefixWord ++ tailWord_5384685) baseStart_5384685 baseEnd_5384685 := by
    simpa [prefixWord, tailWord_5384685, baseEnd_5384685] using wordTrace_append hprefix tailTrace_5384685
  have hstable : (prefixWord ++ tailWord_5384685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5384685).length < 2 ^ (prefixWord ++ tailWord_5384685).sum := by decide
  have hdescent : baseEnd_5384685 < baseStart_5384685 := by decide
  rcases family_descends (prefixWord ++ tailWord_5384685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5384701 : List Nat := [1, 4, 1, 1, 1, 3, 3, 3, 2, 1, 3]
def baseStart_5384701 : Nat := 118140960795 + 5384701 * 2 ^ 59
def prefixEnd_5384701 : Nat := 4983230072969 + 3 ^ 40 * 5384701 * 2
def baseEnd_5384701 : Nat := 2764939793745842066273717

theorem tailTrace_5384701 : CollatzResearch.WordTrace tailWord_5384701 prefixEnd_5384701 2764939793745842066273717 := by
  unfold tailWord_5384701
  simp only [CollatzResearch.WordTrace]
  refine ⟨196396180065155385560129957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130930786710103590373419971 196396180065155385560129957)
  ·
    refine ⟨36824283762216634792524367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 196396180065155385560129957 36824283762216634792524367)
    ·
      refine ⟨55236425643324952188786551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36824283762216634792524367 55236425643324952188786551)
      ·
        refine ⟨82854638464987428283179827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55236425643324952188786551 82854638464987428283179827)
        ·
          refine ⟨124281957697481142424769741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82854638464987428283179827 124281957697481142424769741)
          ·
            refine ⟨46605734136555428409288653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 124281957697481142424769741 46605734136555428409288653)
            ·
              refine ⟨17477150301208285653483245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46605734136555428409288653 17477150301208285653483245)
              ·
                refine ⟨6553931362953107120056217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17477150301208285653483245 6553931362953107120056217)
                ·
                  refine ⟨4915448522214830340042163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6553931362953107120056217 4915448522214830340042163)
                  ·
                    refine ⟨7373172783322245510063245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4915448522214830340042163 7373172783322245510063245)
                    ·
                      refine ⟨2764939793745842066273717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7373172783322245510063245 2764939793745842066273717)
                      ·
                        rfl

theorem cell23_5384701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 3, 2, 1, 3].length) (baseStart_5384701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5384701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5384701 prefixEnd_5384701 := by exact prefixLift 5384701
  have htrace : WordTrace (prefixWord ++ tailWord_5384701) baseStart_5384701 baseEnd_5384701 := by
    simpa [prefixWord, tailWord_5384701, baseEnd_5384701] using wordTrace_append hprefix tailTrace_5384701
  have hstable : (prefixWord ++ tailWord_5384701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5384701).length < 2 ^ (prefixWord ++ tailWord_5384701).sum := by decide
  have hdescent : baseEnd_5384701 < baseStart_5384701 := by decide
  rcases family_descends (prefixWord ++ tailWord_5384701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5384741 : List Nat := [1, 3, 1, 2, 2, 1, 2, 3, 4, 2, 2]
def baseStart_5384741 : Nat := 118140960795 + 5384741 * 2 ^ 59
def prefixEnd_5384741 : Nat := 4983230072969 + 3 ^ 40 * 5384741 * 2
def baseEnd_5384741 : Nat := 2764960332972021909773533

theorem tailTrace_5384741 : CollatzResearch.WordTrace tailWord_5384741 prefixEnd_5384741 2764960332972021909773533 := by
  unfold tailWord_5384741
  simp only [CollatzResearch.WordTrace]
  refine ⟨196397638985010472391586077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130931759323340314927724051 196397638985010472391586077)
  ·
    refine ⟨73649114619378927146844779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 196397638985010472391586077 73649114619378927146844779)
    ·
      refine ⟨110473671929068390720267169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73649114619378927146844779 110473671929068390720267169)
      ·
        refine ⟨82855253946801293040200377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110473671929068390720267169 82855253946801293040200377)
        ·
          refine ⟨62141440460100969780150283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82855253946801293040200377 62141440460100969780150283)
          ·
            refine ⟨93212160690151454670225425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62141440460100969780150283 93212160690151454670225425)
            ·
              refine ⟨69909120517613591002669069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93212160690151454670225425 69909120517613591002669069)
              ·
                refine ⟨26215920194105096626000901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69909120517613591002669069 26215920194105096626000901)
                ·
                  refine ⟨4915485036394705617375169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26215920194105096626000901 4915485036394705617375169)
                  ·
                    refine ⟨3686613777296029213031377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4915485036394705617375169 3686613777296029213031377)
                    ·
                      refine ⟨2764960332972021909773533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3686613777296029213031377 2764960332972021909773533)
                      ·
                        rfl

theorem cell23_5384741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 3, 4, 2, 2].length) (baseStart_5384741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5384741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5384741 prefixEnd_5384741 := by exact prefixLift 5384741
  have htrace : WordTrace (prefixWord ++ tailWord_5384741) baseStart_5384741 baseEnd_5384741 := by
    simpa [prefixWord, tailWord_5384741, baseEnd_5384741] using wordTrace_append hprefix tailTrace_5384741
  have hstable : (prefixWord ++ tailWord_5384741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5384741).length < 2 ^ (prefixWord ++ tailWord_5384741).sum := by decide
  have hdescent : baseEnd_5384741 < baseStart_5384741 := by decide
  rcases family_descends (prefixWord ++ tailWord_5384741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5384758 : List Nat := [5, 1, 2, 1, 2, 1, 1, 3, 1, 4, 2]
def baseStart_5384758 : Nat := 118140960795 + 5384758 * 2 ^ 59
def prefixEnd_5384758 : Nat := 4983230072969 + 3 ^ 40 * 5384758 * 2
def baseEnd_5384758 : Nat := 2764969062143148343260955

theorem tailTrace_5384758 : CollatzResearch.WordTrace tailWord_5384758 prefixEnd_5384758 2764969062143148343260955 := by
  unfold tailWord_5384758
  simp only [CollatzResearch.WordTrace]
  refine ⟨12274891189121805268434683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 130932172683965922863303285 12274891189121805268434683)
  ·
    refine ⟨18412336783682707902652025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12274891189121805268434683 18412336783682707902652025)
    ·
      refine ⟨13809252587762030926989019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18412336783682707902652025 13809252587762030926989019)
      ·
        refine ⟨20713878881643046390483529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13809252587762030926989019 20713878881643046390483529)
        ·
          refine ⟨15535409161232284792862647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20713878881643046390483529 15535409161232284792862647)
          ·
            refine ⟨23303113741848427189293971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15535409161232284792862647 23303113741848427189293971)
            ·
              refine ⟨34954670612772640783940957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23303113741848427189293971 34954670612772640783940957)
              ·
                refine ⟨13108001479789740293977859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34954670612772640783940957 13108001479789740293977859)
                ·
                  refine ⟨19662002219684610440966789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13108001479789740293977859 19662002219684610440966789)
                  ·
                    refine ⟨3686625416190864457681273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19662002219684610440966789 3686625416190864457681273)
                    ·
                      refine ⟨2764969062143148343260955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3686625416190864457681273 2764969062143148343260955)
                      ·
                        rfl

theorem cell23_5384758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 3, 1, 4, 2].length) (baseStart_5384758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5384758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5384758 prefixEnd_5384758 := by exact prefixLift 5384758
  have htrace : WordTrace (prefixWord ++ tailWord_5384758) baseStart_5384758 baseEnd_5384758 := by
    simpa [prefixWord, tailWord_5384758, baseEnd_5384758] using wordTrace_append hprefix tailTrace_5384758
  have hstable : (prefixWord ++ tailWord_5384758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5384758).length < 2 ^ (prefixWord ++ tailWord_5384758).sum := by decide
  have hdescent : baseEnd_5384758 < baseStart_5384758 := by decide
  rcases family_descends (prefixWord ++ tailWord_5384758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5384764 : List Nat := [2, 2, 2, 2, 3, 2, 1, 2, 7]
def baseStart_5384764 : Nat := 118140960795 + 5384764 * 2 ^ 59
def prefixEnd_5384764 : Nat := 4983230072969 + 3 ^ 40 * 5384764 * 2
def baseEnd_5384764 : Nat := 307219127003008368865103

theorem tailTrace_5384764 : CollatzResearch.WordTrace tailWord_5384764 prefixEnd_5384764 307219127003008368865103 := by
  unfold tailWord_5384764
  simp only [CollatzResearch.WordTrace]
  refine ⟨98199238931963573659836673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130932318575951431546448897 98199238931963573659836673)
  ·
    refine ⟨73649429198972680244877505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98199238931963573659836673 73649429198972680244877505)
    ·
      refine ⟨55237071899229510183658129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73649429198972680244877505 55237071899229510183658129)
      ·
        refine ⟨41427803924422132637743597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55237071899229510183658129 41427803924422132637743597)
        ·
          refine ⟨15535426471658299739153849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41427803924422132637743597 15535426471658299739153849)
          ·
            refine ⟨11651569853743724804365387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15535426471658299739153849 11651569853743724804365387)
            ·
              refine ⟨17477354780615587206548081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11651569853743724804365387 17477354780615587206548081)
              ·
                refine ⟨13108016085461690404911061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17477354780615587206548081 13108016085461690404911061)
                ·
                  refine ⟨307219127003008368865103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13108016085461690404911061 307219127003008368865103)
                  ·
                    rfl

theorem cell23_5384764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 2, 7].length) (baseStart_5384764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5384764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5384764 prefixEnd_5384764 := by exact prefixLift 5384764
  have htrace : WordTrace (prefixWord ++ tailWord_5384764) baseStart_5384764 baseEnd_5384764 := by
    simpa [prefixWord, tailWord_5384764, baseEnd_5384764] using wordTrace_append hprefix tailTrace_5384764
  have hstable : (prefixWord ++ tailWord_5384764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5384764).length < 2 ^ (prefixWord ++ tailWord_5384764).sum := by decide
  have hdescent : baseEnd_5384764 < baseStart_5384764 := by decide
  rcases family_descends (prefixWord ++ tailWord_5384764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5384784 : List Nat := [2, 1, 1, 1, 1, 3, 2, 2, 1, 7, 2]
def baseStart_5384784 : Nat := 118140960795 + 5384784 * 2 ^ 59
def prefixEnd_5384784 : Nat := 4983230072969 + 3 ^ 40 * 5384784 * 2
def baseEnd_5384784 : Nat := 2764982412640165241535835

theorem tailTrace_5384784 : CollatzResearch.WordTrace tailWord_5384784 prefixEnd_5384784 2764982412640165241535835 := by
  unfold tailWord_5384784
  simp only [CollatzResearch.WordTrace]
  refine ⟨98199603661927345367700703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130932804882569793823600937 98199603661927345367700703)
  ·
    refine ⟨147299405492891018051551055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98199603661927345367700703 147299405492891018051551055)
    ·
      refine ⟨220949108239336527077326583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147299405492891018051551055 220949108239336527077326583)
      ·
        refine ⟨331423662359004790615989875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220949108239336527077326583 331423662359004790615989875)
        ·
          refine ⟨497135493538507185923984813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 331423662359004790615989875 497135493538507185923984813)
          ·
            refine ⟨186425810076940194721494305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 497135493538507185923984813 186425810076940194721494305)
            ·
              refine ⟨139819357557705146041120729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 186425810076940194721494305 139819357557705146041120729)
              ·
                refine ⟨104864518168278859530840547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 139819357557705146041120729 104864518168278859530840547)
                ·
                  refine ⟨157296777252418289296260821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 104864518168278859530840547 157296777252418289296260821)
                  ·
                    refine ⟨3686643216853553655381113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 157296777252418289296260821 3686643216853553655381113)
                    ·
                      refine ⟨2764982412640165241535835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3686643216853553655381113 2764982412640165241535835)
                      ·
                        rfl

theorem cell23_5384784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 1, 7, 2].length) (baseStart_5384784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5384784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5384784 prefixEnd_5384784 := by exact prefixLift 5384784
  have htrace : WordTrace (prefixWord ++ tailWord_5384784) baseStart_5384784 baseEnd_5384784 := by
    simpa [prefixWord, tailWord_5384784, baseEnd_5384784] using wordTrace_append hprefix tailTrace_5384784
  have hstable : (prefixWord ++ tailWord_5384784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5384784).length < 2 ^ (prefixWord ++ tailWord_5384784).sum := by decide
  have hdescent : baseEnd_5384784 < baseStart_5384784 := by decide
  rcases family_descends (prefixWord ++ tailWord_5384784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5384827 : List Nat := [1, 1, 1, 1, 1, 4, 2, 2, 1, 3, 6]
def baseStart_5384827 : Nat := 118140960795 + 5384827 * 2 ^ 59
def prefixEnd_5384827 : Nat := 4983230072969 + 3 ^ 40 * 5384827 * 2
def baseEnd_5384827 : Nat := 2765004492308308573298137

theorem tailTrace_5384827 : CollatzResearch.WordTrace tailWord_5384827 prefixEnd_5384827 2765004492308308573298137 := by
  unfold tailWord_5384827
  simp only [CollatzResearch.WordTrace]
  refine ⟨196400775662698909079216735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130933850441799272719477823 196400775662698909079216735)
  ·
    refine ⟨294601163494048363618825103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196400775662698909079216735 294601163494048363618825103)
    ·
      refine ⟨441901745241072545428237655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294601163494048363618825103 441901745241072545428237655)
      ·
        refine ⟨662852617861608818142356483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 441901745241072545428237655 662852617861608818142356483)
        ·
          refine ⟨994278926792413227213534725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 662852617861608818142356483 994278926792413227213534725)
          ·
            refine ⟨186427298773577480102537761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 994278926792413227213534725 186427298773577480102537761)
            ·
              refine ⟨139820474080183110076903321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 186427298773577480102537761 139820474080183110076903321)
              ·
                refine ⟨104865355560137332557677491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 139820474080183110076903321 104865355560137332557677491)
                ·
                  refine ⟨157298033340205998836516237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 104865355560137332557677491 157298033340205998836516237)
                  ·
                    refine ⟨58986762502577249563693589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 157298033340205998836516237 58986762502577249563693589)
                    ·
                      refine ⟨2765004492308308573298137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58986762502577249563693589 2765004492308308573298137)
                      ·
                        rfl

theorem cell23_5384827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 3, 6].length) (baseStart_5384827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5384827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5384827 prefixEnd_5384827 := by exact prefixLift 5384827
  have htrace : WordTrace (prefixWord ++ tailWord_5384827) baseStart_5384827 baseEnd_5384827 := by
    simpa [prefixWord, tailWord_5384827, baseEnd_5384827] using wordTrace_append hprefix tailTrace_5384827
  have hstable : (prefixWord ++ tailWord_5384827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5384827).length < 2 ^ (prefixWord ++ tailWord_5384827).sum := by decide
  have hdescent : baseEnd_5384827 < baseStart_5384827 := by decide
  rcases family_descends (prefixWord ++ tailWord_5384827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5384931 : List Nat := [1, 1, 1, 7, 1, 1, 1, 3, 1, 6]
def baseStart_5384931 : Nat := 118140960795 + 5384931 * 2 ^ 59
def prefixEnd_5384931 : Nat := 4983230072969 + 3 ^ 40 * 5384931 * 2
def baseEnd_5384931 : Nat := 921685964765458722132553

theorem tailTrace_5384931 : CollatzResearch.WordTrace tailWord_5384931 prefixEnd_5384931 921685964765458722132553 := by
  unfold tailWord_5384931
  simp only [CollatzResearch.WordTrace]
  refine ⟨196404568854322134841002647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130936379236214756560668431 196404568854322134841002647)
  ·
    refine ⟨294606853281483202261503971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196404568854322134841002647 294606853281483202261503971)
    ·
      refine ⟨441910279922224803392255957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294606853281483202261503971 441910279922224803392255957)
      ·
        refine ⟨10357272185677143829505999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 441910279922224803392255957 10357272185677143829505999)
        ·
          refine ⟨15535908278515715744258999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10357272185677143829505999 15535908278515715744258999)
          ·
            refine ⟨23303862417773573616388499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15535908278515715744258999 23303862417773573616388499)
            ·
              refine ⟨34955793626660360424582749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23303862417773573616388499 34955793626660360424582749)
              ·
                refine ⟨13108422609997635159218531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34955793626660360424582749 13108422609997635159218531)
                ·
                  refine ⟨19662633914996452738827797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13108422609997635159218531 19662633914996452738827797)
                  ·
                    refine ⟨921685964765458722132553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19662633914996452738827797 921685964765458722132553)
                    ·
                      rfl

theorem cell23_5384931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 3, 1, 6].length) (baseStart_5384931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5384931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5384931 prefixEnd_5384931 := by exact prefixLift 5384931
  have htrace : WordTrace (prefixWord ++ tailWord_5384931) baseStart_5384931 baseEnd_5384931 := by
    simpa [prefixWord, tailWord_5384931, baseEnd_5384931] using wordTrace_append hprefix tailTrace_5384931
  have hstable : (prefixWord ++ tailWord_5384931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5384931).length < 2 ^ (prefixWord ++ tailWord_5384931).sum := by decide
  have hdescent : baseEnd_5384931 < baseStart_5384931 := by decide
  rcases family_descends (prefixWord ++ tailWord_5384931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5384988 : List Nat := [2, 2, 3, 1, 1, 3, 3, 1, 1, 3, 3]
def baseStart_5384988 : Nat := 118140960795 + 5384988 * 2 ^ 59
def prefixEnd_5384988 : Nat := 4983230072969 + 3 ^ 40 * 5384988 * 2
def baseEnd_5384988 : Nat := 2765087162693682443384897

theorem tailTrace_5384988 : CollatzResearch.WordTrace tailWord_5384988 prefixEnd_5384988 2765087162693682443384897 := by
  unfold tailWord_5384988
  simp only [CollatzResearch.WordTrace]
  refine ⟨98203323907557816787913809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130937765210077089050551745 98203323907557816787913809)
  ·
    refine ⟨73652492930668362590935357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98203323907557816787913809 73652492930668362590935357)
    ·
      refine ⟨27619684849000635971600759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73652492930668362590935357 27619684849000635971600759)
      ·
        refine ⟨41429527273500953957401139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27619684849000635971600759 41429527273500953957401139)
        ·
          refine ⟨62144290910251430936101709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41429527273500953957401139 62144290910251430936101709)
          ·
            refine ⟨23304109091344286601038141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62144290910251430936101709 23304109091344286601038141)
            ·
              refine ⟨8739040909254107475389303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23304109091344286601038141 8739040909254107475389303)
              ·
                refine ⟨13108561363881161213083955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8739040909254107475389303 13108561363881161213083955)
                ·
                  refine ⟨19662842045821741819625933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13108561363881161213083955 19662842045821741819625933)
                  ·
                    refine ⟨7373565767183153182359725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19662842045821741819625933 7373565767183153182359725)
                    ·
                      refine ⟨2765087162693682443384897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7373565767183153182359725 2765087162693682443384897)
                      ·
                        rfl

theorem cell23_5384988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3, 1, 1, 3, 3].length) (baseStart_5384988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5384988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5384988 prefixEnd_5384988 := by exact prefixLift 5384988
  have htrace : WordTrace (prefixWord ++ tailWord_5384988) baseStart_5384988 baseEnd_5384988 := by
    simpa [prefixWord, tailWord_5384988, baseEnd_5384988] using wordTrace_append hprefix tailTrace_5384988
  have hstable : (prefixWord ++ tailWord_5384988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5384988).length < 2 ^ (prefixWord ++ tailWord_5384988).sum := by decide
  have hdescent : baseEnd_5384988 < baseStart_5384988 := by decide
  rcases family_descends (prefixWord ++ tailWord_5384988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5385006 : List Nat := [4, 1, 3, 2, 1, 3, 1, 3, 1, 2, 2]
def baseStart_5385006 : Nat := 118140960795 + 5385006 * 2 ^ 59
def prefixEnd_5385006 : Nat := 4983230072969 + 3 ^ 40 * 5385006 * 2
def baseEnd_5385006 : Nat := 2765096405345463372959815

theorem tailTrace_5385006 : CollatzResearch.WordTrace tailWord_5385006 prefixEnd_5385006 2765096405345463372959815 := by
  unfold tailWord_5385006
  simp only [CollatzResearch.WordTrace]
  refine ⟨24550913041131302831247859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130938202886033615099988581 24550913041131302831247859)
  ·
    refine ⟨36826369561696954246871789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24550913041131302831247859 36826369561696954246871789)
    ·
      refine ⟨13809888585636357842576921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36826369561696954246871789 13809888585636357842576921)
      ·
        refine ⟨10357416439227268381932691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13809888585636357842576921 10357416439227268381932691)
        ·
          refine ⟨15536124658840902572899037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10357416439227268381932691 15536124658840902572899037)
          ·
            refine ⟨5826046747065338464837139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15536124658840902572899037 5826046747065338464837139)
            ·
              refine ⟨8739070120598007697255709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5826046747065338464837139 8739070120598007697255709)
              ·
                refine ⟨3277151295224252886470891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8739070120598007697255709 3277151295224252886470891)
                ·
                  refine ⟨4915726942836379329706337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3277151295224252886470891 4915726942836379329706337)
                  ·
                    refine ⟨3686795207127284497279753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4915726942836379329706337 3686795207127284497279753)
                    ·
                      refine ⟨2765096405345463372959815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3686795207127284497279753 2765096405345463372959815)
                      ·
                        rfl

theorem cell23_5385006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 1, 3, 1, 2, 2].length) (baseStart_5385006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5385006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5385006 prefixEnd_5385006 := by exact prefixLift 5385006
  have htrace : WordTrace (prefixWord ++ tailWord_5385006) baseStart_5385006 baseEnd_5385006 := by
    simpa [prefixWord, tailWord_5385006, baseEnd_5385006] using wordTrace_append hprefix tailTrace_5385006
  have hstable : (prefixWord ++ tailWord_5385006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5385006).length < 2 ^ (prefixWord ++ tailWord_5385006).sum := by decide
  have hdescent : baseEnd_5385006 < baseStart_5385006 := by decide
  rcases family_descends (prefixWord ++ tailWord_5385006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5385031 : List Nat := [1, 1, 4, 1, 2, 1, 1, 3, 2, 4, 3]
def baseStart_5385031 : Nat := 118140960795 + 5385031 * 2 ^ 59
def prefixEnd_5385031 : Nat := 4983230072969 + 3 ^ 40 * 5385031 * 2
def baseEnd_5385031 : Nat := 2765109242361825775147199

theorem tailTrace_5385031 : CollatzResearch.WordTrace tailWord_5385031 prefixEnd_5385031 2765109242361825775147199 := by
  unfold tailWord_5385031
  simp only [CollatzResearch.WordTrace]
  refine ⟨196408216153959851919642947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130938810769306567946428631 196408216153959851919642947)
  ·
    refine ⟨294612324230939777879464421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196408216153959851919642947 294612324230939777879464421)
    ·
      refine ⟨55239810793301208352399579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 294612324230939777879464421 55239810793301208352399579)
      ·
        refine ⟨82859716189951812528599369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55239810793301208352399579 82859716189951812528599369)
        ·
          refine ⟨62144787142463859396449527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82859716189951812528599369 62144787142463859396449527)
          ·
            refine ⟨93217180713695789094674291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62144787142463859396449527 93217180713695789094674291)
            ·
              refine ⟨139825771070543683642011437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93217180713695789094674291 139825771070543683642011437)
              ·
                refine ⟨52434664151453881365754289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 139825771070543683642011437 52434664151453881365754289)
                ·
                  refine ⟨39325998113590411024315717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52434664151453881365754289 39325998113590411024315717)
                  ·
                    refine ⟨7373624646298202067059197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39325998113590411024315717 7373624646298202067059197)
                    ·
                      refine ⟨2765109242361825775147199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7373624646298202067059197 2765109242361825775147199)
                      ·
                        rfl

theorem cell23_5385031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 3, 2, 4, 3].length) (baseStart_5385031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5385031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5385031 prefixEnd_5385031 := by exact prefixLift 5385031
  have htrace : WordTrace (prefixWord ++ tailWord_5385031) baseStart_5385031 baseEnd_5385031 := by
    simpa [prefixWord, tailWord_5385031, baseEnd_5385031] using wordTrace_append hprefix tailTrace_5385031
  have hstable : (prefixWord ++ tailWord_5385031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5385031).length < 2 ^ (prefixWord ++ tailWord_5385031).sum := by decide
  have hdescent : baseEnd_5385031 < baseStart_5385031 := by decide
  rcases family_descends (prefixWord ++ tailWord_5385031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5385068 : List Nat := [2, 2, 1, 1, 4, 1, 2, 5, 5]
def baseStart_5385068 : Nat := 118140960795 + 5385068 * 2 ^ 59
def prefixEnd_5385068 : Nat := 4983230072969 + 3 ^ 40 * 5385068 * 2
def baseEnd_5385068 : Nat := 307236471238449125598281

theorem tailTrace_5385068 : CollatzResearch.WordTrace tailWord_5385068 prefixEnd_5385068 307236471238449125598281 := by
  unfold tailWord_5385068
  simp only [CollatzResearch.WordTrace]
  refine ⟨98204782827412903619369929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130939710436550538159159905 98204782827412903619369929)
  ·
    refine ⟨73653587120559677714527447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98204782827412903619369929 73653587120559677714527447)
    ·
      refine ⟨110480380680839516571791171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73653587120559677714527447 110480380680839516571791171)
      ·
        refine ⟨165720571021259274857686757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110480380680839516571791171 165720571021259274857686757)
        ·
          refine ⟨31072607066486114035816267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 165720571021259274857686757 31072607066486114035816267)
          ·
            refine ⟨46608910599729171053724401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31072607066486114035816267 46608910599729171053724401)
            ·
              refine ⟨34956682949796878290293301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46608910599729171053724401 34956682949796878290293301)
              ·
                refine ⟨3277189026543457339714997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34956682949796878290293301 3277189026543457339714997)
                ·
                  refine ⟨307236471238449125598281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3277189026543457339714997 307236471238449125598281)
                  ·
                    rfl

theorem cell23_5385068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 5, 5].length) (baseStart_5385068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5385068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5385068 prefixEnd_5385068 := by exact prefixLift 5385068
  have htrace : WordTrace (prefixWord ++ tailWord_5385068) baseStart_5385068 baseEnd_5385068 := by
    simpa [prefixWord, tailWord_5385068, baseEnd_5385068] using wordTrace_append hprefix tailTrace_5385068
  have hstable : (prefixWord ++ tailWord_5385068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5385068).length < 2 ^ (prefixWord ++ tailWord_5385068).sum := by decide
  have hdescent : baseEnd_5385068 < baseStart_5385068 := by decide
  rcases family_descends (prefixWord ++ tailWord_5385068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5385085 : List Nat := [1, 4, 1, 1, 2, 1, 6, 2, 5]
def baseStart_5385085 : Nat := 118140960795 + 5385085 * 2 ^ 59
def prefixEnd_5385085 : Nat := 4983230072969 + 3 ^ 40 * 5385085 * 2
def baseEnd_5385085 : Nat := 307237441146352062652439

theorem tailTrace_5385085 : CollatzResearch.WordTrace tailWord_5385085 prefixEnd_5385085 307237441146352062652439 := by
  unfold tailWord_5385085
  simp only [CollatzResearch.WordTrace]
  refine ⟨196410185695764219142108709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130940123797176146094739139 196410185695764219142108709)
  ·
    refine ⟨36826909817955791089145383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 196410185695764219142108709 36826909817955791089145383)
    ·
      refine ⟨55240364726933686633718075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36826909817955791089145383 55240364726933686633718075)
      ·
        refine ⟨82860547090400529950577113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55240364726933686633718075 82860547090400529950577113)
        ·
          refine ⟨62145410317800397462932835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82860547090400529950577113 62145410317800397462932835)
          ·
            refine ⟨93218115476700596194399253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62145410317800397462932835 93218115476700596194399253)
            ·
              refine ⟨4369599162970340446612465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 93218115476700596194399253 4369599162970340446612465)
              ·
                refine ⟨3277199372227755334959349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4369599162970340446612465 3277199372227755334959349)
                ·
                  refine ⟨307237441146352062652439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3277199372227755334959349 307237441146352062652439)
                  ·
                    rfl

theorem cell23_5385085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 6, 2, 5].length) (baseStart_5385085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5385085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5385085 prefixEnd_5385085 := by exact prefixLift 5385085
  have htrace : WordTrace (prefixWord ++ tailWord_5385085) baseStart_5385085 baseEnd_5385085 := by
    simpa [prefixWord, tailWord_5385085, baseEnd_5385085] using wordTrace_append hprefix tailTrace_5385085
  have hstable : (prefixWord ++ tailWord_5385085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5385085).length < 2 ^ (prefixWord ++ tailWord_5385085).sum := by decide
  have hdescent : baseEnd_5385085 < baseStart_5385085 := by decide
  rcases family_descends (prefixWord ++ tailWord_5385085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5385091 : List Nat := [1, 1, 1, 3, 4, 1, 1, 3, 1, 2, 5]
def baseStart_5385091 : Nat := 118140960795 + 5385091 * 2 ^ 59
def prefixEnd_5385091 : Nat := 4983230072969 + 3 ^ 40 * 5385091 * 2
def baseEnd_5385091 : Nat := 2765140051201095540396923

theorem tailTrace_5385091 : CollatzResearch.WordTrace tailWord_5385091 prefixEnd_5385091 2765140051201095540396923 := by
  unfold tailWord_5385091
  simp only [CollatzResearch.WordTrace]
  refine ⟨196410404533742482166827127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130940269689161654777884751 196410404533742482166827127)
  ·
    refine ⟨294615606800613723250240691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196410404533742482166827127 294615606800613723250240691)
    ·
      refine ⟨441923410200920584875361037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294615606800613723250240691 441923410200920584875361037)
      ·
        refine ⟨165721278825345219328260389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 441923410200920584875361037 165721278825345219328260389)
        ·
          refine ⟨31072739779752228624048823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 165721278825345219328260389 31072739779752228624048823)
          ·
            refine ⟨46609109669628342936073235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31072739779752228624048823 46609109669628342936073235)
            ·
              refine ⟨69913664504442514404109853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46609109669628342936073235 69913664504442514404109853)
              ·
                refine ⟨26217624189165942901541195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69913664504442514404109853 26217624189165942901541195)
                ·
                  refine ⟨39326436283748914352311793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26217624189165942901541195 39326436283748914352311793)
                  ·
                    refine ⟨29494827212811685764233845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39326436283748914352311793 29494827212811685764233845)
                    ·
                      refine ⟨2765140051201095540396923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29494827212811685764233845 2765140051201095540396923)
                      ·
                        rfl

theorem cell23_5385091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 3, 1, 2, 5].length) (baseStart_5385091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5385091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5385091 prefixEnd_5385091 := by exact prefixLift 5385091
  have htrace : WordTrace (prefixWord ++ tailWord_5385091) baseStart_5385091 baseEnd_5385091 := by
    simpa [prefixWord, tailWord_5385091, baseEnd_5385091] using wordTrace_append hprefix tailTrace_5385091
  have hstable : (prefixWord ++ tailWord_5385091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5385091).length < 2 ^ (prefixWord ++ tailWord_5385091).sum := by decide
  have hdescent : baseEnd_5385091 < baseStart_5385091 := by decide
  rcases family_descends (prefixWord ++ tailWord_5385091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5385145 : List Nat := [1, 2, 1, 4, 2, 3, 2, 1, 3, 4]
def baseStart_5385145 : Nat := 118140960795 + 5385145 * 2 ^ 59
def prefixEnd_5385145 : Nat := 4983230072969 + 3 ^ 40 * 5385145 * 2
def baseEnd_5385145 : Nat := 921722593052146109707225

theorem tailTrace_5385145 : CollatzResearch.WordTrace tailWord_5385145 prefixEnd_5385145 921722593052146109707225 := by
  unfold tailWord_5385145
  simp only [CollatzResearch.WordTrace]
  refine ⟨196412374075546849389292889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130941582717031232926195259 196412374075546849389292889)
  ·
    refine ⟨147309280556660137041969667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196412374075546849389292889 147309280556660137041969667)
    ·
      refine ⟨220963920834990205562954501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147309280556660137041969667 220963920834990205562954501)
      ·
        refine ⟨41430735156560663543053969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 220963920834990205562954501 41430735156560663543053969)
        ·
          refine ⟨31073051367420497657290477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41430735156560663543053969 31073051367420497657290477)
          ·
            refine ⟨11652394262782686621483929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31073051367420497657290477 11652394262782686621483929)
            ·
              refine ⟨8739295697087014966112947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11652394262782686621483929 8739295697087014966112947)
              ·
                refine ⟨13108943545630522449169421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8739295697087014966112947 13108943545630522449169421)
                ·
                  refine ⟨4915853829611445918438533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13108943545630522449169421 4915853829611445918438533)
                  ·
                    refine ⟨921722593052146109707225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4915853829611445918438533 921722593052146109707225)
                    ·
                      rfl

theorem cell23_5385145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2, 1, 3, 4].length) (baseStart_5385145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5385145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5385145 prefixEnd_5385145 := by exact prefixLift 5385145
  have htrace : WordTrace (prefixWord ++ tailWord_5385145) baseStart_5385145 baseEnd_5385145 := by
    simpa [prefixWord, tailWord_5385145, baseEnd_5385145] using wordTrace_append hprefix tailTrace_5385145
  have hstable : (prefixWord ++ tailWord_5385145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5385145).length < 2 ^ (prefixWord ++ tailWord_5385145).sum := by decide
  have hdescent : baseEnd_5385145 < baseStart_5385145 := by decide
  rcases family_descends (prefixWord ++ tailWord_5385145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5385208 : List Nat := [2, 1, 2, 1, 1, 3, 1, 4, 3, 1, 4]
def baseStart_5385208 : Nat := 118140960795 + 5385208 * 2 ^ 59
def prefixEnd_5385208 : Nat := 4983230072969 + 3 ^ 40 * 5385208 * 2
def baseEnd_5385208 : Nat := 2765200128437671582633885

theorem tailTrace_5385208 : CollatzResearch.WordTrace tailWord_5385208 prefixEnd_5385208 2765200128437671582633885 := by
  unfold tailWord_5385208
  simp only [CollatzResearch.WordTrace]
  refine ⟨98207335937159305574418139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130943114582879074099224185 98207335937159305574418139)
  ·
    refine ⟨147311003905738958361627209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98207335937159305574418139 147311003905738958361627209)
    ·
      refine ⟨110483252929304218771220407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147311003905738958361627209 110483252929304218771220407)
      ·
        refine ⟨165724879393956328156830611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110483252929304218771220407 165724879393956328156830611)
        ·
          refine ⟨248587319090934492235245917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165724879393956328156830611 248587319090934492235245917)
          ·
            refine ⟨93220244659100434588217219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 248587319090934492235245917 93220244659100434588217219)
            ·
              refine ⟨139830366988650651882325829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93220244659100434588217219 139830366988650651882325829)
              ·
                refine ⟨26218193810371997227936093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 139830366988650651882325829 26218193810371997227936093)
                ·
                  refine ⟨9831822678889498960476035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26218193810371997227936093 9831822678889498960476035)
                  ·
                    refine ⟨14747734018334248440714053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9831822678889498960476035 14747734018334248440714053)
                    ·
                      refine ⟨2765200128437671582633885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14747734018334248440714053 2765200128437671582633885)
                      ·
                        rfl

theorem cell23_5385208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 4, 3, 1, 4].length) (baseStart_5385208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5385208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5385208 prefixEnd_5385208 := by exact prefixLift 5385208
  have htrace : WordTrace (prefixWord ++ tailWord_5385208) baseStart_5385208 baseEnd_5385208 := by
    simpa [prefixWord, tailWord_5385208, baseEnd_5385208] using wordTrace_append hprefix tailTrace_5385208
  have hstable : (prefixWord ++ tailWord_5385208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5385208).length < 2 ^ (prefixWord ++ tailWord_5385208).sum := by decide
  have hdescent : baseEnd_5385208 < baseStart_5385208 := by decide
  rcases family_descends (prefixWord ++ tailWord_5385208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5385242 : List Nat := [3, 1, 1, 3, 1, 2, 5, 1, 1, 1, 4]
def baseStart_5385242 : Nat := 118140960795 + 5385242 * 2 ^ 59
def prefixEnd_5385242 : Nat := 4983230072969 + 3 ^ 40 * 5385242 * 2
def baseEnd_5385242 : Nat := 2765217586779924449608729

theorem tailTrace_5385242 : CollatzResearch.WordTrace tailWord_5385242 prefixEnd_5385242 2765217586779924449608729 := by
  unfold tailWord_5385242
  simp only [CollatzResearch.WordTrace]
  refine ⟨49103977989048858738893495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130943941304130289970382653 49103977989048858738893495)
  ·
    refine ⟨73655966983573288108340243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49103977989048858738893495 73655966983573288108340243)
    ·
      refine ⟨110483950475359932162510365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73655966983573288108340243 110483950475359932162510365)
      ·
        refine ⟨41431481428259974560941387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110483950475359932162510365 41431481428259974560941387)
        ·
          refine ⟨62147222142389961841412081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41431481428259974560941387 62147222142389961841412081)
          ·
            refine ⟨46610416606792471381059061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62147222142389961841412081 46610416606792471381059061)
            ·
              refine ⟨4369726556886794191974287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46610416606792471381059061 4369726556886794191974287)
              ·
                refine ⟨6554589835330191287961431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4369726556886794191974287 6554589835330191287961431)
                ·
                  refine ⟨9831884752995286931942147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6554589835330191287961431 9831884752995286931942147)
                  ·
                    refine ⟨14747827129492930397913221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9831884752995286931942147 14747827129492930397913221)
                    ·
                      refine ⟨2765217586779924449608729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14747827129492930397913221 2765217586779924449608729)
                      ·
                        rfl

theorem cell23_5385242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 5, 1, 1, 1, 4].length) (baseStart_5385242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5385242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5385242 prefixEnd_5385242 := by exact prefixLift 5385242
  have htrace : WordTrace (prefixWord ++ tailWord_5385242) baseStart_5385242 baseEnd_5385242 := by
    simpa [prefixWord, tailWord_5385242, baseEnd_5385242] using wordTrace_append hprefix tailTrace_5385242
  have hstable : (prefixWord ++ tailWord_5385242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5385242).length < 2 ^ (prefixWord ++ tailWord_5385242).sum := by decide
  have hdescent : baseEnd_5385242 < baseStart_5385242 := by decide
  rcases family_descends (prefixWord ++ tailWord_5385242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5385248 : List Nat := [2, 1, 1, 7, 12]
def baseStart_5385248 : Nat := 118140960795 + 5385248 * 2 ^ 59
def prefixEnd_5385248 : Nat := 4983230072969 + 3 ^ 40 * 5385248 * 2
def baseEnd_5385248 : Nat := 3793169640142457374669

theorem tailTrace_5385248 : CollatzResearch.WordTrace tailWord_5385248 prefixEnd_5385248 3793169640142457374669 := by
  unfold tailWord_5385248
  simp only [CollatzResearch.WordTrace]
  refine ⟨98208065397086848990146199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130944087196115798653528265 98208065397086848990146199)
  ·
    refine ⟨147312098095630273485219299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98208065397086848990146199 147312098095630273485219299)
    ·
      refine ⟨220968147143445410227828949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147312098095630273485219299 220968147143445410227828949)
      ·
        refine ⟨5178940948674501802214741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 220968147143445410227828949 5178940948674501802214741)
        ·
          refine ⟨3793169640142457374669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 5178940948674501802214741 3793169640142457374669)
          ·
            rfl

theorem cell23_5385248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 12].length) (baseStart_5385248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5385248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5385248 prefixEnd_5385248 := by exact prefixLift 5385248
  have htrace : WordTrace (prefixWord ++ tailWord_5385248) baseStart_5385248 baseEnd_5385248 := by
    simpa [prefixWord, tailWord_5385248, baseEnd_5385248] using wordTrace_append hprefix tailTrace_5385248
  have hstable : (prefixWord ++ tailWord_5385248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5385248).length < 2 ^ (prefixWord ++ tailWord_5385248).sum := by decide
  have hdescent : baseEnd_5385248 < baseStart_5385248 := by decide
  rcases family_descends (prefixWord ++ tailWord_5385248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5385252 : List Nat := [2, 3, 1, 4, 1, 1, 1, 4, 2, 4]
def baseStart_5385252 : Nat := 118140960795 + 5385252 * 2 ^ 59
def prefixEnd_5385252 : Nat := 4983230072969 + 3 ^ 40 * 5385252 * 2
def baseEnd_5385252 : Nat := 921740907195489803494561

theorem tailTrace_5385252 : CollatzResearch.WordTrace tailWord_5385252 prefixEnd_5385252 921740907195489803494561 := by
  unfold tailWord_5385252
  simp only [CollatzResearch.WordTrace]
  refine ⟨98208138343079603331719005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130944184457439471108958673 98208138343079603331719005)
  ·
    refine ⟨36828051878654851249394627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98208138343079603331719005 36828051878654851249394627)
    ·
      refine ⟨55242077817982276874091941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36828051878654851249394627 55242077817982276874091941)
      ·
        refine ⟨10357889590871676913892239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55242077817982276874091941 10357889590871676913892239)
        ·
          refine ⟨15536834386307515370838359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10357889590871676913892239 15536834386307515370838359)
          ·
            refine ⟨23305251579461273056257539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15536834386307515370838359 23305251579461273056257539)
            ·
              refine ⟨34957877369191909584386309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23305251579461273056257539 34957877369191909584386309)
              ·
                refine ⟨6554602006723483047072433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34957877369191909584386309 6554602006723483047072433)
                ·
                  refine ⟨4915951505042612285304325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6554602006723483047072433 4915951505042612285304325)
                  ·
                    refine ⟨921740907195489803494561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4915951505042612285304325 921740907195489803494561)
                    ·
                      rfl

theorem cell23_5385252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 4, 2, 4].length) (baseStart_5385252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5385252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5385252 prefixEnd_5385252 := by exact prefixLift 5385252
  have htrace : WordTrace (prefixWord ++ tailWord_5385252) baseStart_5385252 baseEnd_5385252 := by
    simpa [prefixWord, tailWord_5385252, baseEnd_5385252] using wordTrace_append hprefix tailTrace_5385252
  have hstable : (prefixWord ++ tailWord_5385252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5385252).length < 2 ^ (prefixWord ++ tailWord_5385252).sum := by decide
  have hdescent : baseEnd_5385252 < baseStart_5385252 := by decide
  rcases family_descends (prefixWord ++ tailWord_5385252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5385259 : List Nat := [1, 1, 1, 1, 2, 1, 7, 4, 1, 2, 2]
def baseStart_5385259 : Nat := 118140960795 + 5385259 * 2 ^ 59
def prefixEnd_5385259 : Nat := 4983230072969 + 3 ^ 40 * 5385259 * 2
def baseEnd_5385259 : Nat := 2765226315951050883096151

theorem tailTrace_5385259 : CollatzResearch.WordTrace tailWord_5385259 prefixEnd_5385259 2765226315951050883096151 := by
  unfold tailWord_5385259
  simp only [CollatzResearch.WordTrace]
  refine ⟨196416531997133846858942831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130944354664755897905961887 196416531997133846858942831)
  ·
    refine ⟨294624797995700770288414247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196416531997133846858942831 294624797995700770288414247)
    ·
      refine ⟨441937196993551155432621371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294624797995700770288414247 441937196993551155432621371)
      ·
        refine ⟨662905795490326733148932057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 441937196993551155432621371 662905795490326733148932057)
        ·
          refine ⟨497179346617745049861699043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 662905795490326733148932057 497179346617745049861699043)
          ·
            refine ⟨745769019926617574792548565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 497179346617745049861699043 745769019926617574792548565)
            ·
              refine ⟨17478961404530099409200357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 745769019926617574792548565 17478961404530099409200357)
              ·
                refine ⟨3277305263349393639225067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17478961404530099409200357 3277305263349393639225067)
                ·
                  refine ⟨4915957895024090458837601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3277305263349393639225067 4915957895024090458837601)
                  ·
                    refine ⟨3686968421268067844128201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4915957895024090458837601 3686968421268067844128201)
                    ·
                      refine ⟨2765226315951050883096151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3686968421268067844128201 2765226315951050883096151)
                      ·
                        rfl

theorem cell23_5385259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 4, 1, 2, 2].length) (baseStart_5385259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5385259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5385259 prefixEnd_5385259 := by exact prefixLift 5385259
  have htrace : WordTrace (prefixWord ++ tailWord_5385259) baseStart_5385259 baseEnd_5385259 := by
    simpa [prefixWord, tailWord_5385259, baseEnd_5385259] using wordTrace_append hprefix tailTrace_5385259
  have hstable : (prefixWord ++ tailWord_5385259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5385259).length < 2 ^ (prefixWord ++ tailWord_5385259).sum := by decide
  have hdescent : baseEnd_5385259 < baseStart_5385259 := by decide
  rcases family_descends (prefixWord ++ tailWord_5385259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5385288 : List Nat := [2, 1, 3, 1, 1, 1, 4, 1, 2, 2, 5]
def baseStart_5385288 : Nat := 118140960795 + 5385288 * 2 ^ 59
def prefixEnd_5385288 : Nat := 4983230072969 + 3 ^ 40 * 5385288 * 2
def baseEnd_5385288 : Nat := 2765241206890031269633517

theorem tailTrace_5385288 : CollatzResearch.WordTrace tailWord_5385288 prefixEnd_5385288 2765241206890031269633517 := by
  unfold tailWord_5385288
  simp only [CollatzResearch.WordTrace]
  refine ⟨98208794857014392405874259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130945059809352523207832345 98208794857014392405874259)
  ·
    refine ⟨147313192285521588608811389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98208794857014392405874259 147313192285521588608811389)
    ·
      refine ⟨55242447107070595728304271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147313192285521588608811389 55242447107070595728304271)
      ·
        refine ⟨82863670660605893592456407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55242447107070595728304271 82863670660605893592456407)
        ·
          refine ⟨124295505990908840388684611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82863670660605893592456407 124295505990908840388684611)
          ·
            refine ⟨186443258986363260583026917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124295505990908840388684611 186443258986363260583026917)
            ·
              refine ⟨34958111059943111359317547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 186443258986363260583026917 34958111059943111359317547)
              ·
                refine ⟨52437166589914667038976321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34958111059943111359317547 52437166589914667038976321)
                ·
                  refine ⟨39327874942436000279232241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52437166589914667038976321 39327874942436000279232241)
                  ·
                    refine ⟨29495906206827000209424181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39327874942436000279232241 29495906206827000209424181)
                    ·
                      refine ⟨2765241206890031269633517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29495906206827000209424181 2765241206890031269633517)
                      ·
                        rfl

theorem cell23_5385288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 1, 2, 2, 5].length) (baseStart_5385288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5385288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5385288 prefixEnd_5385288 := by exact prefixLift 5385288
  have htrace : WordTrace (prefixWord ++ tailWord_5385288) baseStart_5385288 baseEnd_5385288 := by
    simpa [prefixWord, tailWord_5385288, baseEnd_5385288] using wordTrace_append hprefix tailTrace_5385288
  have hstable : (prefixWord ++ tailWord_5385288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5385288).length < 2 ^ (prefixWord ++ tailWord_5385288).sum := by decide
  have hdescent : baseEnd_5385288 < baseStart_5385288 := by decide
  rcases family_descends (prefixWord ++ tailWord_5385288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5385293 : List Nat := [1, 6, 1, 1, 1, 3, 2, 3, 1, 2, 2]
def baseStart_5385293 : Nat := 118140960795 + 5385293 * 2 ^ 59
def prefixEnd_5385293 : Nat := 4983230072969 + 3 ^ 40 * 5385293 * 2
def baseEnd_5385293 : Nat := 2765243774293303750070995

theorem tailTrace_5385293 : CollatzResearch.WordTrace tailWord_5385293 prefixEnd_5385293 2765243774293303750070995 := by
  unfold tailWord_5385293
  simp only [CollatzResearch.WordTrace]
  refine ⟨196417772079010670665680533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130945181386007113777120355 196417772079010670665680533)
  ·
    refine ⟨9207083066203625187453775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 196417772079010670665680533 9207083066203625187453775)
    ·
      refine ⟨13810624599305437781180663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9207083066203625187453775 13810624599305437781180663)
      ·
        refine ⟨20715936898958156671770995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13810624599305437781180663 20715936898958156671770995)
        ·
          refine ⟨31073905348437235007656493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20715936898958156671770995 31073905348437235007656493)
          ·
            refine ⟨11652714505663963127871185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31073905348437235007656493 11652714505663963127871185)
            ·
              refine ⟨8739535879247972345903389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11652714505663963127871185 8739535879247972345903389)
              ·
                refine ⟨3277325954717989629713771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8739535879247972345903389 3277325954717989629713771)
                ·
                  refine ⟨4915988932076984444570657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3277325954717989629713771 4915988932076984444570657)
                  ·
                    refine ⟨3686991699057738333427993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4915988932076984444570657 3686991699057738333427993)
                    ·
                      refine ⟨2765243774293303750070995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3686991699057738333427993 2765243774293303750070995)
                      ·
                        rfl

theorem cell23_5385293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 2, 3, 1, 2, 2].length) (baseStart_5385293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5385293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5385293 prefixEnd_5385293 := by exact prefixLift 5385293
  have htrace : WordTrace (prefixWord ++ tailWord_5385293) baseStart_5385293 baseEnd_5385293 := by
    simpa [prefixWord, tailWord_5385293, baseEnd_5385293] using wordTrace_append hprefix tailTrace_5385293
  have hstable : (prefixWord ++ tailWord_5385293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5385293).length < 2 ^ (prefixWord ++ tailWord_5385293).sum := by decide
  have hdescent : baseEnd_5385293 < baseStart_5385293 := by decide
  rcases family_descends (prefixWord ++ tailWord_5385293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5385310 : List Nat := [4, 4, 1, 1, 1, 1, 2, 4, 1, 2, 2]
def baseStart_5385310 : Nat := 118140960795 + 5385310 * 2 ^ 59
def prefixEnd_5385310 : Nat := 4983230072969 + 3 ^ 40 * 5385310 * 2
def baseEnd_5385310 : Nat := 2765252503464430183558417

theorem tailTrace_5385310 : CollatzResearch.WordTrace tailWord_5385310 prefixEnd_5385310 2765252503464430183558417 := by
  unfold tailWord_5385310
  simp only [CollatzResearch.WordTrace]
  refine ⟨24552299014993635321131173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130945594746632721712699589 24552299014993635321131173)
  ·
    refine ⟨4603556065311306622712095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24552299014993635321131173 4603556065311306622712095)
    ·
      refine ⟨6905334097966959934068143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4603556065311306622712095 6905334097966959934068143)
      ·
        refine ⟨10358001146950439901102215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6905334097966959934068143 10358001146950439901102215)
        ·
          refine ⟨15537001720425659851653323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10358001146950439901102215 15537001720425659851653323)
          ·
            refine ⟨23305502580638489777479985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15537001720425659851653323 23305502580638489777479985)
            ·
              refine ⟨17479126935478867333109989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23305502580638489777479985 17479126935478867333109989)
              ·
                refine ⟨3277336300402287624958123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17479126935478867333109989 3277336300402287624958123)
                ·
                  refine ⟨4916004450603431437437185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3277336300402287624958123 4916004450603431437437185)
                  ·
                    refine ⟨3687003337952573578077889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4916004450603431437437185 3687003337952573578077889)
                    ·
                      refine ⟨2765252503464430183558417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3687003337952573578077889 2765252503464430183558417)
                      ·
                        rfl

theorem cell23_5385310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 4, 1, 2, 2].length) (baseStart_5385310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5385310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5385310 prefixEnd_5385310 := by exact prefixLift 5385310
  have htrace : WordTrace (prefixWord ++ tailWord_5385310) baseStart_5385310 baseEnd_5385310 := by
    simpa [prefixWord, tailWord_5385310, baseEnd_5385310] using wordTrace_append hprefix tailTrace_5385310
  have hstable : (prefixWord ++ tailWord_5385310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5385310).length < 2 ^ (prefixWord ++ tailWord_5385310).sum := by decide
  have hdescent : baseEnd_5385310 < baseStart_5385310 := by decide
  rcases family_descends (prefixWord ++ tailWord_5385310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5385325 : List Nat := [1, 5, 1, 1, 2, 2, 2, 1, 2, 6]
def baseStart_5385325 : Nat := 118140960795 + 5385325 * 2 ^ 59
def prefixEnd_5385325 : Nat := 4983230072969 + 3 ^ 40 * 5385325 * 2
def baseEnd_5385325 : Nat := 921753401891415874956949

theorem tailTrace_5385325 : CollatzResearch.WordTrace tailWord_5385325 prefixEnd_5385325 921753401891415874956949 := by
  unfold tailWord_5385325
  simp only [CollatzResearch.WordTrace]
  refine ⟨196418939214894740130845429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130945959476596493420563619 196418939214894740130845429)
  ·
    refine ⟨18414275551396381887266759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 196418939214894740130845429 18414275551396381887266759)
    ·
      refine ⟨27621413327094572830900139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18414275551396381887266759 27621413327094572830900139)
      ·
        refine ⟨41432119990641859246350209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27621413327094572830900139 41432119990641859246350209)
        ·
          refine ⟨31074089992981394434762657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41432119990641859246350209 31074089992981394434762657)
          ·
            refine ⟨23305567494736045826071993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31074089992981394434762657 23305567494736045826071993)
            ·
              refine ⟨17479175621052034369553995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23305567494736045826071993 17479175621052034369553995)
              ·
                refine ⟨26218763431578051554330993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17479175621052034369553995 26218763431578051554330993)
                ·
                  refine ⟨19664072573683538665748245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26218763431578051554330993 19664072573683538665748245)
                  ·
                    refine ⟨921753401891415874956949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19664072573683538665748245 921753401891415874956949)
                    ·
                      rfl

theorem cell23_5385325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 1, 2, 6].length) (baseStart_5385325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5385325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5385325 prefixEnd_5385325 := by exact prefixLift 5385325
  have htrace : WordTrace (prefixWord ++ tailWord_5385325) baseStart_5385325 baseEnd_5385325 := by
    simpa [prefixWord, tailWord_5385325, baseEnd_5385325] using wordTrace_append hprefix tailTrace_5385325
  have hstable : (prefixWord ++ tailWord_5385325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5385325).length < 2 ^ (prefixWord ++ tailWord_5385325).sum := by decide
  have hdescent : baseEnd_5385325 < baseStart_5385325 := by decide
  rcases family_descends (prefixWord ++ tailWord_5385325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5385326 : List Nat := [4, 1, 2, 2, 1, 3, 3, 1, 2, 1, 3]
def baseStart_5385326 : Nat := 118140960795 + 5385326 * 2 ^ 59
def prefixEnd_5385326 : Nat := 4983230072969 + 3 ^ 40 * 5385326 * 2
def baseEnd_5385326 : Nat := 2765260719154902120958343

theorem tailTrace_5385326 : CollatzResearch.WordTrace tailWord_5385326 prefixEnd_5385326 2765260719154902120958343 := by
  unfold tailWord_5385326
  simp only [CollatzResearch.WordTrace]
  refine ⟨24552371960986389662703979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130945983791927411534421221 24552371960986389662703979)
  ·
    refine ⟨36828557941479584494055969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24552371960986389662703979 36828557941479584494055969)
    ·
      refine ⟨27621418456109688370541977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36828557941479584494055969 27621418456109688370541977)
      ·
        refine ⟨20716063842082266277906483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27621418456109688370541977 20716063842082266277906483)
        ·
          refine ⟨31074095763123399416859725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20716063842082266277906483 31074095763123399416859725)
          ·
            refine ⟨11652785911171274781322397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31074095763123399416859725 11652785911171274781322397)
            ·
              refine ⟨4369794716689228042995899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11652785911171274781322397 4369794716689228042995899)
              ·
                refine ⟨6554692075033842064493849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4369794716689228042995899 6554692075033842064493849)
                ·
                  refine ⟨4916019056275381548370387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6554692075033842064493849 4916019056275381548370387)
                  ·
                    refine ⟨7374028584413072322555581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4916019056275381548370387 7374028584413072322555581)
                    ·
                      refine ⟨2765260719154902120958343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7374028584413072322555581 2765260719154902120958343)
                      ·
                        rfl

theorem cell23_5385326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 3, 1, 2, 1, 3].length) (baseStart_5385326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5385326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5385326 prefixEnd_5385326 := by exact prefixLift 5385326
  have htrace : WordTrace (prefixWord ++ tailWord_5385326) baseStart_5385326 baseEnd_5385326 := by
    simpa [prefixWord, tailWord_5385326, baseEnd_5385326] using wordTrace_append hprefix tailTrace_5385326
  have hstable : (prefixWord ++ tailWord_5385326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5385326).length < 2 ^ (prefixWord ++ tailWord_5385326).sum := by decide
  have hdescent : baseEnd_5385326 < baseStart_5385326 := by decide
  rcases family_descends (prefixWord ++ tailWord_5385326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5385352 : List Nat := [2, 1, 3, 4, 2, 1, 1, 1, 2, 1, 5]
def baseStart_5385352 : Nat := 118140960795 + 5385352 * 2 ^ 59
def prefixEnd_5385352 : Nat := 4983230072969 + 3 ^ 40 * 5385352 * 2
def baseEnd_5385352 : Nat := 2765274069651919019233223

theorem tailTrace_5385352 : CollatzResearch.WordTrace tailWord_5385352 prefixEnd_5385352 2765274069651919019233223 := by
  unfold tailWord_5385352
  simp only [CollatzResearch.WordTrace]
  refine ⟨98209961992898461871039155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130946615990531282494718873 98209961992898461871039155)
  ·
    refine ⟨147314942989347692806558733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98209961992898461871039155 147314942989347692806558733)
    ·
      refine ⟨55243103621005384802459525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147314942989347692806558733 55243103621005384802459525)
      ·
        refine ⟨10358081928938509650461161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55243103621005384802459525 10358081928938509650461161)
        ·
          refine ⟨7768561446703882237845871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10358081928938509650461161 7768561446703882237845871)
          ·
            refine ⟨11652842170055823356768807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7768561446703882237845871 11652842170055823356768807)
            ·
              refine ⟨17479263255083735035153211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11652842170055823356768807 17479263255083735035153211)
              ·
                refine ⟨26218894882625602552729817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17479263255083735035153211 26218894882625602552729817)
                ·
                  refine ⟨19664171161969201914547363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26218894882625602552729817 19664171161969201914547363)
                  ·
                    refine ⟨29496256742953802871821045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19664171161969201914547363 29496256742953802871821045)
                    ·
                      refine ⟨2765274069651919019233223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29496256742953802871821045 2765274069651919019233223)
                      ·
                        rfl

theorem cell23_5385352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_5385352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5385352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5385352 prefixEnd_5385352 := by exact prefixLift 5385352
  have htrace : WordTrace (prefixWord ++ tailWord_5385352) baseStart_5385352 baseEnd_5385352 := by
    simpa [prefixWord, tailWord_5385352, baseEnd_5385352] using wordTrace_append hprefix tailTrace_5385352
  have hstable : (prefixWord ++ tailWord_5385352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5385352).length < 2 ^ (prefixWord ++ tailWord_5385352).sum := by decide
  have hdescent : baseEnd_5385352 < baseStart_5385352 := by decide
  rcases family_descends (prefixWord ++ tailWord_5385352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5385365 : List Nat := [1, 3, 2, 1, 1, 1, 2, 4, 2, 3, 3]
def baseStart_5385365 : Nat := 118140960795 + 5385365 * 2 ^ 59
def prefixEnd_5385365 : Nat := 4983230072969 + 3 ^ 40 * 5385365 * 2
def baseEnd_5385365 : Nat := 2765280744900427468370663

theorem tailTrace_5385365 : CollatzResearch.WordTrace tailWord_5385365 prefixEnd_5385365 2765280744900427468370663 := by
  unfold tailWord_5385365
  simp only [CollatzResearch.WordTrace]
  refine ⟨196420398134749826962301549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130946932089833217974867699 196420398134749826962301549)
  ·
    refine ⟨73657649300531185110863081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 196420398134749826962301549 73657649300531185110863081)
    ·
      refine ⟨55243236975398388833147311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73657649300531185110863081 55243236975398388833147311)
      ·
        refine ⟨82864855463097583249720967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55243236975398388833147311 82864855463097583249720967)
        ·
          refine ⟨124297283194646374874581451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82864855463097583249720967 124297283194646374874581451)
          ·
            refine ⟨186445924791969562311872177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124297283194646374874581451 186445924791969562311872177)
            ·
              refine ⟨139834443593977171733904133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 186445924791969562311872177 139834443593977171733904133)
              ·
                refine ⟨26218958173870719700107025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 139834443593977171733904133 26218958173870719700107025)
                ·
                  refine ⟨19664218630403039775080269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26218958173870719700107025 19664218630403039775080269)
                  ·
                    refine ⟨7374081986401139915655101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19664218630403039775080269 7374081986401139915655101)
                    ·
                      refine ⟨2765280744900427468370663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7374081986401139915655101 2765280744900427468370663)
                      ·
                        rfl

theorem cell23_5385365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 4, 2, 3, 3].length) (baseStart_5385365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5385365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5385365 prefixEnd_5385365 := by exact prefixLift 5385365
  have htrace : WordTrace (prefixWord ++ tailWord_5385365) baseStart_5385365 baseEnd_5385365 := by
    simpa [prefixWord, tailWord_5385365, baseEnd_5385365] using wordTrace_append hprefix tailTrace_5385365
  have hstable : (prefixWord ++ tailWord_5385365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5385365).length < 2 ^ (prefixWord ++ tailWord_5385365).sum := by decide
  have hdescent : baseEnd_5385365 < baseStart_5385365 := by decide
  rcases family_descends (prefixWord ++ tailWord_5385365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5385372 : List Nat := [2, 2, 3, 2, 1, 4, 1, 1, 7]
def baseStart_5385372 : Nat := 118140960795 + 5385372 * 2 ^ 59
def prefixEnd_5385372 : Nat := 4983230072969 + 3 ^ 40 * 5385372 * 2
def baseEnd_5385372 : Nat := 307253815473889882331459

theorem tailTrace_5385372 : CollatzResearch.WordTrace tailWord_5385372 prefixEnd_5385372 307253815473889882331459 := by
  unfold tailWord_5385372
  simp only [CollatzResearch.WordTrace]
  refine ⟨98210326722862233578903185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130947102297149644771870913 98210326722862233578903185)
  ·
    refine ⟨73657745042146675184177389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98210326722862233578903185 73657745042146675184177389)
    ·
      refine ⟨27621654390805003194066521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73657745042146675184177389 27621654390805003194066521)
      ·
        refine ⟨20716240793103752395549891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27621654390805003194066521 20716240793103752395549891)
        ·
          refine ⟨31074361189655628593324837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20716240793103752395549891 31074361189655628593324837)
          ·
            refine ⟨5826442723060430361248407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31074361189655628593324837 5826442723060430361248407)
            ·
              refine ⟨8739664084590645541872611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5826442723060430361248407 8739664084590645541872611)
              ·
                refine ⟨13109496126885968312808917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8739664084590645541872611 13109496126885968312808917)
                ·
                  refine ⟨307253815473889882331459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13109496126885968312808917 307253815473889882331459)
                  ·
                    rfl

theorem cell23_5385372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 1, 1, 7].length) (baseStart_5385372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5385372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5385372 prefixEnd_5385372 := by exact prefixLift 5385372
  have htrace : WordTrace (prefixWord ++ tailWord_5385372) baseStart_5385372 baseEnd_5385372 := by
    simpa [prefixWord, tailWord_5385372, baseEnd_5385372] using wordTrace_append hprefix tailTrace_5385372
  have hstable : (prefixWord ++ tailWord_5385372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5385372).length < 2 ^ (prefixWord ++ tailWord_5385372).sum := by decide
  have hdescent : baseEnd_5385372 < baseStart_5385372 := by decide
  rcases family_descends (prefixWord ++ tailWord_5385372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5385383 : List Nat := [1, 1, 6, 2, 1, 1, 4, 1, 2, 2, 2]
def baseStart_5385383 : Nat := 118140960795 + 5385383 * 2 ^ 59
def prefixEnd_5385383 : Nat := 4983230072969 + 3 ^ 40 * 5385383 * 2
def baseEnd_5385383 : Nat := 2765289987552208397945581

theorem tailTrace_5385383 : CollatzResearch.WordTrace tailWord_5385383 prefixEnd_5385383 2765289987552208397945581 := by
  unfold tailWord_5385383
  simp only [CollatzResearch.WordTrace]
  refine ⟨196421054648684616036456803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130947369765789744024304535 196421054648684616036456803)
  ·
    refine ⟨294631581973026924054685205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196421054648684616036456803 294631581973026924054685205)
    ·
      refine ⟨13810855404985637065063369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 294631581973026924054685205 13810855404985637065063369)
      ·
        refine ⟨10358141553739227798797527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13810855404985637065063369 10358141553739227798797527)
        ·
          refine ⟨15537212330608841698196291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10358141553739227798797527 15537212330608841698196291)
          ·
            refine ⟨23305818495913262547294437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15537212330608841698196291 23305818495913262547294437)
            ·
              refine ⟨4369840967983736727617707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23305818495913262547294437 4369840967983736727617707)
              ·
                refine ⟨6554761451975605091426561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4369840967983736727617707 6554761451975605091426561)
                ·
                  refine ⟨4916071088981703818569921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6554761451975605091426561 4916071088981703818569921)
                  ·
                    refine ⟨3687053316736277863927441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4916071088981703818569921 3687053316736277863927441)
                    ·
                      refine ⟨2765289987552208397945581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3687053316736277863927441 2765289987552208397945581)
                      ·
                        rfl

theorem cell23_5385383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 4, 1, 2, 2, 2].length) (baseStart_5385383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5385383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5385383 prefixEnd_5385383 := by exact prefixLift 5385383
  have htrace : WordTrace (prefixWord ++ tailWord_5385383) baseStart_5385383 baseEnd_5385383 := by
    simpa [prefixWord, tailWord_5385383, baseEnd_5385383] using wordTrace_append hprefix tailTrace_5385383
  have hstable : (prefixWord ++ tailWord_5385383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5385383).length < 2 ^ (prefixWord ++ tailWord_5385383).sum := by decide
  have hdescent : baseEnd_5385383 < baseStart_5385383 := by decide
  rcases family_descends (prefixWord ++ tailWord_5385383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5385405 : List Nat := [1, 4, 1, 2, 1, 1, 2, 3, 1, 3, 4]
def baseStart_5385405 : Nat := 118140960795 + 5385405 * 2 ^ 59
def prefixEnd_5385405 : Nat := 4983230072969 + 3 ^ 40 * 5385405 * 2
def baseEnd_5385405 : Nat := 2765301284126607311870479

theorem tailTrace_5385405 : CollatzResearch.WordTrace tailWord_5385405 prefixEnd_5385405 2765301284126607311870479 := by
  unfold tailWord_5385405
  simp only [CollatzResearch.WordTrace]
  refine ⟨196421857054604913793757669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130947904703069942529171779 196421857054604913793757669)
  ·
    refine ⟨36829098197738421336329563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 196421857054604913793757669 36829098197738421336329563)
    ·
      refine ⟨55243647296607632004494345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36829098197738421336329563 55243647296607632004494345)
      ·
        refine ⟨41432735472455724003370759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55243647296607632004494345 41432735472455724003370759)
        ·
          refine ⟨62149103208683586005056139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41432735472455724003370759 62149103208683586005056139)
          ·
            refine ⟨93223654813025379007584209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62149103208683586005056139 93223654813025379007584209)
            ·
              refine ⟨69917741109769034255688157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93223654813025379007584209 69917741109769034255688157)
              ·
                refine ⟨26219152916163387845883059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69917741109769034255688157 26219152916163387845883059)
                ·
                  refine ⟨39328729374245081768824589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26219152916163387845883059 39328729374245081768824589)
                  ·
                    refine ⟨14748273515341905663309221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39328729374245081768824589 14748273515341905663309221)
                    ·
                      refine ⟨2765301284126607311870479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14748273515341905663309221 2765301284126607311870479)
                      ·
                        rfl

theorem cell23_5385405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 3, 1, 3, 4].length) (baseStart_5385405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5385405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5385405 prefixEnd_5385405 := by exact prefixLift 5385405
  have htrace : WordTrace (prefixWord ++ tailWord_5385405) baseStart_5385405 baseEnd_5385405 := by
    simpa [prefixWord, tailWord_5385405, baseEnd_5385405] using wordTrace_append hprefix tailTrace_5385405
  have hstable : (prefixWord ++ tailWord_5385405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5385405).length < 2 ^ (prefixWord ++ tailWord_5385405).sum := by decide
  have hdescent : baseEnd_5385405 < baseStart_5385405 := by decide
  rcases family_descends (prefixWord ++ tailWord_5385405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5385425 : List Nat := [1, 2, 2, 1, 2, 2, 1, 2, 3, 4, 3]
def baseStart_5385425 : Nat := 118140960795 + 5385425 * 2 ^ 59
def prefixEnd_5385425 : Nat := 4983230072969 + 3 ^ 40 * 5385425 * 2
def baseEnd_5385425 : Nat := 2765311553739697233620387

theorem tailTrace_5385425 : CollatzResearch.WordTrace tailWord_5385425 prefixEnd_5385425 2765311553739697233620387 := by
  unfold tailWord_5385425
  simp only [CollatzResearch.WordTrace]
  refine ⟨196422586514532457209485729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130948391009688304806323819 196422586514532457209485729)
  ·
    refine ⟨147316939885899342907114297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196422586514532457209485729 147316939885899342907114297)
    ·
      refine ⟨110487704914424507180335723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147316939885899342907114297 110487704914424507180335723)
      ·
        refine ⟨165731557371636760770503585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110487704914424507180335723 165731557371636760770503585)
        ·
          refine ⟨124298668028727570577877689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165731557371636760770503585 124298668028727570577877689)
          ·
            refine ⟨93224001021545677933408267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124298668028727570577877689 93224001021545677933408267)
            ·
              refine ⟨139836001532318516900112401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93224001021545677933408267 139836001532318516900112401)
              ·
                refine ⟨104877001149238887675084301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 139836001532318516900112401 104877001149238887675084301)
                ·
                  refine ⟨39328875430964582878156613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 104877001149238887675084301 39328875430964582878156613)
                  ·
                    refine ⟨7374164143305859289654365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39328875430964582878156613 7374164143305859289654365)
                    ·
                      refine ⟨2765311553739697233620387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7374164143305859289654365 2765311553739697233620387)
                      ·
                        rfl

theorem cell23_5385425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 3, 4, 3].length) (baseStart_5385425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5385425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5385425 prefixEnd_5385425 := by exact prefixLift 5385425
  have htrace : WordTrace (prefixWord ++ tailWord_5385425) baseStart_5385425 baseEnd_5385425 := by
    simpa [prefixWord, tailWord_5385425, baseEnd_5385425] using wordTrace_append hprefix tailTrace_5385425
  have hstable : (prefixWord ++ tailWord_5385425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5385425).length < 2 ^ (prefixWord ++ tailWord_5385425).sum := by decide
  have hdescent : baseEnd_5385425 < baseStart_5385425 := by decide
  rcases family_descends (prefixWord ++ tailWord_5385425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5385459 : List Nat := [1, 1, 1, 2, 2, 7, 1, 1, 2, 2, 3]
def baseStart_5385459 : Nat := 118140960795 + 5385459 * 2 ^ 59
def prefixEnd_5385459 : Nat := 4983230072969 + 3 ^ 40 * 5385459 * 2
def baseEnd_5385459 : Nat := 2765329012081950100595231

theorem tailTrace_5385459 : CollatzResearch.WordTrace tailWord_5385459 prefixEnd_5385459 2765329012081950100595231 := by
  unfold tailWord_5385459
  simp only [CollatzResearch.WordTrace]
  refine ⟨196423826596409281016223431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130949217730939520677482287 196423826596409281016223431)
  ·
    refine ⟨294635739894613921524335147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196423826596409281016223431 294635739894613921524335147)
    ·
      refine ⟨441953609841920882286502721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294635739894613921524335147 441953609841920882286502721)
      ·
        refine ⟨331465207381440661714877041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 441953609841920882286502721 331465207381440661714877041)
        ·
          refine ⟨248598905536080496286157781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 331465207381440661714877041 248598905536080496286157781)
          ·
            refine ⟨5826536848501886631706823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 248598905536080496286157781 5826536848501886631706823)
            ·
              refine ⟨8739805272752829947560235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5826536848501886631706823 8739805272752829947560235)
              ·
                refine ⟨13109707909129244921340353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8739805272752829947560235 13109707909129244921340353)
                ·
                  refine ⟨9832280931846933691005265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13109707909129244921340353 9832280931846933691005265)
                  ·
                    refine ⟨7374210698885200268253949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9832280931846933691005265 7374210698885200268253949)
                    ·
                      refine ⟨2765329012081950100595231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7374210698885200268253949 2765329012081950100595231)
                      ·
                        rfl

theorem cell23_5385459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 1, 1, 2, 2, 3].length) (baseStart_5385459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5385459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5385459 prefixEnd_5385459 := by exact prefixLift 5385459
  have htrace : WordTrace (prefixWord ++ tailWord_5385459) baseStart_5385459 baseEnd_5385459 := by
    simpa [prefixWord, tailWord_5385459, baseEnd_5385459] using wordTrace_append hprefix tailTrace_5385459
  have hstable : (prefixWord ++ tailWord_5385459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5385459).length < 2 ^ (prefixWord ++ tailWord_5385459).sum := by decide
  have hdescent : baseEnd_5385459 < baseStart_5385459 := by decide
  rcases family_descends (prefixWord ++ tailWord_5385459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5385472 : List Nat := [2, 1, 1, 2, 1, 1, 3, 1, 7, 1, 3]
def baseStart_5385472 : Nat := 118140960795 + 5385472 * 2 ^ 59
def prefixEnd_5385472 : Nat := 4983230072969 + 3 ^ 40 * 5385472 * 2
def baseEnd_5385472 : Nat := 2765335687330458549732671

theorem tailTrace_5385472 : CollatzResearch.WordTrace tailWord_5385472 prefixEnd_5385472 2765335687330458549732671 := by
  unfold tailWord_5385472
  simp only [CollatzResearch.WordTrace]
  refine ⟨98212150372681092118223335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130949533830241456157631113 98212150372681092118223335)
  ·
    refine ⟨147318225559021638177335003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98212150372681092118223335 147318225559021638177335003)
    ·
      refine ⟨220977338338532457266002505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147318225559021638177335003 220977338338532457266002505)
      ·
        refine ⟨165733003753899342949501879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 220977338338532457266002505 165733003753899342949501879)
        ·
          refine ⟨248599505630849014424252819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165733003753899342949501879 248599505630849014424252819)
          ·
            refine ⟨372899258446273521636379229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 248599505630849014424252819 372899258446273521636379229)
            ·
              refine ⟨139837221917352570613642211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 372899258446273521636379229 139837221917352570613642211)
              ·
                refine ⟨209755832876028855920463317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 139837221917352570613642211 209755832876028855920463317)
                ·
                  refine ⟨4916152333031926310635859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 209755832876028855920463317 4916152333031926310635859)
                  ·
                    refine ⟨7374228499547889465953789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4916152333031926310635859 7374228499547889465953789)
                    ·
                      refine ⟨2765335687330458549732671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7374228499547889465953789 2765335687330458549732671)
                      ·
                        rfl

theorem cell23_5385472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 7, 1, 3].length) (baseStart_5385472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5385472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5385472 prefixEnd_5385472 := by exact prefixLift 5385472
  have htrace : WordTrace (prefixWord ++ tailWord_5385472) baseStart_5385472 baseEnd_5385472 := by
    simpa [prefixWord, tailWord_5385472, baseEnd_5385472] using wordTrace_append hprefix tailTrace_5385472
  have hstable : (prefixWord ++ tailWord_5385472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5385472).length < 2 ^ (prefixWord ++ tailWord_5385472).sum := by decide
  have hdescent : baseEnd_5385472 < baseStart_5385472 := by decide
  rcases family_descends (prefixWord ++ tailWord_5385472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5385489 : List Nat := [1, 2, 2, 1, 1, 4, 4, 1, 3, 1, 3]
def baseStart_5385489 : Nat := 118140960795 + 5385489 * 2 ^ 59
def prefixEnd_5385489 : Nat := 4983230072969 + 3 ^ 40 * 5385489 * 2
def baseEnd_5385489 : Nat := 2765344416501584983220093

theorem tailTrace_5385489 : CollatzResearch.WordTrace tailWord_5385489 prefixEnd_5385489 2765344416501584983220093 := by
  unfold tailWord_5385489
  simp only [CollatzResearch.WordTrace]
  refine ⟨196424920786300596139815521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130949947190867064093210347 196424920786300596139815521)
  ·
    refine ⟨147318690589725447104861641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196424920786300596139815521 147318690589725447104861641)
    ·
      refine ⟨110489017942294085328646231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147318690589725447104861641 110489017942294085328646231)
      ·
        refine ⟨165733526913441127992969347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110489017942294085328646231 165733526913441127992969347)
        ·
          refine ⟨248600290370161691989454021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165733526913441127992969347 248600290370161691989454021)
          ·
            refine ⟨46612554444405317248022629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 248600290370161691989454021 46612554444405317248022629)
            ·
              refine ⟨8739853958325996984004243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46612554444405317248022629 8739853958325996984004243)
              ·
                refine ⟨13109780937488995476006365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8739853958325996984004243 13109780937488995476006365)
                ·
                  refine ⟨4916167851558373303502387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13109780937488995476006365 4916167851558373303502387)
                  ·
                    refine ⟨7374251777337559955253581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4916167851558373303502387 7374251777337559955253581)
                    ·
                      refine ⟨2765344416501584983220093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7374251777337559955253581 2765344416501584983220093)
                      ·
                        rfl

theorem cell23_5385489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4, 1, 3, 1, 3].length) (baseStart_5385489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5385489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5385489 prefixEnd_5385489 := by exact prefixLift 5385489
  have htrace : WordTrace (prefixWord ++ tailWord_5385489) baseStart_5385489 baseEnd_5385489 := by
    simpa [prefixWord, tailWord_5385489, baseEnd_5385489] using wordTrace_append hprefix tailTrace_5385489
  have hstable : (prefixWord ++ tailWord_5385489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5385489).length < 2 ^ (prefixWord ++ tailWord_5385489).sum := by decide
  have hdescent : baseEnd_5385489 < baseStart_5385489 := by decide
  rcases family_descends (prefixWord ++ tailWord_5385489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5385509 : List Nat := [1, 3, 1, 2, 4, 2, 2, 2, 1, 5]
def baseStart_5385509 : Nat := 118140960795 + 5385509 * 2 ^ 59
def prefixEnd_5385509 : Nat := 4983230072969 + 3 ^ 40 * 5385509 * 2
def baseEnd_5385509 : Nat := 921784895371558301656667

theorem tailTrace_5385509 : CollatzResearch.WordTrace tailWord_5385509 prefixEnd_5385509 921784895371558301656667 := by
  unfold tailWord_5385509
  simp only [CollatzResearch.WordTrace]
  refine ⟨196425650246228139555543581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130950433497485426370362387 196425650246228139555543581)
  ·
    refine ⟨73659618842335552333328843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 196425650246228139555543581 73659618842335552333328843)
    ·
      refine ⟨110489428263503328499993265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73659618842335552333328843 110489428263503328499993265)
      ·
        refine ⟨82867071197627496374994949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110489428263503328499993265 82867071197627496374994949)
        ·
          refine ⟨15537575849555155570311553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82867071197627496374994949 15537575849555155570311553)
          ·
            refine ⟨11653181887166366677733665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15537575849555155570311553 11653181887166366677733665)
            ·
              refine ⟨8739886415374775008300249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11653181887166366677733665 8739886415374775008300249)
              ·
                refine ⟨6554914811531081256225187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8739886415374775008300249 6554914811531081256225187)
                ·
                  refine ⟨9832372217296621884337781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6554914811531081256225187 9832372217296621884337781)
                  ·
                    refine ⟨921784895371558301656667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9832372217296621884337781 921784895371558301656667)
                    ·
                      rfl

theorem cell23_5385509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2, 2, 1, 5].length) (baseStart_5385509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5385509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5385509 prefixEnd_5385509 := by exact prefixLift 5385509
  have htrace : WordTrace (prefixWord ++ tailWord_5385509) baseStart_5385509 baseEnd_5385509 := by
    simpa [prefixWord, tailWord_5385509, baseEnd_5385509] using wordTrace_append hprefix tailTrace_5385509
  have hstable : (prefixWord ++ tailWord_5385509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5385509).length < 2 ^ (prefixWord ++ tailWord_5385509).sum := by decide
  have hdescent : baseEnd_5385509 < baseStart_5385509 := by decide
  rcases family_descends (prefixWord ++ tailWord_5385509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5385523 : List Nat := [1, 1, 1, 2, 5, 4, 1, 3, 1, 1, 3]
def baseStart_5385523 : Nat := 118140960795 + 5385523 * 2 ^ 59
def prefixEnd_5385523 : Nat := 4983230072969 + 3 ^ 40 * 5385523 * 2
def baseEnd_5385523 : Nat := 2765361874843837850194937

theorem tailTrace_5385523 : CollatzResearch.WordTrace tailWord_5385523 prefixEnd_5385523 2765361874843837850194937 := by
  unfold tailWord_5385523
  simp only [CollatzResearch.WordTrace]
  refine ⟨196426160868177419946553223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130950773912118279964368815 196426160868177419946553223)
  ·
    refine ⟨294639241302266129919829835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196426160868177419946553223 294639241302266129919829835)
    ·
      refine ⟨441958861953399194879744753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294639241302266129919829835 441958861953399194879744753)
      ·
        refine ⟨331469146465049396159808565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 441958861953399194879744753 331469146465049396159808565)
        ·
          refine ⟨31075232481098380889982053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 331469146465049396159808565 31075232481098380889982053)
          ·
            refine ⟨5826606090205946416871635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31075232481098380889982053 5826606090205946416871635)
            ·
              refine ⟨8739909135308919625307453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5826606090205946416871635 8739909135308919625307453)
              ·
                refine ⟨3277465925740844859490295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8739909135308919625307453 3277465925740844859490295)
                ·
                  refine ⟨4916198888611267289235443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3277465925740844859490295 4916198888611267289235443)
                  ·
                    refine ⟨7374298332916900933853165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4916198888611267289235443 7374298332916900933853165)
                    ·
                      refine ⟨2765361874843837850194937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7374298332916900933853165 2765361874843837850194937)
                      ·
                        rfl

theorem cell23_5385523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 1, 3, 1, 1, 3].length) (baseStart_5385523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5385523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5385523 prefixEnd_5385523 := by exact prefixLift 5385523
  have htrace : WordTrace (prefixWord ++ tailWord_5385523) baseStart_5385523 baseEnd_5385523 := by
    simpa [prefixWord, tailWord_5385523, baseEnd_5385523] using wordTrace_append hprefix tailTrace_5385523
  have hstable : (prefixWord ++ tailWord_5385523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5385523).length < 2 ^ (prefixWord ++ tailWord_5385523).sum := by decide
  have hdescent : baseEnd_5385523 < baseStart_5385523 := by decide
  rcases family_descends (prefixWord ++ tailWord_5385523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5385532 : List Nat := [2, 2, 2, 2, 1, 3, 1, 3, 1, 1, 5]
def baseStart_5385532 : Nat := 118140960795 + 5385532 * 2 ^ 59
def prefixEnd_5385532 : Nat := 4983230072969 + 3 ^ 40 * 5385532 * 2
def baseEnd_5385532 : Nat := 2765366496169728314982395

theorem tailTrace_5385532 : CollatzResearch.WordTrace tailWord_5385532 prefixEnd_5385532 2765366496169728314982395 := by
  unfold tailWord_5385532
  simp only [CollatzResearch.WordTrace]
  refine ⟨98213244562572407241815425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130950992750096542989087233 98213244562572407241815425)
  ·
    refine ⟨73659933421929305431361569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98213244562572407241815425 73659933421929305431361569)
    ·
      refine ⟨55244950066446979073521177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73659933421929305431361569 55244950066446979073521177)
      ·
        refine ⟨41433712549835234305140883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55244950066446979073521177 41433712549835234305140883)
        ·
          refine ⟨62150568824752851457711325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41433712549835234305140883 62150568824752851457711325)
          ·
            refine ⟨23306463309282319296641747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62150568824752851457711325 23306463309282319296641747)
            ·
              refine ⟨34959694963923478944962621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23306463309282319296641747 34959694963923478944962621)
              ·
                refine ⟨13109885611471304604360983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34959694963923478944962621 13109885611471304604360983)
                ·
                  refine ⟨19664828417206956906541475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13109885611471304604360983 19664828417206956906541475)
                  ·
                    refine ⟨29497242625810435359812213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19664828417206956906541475 29497242625810435359812213)
                    ·
                      refine ⟨2765366496169728314982395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29497242625810435359812213 2765366496169728314982395)
                      ·
                        rfl

theorem cell23_5385532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 3, 1, 1, 5].length) (baseStart_5385532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5385532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5385532 prefixEnd_5385532 := by exact prefixLift 5385532
  have htrace : WordTrace (prefixWord ++ tailWord_5385532) baseStart_5385532 baseEnd_5385532 := by
    simpa [prefixWord, tailWord_5385532, baseEnd_5385532] using wordTrace_append hprefix tailTrace_5385532
  have hstable : (prefixWord ++ tailWord_5385532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5385532).length < 2 ^ (prefixWord ++ tailWord_5385532).sum := by decide
  have hdescent : baseEnd_5385532 < baseStart_5385532 := by decide
  rcases family_descends (prefixWord ++ tailWord_5385532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5385533 : List Nat := [1, 4, 1, 5, 1, 1, 1, 2, 2, 3, 2]
def baseStart_5385533 : Nat := 118140960795 + 5385533 * 2 ^ 59
def prefixEnd_5385533 : Nat := 4983230072969 + 3 ^ 40 * 5385533 * 2
def baseEnd_5385533 : Nat := 2765367009650382811069891

theorem tailTrace_5385533 : CollatzResearch.WordTrace tailWord_5385533 prefixEnd_5385533 2765367009650382811069891 := by
  unfold tailWord_5385533
  simp only [CollatzResearch.WordTrace]
  refine ⟨196426525598141191654417253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130951017065427461102944835 196426525598141191654417253)
  ·
    refine ⟨36829973549651473435203235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 196426525598141191654417253 36829973549651473435203235)
    ·
      refine ⟨55244960324477210152804853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36829973549651473435203235 55244960324477210152804853)
      ·
        refine ⟨5179215030419738451825455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 55244960324477210152804853 5179215030419738451825455)
        ·
          refine ⟨7768822545629607677738183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5179215030419738451825455 7768822545629607677738183)
          ·
            refine ⟨11653233818444411516607275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7768822545629607677738183 11653233818444411516607275)
            ·
              refine ⟨17479850727666617274910913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11653233818444411516607275 17479850727666617274910913)
              ·
                refine ⟨13109888045749962956183185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17479850727666617274910913 13109888045749962956183185)
                ·
                  refine ⟨9832416034312472217137389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13109888045749962956183185 9832416034312472217137389)
                  ·
                    refine ⟨3687156012867177081426521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9832416034312472217137389 3687156012867177081426521)
                    ·
                      refine ⟨2765367009650382811069891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3687156012867177081426521 2765367009650382811069891)
                      ·
                        rfl

theorem cell23_5385533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_5385533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5385533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5385533 prefixEnd_5385533 := by exact prefixLift 5385533
  have htrace : WordTrace (prefixWord ++ tailWord_5385533) baseStart_5385533 baseEnd_5385533 := by
    simpa [prefixWord, tailWord_5385533, baseEnd_5385533] using wordTrace_append hprefix tailTrace_5385533
  have hstable : (prefixWord ++ tailWord_5385533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5385533).length < 2 ^ (prefixWord ++ tailWord_5385533).sum := by decide
  have hdescent : baseEnd_5385533 < baseStart_5385533 := by decide
  rcases family_descends (prefixWord ++ tailWord_5385533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5385535 : List Nat := [1, 1, 2, 2, 4, 2, 11]
def baseStart_5385535 : Nat := 118140960795 + 5385535 * 2 ^ 59
def prefixEnd_5385535 : Nat := 4983230072969 + 3 ^ 40 * 5385535 * 2
def baseEnd_5385535 : Nat := 34140346131008540780801

theorem tailTrace_5385535 : CollatzResearch.WordTrace tailWord_5385535 prefixEnd_5385535 34140346131008540780801 := by
  unfold tailWord_5385535
  simp only [CollatzResearch.WordTrace]
  refine ⟨196426598544133945995990059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130951065696089297330660039 196426598544133945995990059)
  ·
    refine ⟨294639897816200918993985089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196426598544133945995990059 294639897816200918993985089)
    ·
      refine ⟨220979923362150689245488817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 294639897816200918993985089 220979923362150689245488817)
      ·
        refine ⟨165734942521613016934116613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 220979923362150689245488817 165734942521613016934116613)
        ·
          refine ⟨31075301722802440675146865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 165734942521613016934116613 31075301722802440675146865)
          ·
            refine ⟨23306476292101830506360149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31075301722802440675146865 23306476292101830506360149)
            ·
              refine ⟨34140346131008540780801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 23306476292101830506360149 34140346131008540780801)
              ·
                rfl

theorem cell23_5385535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 11].length) (baseStart_5385535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5385535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5385535 prefixEnd_5385535 := by exact prefixLift 5385535
  have htrace : WordTrace (prefixWord ++ tailWord_5385535) baseStart_5385535 baseEnd_5385535 := by
    simpa [prefixWord, tailWord_5385535, baseEnd_5385535] using wordTrace_append hprefix tailTrace_5385535
  have hstable : (prefixWord ++ tailWord_5385535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5385535).length < 2 ^ (prefixWord ++ tailWord_5385535).sum := by decide
  have hdescent : baseEnd_5385535 < baseStart_5385535 := by decide
  rcases family_descends (prefixWord ++ tailWord_5385535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5385555 : List Nat := [1, 1, 1, 2, 1, 1, 5, 1, 2, 2, 6]
def baseStart_5385555 : Nat := 118140960795 + 5385555 * 2 ^ 59
def prefixEnd_5385555 : Nat := 4983230072969 + 3 ^ 40 * 5385555 * 2
def baseEnd_5385555 : Nat := 2765378306224781724994789

theorem tailTrace_5385555 : CollatzResearch.WordTrace tailWord_5385555 prefixEnd_5385555 2765378306224781724994789 := by
  unfold tailWord_5385555
  simp only [CollatzResearch.WordTrace]
  refine ⟨196427328004061489411718119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130951552002707659607812079 196427328004061489411718119)
  ·
    refine ⟨294640992006092234117577179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196427328004061489411718119 294640992006092234117577179)
    ·
      refine ⟨441961488009138351176365769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294640992006092234117577179 441961488009138351176365769)
      ·
        refine ⟨331471116006853763382274327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 441961488009138351176365769 331471116006853763382274327)
        ·
          refine ⟨497206674010280645073411491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 331471116006853763382274327 497206674010280645073411491)
          ·
            refine ⟨745810011015420967610117237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 497206674010280645073411491 745810011015420967610117237)
            ·
              refine ⟨69919688532695715713448491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 745810011015420967610117237 69919688532695715713448491)
              ·
                refine ⟨104879532799043573570172737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69919688532695715713448491 104879532799043573570172737)
                ·
                  refine ⟨78659649599282680177629553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 104879532799043573570172737 78659649599282680177629553)
                  ·
                    refine ⟨58994737199462010133222165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 78659649599282680177629553 58994737199462010133222165)
                    ·
                      refine ⟨2765378306224781724994789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58994737199462010133222165 2765378306224781724994789)
                      ·
                        rfl

theorem cell23_5385555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 2, 2, 6].length) (baseStart_5385555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5385555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5385555 prefixEnd_5385555 := by exact prefixLift 5385555
  have htrace : WordTrace (prefixWord ++ tailWord_5385555) baseStart_5385555 baseEnd_5385555 := by
    simpa [prefixWord, tailWord_5385555, baseEnd_5385555] using wordTrace_append hprefix tailTrace_5385555
  have hstable : (prefixWord ++ tailWord_5385555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5385555).length < 2 ^ (prefixWord ++ tailWord_5385555).sum := by decide
  have hdescent : baseEnd_5385555 < baseStart_5385555 := by decide
  rcases family_descends (prefixWord ++ tailWord_5385555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5385596 : List Nat := [2, 2, 2, 1, 1, 1, 6, 2, 2, 1, 3]
def baseStart_5385596 : Nat := 118140960795 + 5385596 * 2 ^ 59
def prefixEnd_5385596 : Nat := 4983230072969 + 3 ^ 40 * 5385596 * 2
def baseEnd_5385596 : Nat := 2765399358931616064582101

theorem tailTrace_5385596 : CollatzResearch.WordTrace tailWord_5385596 prefixEnd_5385596 2765399358931616064582101 := by
  unfold tailWord_5385596
  simp only [CollatzResearch.WordTrace]
  refine ⟨98214411698456476706980321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130952548931275302275973761 98214411698456476706980321)
  ·
    refine ⟨73660808773842357530235241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98214411698456476706980321 73660808773842357530235241)
    ·
      refine ⟨55245606580381768147676431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73660808773842357530235241 55245606580381768147676431)
      ·
        refine ⟨82868409870572652221514647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55245606580381768147676431 82868409870572652221514647)
        ·
          refine ⟨124302614805858978332271971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82868409870572652221514647 124302614805858978332271971)
          ·
            refine ⟨186453922208788467498407957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124302614805858978332271971 186453922208788467498407957)
            ·
              refine ⟨8740027603536959413987873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 186453922208788467498407957 8740027603536959413987873)
              ·
                refine ⟨6555020702652719560490905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8740027603536959413987873 6555020702652719560490905)
                ·
                  refine ⟨4916265526989539670368179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6555020702652719560490905 4916265526989539670368179)
                  ·
                    refine ⟨7374398290484309505552269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4916265526989539670368179 7374398290484309505552269)
                    ·
                      refine ⟨2765399358931616064582101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7374398290484309505552269 2765399358931616064582101)
                      ·
                        rfl

theorem cell23_5385596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6, 2, 2, 1, 3].length) (baseStart_5385596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5385596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5385596 prefixEnd_5385596 := by exact prefixLift 5385596
  have htrace : WordTrace (prefixWord ++ tailWord_5385596) baseStart_5385596 baseEnd_5385596 := by
    simpa [prefixWord, tailWord_5385596, baseEnd_5385596] using wordTrace_append hprefix tailTrace_5385596
  have hstable : (prefixWord ++ tailWord_5385596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5385596).length < 2 ^ (prefixWord ++ tailWord_5385596).sum := by decide
  have hdescent : baseEnd_5385596 < baseStart_5385596 := by decide
  rcases family_descends (prefixWord ++ tailWord_5385596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5385612 : List Nat := [2, 2, 1, 2, 1, 3, 3, 1, 2, 6]
def baseStart_5385612 : Nat := 118140960795 + 5385612 * 2 ^ 59
def prefixEnd_5385612 : Nat := 4983230072969 + 3 ^ 40 * 5385612 * 2
def baseEnd_5385612 : Nat := 921802524874029333994009

theorem tailTrace_5385612 : CollatzResearch.WordTrace tailWord_5385612 prefixEnd_5385612 921802524874029333994009 := by
  unfold tailWord_5385612
  simp only [CollatzResearch.WordTrace]
  refine ⟨98214703482427494073271545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130952937976569992097695393 98214703482427494073271545)
  ·
    refine ⟨73661027611820620554953659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98214703482427494073271545 73661027611820620554953659)
    ·
      refine ⟨110491541417730930832430489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73661027611820620554953659 110491541417730930832430489)
      ·
        refine ⟨82868656063298198124322867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110491541417730930832430489 82868656063298198124322867)
        ·
          refine ⟨124302984094947297186484301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82868656063298198124322867 124302984094947297186484301)
          ·
            refine ⟨46613619035605236444931613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 124302984094947297186484301 46613619035605236444931613)
            ·
              refine ⟨17480107138351963666849355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46613619035605236444931613 17480107138351963666849355)
              ·
                refine ⟨26220160707527945500274033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17480107138351963666849355 26220160707527945500274033)
                ·
                  refine ⟨19665120530645959125205525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26220160707527945500274033 19665120530645959125205525)
                  ·
                    refine ⟨921802524874029333994009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19665120530645959125205525 921802524874029333994009)
                    ·
                      rfl

theorem cell23_5385612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 1, 2, 6].length) (baseStart_5385612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5385612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5385612 prefixEnd_5385612 := by exact prefixLift 5385612
  have htrace : WordTrace (prefixWord ++ tailWord_5385612) baseStart_5385612 baseEnd_5385612 := by
    simpa [prefixWord, tailWord_5385612, baseEnd_5385612] using wordTrace_append hprefix tailTrace_5385612
  have hstable : (prefixWord ++ tailWord_5385612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5385612).length < 2 ^ (prefixWord ++ tailWord_5385612).sum := by decide
  have hdescent : baseEnd_5385612 < baseStart_5385612 := by decide
  rcases family_descends (prefixWord ++ tailWord_5385612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5385632 : List Nat := [2, 1, 1, 4, 1, 2, 1, 2, 1, 4, 4]
def baseStart_5385632 : Nat := 118140960795 + 5385632 * 2 ^ 59
def prefixEnd_5385632 : Nat := 4983230072969 + 3 ^ 40 * 5385632 * 2
def baseEnd_5385632 : Nat := 2765417844235177923731935

theorem tailTrace_5385632 : CollatzResearch.WordTrace tailWord_5385632 prefixEnd_5385632 2765417844235177923731935 := by
  unfold tailWord_5385632
  simp only [CollatzResearch.WordTrace]
  refine ⟨98215068212391265781135575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130953424283188354374847433 98215068212391265781135575)
  ·
    refine ⟨147322602318586898671703363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98215068212391265781135575 147322602318586898671703363)
    ·
      refine ⟨220983903477880348007555045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147322602318586898671703363 220983903477880348007555045)
      ·
        refine ⟨41434481902102565251416571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 220983903477880348007555045 41434481902102565251416571)
        ·
          refine ⟨62151722853153847877124857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41434481902102565251416571 62151722853153847877124857)
          ·
            refine ⟨46613792139865385907843643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62151722853153847877124857 46613792139865385907843643)
            ·
              refine ⟨69920688209798078861765465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46613792139865385907843643 69920688209798078861765465)
              ·
                refine ⟨52440516157348559146324099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69920688209798078861765465 52440516157348559146324099)
                ·
                  refine ⟨78660774236022838719486149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52440516157348559146324099 78660774236022838719486149)
                  ·
                    refine ⟨14748895169254282259903653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 78660774236022838719486149 14748895169254282259903653)
                    ·
                      refine ⟨2765417844235177923731935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14748895169254282259903653 2765417844235177923731935)
                      ·
                        rfl

theorem cell23_5385632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4, 4].length) (baseStart_5385632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5385632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5385632 prefixEnd_5385632 := by exact prefixLift 5385632
  have htrace : WordTrace (prefixWord ++ tailWord_5385632) baseStart_5385632 baseEnd_5385632 := by
    simpa [prefixWord, tailWord_5385632, baseEnd_5385632] using wordTrace_append hprefix tailTrace_5385632
  have hstable : (prefixWord ++ tailWord_5385632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5385632).length < 2 ^ (prefixWord ++ tailWord_5385632).sum := by decide
  have hdescent : baseEnd_5385632 < baseStart_5385632 := by decide
  rcases family_descends (prefixWord ++ tailWord_5385632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5385636 : List Nat := [2, 3, 1, 2, 1, 1, 1, 4, 4, 2, 2]
def baseStart_5385636 : Nat := 118140960795 + 5385636 * 2 ^ 59
def prefixEnd_5385636 : Nat := 4983230072969 + 3 ^ 40 * 5385636 * 2
def baseEnd_5385636 : Nat := 2765419898157795908081917

theorem tailTrace_5385636 : CollatzResearch.WordTrace tailWord_5385636 prefixEnd_5385636 2765419898157795908081917 := by
  unfold tailWord_5385636
  simp only [CollatzResearch.WordTrace]
  refine ⟨98215141158384020122708381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130953521544512026830277841 98215141158384020122708381)
  ·
    refine ⟨36830677934394007546015643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98215141158384020122708381 36830677934394007546015643)
    ·
      refine ⟨55246016901591011319023465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36830677934394007546015643 55246016901591011319023465)
      ·
        refine ⟨41434512676193258489267599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55246016901591011319023465 41434512676193258489267599)
        ·
          refine ⟨62151769014289887733901399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41434512676193258489267599 62151769014289887733901399)
          ·
            refine ⟨93227653521434831600852099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62151769014289887733901399 93227653521434831600852099)
            ·
              refine ⟨139841480282152247401278149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93227653521434831600852099 139841480282152247401278149)
              ·
                refine ⟨26220277552903546387739653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 139841480282152247401278149 26220277552903546387739653)
                ·
                  refine ⟨4916302041169414947701185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26220277552903546387739653 4916302041169414947701185)
                  ·
                    refine ⟨3687226530877061210775889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4916302041169414947701185 3687226530877061210775889)
                    ·
                      refine ⟨2765419898157795908081917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3687226530877061210775889 2765419898157795908081917)
                      ·
                        rfl

theorem cell23_5385636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 4, 4, 2, 2].length) (baseStart_5385636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5385636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5385636 prefixEnd_5385636 := by exact prefixLift 5385636
  have htrace : WordTrace (prefixWord ++ tailWord_5385636) baseStart_5385636 baseEnd_5385636 := by
    simpa [prefixWord, tailWord_5385636, baseEnd_5385636] using wordTrace_append hprefix tailTrace_5385636
  have hstable : (prefixWord ++ tailWord_5385636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5385636).length < 2 ^ (prefixWord ++ tailWord_5385636).sum := by decide
  have hdescent : baseEnd_5385636 < baseStart_5385636 := by decide
  rcases family_descends (prefixWord ++ tailWord_5385636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5385640 : List Nat := [2, 1, 6, 1, 2, 1, 1, 3, 1, 3, 2]
def baseStart_5385640 : Nat := 118140960795 + 5385640 * 2 ^ 59
def prefixEnd_5385640 : Nat := 4983230072969 + 3 ^ 40 * 5385640 * 2
def baseEnd_5385640 : Nat := 2765421952080413892431899

theorem tailTrace_5385640 : CollatzResearch.WordTrace tailWord_5385640 prefixEnd_5385640 2765421952080413892431899 := by
  unfold tailWord_5385640
  simp only [CollatzResearch.WordTrace]
  refine ⟨98215214104376774464281187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130953618805835699285708249 98215214104376774464281187)
  ·
    refine ⟨147322821156565161696421781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98215214104376774464281187 147322821156565161696421781)
    ·
      refine ⟨6905757241713991954519771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 147322821156565161696421781 6905757241713991954519771)
      ·
        refine ⟨10358635862570987931779657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6905757241713991954519771 10358635862570987931779657)
        ·
          refine ⟨7768976896928240948834743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10358635862570987931779657 7768976896928240948834743)
          ·
            refine ⟨11653465345392361423252115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7768976896928240948834743 11653465345392361423252115)
            ·
              refine ⟨17480198018088542134878173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11653465345392361423252115 17480198018088542134878173)
              ·
                refine ⟨6555074256783203300579315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17480198018088542134878173 6555074256783203300579315)
                ·
                  refine ⟨9832611385174804950868973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6555074256783203300579315 9832611385174804950868973)
                  ·
                    refine ⟨3687229269440551856575865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9832611385174804950868973 3687229269440551856575865)
                    ·
                      refine ⟨2765421952080413892431899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3687229269440551856575865 2765421952080413892431899)
                      ·
                        rfl

theorem cell23_5385640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 3, 1, 3, 2].length) (baseStart_5385640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5385640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5385640 prefixEnd_5385640 := by exact prefixLift 5385640
  have htrace : WordTrace (prefixWord ++ tailWord_5385640) baseStart_5385640 baseEnd_5385640 := by
    simpa [prefixWord, tailWord_5385640, baseEnd_5385640] using wordTrace_append hprefix tailTrace_5385640
  have hstable : (prefixWord ++ tailWord_5385640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5385640).length < 2 ^ (prefixWord ++ tailWord_5385640).sum := by decide
  have hdescent : baseEnd_5385640 < baseStart_5385640 := by decide
  rcases family_descends (prefixWord ++ tailWord_5385640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5385653 : List Nat := [1, 3, 3, 2, 2, 2, 1, 1, 4, 2, 2]
def baseStart_5385653 : Nat := 118140960795 + 5385653 * 2 ^ 59
def prefixEnd_5385653 : Nat := 4983230072969 + 3 ^ 40 * 5385653 * 2
def baseEnd_5385653 : Nat := 2765428627328922341569339

theorem tailTrace_5385653 : CollatzResearch.WordTrace tailWord_5385653 prefixEnd_5385653 2765428627328922341569339 := by
  unfold tailWord_5385653
  simp only [CollatzResearch.WordTrace]
  refine ⟨196430902357706452148785613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130953934905137634765857075 196430902357706452148785613)
  ·
    refine ⟨73661588384139919555794605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 196430902357706452148785613 73661588384139919555794605)
    ·
      refine ⟨27623095644052469833422977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73661588384139919555794605 27623095644052469833422977)
      ·
        refine ⟨20717321733039352375067233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27623095644052469833422977 20717321733039352375067233)
        ·
          refine ⟨15537991299779514281300425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20717321733039352375067233 15537991299779514281300425)
          ·
            refine ⟨11653493474834635710975319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15537991299779514281300425 11653493474834635710975319)
            ·
              refine ⟨17480240212251953566462979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11653493474834635710975319 17480240212251953566462979)
              ·
                refine ⟨26220360318377930349694469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17480240212251953566462979 26220360318377930349694469)
                ·
                  refine ⟨4916317559695861940567713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26220360318377930349694469 4916317559695861940567713)
                  ·
                    refine ⟨3687238169771896455425785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4916317559695861940567713 3687238169771896455425785)
                    ·
                      refine ⟨2765428627328922341569339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3687238169771896455425785 2765428627328922341569339)
                      ·
                        rfl

theorem cell23_5385653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 1, 4, 2, 2].length) (baseStart_5385653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5385653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5385653 prefixEnd_5385653 := by exact prefixLift 5385653
  have htrace : WordTrace (prefixWord ++ tailWord_5385653) baseStart_5385653 baseEnd_5385653 := by
    simpa [prefixWord, tailWord_5385653, baseEnd_5385653] using wordTrace_append hprefix tailTrace_5385653
  have hstable : (prefixWord ++ tailWord_5385653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5385653).length < 2 ^ (prefixWord ++ tailWord_5385653).sum := by decide
  have hdescent : baseEnd_5385653 < baseStart_5385653 := by decide
  rcases family_descends (prefixWord ++ tailWord_5385653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5385672 : List Nat := [2, 1, 3, 1, 3, 1, 1, 1, 3, 7]
def baseStart_5385672 : Nat := 118140960795 + 5385672 * 2 ^ 59
def prefixEnd_5385672 : Nat := 4983230072969 + 3 ^ 40 * 5385672 * 2
def baseEnd_5385672 : Nat := 921812794487119255743917

theorem tailTrace_5385672 : CollatzResearch.WordTrace tailWord_5385672 prefixEnd_5385672 921812794487119255743917 := by
  unfold tailWord_5385672
  simp only [CollatzResearch.WordTrace]
  refine ⟨98215797672318809196863635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130954396896425078929151513 98215797672318809196863635)
  ·
    refine ⟨147323696508478213795295453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98215797672318809196863635 147323696508478213795295453)
    ·
      refine ⟨55246386190679330173235795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147323696508478213795295453 55246386190679330173235795)
      ·
        refine ⟨82869579286018995259853693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55246386190679330173235795 82869579286018995259853693)
        ·
          refine ⟨31076092232257123222445135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82869579286018995259853693 31076092232257123222445135)
          ·
            refine ⟨46614138348385684833667703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31076092232257123222445135 46614138348385684833667703)
            ·
              refine ⟨69921207522578527250501555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46614138348385684833667703 69921207522578527250501555)
              ·
                refine ⟨104881811283867790875752333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69921207522578527250501555 104881811283867790875752333)
                ·
                  refine ⟨39330679231450421578407125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 104881811283867790875752333 39330679231450421578407125)
                  ·
                    refine ⟨921812794487119255743917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39330679231450421578407125 921812794487119255743917)
                    ·
                      rfl

theorem cell23_5385672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 3, 7].length) (baseStart_5385672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5385672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5385672 prefixEnd_5385672 := by exact prefixLift 5385672
  have htrace : WordTrace (prefixWord ++ tailWord_5385672) baseStart_5385672 baseEnd_5385672 := by
    simpa [prefixWord, tailWord_5385672, baseEnd_5385672] using wordTrace_append hprefix tailTrace_5385672
  have hstable : (prefixWord ++ tailWord_5385672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5385672).length < 2 ^ (prefixWord ++ tailWord_5385672).sum := by decide
  have hdescent : baseEnd_5385672 < baseStart_5385672 := by decide
  rcases family_descends (prefixWord ++ tailWord_5385672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5385679 : List Nat := [1, 1, 2, 1, 1, 4, 2, 2, 2, 5, 2]
def baseStart_5385679 : Nat := 118140960795 + 5385679 * 2 ^ 59
def prefixEnd_5385679 : Nat := 4983230072969 + 3 ^ 40 * 5385679 * 2
def baseEnd_5385679 : Nat := 2765441977825939239844219

theorem tailTrace_5385679 : CollatzResearch.WordTrace tailWord_5385679 prefixEnd_5385679 2765441977825939239844219 := by
  unfold tailWord_5385679
  simp only [CollatzResearch.WordTrace]
  refine ⟨196431850655612258589232091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130954567103741505726154727 196431850655612258589232091)
  ·
    refine ⟨294647775983418387883848137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196431850655612258589232091 294647775983418387883848137)
    ·
      refine ⟨220985831987563790912886103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 294647775983418387883848137 220985831987563790912886103)
      ·
        refine ⟨331478747981345686369329155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220985831987563790912886103 331478747981345686369329155)
        ·
          refine ⟨497218121972018529553993733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 331478747981345686369329155 497218121972018529553993733)
          ·
            refine ⟨93228397869753474291373825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 497218121972018529553993733 93228397869753474291373825)
            ·
              refine ⟨69921298402315105718530369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93228397869753474291373825 69921298402315105718530369)
              ·
                refine ⟨52440973801736329288897777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69921298402315105718530369 52440973801736329288897777)
                ·
                  refine ⟨39330730351302246966673333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52440973801736329288897777 39330730351302246966673333)
                  ·
                    refine ⟨3687255970434585653125625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39330730351302246966673333 3687255970434585653125625)
                    ·
                      refine ⟨2765441977825939239844219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3687255970434585653125625 2765441977825939239844219)
                      ·
                        rfl

theorem cell23_5385679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 2, 2, 5, 2].length) (baseStart_5385679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5385679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5385679 prefixEnd_5385679 := by exact prefixLift 5385679
  have htrace : WordTrace (prefixWord ++ tailWord_5385679) baseStart_5385679 baseEnd_5385679 := by
    simpa [prefixWord, tailWord_5385679, baseEnd_5385679] using wordTrace_append hprefix tailTrace_5385679
  have hstable : (prefixWord ++ tailWord_5385679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5385679).length < 2 ^ (prefixWord ++ tailWord_5385679).sum := by decide
  have hdescent : baseEnd_5385679 < baseStart_5385679 := by decide
  rcases family_descends (prefixWord ++ tailWord_5385679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5385693 : List Nat := [1, 4, 3, 1, 1, 4, 1, 3, 5]
def baseStart_5385693 : Nat := 118140960795 + 5385693 * 2 ^ 59
def prefixEnd_5385693 : Nat := 4983230072969 + 3 ^ 40 * 5385693 * 2
def baseEnd_5385693 : Nat := 307272129617233576118795

theorem tailTrace_5385693 : CollatzResearch.WordTrace tailWord_5385693 prefixEnd_5385693 307272129617233576118795 := by
  unfold tailWord_5385693
  simp only [CollatzResearch.WordTrace]
  refine ⟨196432361277561538980241733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130954907518374359320161155 196432361277561538980241733)
  ·
    refine ⟨36831067739542788558795325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 196432361277561538980241733 36831067739542788558795325)
    ·
      refine ⟨13811650402328545709548247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36831067739542788558795325 13811650402328545709548247)
      ·
        refine ⟨20717475603492818564322371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13811650402328545709548247 20717475603492818564322371)
        ·
          refine ⟨31076213405239227846483557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20717475603492818564322371 31076213405239227846483557)
          ·
            refine ⟨5826790013482355221215667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31076213405239227846483557 5826790013482355221215667)
            ·
              refine ⟨8740185020223532831823501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5826790013482355221215667 8740185020223532831823501)
              ·
                refine ⟨3277569382583824811933813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8740185020223532831823501 3277569382583824811933813)
                ·
                  refine ⟨307272129617233576118795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3277569382583824811933813 307272129617233576118795)
                  ·
                    rfl

theorem cell23_5385693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 1, 3, 5].length) (baseStart_5385693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5385693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5385693 prefixEnd_5385693 := by exact prefixLift 5385693
  have htrace : WordTrace (prefixWord ++ tailWord_5385693) baseStart_5385693 baseEnd_5385693 := by
    simpa [prefixWord, tailWord_5385693, baseEnd_5385693] using wordTrace_append hprefix tailTrace_5385693
  have hstable : (prefixWord ++ tailWord_5385693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5385693).length < 2 ^ (prefixWord ++ tailWord_5385693).sum := by decide
  have hdescent : baseEnd_5385693 < baseStart_5385693 := by decide
  rcases family_descends (prefixWord ++ tailWord_5385693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5385706 : List Nat := [3, 1, 3, 1, 4, 1, 1, 2, 2, 5]
def baseStart_5385706 : Nat := 118140960795 + 5385706 * 2 ^ 59
def prefixEnd_5385706 : Nat := 4983230072969 + 3 ^ 40 * 5385706 * 2
def baseEnd_5385706 : Nat := 921818613934536878068865

theorem tailTrace_5385706 : CollatzResearch.WordTrace tailWord_5385706 prefixEnd_5385706 921818613934536878068865 := by
  unfold tailWord_5385706
  simp only [CollatzResearch.WordTrace]
  refine ⟨49108208856628610550116243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130955223617676294800309981 49108208856628610550116243)
  ·
    refine ⟨73662313284942915825174365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49108208856628610550116243 73662313284942915825174365)
    ·
      refine ⟨27623367481853593434440387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73662313284942915825174365 27623367481853593434440387)
      ·
        refine ⟨41435051222780390151660581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27623367481853593434440387 41435051222780390151660581)
        ·
          refine ⟨7769072104271323153436359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41435051222780390151660581 7769072104271323153436359)
          ·
            refine ⟨11653608156406984730154539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7769072104271323153436359 11653608156406984730154539)
            ·
              refine ⟨17480412234610477095231809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11653608156406984730154539 17480412234610477095231809)
              ·
                refine ⟨13110309175957857821423857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17480412234610477095231809 13110309175957857821423857)
                ·
                  refine ⟨9832731881968393366067893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13110309175957857821423857 9832731881968393366067893)
                  ·
                    refine ⟨921818613934536878068865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9832731881968393366067893 921818613934536878068865)
                    ·
                      rfl

theorem cell23_5385706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 2, 2, 5].length) (baseStart_5385706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5385706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5385706 prefixEnd_5385706 := by exact prefixLift 5385706
  have htrace : WordTrace (prefixWord ++ tailWord_5385706) baseStart_5385706 baseEnd_5385706 := by
    simpa [prefixWord, tailWord_5385706, baseEnd_5385706] using wordTrace_append hprefix tailTrace_5385706
  have hstable : (prefixWord ++ tailWord_5385706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5385706).length < 2 ^ (prefixWord ++ tailWord_5385706).sum := by decide
  have hdescent : baseEnd_5385706 < baseStart_5385706 := by decide
  rcases family_descends (prefixWord ++ tailWord_5385706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5385719 : List Nat := [1, 1, 3, 1, 1, 1, 1, 7, 3, 4]
def baseStart_5385719 : Nat := 118140960795 + 5385719 * 2 ^ 59
def prefixEnd_5385719 : Nat := 4983230072969 + 3 ^ 40 * 5385719 * 2
def baseEnd_5385719 : Nat := 921820839017373027781345

theorem tailTrace_5385719 : CollatzResearch.WordTrace tailWord_5385719 prefixEnd_5385719 921820839017373027781345 := by
  unfold tailWord_5385719
  simp only [CollatzResearch.WordTrace]
  refine ⟨196433309575467345420688211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130955539716978230280458807 196433309575467345420688211)
  ·
    refine ⟨294649964363201018131032317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196433309575467345420688211 294649964363201018131032317)
    ·
      refine ⟨110493736636200381799137119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 294649964363201018131032317 110493736636200381799137119)
      ·
        refine ⟨165740604954300572698705679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110493736636200381799137119 165740604954300572698705679)
        ·
          refine ⟨248610907431450859048058519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165740604954300572698705679 248610907431450859048058519)
          ·
            refine ⟨372916361147176288572087779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 248610907431450859048058519 372916361147176288572087779)
            ·
              refine ⟨559374541720764432858131669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 372916361147176288572087779 559374541720764432858131669)
              ·
                refine ⟨13110340821580416395112461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 559374541720764432858131669 13110340821580416395112461)
                ·
                  refine ⟨4916377808092656148167173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13110340821580416395112461 4916377808092656148167173)
                  ·
                    refine ⟨921820839017373027781345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4916377808092656148167173 921820839017373027781345)
                    ·
                      rfl

theorem cell23_5385719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 7, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 7, 3, 4].length) (baseStart_5385719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5385719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5385719 prefixEnd_5385719 := by exact prefixLift 5385719
  have htrace : WordTrace (prefixWord ++ tailWord_5385719) baseStart_5385719 baseEnd_5385719 := by
    simpa [prefixWord, tailWord_5385719, baseEnd_5385719] using wordTrace_append hprefix tailTrace_5385719
  have hstable : (prefixWord ++ tailWord_5385719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5385719).length < 2 ^ (prefixWord ++ tailWord_5385719).sum := by decide
  have hdescent : baseEnd_5385719 < baseStart_5385719 := by decide
  rcases family_descends (prefixWord ++ tailWord_5385719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5385776 : List Nat := [2, 1, 1, 1, 2, 3, 1, 5, 3, 1, 3]
def baseStart_5385776 : Nat := 118140960795 + 5385776 * 2 ^ 59
def prefixEnd_5385776 : Nat := 4983230072969 + 3 ^ 40 * 5385776 * 2
def baseEnd_5385776 : Nat := 2765491785449425360331273

theorem tailTrace_5385776 : CollatzResearch.WordTrace tailWord_5385776 prefixEnd_5385776 2765491785449425360331273 := by
  unfold tailWord_5385776
  simp only [CollatzResearch.WordTrace]
  refine ⟨98217694268130422077756591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130956925690840562770342121 98217694268130422077756591)
  ·
    refine ⟨147326541402195633116634887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98217694268130422077756591 147326541402195633116634887)
    ·
      refine ⟨220989812103293449674952331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147326541402195633116634887 220989812103293449674952331)
      ·
        refine ⟨331484718154940174512428497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220989812103293449674952331 331484718154940174512428497)
        ·
          refine ⟨248613538616205130884321373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 331484718154940174512428497 248613538616205130884321373)
          ·
            refine ⟨93230076981076924081620515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 248613538616205130884321373 93230076981076924081620515)
            ·
              refine ⟨139845115471615386122430773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93230076981076924081620515 139845115471615386122430773)
              ·
                refine ⟨13110479575463942448977885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 139845115471615386122430773 13110479575463942448977885)
                ·
                  refine ⟨4916429840798978418366707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13110479575463942448977885 4916429840798978418366707)
                  ·
                    refine ⟨7374644761198467627550061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4916429840798978418366707 7374644761198467627550061)
                    ·
                      refine ⟨2765491785449425360331273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7374644761198467627550061 2765491785449425360331273)
                      ·
                        rfl

theorem cell23_5385776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 5, 3, 1, 3].length) (baseStart_5385776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5385776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5385776 prefixEnd_5385776 := by exact prefixLift 5385776
  have htrace : WordTrace (prefixWord ++ tailWord_5385776) baseStart_5385776 baseEnd_5385776 := by
    simpa [prefixWord, tailWord_5385776, baseEnd_5385776] using wordTrace_append hprefix tailTrace_5385776
  have hstable : (prefixWord ++ tailWord_5385776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5385776).length < 2 ^ (prefixWord ++ tailWord_5385776).sum := by decide
  have hdescent : baseEnd_5385776 < baseStart_5385776 := by decide
  rcases family_descends (prefixWord ++ tailWord_5385776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5385779 : List Nat := [1, 1, 1, 2, 4, 3, 1, 2, 3, 5]
def baseStart_5385779 : Nat := 118140960795 + 5385779 * 2 ^ 59
def prefixEnd_5385779 : Nat := 4983230072969 + 3 ^ 40 * 5385779 * 2
def baseEnd_5385779 : Nat := 921831108630462949531253

theorem tailTrace_5385779 : CollatzResearch.WordTrace tailWord_5385779 prefixEnd_5385779 921831108630462949531253 := by
  unfold tailWord_5385779
  simp only [CollatzResearch.WordTrace]
  refine ⟨196435497955249975667872391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130956998636833317111914927 196435497955249975667872391)
  ·
    refine ⟨294653246932874963501808587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196435497955249975667872391 294653246932874963501808587)
    ·
      refine ⟨441979870399312445252712881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294653246932874963501808587 441979870399312445252712881)
      ·
        refine ⟨331484902799484333939534661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 441979870399312445252712881 331484902799484333939534661)
        ·
          refine ⟨62153419274903312613662749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 331484902799484333939534661 62153419274903312613662749)
          ·
            refine ⟨23307532228088742230123531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62153419274903312613662749 23307532228088742230123531)
            ·
              refine ⟨34961298342133113345185297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23307532228088742230123531 34961298342133113345185297)
              ·
                refine ⟨26220973756599835008888973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34961298342133113345185297 26220973756599835008888973)
                ·
                  refine ⟨9832865158724938128333365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26220973756599835008888973 9832865158724938128333365)
                  ·
                    refine ⟨921831108630462949531253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9832865158724938128333365 921831108630462949531253)
                    ·
                      rfl

theorem cell23_5385779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 2, 3, 5].length) (baseStart_5385779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5385779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5385779 prefixEnd_5385779 := by exact prefixLift 5385779
  have htrace : WordTrace (prefixWord ++ tailWord_5385779) baseStart_5385779 baseEnd_5385779 := by
    simpa [prefixWord, tailWord_5385779, baseEnd_5385779] using wordTrace_append hprefix tailTrace_5385779
  have hstable : (prefixWord ++ tailWord_5385779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5385779).length < 2 ^ (prefixWord ++ tailWord_5385779).sum := by decide
  have hdescent : baseEnd_5385779 < baseStart_5385779 := by decide
  rcases family_descends (prefixWord ++ tailWord_5385779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5385786 : List Nat := [3, 1, 1, 1, 3, 2, 2, 2, 1, 5, 2]
def baseStart_5385786 : Nat := 118140960795 + 5385786 * 2 ^ 59
def prefixEnd_5385786 : Nat := 4983230072969 + 3 ^ 40 * 5385786 * 2
def baseEnd_5385786 : Nat := 2765496920255970321206227

theorem tailTrace_5385786 : CollatzResearch.WordTrace tailWord_5385786 prefixEnd_5385786 2765496920255970321206227 := by
  unfold tailWord_5385786
  simp only [CollatzResearch.WordTrace]
  refine ⟨49108938316556153965844303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130957168844149743908918141 49108938316556153965844303)
  ·
    refine ⟨73663407474834230948766455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49108938316556153965844303 73663407474834230948766455)
    ·
      refine ⟨110495111212251346423149683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73663407474834230948766455 110495111212251346423149683)
      ·
        refine ⟨165742666818377019634724525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110495111212251346423149683 165742666818377019634724525)
        ·
          refine ⟨62153500056891382363021697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 165742666818377019634724525 62153500056891382363021697)
          ·
            refine ⟨46615125042668536772266273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62153500056891382363021697 46615125042668536772266273)
            ·
              refine ⟨34961343782001402579199705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46615125042668536772266273 34961343782001402579199705)
              ·
                refine ⟨26221007836501051934399779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34961343782001402579199705 26221007836501051934399779)
                ·
                  refine ⟨39331511754751577901599669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26221007836501051934399779 39331511754751577901599669)
                  ·
                    refine ⟨3687329227007960428274969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39331511754751577901599669 3687329227007960428274969)
                    ·
                      refine ⟨2765496920255970321206227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3687329227007960428274969 2765496920255970321206227)
                      ·
                        rfl

theorem cell23_5385786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 2, 1, 5, 2].length) (baseStart_5385786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5385786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5385786 prefixEnd_5385786 := by exact prefixLift 5385786
  have htrace : WordTrace (prefixWord ++ tailWord_5385786) baseStart_5385786 baseEnd_5385786 := by
    simpa [prefixWord, tailWord_5385786, baseEnd_5385786] using wordTrace_append hprefix tailTrace_5385786
  have hstable : (prefixWord ++ tailWord_5385786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5385786).length < 2 ^ (prefixWord ++ tailWord_5385786).sum := by decide
  have hdescent : baseEnd_5385786 < baseStart_5385786 := by decide
  rcases family_descends (prefixWord ++ tailWord_5385786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5385793 : List Nat := [1, 2, 5, 1, 1, 1, 3, 2, 3, 1, 3]
def baseStart_5385793 : Nat := 118140960795 + 5385793 * 2 ^ 59
def prefixEnd_5385793 : Nat := 4983230072969 + 3 ^ 40 * 5385793 * 2
def baseEnd_5385793 : Nat := 2765500514620551793818695

theorem tailTrace_5385793 : CollatzResearch.WordTrace tailWord_5385793 prefixEnd_5385793 2765500514620551793818695 := by
  unfold tailWord_5385793
  simp only [CollatzResearch.WordTrace]
  refine ⟨196436008577199256058882033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130957339051466170705921355 196436008577199256058882033)
  ·
    refine ⟨147327006432899442044161525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196436008577199256058882033 147327006432899442044161525)
    ·
      refine ⟨13811906853084322691640143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 147327006432899442044161525 13811906853084322691640143)
      ·
        refine ⟨20717860279626484037460215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13811906853084322691640143 20717860279626484037460215)
        ·
          refine ⟨31076790419439726056190323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20717860279626484037460215 31076790419439726056190323)
          ·
            refine ⟨46615185629159589084285485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31076790419439726056190323 46615185629159589084285485)
            ·
              refine ⟨17480694610934845906607057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46615185629159589084285485 17480694610934845906607057)
              ·
                refine ⟨13110520958201134429955293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17480694610934845906607057 13110520958201134429955293)
                ·
                  refine ⟨4916445359325425411233235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13110520958201134429955293 4916445359325425411233235)
                  ·
                    refine ⟨7374668038988138116849853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4916445359325425411233235 7374668038988138116849853)
                    ·
                      refine ⟨2765500514620551793818695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7374668038988138116849853 2765500514620551793818695)
                      ·
                        rfl

theorem cell23_5385793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 2, 3, 1, 3].length) (baseStart_5385793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5385793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5385793 prefixEnd_5385793 := by exact prefixLift 5385793
  have htrace : WordTrace (prefixWord ++ tailWord_5385793) baseStart_5385793 baseEnd_5385793 := by
    simpa [prefixWord, tailWord_5385793, baseEnd_5385793] using wordTrace_append hprefix tailTrace_5385793
  have hstable : (prefixWord ++ tailWord_5385793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5385793).length < 2 ^ (prefixWord ++ tailWord_5385793).sum := by decide
  have hdescent : baseEnd_5385793 < baseStart_5385793 := by decide
  rcases family_descends (prefixWord ++ tailWord_5385793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5385809 : List Nat := [1, 2, 2, 1, 3, 2, 1, 4, 1, 6]
def baseStart_5385809 : Nat := 118140960795 + 5385809 * 2 ^ 59
def prefixEnd_5385809 : Nat := 4983230072969 + 3 ^ 40 * 5385809 * 2
def baseEnd_5385809 : Nat := 921836243437007910406207

theorem tailTrace_5385809 : CollatzResearch.WordTrace tailWord_5385809 prefixEnd_5385809 921836243437007910406207 := by
  unfold tailWord_5385809
  simp only [CollatzResearch.WordTrace]
  refine ⟨196436592145141290791464481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130957728096760860527642987 196436592145141290791464481)
  ·
    refine ⟨147327444108855968093598361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196436592145141290791464481 147327444108855968093598361)
    ·
      refine ⟨110495583081641976070198771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147327444108855968093598361 110495583081641976070198771)
      ·
        refine ⟨165743374622462964105298157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110495583081641976070198771 165743374622462964105298157)
        ·
          refine ⟨62153765483423611539486809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 165743374622462964105298157 62153765483423611539486809)
          ·
            refine ⟨46615324112567708654615107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62153765483423611539486809 46615324112567708654615107)
            ·
              refine ⟨69922986168851562981922661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46615324112567708654615107 69922986168851562981922661)
              ·
                refine ⟨13110559906659668059110499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69922986168851562981922661 13110559906659668059110499)
                ·
                  refine ⟨19665839859989502088665749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13110559906659668059110499 19665839859989502088665749)
                  ·
                    refine ⟨921836243437007910406207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19665839859989502088665749 921836243437007910406207)
                    ·
                      rfl

theorem cell23_5385809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 4, 1, 6].length) (baseStart_5385809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5385809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5385809 prefixEnd_5385809 := by exact prefixLift 5385809
  have htrace : WordTrace (prefixWord ++ tailWord_5385809) baseStart_5385809 baseEnd_5385809 := by
    simpa [prefixWord, tailWord_5385809, baseEnd_5385809] using wordTrace_append hprefix tailTrace_5385809
  have hstable : (prefixWord ++ tailWord_5385809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5385809).length < 2 ^ (prefixWord ++ tailWord_5385809).sum := by decide
  have hdescent : baseEnd_5385809 < baseStart_5385809 := by decide
  rcases family_descends (prefixWord ++ tailWord_5385809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5385810 : List Nat := [3, 2, 2, 1, 2, 2, 1, 5, 1, 1, 3]
def baseStart_5385810 : Nat := 118140960795 + 5385810 * 2 ^ 59
def prefixEnd_5385810 : Nat := 4983230072969 + 3 ^ 40 * 5385810 * 2
def baseEnd_5385810 : Nat := 2765509243791678227306117

theorem tailTrace_5385810 : CollatzResearch.WordTrace tailWord_5385810 prefixEnd_5385810 2765509243791678227306117 := by
  unfold tailWord_5385810
  simp only [CollatzResearch.WordTrace]
  refine ⟨49109157154534416990562721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130957752412091778641500589 49109157154534416990562721)
  ·
    refine ⟨36831867865900812742922041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49109157154534416990562721 36831867865900812742922041)
    ·
      refine ⟨27623900899425609557191531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36831867865900812742922041 27623900899425609557191531)
      ·
        refine ⟨41435851349138414335787297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27623900899425609557191531 41435851349138414335787297)
        ·
          refine ⟨31076888511853810751840473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41435851349138414335787297 31076888511853810751840473)
          ·
            refine ⟨23307666383890358063880355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31076888511853810751840473 23307666383890358063880355)
            ·
              refine ⟨34961499575835537095820533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23307666383890358063880355 34961499575835537095820533)
              ·
                refine ⟨3277640585234581602733175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34961499575835537095820533 3277640585234581602733175)
                ·
                  refine ⟨4916460877851872404099763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3277640585234581602733175 4916460877851872404099763)
                  ·
                    refine ⟨7374691316777808606149645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4916460877851872404099763 7374691316777808606149645)
                    ·
                      refine ⟨2765509243791678227306117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7374691316777808606149645 2765509243791678227306117)
                      ·
                        rfl

theorem cell23_5385810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 5, 1, 1, 3].length) (baseStart_5385810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5385810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5385810 prefixEnd_5385810 := by exact prefixLift 5385810
  have htrace : WordTrace (prefixWord ++ tailWord_5385810) baseStart_5385810 baseEnd_5385810 := by
    simpa [prefixWord, tailWord_5385810, baseEnd_5385810] using wordTrace_append hprefix tailTrace_5385810
  have hstable : (prefixWord ++ tailWord_5385810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5385810).length < 2 ^ (prefixWord ++ tailWord_5385810).sum := by decide
  have hdescent : baseEnd_5385810 < baseStart_5385810 := by decide
  rcases family_descends (prefixWord ++ tailWord_5385810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5385833 : List Nat := [1, 2, 1, 1, 1, 4, 3, 3, 3, 2, 2]
def baseStart_5385833 : Nat := 118140960795 + 5385833 * 2 ^ 59
def prefixEnd_5385833 : Nat := 4983230072969 + 3 ^ 40 * 5385833 * 2
def baseEnd_5385833 : Nat := 2765521053846731637318511

theorem tailTrace_5385833 : CollatzResearch.WordTrace tailWord_5385833 prefixEnd_5385833 2765521053846731637318511 := by
  unfold tailWord_5385833
  simp only [CollatzResearch.WordTrace]
  refine ⟨196437467497054342890338153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130958311664702895260225435 196437467497054342890338153)
  ·
    refine ⟨147328100622790757167753615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196437467497054342890338153 147328100622790757167753615)
    ·
      refine ⟨220992150934186135751630423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147328100622790757167753615 220992150934186135751630423)
      ·
        refine ⟨331488226401279203627445635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220992150934186135751630423 331488226401279203627445635)
        ·
          refine ⟨497232339601918805441168453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 331488226401279203627445635 497232339601918805441168453)
          ·
            refine ⟨93231063675359776020219085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 497232339601918805441168453 93231063675359776020219085)
            ·
              refine ⟨34961648878259916007582157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93231063675359776020219085 34961648878259916007582157)
              ·
                refine ⟨13110618329347468502843309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34961648878259916007582157 13110618329347468502843309)
                ·
                  refine ⟨4916481873505300688566241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13110618329347468502843309 4916481873505300688566241)
                  ·
                    refine ⟨3687361405128975516424681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4916481873505300688566241 3687361405128975516424681)
                    ·
                      refine ⟨2765521053846731637318511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3687361405128975516424681 2765521053846731637318511)
                      ·
                        rfl

theorem cell23_5385833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 3, 3, 2, 2].length) (baseStart_5385833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5385833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5385833 prefixEnd_5385833 := by exact prefixLift 5385833
  have htrace : WordTrace (prefixWord ++ tailWord_5385833) baseStart_5385833 baseEnd_5385833 := by
    simpa [prefixWord, tailWord_5385833, baseEnd_5385833] using wordTrace_append hprefix tailTrace_5385833
  have hstable : (prefixWord ++ tailWord_5385833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5385833).length < 2 ^ (prefixWord ++ tailWord_5385833).sum := by decide
  have hdescent : baseEnd_5385833 < baseStart_5385833 := by decide
  rcases family_descends (prefixWord ++ tailWord_5385833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5385853 : List Nat := [1, 4, 1, 1, 4, 1, 1, 4, 1, 2, 3]
def baseStart_5385853 : Nat := 118140960795 + 5385853 * 2 ^ 59
def prefixEnd_5385853 : Nat := 4983230072969 + 3 ^ 40 * 5385853 * 2
def baseEnd_5385853 : Nat := 2765531323459821559068419

theorem tailTrace_5385853 : CollatzResearch.WordTrace tailWord_5385853 prefixEnd_5385853 2765531323459821559068419 := by
  unfold tailWord_5385853
  simp only [CollatzResearch.WordTrace]
  refine ⟨196438196956981886306066213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130958797971321257537377475 196438196956981886306066213)
  ·
    refine ⟨36832161929434103682387415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 196438196956981886306066213 36832161929434103682387415)
    ·
      refine ⟨55248242894151155523581123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36832161929434103682387415 55248242894151155523581123)
      ·
        refine ⟨82872364341226733285371685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55248242894151155523581123 82872364341226733285371685)
        ·
          refine ⟨15538568313980012491007191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82872364341226733285371685 15538568313980012491007191)
          ·
            refine ⟨23307852470970018736510787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15538568313980012491007191 23307852470970018736510787)
            ·
              refine ⟨34961778706455028104766181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23307852470970018736510787 34961778706455028104766181)
              ·
                refine ⟨6555333507460317769643659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34961778706455028104766181 6555333507460317769643659)
                ·
                  refine ⟨9833000261190476654465489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6555333507460317769643659 9833000261190476654465489)
                  ·
                    refine ⟨7374750195892857490849117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9833000261190476654465489 7374750195892857490849117)
                    ·
                      refine ⟨2765531323459821559068419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7374750195892857490849117 2765531323459821559068419)
                      ·
                        rfl

theorem cell23_5385853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 4, 1, 2, 3].length) (baseStart_5385853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5385853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5385853 prefixEnd_5385853 := by exact prefixLift 5385853
  have htrace : WordTrace (prefixWord ++ tailWord_5385853) baseStart_5385853 baseEnd_5385853 := by
    simpa [prefixWord, tailWord_5385853, baseEnd_5385853] using wordTrace_append hprefix tailTrace_5385853
  have hstable : (prefixWord ++ tailWord_5385853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5385853).length < 2 ^ (prefixWord ++ tailWord_5385853).sum := by decide
  have hdescent : baseEnd_5385853 < baseStart_5385853 := by decide
  rcases family_descends (prefixWord ++ tailWord_5385853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5385884 : List Nat := [2, 2, 3, 2, 4, 1, 1, 1, 3, 2, 2]
def baseStart_5385884 : Nat := 118140960795 + 5385884 * 2 ^ 59
def prefixEnd_5385884 : Nat := 4983230072969 + 3 ^ 40 * 5385884 * 2
def baseEnd_5385884 : Nat := 2765547241360110937780777

theorem tailTrace_5385884 : CollatzResearch.WordTrace tailWord_5385884 prefixEnd_5385884 2765547241360110937780777 := by
  unfold tailWord_5385884
  simp only [CollatzResearch.WordTrace]
  refine ⟨98219663809934789300222353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130959551746579719066963137 98219663809934789300222353)
  ·
    refine ⟨73664747857451091975166765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98219663809934789300222353 73664747857451091975166765)
    ·
      refine ⟨27624280446544159490687537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73664747857451091975166765 27624280446544159490687537)
      ·
        refine ⟨20718210334908119618015653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27624280446544159490687537 20718210334908119618015653)
        ·
          refine ⟨3884664437795272428377935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20718210334908119618015653 3884664437795272428377935)
          ·
            refine ⟨5826996656692908642566903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3884664437795272428377935 5826996656692908642566903)
            ·
              refine ⟨8740494985039362963850355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5826996656692908642566903 8740494985039362963850355)
              ·
                refine ⟨13110742477559044445775533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8740494985039362963850355 13110742477559044445775533)
                ·
                  refine ⟨4916528429084641667165825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13110742477559044445775533 4916528429084641667165825)
                  ·
                    refine ⟨3687396321813481250374369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4916528429084641667165825 3687396321813481250374369)
                    ·
                      refine ⟨2765547241360110937780777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3687396321813481250374369 2765547241360110937780777)
                      ·
                        rfl

theorem cell23_5385884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 1, 1, 3, 2, 2].length) (baseStart_5385884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5385884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5385884 prefixEnd_5385884 := by exact prefixLift 5385884
  have htrace : WordTrace (prefixWord ++ tailWord_5385884) baseStart_5385884 baseEnd_5385884 := by
    simpa [prefixWord, tailWord_5385884, baseEnd_5385884] using wordTrace_append hprefix tailTrace_5385884
  have hstable : (prefixWord ++ tailWord_5385884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5385884).length < 2 ^ (prefixWord ++ tailWord_5385884).sum := by decide
  have hdescent : baseEnd_5385884 < baseStart_5385884 := by decide
  rcases family_descends (prefixWord ++ tailWord_5385884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5385953 : List Nat := [1, 2, 3, 1, 5, 1, 1, 1, 2, 2, 4]
def baseStart_5385953 : Nat := 118140960795 + 5385953 * 2 ^ 59
def prefixEnd_5385953 : Nat := 4983230072969 + 3 ^ 40 * 5385953 * 2
def baseEnd_5385953 : Nat := 2765582671525271167817959

theorem tailTrace_5385953 : CollatzResearch.WordTrace tailWord_5385953 prefixEnd_5385953 2765582671525271167817959 := by
  unfold tailWord_5385953
  simp only [CollatzResearch.WordTrace]
  refine ⟨196441844256619603384706513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130961229504413068923137675 196441844256619603384706513)
  ·
    refine ⟨147331383192464702538529885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196441844256619603384706513 147331383192464702538529885)
    ·
      refine ⟨55249268697174263451948707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147331383192464702538529885 55249268697174263451948707)
      ·
        refine ⟨82873903045761395177923061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55249268697174263451948707 82873903045761395177923061)
        ·
          refine ⟨7769428410540130797930287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 82873903045761395177923061 7769428410540130797930287)
          ·
            refine ⟨11654142615810196196895431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7769428410540130797930287 11654142615810196196895431)
            ·
              refine ⟨17481213923715294295343147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11654142615810196196895431 17481213923715294295343147)
              ·
                refine ⟨26221820885572941443014721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17481213923715294295343147 26221820885572941443014721)
                ·
                  refine ⟨19666365664179706082261041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26221820885572941443014721 19666365664179706082261041)
                  ·
                    refine ⟨14749774248134779561695781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19666365664179706082261041 14749774248134779561695781)
                    ·
                      refine ⟨2765582671525271167817959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14749774248134779561695781 2765582671525271167817959)
                      ·
                        rfl

theorem cell23_5385953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 1, 2, 2, 4].length) (baseStart_5385953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5385953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5385953 prefixEnd_5385953 := by exact prefixLift 5385953
  have htrace : WordTrace (prefixWord ++ tailWord_5385953) baseStart_5385953 baseEnd_5385953 := by
    simpa [prefixWord, tailWord_5385953, baseEnd_5385953] using wordTrace_append hprefix tailTrace_5385953
  have hstable : (prefixWord ++ tailWord_5385953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5385953).length < 2 ^ (prefixWord ++ tailWord_5385953).sum := by decide
  have hdescent : baseEnd_5385953 < baseStart_5385953 := by decide
  rcases family_descends (prefixWord ++ tailWord_5385953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5385976 : List Nat := [2, 1, 2, 1, 1, 2, 2, 5, 2, 5]
def baseStart_5385976 : Nat := 118140960795 + 5385976 * 2 ^ 59
def prefixEnd_5385976 : Nat := 4983230072969 + 3 ^ 40 * 5385976 * 2
def baseEnd_5385976 : Nat := 921864827193441525943451

theorem tailTrace_5385976 : CollatzResearch.WordTrace tailWord_5385976 prefixEnd_5385976 921864827193441525943451 := by
  unfold tailWord_5385976
  simp only [CollatzResearch.WordTrace]
  refine ⟨98221341567768139156396891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130961788757024185541862521 98221341567768139156396891)
  ·
    refine ⟨147332012351652208734595337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98221341567768139156396891 147332012351652208734595337)
    ·
      refine ⟨110499009263739156550946503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147332012351652208734595337 110499009263739156550946503)
      ·
        refine ⟨165748513895608734826419755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110499009263739156550946503 165748513895608734826419755)
        ·
          refine ⟨248622770843413102239629633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165748513895608734826419755 248622770843413102239629633)
          ·
            refine ⟨186467078132559826679722225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 248622770843413102239629633 186467078132559826679722225)
            ·
              refine ⟨139850308599419870009791669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 186467078132559826679722225 139850308599419870009791669)
              ·
                refine ⟨13110966431195612813417969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 139850308599419870009791669 13110966431195612813417969)
                ·
                  refine ⟨9833224823396709610063477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13110966431195612813417969 9833224823396709610063477)
                  ·
                    refine ⟨921864827193441525943451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9833224823396709610063477 921864827193441525943451)
                    ·
                      rfl

theorem cell23_5385976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 5, 2, 5].length) (baseStart_5385976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5385976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5385976 prefixEnd_5385976 := by exact prefixLift 5385976
  have htrace : WordTrace (prefixWord ++ tailWord_5385976) baseStart_5385976 baseEnd_5385976 := by
    simpa [prefixWord, tailWord_5385976, baseEnd_5385976] using wordTrace_append hprefix tailTrace_5385976
  have hstable : (prefixWord ++ tailWord_5385976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5385976).length < 2 ^ (prefixWord ++ tailWord_5385976).sum := by decide
  have hdescent : baseEnd_5385976 < baseStart_5385976 := by decide
  rcases family_descends (prefixWord ++ tailWord_5385976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5385991 : List Nat := [1, 1, 4, 4, 3, 1, 1, 2, 2, 2, 2]
def baseStart_5385991 : Nat := 118140960795 + 5385991 * 2 ^ 59
def prefixEnd_5385991 : Nat := 4983230072969 + 3 ^ 40 * 5385991 * 2
def baseEnd_5385991 : Nat := 2765602183790142019142785

theorem tailTrace_5385991 : CollatzResearch.WordTrace tailWord_5385991 prefixEnd_5385991 2765602183790142019142785 := by
  unfold tailWord_5385991
  simp only [CollatzResearch.WordTrace]
  refine ⟨196443230230481935874589827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130962153486987957249726551 196443230230481935874589827)
  ·
    refine ⟨294664845345722903811884741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196443230230481935874589827 294664845345722903811884741)
    ·
      refine ⟨55249658502323044464728389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 294664845345722903811884741 55249658502323044464728389)
      ·
        refine ⟨10359310969185570837136573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55249658502323044464728389 10359310969185570837136573)
        ·
          refine ⟨3884741613444589063926215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10359310969185570837136573 3884741613444589063926215)
          ·
            refine ⟨5827112420166883595889323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3884741613444589063926215 5827112420166883595889323)
            ·
              refine ⟨8740668630250325393833985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5827112420166883595889323 8740668630250325393833985)
              ·
                refine ⟨6555501472687744045375489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8740668630250325393833985 6555501472687744045375489)
                ·
                  refine ⟨4916626104515808034031617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6555501472687744045375489 4916626104515808034031617)
                  ·
                    refine ⟨3687469578386856025523713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4916626104515808034031617 3687469578386856025523713)
                    ·
                      refine ⟨2765602183790142019142785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3687469578386856025523713 2765602183790142019142785)
                      ·
                        rfl

theorem cell23_5385991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 1, 2, 2, 2, 2].length) (baseStart_5385991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5385991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5385991 prefixEnd_5385991 := by exact prefixLift 5385991
  have htrace : WordTrace (prefixWord ++ tailWord_5385991) baseStart_5385991 baseEnd_5385991 := by
    simpa [prefixWord, tailWord_5385991, baseEnd_5385991] using wordTrace_append hprefix tailTrace_5385991
  have hstable : (prefixWord ++ tailWord_5385991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5385991).length < 2 ^ (prefixWord ++ tailWord_5385991).sum := by decide
  have hdescent : baseEnd_5385991 < baseStart_5385991 := by decide
  rcases family_descends (prefixWord ++ tailWord_5385991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5386033 : List Nat := [1, 2, 2, 3, 2, 2, 2, 1, 1, 4, 3]
def baseStart_5386033 : Nat := 118140960795 + 5386033 * 2 ^ 59
def prefixEnd_5386033 : Nat := 4983230072969 + 3 ^ 40 * 5386033 * 2
def baseEnd_5386033 : Nat := 2765623749977630854817591

theorem tailTrace_5386033 : CollatzResearch.WordTrace tailWord_5386033 prefixEnd_5386033 2765623749977630854817591 := by
  unfold tailWord_5386033
  simp only [CollatzResearch.WordTrace]
  refine ⟨196444762096329777047618753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130963174730886518031745835 196444762096329777047618753)
  ·
    refine ⟨147333571572247332785714065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196444762096329777047618753 147333571572247332785714065)
    ·
      refine ⟨110500178679185499589285549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147333571572247332785714065 110500178679185499589285549)
      ·
        refine ⟨41437567004694562345982081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110500178679185499589285549 41437567004694562345982081)
        ·
          refine ⟨31078175253520921759486561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41437567004694562345982081 31078175253520921759486561)
          ·
            refine ⟨23308631440140691319614921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31078175253520921759486561 23308631440140691319614921)
            ·
              refine ⟨17481473580105518489711191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23308631440140691319614921 17481473580105518489711191)
              ·
                refine ⟨26222210370158277734566787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17481473580105518489711191 26222210370158277734566787)
                ·
                  refine ⟨39333315555237416601850181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26222210370158277734566787 39333315555237416601850181)
                  ·
                    refine ⟨7374996666607015612846909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39333315555237416601850181 7374996666607015612846909)
                    ·
                      refine ⟨2765623749977630854817591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7374996666607015612846909 2765623749977630854817591)
                      ·
                        rfl

theorem cell23_5386033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 1, 1, 4, 3].length) (baseStart_5386033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5386033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5386033 prefixEnd_5386033 := by exact prefixLift 5386033
  have htrace : WordTrace (prefixWord ++ tailWord_5386033) baseStart_5386033 baseEnd_5386033 := by
    simpa [prefixWord, tailWord_5386033, baseEnd_5386033] using wordTrace_append hprefix tailTrace_5386033
  have hstable : (prefixWord ++ tailWord_5386033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5386033).length < 2 ^ (prefixWord ++ tailWord_5386033).sum := by decide
  have hdescent : baseEnd_5386033 < baseStart_5386033 := by decide
  rcases family_descends (prefixWord ++ tailWord_5386033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5386057 : List Nat := [1, 2, 1, 1, 2, 4, 5, 2, 1, 4]
def baseStart_5386057 : Nat := 118140960795 + 5386057 * 2 ^ 59
def prefixEnd_5386057 : Nat := 4983230072969 + 3 ^ 40 * 5386057 * 2
def baseEnd_5386057 : Nat := 921878691171112920305827

theorem tailTrace_5386057 : CollatzResearch.WordTrace tailWord_5386057 prefixEnd_5386057 921878691171112920305827 := by
  unfold tailWord_5386057
  simp only [CollatzResearch.WordTrace]
  refine ⟨196445637448242829146492425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130963758298828552764328283 196445637448242829146492425)
  ·
    refine ⟨147334228086182121859869319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196445637448242829146492425 147334228086182121859869319)
    ·
      refine ⟨221001342129273182789803979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147334228086182121859869319 221001342129273182789803979)
      ·
        refine ⟨331502013193909774184705969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221001342129273182789803979 331502013193909774184705969)
        ·
          refine ⟨248626509895432330638529477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 331502013193909774184705969 248626509895432330638529477)
          ·
            refine ⟨46617470605393561994724277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 248626509895432330638529477 46617470605393561994724277)
            ·
              refine ⟨4370387869255646437005401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46617470605393561994724277 4370387869255646437005401)
              ·
                refine ⟨3277790901941734827754051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4370387869255646437005401 3277790901941734827754051)
                ·
                  refine ⟨4916686352912602241631077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3277790901941734827754051 4916686352912602241631077)
                  ·
                    refine ⟨921878691171112920305827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4916686352912602241631077 921878691171112920305827)
                    ·
                      rfl

theorem cell23_5386057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 5, 2, 1, 4].length) (baseStart_5386057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5386057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5386057 prefixEnd_5386057 := by exact prefixLift 5386057
  have htrace : WordTrace (prefixWord ++ tailWord_5386057) baseStart_5386057 baseEnd_5386057 := by
    simpa [prefixWord, tailWord_5386057, baseEnd_5386057] using wordTrace_append hprefix tailTrace_5386057
  have hstable : (prefixWord ++ tailWord_5386057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5386057).length < 2 ^ (prefixWord ++ tailWord_5386057).sum := by decide
  have hdescent : baseEnd_5386057 < baseStart_5386057 := by decide
  rcases family_descends (prefixWord ++ tailWord_5386057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5386097 : List Nat := [1, 2, 2, 2, 1, 3, 2, 5, 1, 1, 3]
def baseStart_5386097 : Nat := 118140960795 + 5386097 * 2 ^ 59
def prefixEnd_5386097 : Nat := 4983230072969 + 3 ^ 40 * 5386097 * 2
def baseEnd_5386097 : Nat := 2765656612739518604417297

theorem tailTrace_5386097 : CollatzResearch.WordTrace tailWord_5386097 prefixEnd_5386097 2765656612739518604417297 := by
  unfold tailWord_5386097
  simp only [CollatzResearch.WordTrace]
  refine ⟨196447096368097915977948545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130964730912065277318632363 196447096368097915977948545)
  ·
    refine ⟨147335322276073436983461409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196447096368097915977948545 147335322276073436983461409)
    ·
      refine ⟨110501491707055077737596057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147335322276073436983461409 110501491707055077737596057)
      ·
        refine ⟨82876118780291308303197043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110501491707055077737596057 82876118780291308303197043)
        ·
          refine ⟨124314178170436962454795565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82876118780291308303197043 124314178170436962454795565)
          ·
            refine ⟨46617816813913860920548337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 124314178170436962454795565 46617816813913860920548337)
            ·
              refine ⟨34963362610435395690411253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46617816813913860920548337 34963362610435395690411253)
              ·
                refine ⟨3277815244728318345976055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34963362610435395690411253 3277815244728318345976055)
                ·
                  refine ⟨4916722867092477518964083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3277815244728318345976055 4916722867092477518964083)
                  ·
                    refine ⟨7375084300638716278446125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4916722867092477518964083 7375084300638716278446125)
                    ·
                      refine ⟨2765656612739518604417297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7375084300638716278446125 2765656612739518604417297)
                      ·
                        rfl

theorem cell23_5386097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 5, 1, 1, 3].length) (baseStart_5386097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5386097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5386097 prefixEnd_5386097 := by exact prefixLift 5386097
  have htrace : WordTrace (prefixWord ++ tailWord_5386097) baseStart_5386097 baseEnd_5386097 := by
    simpa [prefixWord, tailWord_5386097, baseEnd_5386097] using wordTrace_append hprefix tailTrace_5386097
  have hstable : (prefixWord ++ tailWord_5386097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5386097).length < 2 ^ (prefixWord ++ tailWord_5386097).sum := by decide
  have hdescent : baseEnd_5386097 < baseStart_5386097 := by decide
  rcases family_descends (prefixWord ++ tailWord_5386097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5386130 : List Nat := [3, 2, 3, 2, 1, 1, 1, 3, 1, 6]
def baseStart_5386130 : Nat := 118140960795 + 5386130 * 2 ^ 59
def prefixEnd_5386130 : Nat := 4983230072969 + 3 ^ 40 * 5386130 * 2
def baseEnd_5386130 : Nat := 921891185867038991768215

theorem tailTrace_5386130 : CollatzResearch.WordTrace tailWord_5386130 prefixEnd_5386130 921891185867038991768215 := by
  unfold tailWord_5386130
  simp only [CollatzResearch.WordTrace]
  refine ⟨49112074994244590653474961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130965533317985575075933229 49112074994244590653474961)
  ·
    refine ⟨36834056245683442990106221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49112074994244590653474961 36834056245683442990106221)
    ·
      refine ⟨13812771092131291121289833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36834056245683442990106221 13812771092131291121289833)
      ·
        refine ⟨10359578319098468340967375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13812771092131291121289833 10359578319098468340967375)
        ·
          refine ⟨15539367478647702511451063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10359578319098468340967375 15539367478647702511451063)
          ·
            refine ⟨23309051217971553767176595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15539367478647702511451063 23309051217971553767176595)
            ·
              refine ⟨34963576826957330650764893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23309051217971553767176595 34963576826957330650764893)
              ·
                refine ⟨13111341310108998994036835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34963576826957330650764893 13111341310108998994036835)
                ·
                  refine ⟨19667011965163498491055253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13111341310108998994036835 19667011965163498491055253)
                  ·
                    refine ⟨921891185867038991768215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19667011965163498491055253 921891185867038991768215)
                    ·
                      rfl

theorem cell23_5386130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_5386130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5386130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5386130 prefixEnd_5386130 := by exact prefixLift 5386130
  have htrace : WordTrace (prefixWord ++ tailWord_5386130) baseStart_5386130 baseEnd_5386130 := by
    simpa [prefixWord, tailWord_5386130, baseEnd_5386130] using wordTrace_append hprefix tailTrace_5386130
  have hstable : (prefixWord ++ tailWord_5386130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5386130).length < 2 ^ (prefixWord ++ tailWord_5386130).sum := by decide
  have hdescent : baseEnd_5386130 < baseStart_5386130 := by decide
  rcases family_descends (prefixWord ++ tailWord_5386130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5386153 : List Nat := [1, 2, 1, 1, 1, 1, 4, 3, 3, 3, 3]
def baseStart_5386153 : Nat := 118140960795 + 5386153 * 2 ^ 59
def prefixEnd_5386153 : Nat := 4983230072969 + 3 ^ 40 * 5386153 * 2
def baseEnd_5386153 : Nat := 2765685367656170385317039

theorem tailTrace_5386153 : CollatzResearch.WordTrace tailWord_5386153 prefixEnd_5386153 2765685367656170385317039 := by
  unfold tailWord_5386153
  simp only [CollatzResearch.WordTrace]
  refine ⟨196449138855895037541987113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130966092570596691694658075 196449138855895037541987113)
  ·
    refine ⟨147336854141921278156490335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196449138855895037541987113 147336854141921278156490335)
    ·
      refine ⟨221005281212881917234735503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147336854141921278156490335 221005281212881917234735503)
      ·
        refine ⟨331507921819322875852103255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221005281212881917234735503 331507921819322875852103255)
        ·
          refine ⟨497261882728984313778154883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 331507921819322875852103255 497261882728984313778154883)
          ·
            refine ⟨745892824093476470667232325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 497261882728984313778154883 745892824093476470667232325)
            ·
              refine ⟨139854904517526838250106061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 745892824093476470667232325 139854904517526838250106061)
              ·
                refine ⟨52445589194072564343789773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 139854904517526838250106061 52445589194072564343789773)
                ·
                  refine ⟨19667095947777211628921165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52445589194072564343789773 19667095947777211628921165)
                  ·
                    refine ⟨7375160980416454360845437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19667095947777211628921165 7375160980416454360845437)
                    ·
                      refine ⟨2765685367656170385317039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7375160980416454360845437 2765685367656170385317039)
                      ·
                        rfl

theorem cell23_5386153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 3, 3, 3, 3].length) (baseStart_5386153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5386153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5386153 prefixEnd_5386153 := by exact prefixLift 5386153
  have htrace : WordTrace (prefixWord ++ tailWord_5386153) baseStart_5386153 baseEnd_5386153 := by
    simpa [prefixWord, tailWord_5386153, baseEnd_5386153] using wordTrace_append hprefix tailTrace_5386153
  have hstable : (prefixWord ++ tailWord_5386153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5386153).length < 2 ^ (prefixWord ++ tailWord_5386153).sum := by decide
  have hdescent : baseEnd_5386153 < baseStart_5386153 := by decide
  rcases family_descends (prefixWord ++ tailWord_5386153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5386164 : List Nat := [2, 5, 2, 1, 2, 1, 1, 1, 4, 4]
def baseStart_5386164 : Nat := 118140960795 + 5386164 * 2 ^ 59
def prefixEnd_5386164 : Nat := 4983230072969 + 3 ^ 40 * 5386164 * 2
def baseEnd_5386164 : Nat := 921897005314456614093163

theorem tailTrace_5386164 : CollatzResearch.WordTrace tailWord_5386164 prefixEnd_5386164 921897005314456614093163 := by
  unfold tailWord_5386164
  simp only [CollatzResearch.WordTrace]
  refine ⟨98224770029427593210318773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130966360039236790947091697 98224770029427593210318773)
  ·
    refine ⟨9208572190258836863467385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 98224770029427593210318773 9208572190258836863467385)
    ·
      refine ⟨6906429142694127647600539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9208572190258836863467385 6906429142694127647600539)
      ·
        refine ⟨10359643714041191471400809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6906429142694127647600539 10359643714041191471400809)
        ·
          refine ⟨7769732785530893603550607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10359643714041191471400809 7769732785530893603550607)
          ·
            refine ⟨11654599178296340405325911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7769732785530893603550607 11654599178296340405325911)
            ·
              refine ⟨17481898767444510607988867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11654599178296340405325911 17481898767444510607988867)
              ·
                refine ⟨26222848151166765911983301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17481898767444510607988867 26222848151166765911983301)
                ·
                  refine ⟨4916784028343768608496869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26222848151166765911983301 4916784028343768608496869)
                  ·
                    refine ⟨921897005314456614093163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4916784028343768608496869 921897005314456614093163)
                    ·
                      rfl

theorem cell23_5386164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_5386164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5386164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5386164 prefixEnd_5386164 := by exact prefixLift 5386164
  have htrace : WordTrace (prefixWord ++ tailWord_5386164) baseStart_5386164 baseEnd_5386164 := by
    simpa [prefixWord, tailWord_5386164, baseEnd_5386164] using wordTrace_append hprefix tailTrace_5386164
  have hstable : (prefixWord ++ tailWord_5386164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5386164).length < 2 ^ (prefixWord ++ tailWord_5386164).sum := by decide
  have hdescent : baseEnd_5386164 < baseStart_5386164 := by decide
  rcases family_descends (prefixWord ++ tailWord_5386164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5386194 : List Nat := [3, 2, 2, 3, 3, 1, 2, 7]
def baseStart_5386194 : Nat := 118140960795 + 5386194 * 2 ^ 59
def prefixEnd_5386194 : Nat := 4983230072969 + 3 ^ 40 * 5386194 * 2
def baseEnd_5386194 : Nat := 102433571124555730552013

theorem tailTrace_5386194 : CollatzResearch.WordTrace tailWord_5386194 prefixEnd_5386194 102433571124555730552013 := by
  unfold tailWord_5386194
  simp only [CollatzResearch.WordTrace]
  refine ⟨49112658562186625386057409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130967089499164334362819757 49112658562186625386057409)
  ·
    refine ⟨36834493921639969039543057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49112658562186625386057409 36834493921639969039543057)
    ·
      refine ⟨27625870441229976779657293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36834493921639969039543057 27625870441229976779657293)
      ·
        refine ⟨10359701415461241292371485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27625870441229976779657293 10359701415461241292371485)
        ·
          refine ⟨3884888030797965484639307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10359701415461241292371485 3884888030797965484639307)
          ·
            refine ⟨5827332046196948226958961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3884888030797965484639307 5827332046196948226958961)
            ·
              refine ⟨4370499034647711170219221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5827332046196948226958961 4370499034647711170219221)
              ·
                refine ⟨102433571124555730552013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4370499034647711170219221 102433571124555730552013)
                ·
                  rfl

theorem cell23_5386194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 2, 7].length) (baseStart_5386194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5386194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5386194 prefixEnd_5386194 := by exact prefixLift 5386194
  have htrace : WordTrace (prefixWord ++ tailWord_5386194) baseStart_5386194 baseEnd_5386194 := by
    simpa [prefixWord, tailWord_5386194, baseEnd_5386194] using wordTrace_append hprefix tailTrace_5386194
  have hstable : (prefixWord ++ tailWord_5386194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5386194).length < 2 ^ (prefixWord ++ tailWord_5386194).sum := by decide
  have hdescent : baseEnd_5386194 < baseStart_5386194 := by decide
  rcases family_descends (prefixWord ++ tailWord_5386194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5386205 : List Nat := [1, 4, 3, 1, 4, 1, 1, 3, 1, 2, 2]
def baseStart_5386205 : Nat := 118140960795 + 5386205 * 2 ^ 59
def prefixEnd_5386205 : Nat := 4983230072969 + 3 ^ 40 * 5386205 * 2
def baseEnd_5386205 : Nat := 2765712068650204181866801

theorem tailTrace_5386205 : CollatzResearch.WordTrace tailWord_5386205 prefixEnd_5386205 2765712068650204181866801 := by
  unfold tailWord_5386205
  simp only [CollatzResearch.WordTrace]
  refine ⟨196451035451706650422880069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130967356967804433615253379 196451035451706650422880069)
  ·
    refine ⟨36834569147194996954290013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 196451035451706650422880069 36834569147194996954290013)
    ·
      refine ⟨13812963430198123857858755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36834569147194996954290013 13812963430198123857858755)
      ·
        refine ⟨20719445145297185786788133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13812963430198123857858755 20719445145297185786788133)
        ·
          refine ⟨3884895964743222335022775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20719445145297185786788133 3884895964743222335022775)
          ·
            refine ⟨5827343947114833502534163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3884895964743222335022775 5827343947114833502534163)
            ·
              refine ⟨8741015920672250253801245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5827343947114833502534163 8741015920672250253801245)
              ·
                refine ⟨3277880970252093845175467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8741015920672250253801245 3277880970252093845175467)
                ·
                  refine ⟨4916821455378140767763201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3277880970252093845175467 4916821455378140767763201)
                  ·
                    refine ⟨3687616091533605575822401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4916821455378140767763201 3687616091533605575822401)
                    ·
                      refine ⟨2765712068650204181866801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3687616091533605575822401 2765712068650204181866801)
                      ·
                        rfl

theorem cell23_5386205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 1, 3, 1, 2, 2].length) (baseStart_5386205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5386205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5386205 prefixEnd_5386205 := by exact prefixLift 5386205
  have htrace : WordTrace (prefixWord ++ tailWord_5386205) baseStart_5386205 baseEnd_5386205 := by
    simpa [prefixWord, tailWord_5386205, baseEnd_5386205] using wordTrace_append hprefix tailTrace_5386205
  have hstable : (prefixWord ++ tailWord_5386205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5386205).length < 2 ^ (prefixWord ++ tailWord_5386205).sum := by decide
  have hdescent : baseEnd_5386205 < baseStart_5386205 := by decide
  rcases family_descends (prefixWord ++ tailWord_5386205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5386238 : List Nat := [4, 2, 2, 2, 1, 3, 2, 1, 2, 1, 3]
def baseStart_5386238 : Nat := 118140960795 + 5386238 * 2 ^ 59
def prefixEnd_5386238 : Nat := 4983230072969 + 3 ^ 40 * 5386238 * 2
def baseEnd_5386238 : Nat := 2765729013511802552754149

theorem tailTrace_5386238 : CollatzResearch.WordTrace tailWord_5386238 prefixEnd_5386238 2765729013511802552754149 := by
  unfold tailWord_5386238
  simp only [CollatzResearch.WordTrace]
  refine ⟨24556529882573387132353921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130968159373724731372554245 24556529882573387132353921)
  ·
    refine ⟨18417397411930040349265441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24556529882573387132353921 18417397411930040349265441)
    ·
      refine ⟨13813048058947530261949081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18417397411930040349265441 13813048058947530261949081)
      ·
        refine ⟨10359786044210647696461811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13813048058947530261949081 10359786044210647696461811)
        ·
          refine ⟨15539679066315971544692717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10359786044210647696461811 15539679066315971544692717)
          ·
            refine ⟨5827379649868489329259769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15539679066315971544692717 5827379649868489329259769)
            ·
              refine ⟨4370534737401366996944827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5827379649868489329259769 4370534737401366996944827)
              ·
                refine ⟨6555802106102050495417241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4370534737401366996944827 6555802106102050495417241)
                ·
                  refine ⟨4916851579576537871562931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6555802106102050495417241 4916851579576537871562931)
                  ·
                    refine ⟨7375277369364806807344397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4916851579576537871562931 7375277369364806807344397)
                    ·
                      refine ⟨2765729013511802552754149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7375277369364806807344397 2765729013511802552754149)
                      ·
                        rfl

theorem cell23_5386238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 2, 1, 2, 1, 3].length) (baseStart_5386238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5386238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5386238 prefixEnd_5386238 := by exact prefixLift 5386238
  have htrace : WordTrace (prefixWord ++ tailWord_5386238) baseStart_5386238 baseEnd_5386238 := by
    simpa [prefixWord, tailWord_5386238, baseEnd_5386238] using wordTrace_append hprefix tailTrace_5386238
  have hstable : (prefixWord ++ tailWord_5386238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5386238).length < 2 ^ (prefixWord ++ tailWord_5386238).sum := by decide
  have hdescent : baseEnd_5386238 < baseStart_5386238 := by decide
  rcases family_descends (prefixWord ++ tailWord_5386238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5386290 : List Nat := [3, 2, 1, 1, 2, 3, 2, 1, 1, 2, 5]
def baseStart_5386290 : Nat := 118140960795 + 5386290 * 2 ^ 59
def prefixEnd_5386290 : Nat := 4983230072969 + 3 ^ 40 * 5386290 * 2
def baseEnd_5386290 : Nat := 2765755714505836349303909

theorem tailTrace_5386290 : CollatzResearch.WordTrace tailWord_5386290 prefixEnd_5386290 2765755714505836349303909 := by
  unfold tailWord_5386290
  simp only [CollatzResearch.WordTrace]
  refine ⟨49113533914099677484931081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130969423770932473293149549 49113533914099677484931081)
  ·
    refine ⟨36835150435574758113698311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49113533914099677484931081 36835150435574758113698311)
    ·
      refine ⟨55252725653362137170547467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36835150435574758113698311 55252725653362137170547467)
      ·
        refine ⟨82879088480043205755821201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55252725653362137170547467 82879088480043205755821201)
        ·
          refine ⟨62159316360032404316865901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82879088480043205755821201 62159316360032404316865901)
          ·
            refine ⟨23309743635012151618824713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62159316360032404316865901 23309743635012151618824713)
            ·
              refine ⟨17482307726259113714118535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23309743635012151618824713 17482307726259113714118535)
              ·
                refine ⟨26223461589388670571177803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17482307726259113714118535 26223461589388670571177803)
                ·
                  refine ⟨39335192384083005856766705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26223461589388670571177803 39335192384083005856766705)
                  ·
                    refine ⟨29501394288062254392575029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39335192384083005856766705 29501394288062254392575029)
                    ·
                      refine ⟨2765755714505836349303909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29501394288062254392575029 2765755714505836349303909)
                      ·
                        rfl

theorem cell23_5386290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 1, 1, 2, 5].length) (baseStart_5386290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5386290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5386290 prefixEnd_5386290 := by exact prefixLift 5386290
  have htrace : WordTrace (prefixWord ++ tailWord_5386290) baseStart_5386290 baseEnd_5386290 := by
    simpa [prefixWord, tailWord_5386290, baseEnd_5386290] using wordTrace_append hprefix tailTrace_5386290
  have hstable : (prefixWord ++ tailWord_5386290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5386290).length < 2 ^ (prefixWord ++ tailWord_5386290).sum := by decide
  have hdescent : baseEnd_5386290 < baseStart_5386290 := by decide
  rcases family_descends (prefixWord ++ tailWord_5386290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5386300 : List Nat := [2, 2, 2, 2, 2, 1, 2, 2, 1, 3, 4]
def baseStart_5386300 : Nat := 118140960795 + 5386300 * 2 ^ 59
def prefixEnd_5386300 : Nat := 4983230072969 + 3 ^ 40 * 5386300 * 2
def baseEnd_5386300 : Nat := 2765760849312381310178863

theorem tailTrace_5386300 : CollatzResearch.WordTrace tailWord_5386300 prefixEnd_5386300 2765760849312381310178863 := by
  unfold tailWord_5386300
  simp only [CollatzResearch.WordTrace]
  refine ⟨98227250193181240823794177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130969666924241654431725569 98227250193181240823794177)
  ·
    refine ⟨73670437644885930617845633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98227250193181240823794177 73670437644885930617845633)
    ·
      refine ⟨55252828233664447963384225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73670437644885930617845633 55252828233664447963384225)
      ·
        refine ⟨41439621175248335972538169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55252828233664447963384225 41439621175248335972538169)
        ·
          refine ⟨31079715881436251979403627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41439621175248335972538169 31079715881436251979403627)
          ·
            refine ⟨46619573822154377969105441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31079715881436251979403627 46619573822154377969105441)
            ·
              refine ⟨34964680366615783476829081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46619573822154377969105441 34964680366615783476829081)
              ·
                refine ⟨26223510274961837607621811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34964680366615783476829081 26223510274961837607621811)
                ·
                  refine ⟨39335265412442756411432717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26223510274961837607621811 39335265412442756411432717)
                  ·
                    refine ⟨14750724529666033654287269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39335265412442756411432717 14750724529666033654287269)
                    ·
                      refine ⟨2765760849312381310178863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14750724529666033654287269 2765760849312381310178863)
                      ·
                        rfl

theorem cell23_5386300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 2, 1, 3, 4].length) (baseStart_5386300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5386300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5386300 prefixEnd_5386300 := by exact prefixLift 5386300
  have htrace : WordTrace (prefixWord ++ tailWord_5386300) baseStart_5386300 baseEnd_5386300 := by
    simpa [prefixWord, tailWord_5386300, baseEnd_5386300] using wordTrace_append hprefix tailTrace_5386300
  have hstable : (prefixWord ++ tailWord_5386300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5386300).length < 2 ^ (prefixWord ++ tailWord_5386300).sum := by decide
  have hdescent : baseEnd_5386300 < baseStart_5386300 := by decide
  rcases family_descends (prefixWord ++ tailWord_5386300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5386317 : List Nat := [1, 6, 1, 1, 1, 1, 3, 1, 1, 3, 4]
def baseStart_5386317 : Nat := 118140960795 + 5386317 * 2 ^ 59
def prefixEnd_5386317 : Nat := 4983230072969 + 3 ^ 40 * 5386317 * 2
def baseEnd_5386317 : Nat := 2765769578483507743666285

theorem tailTrace_5386317 : CollatzResearch.WordTrace tailWord_5386317 prefixEnd_5386317 2765769578483507743666285 := by
  unfold tailWord_5386317
  simp only [CollatzResearch.WordTrace]
  refine ⟨196455120427300893550957205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130970080284867262367304803 196455120427300893550957205)
  ·
    refine ⟨9208833770029729385201119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 196455120427300893550957205 9208833770029729385201119)
    ·
      refine ⟨13813250655044594077801679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9208833770029729385201119 13813250655044594077801679)
      ·
        refine ⟨20719875982566891116702519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13813250655044594077801679 20719875982566891116702519)
        ·
          refine ⟨31079813973850336675053779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20719875982566891116702519 31079813973850336675053779)
          ·
            refine ⟨46619720960775505012580669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31079813973850336675053779 46619720960775505012580669)
            ·
              refine ⟨17482395360290814379717751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46619720960775505012580669 17482395360290814379717751)
              ·
                refine ⟨26223593040436221569576627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17482395360290814379717751 26223593040436221569576627)
                ·
                  refine ⟨39335389560654332354364941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26223593040436221569576627 39335389560654332354364941)
                  ·
                    refine ⟨14750771085245374632886853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39335389560654332354364941 14750771085245374632886853)
                    ·
                      refine ⟨2765769578483507743666285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14750771085245374632886853 2765769578483507743666285)
                      ·
                        rfl

theorem cell23_5386317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_5386317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5386317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5386317 prefixEnd_5386317 := by exact prefixLift 5386317
  have htrace : WordTrace (prefixWord ++ tailWord_5386317) baseStart_5386317 baseEnd_5386317 := by
    simpa [prefixWord, tailWord_5386317, baseEnd_5386317] using wordTrace_append hprefix tailTrace_5386317
  have hstable : (prefixWord ++ tailWord_5386317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5386317).length < 2 ^ (prefixWord ++ tailWord_5386317).sum := by decide
  have hdescent : baseEnd_5386317 < baseStart_5386317 := by decide
  rcases family_descends (prefixWord ++ tailWord_5386317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5386377 : List Nat := [1, 2, 1, 1, 4, 2, 1, 3, 1, 5, 2]
def baseStart_5386377 : Nat := 118140960795 + 5386377 * 2 ^ 59
def prefixEnd_5386377 : Nat := 4983230072969 + 3 ^ 40 * 5386377 * 2
def baseEnd_5386377 : Nat := 2765800387322777508916009

theorem tailTrace_5386377 : CollatzResearch.WordTrace tailWord_5386377 prefixEnd_5386377 2765800387322777508916009 := by
  unfold tailWord_5386377
  simp only [CollatzResearch.WordTrace]
  refine ⟨196457308807083523798141385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130971539204722349198760923 196457308807083523798141385)
  ·
    refine ⟨147342981605312642848606039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196457308807083523798141385 147342981605312642848606039)
    ·
      refine ⟨221014472407968964272909059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147342981605312642848606039 221014472407968964272909059)
      ·
        refine ⟨331521708611953446409363589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221014472407968964272909059 331521708611953446409363589)
        ·
          refine ⟨62160320364741271201755673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 331521708611953446409363589 62160320364741271201755673)
          ·
            refine ⟨46620240273555953401316755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62160320364741271201755673 46620240273555953401316755)
            ·
              refine ⟨69930360410333930101975133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46620240273555953401316755 69930360410333930101975133)
              ·
                refine ⟨26223885153875223788240675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69930360410333930101975133 26223885153875223788240675)
                ·
                  refine ⟨39335827730812835682361013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26223885153875223788240675 39335827730812835682361013)
                  ·
                    refine ⟨3687733849763703345221345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39335827730812835682361013 3687733849763703345221345)
                    ·
                      refine ⟨2765800387322777508916009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3687733849763703345221345 2765800387322777508916009)
                      ·
                        rfl

theorem cell23_5386377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 3, 1, 5, 2].length) (baseStart_5386377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5386377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5386377 prefixEnd_5386377 := by exact prefixLift 5386377
  have htrace : WordTrace (prefixWord ++ tailWord_5386377) baseStart_5386377 baseEnd_5386377 := by
    simpa [prefixWord, tailWord_5386377, baseEnd_5386377] using wordTrace_append hprefix tailTrace_5386377
  have hstable : (prefixWord ++ tailWord_5386377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5386377).length < 2 ^ (prefixWord ++ tailWord_5386377).sum := by decide
  have hdescent : baseEnd_5386377 < baseStart_5386377 := by decide
  rcases family_descends (prefixWord ++ tailWord_5386377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5386401 : List Nat := [1, 2, 3, 3, 1, 4, 1, 1, 3, 1, 3]
def baseStart_5386401 : Nat := 118140960795 + 5386401 * 2 ^ 59
def prefixEnd_5386401 : Nat := 4983230072969 + 3 ^ 40 * 5386401 * 2
def baseEnd_5386401 : Nat := 2765812710858485415015899

theorem tailTrace_5386401 : CollatzResearch.WordTrace tailWord_5386401 prefixEnd_5386401 2765812710858485415015899 := by
  unfold tailWord_5386401
  simp only [CollatzResearch.WordTrace]
  refine ⟨196458184158996575897015057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130972122772664383931343371 196458184158996575897015057)
  ·
    refine ⟨147343638119247431922761293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196458184158996575897015057 147343638119247431922761293)
    ·
      refine ⟨55253864294717786971035485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147343638119247431922761293 55253864294717786971035485)
      ·
        refine ⟨20720199110519170114138307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55253864294717786971035485 20720199110519170114138307)
        ·
          refine ⟨31080298665778755171207461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20720199110519170114138307 31080298665778755171207461)
          ·
            refine ⟨5827555999833516594601399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31080298665778755171207461 5827555999833516594601399)
            ·
              refine ⟨8741333999750274891902099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5827555999833516594601399 8741333999750274891902099)
              ·
                refine ⟨13112000999625412337853149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8741333999750274891902099 13112000999625412337853149)
                ·
                  refine ⟨4917000374859529626694931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13112000999625412337853149 4917000374859529626694931)
                  ·
                    refine ⟨7375500562289294440042397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4917000374859529626694931 7375500562289294440042397)
                    ·
                      refine ⟨2765812710858485415015899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7375500562289294440042397 2765812710858485415015899)
                      ·
                        rfl

theorem cell23_5386401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 1, 1, 3, 1, 3].length) (baseStart_5386401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5386401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5386401 prefixEnd_5386401 := by exact prefixLift 5386401
  have htrace : WordTrace (prefixWord ++ tailWord_5386401) baseStart_5386401 baseEnd_5386401 := by
    simpa [prefixWord, tailWord_5386401, baseEnd_5386401] using wordTrace_append hprefix tailTrace_5386401
  have hstable : (prefixWord ++ tailWord_5386401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5386401).length < 2 ^ (prefixWord ++ tailWord_5386401).sum := by decide
  have hdescent : baseEnd_5386401 < baseStart_5386401 := by decide
  rcases family_descends (prefixWord ++ tailWord_5386401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
