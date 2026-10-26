import V185TrunkScan23Chunk0557

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3298596 : List Nat := [2, 3, 1, 3, 1, 1, 3, 1, 1, 3, 4]
def baseStart_3298596 : Nat := 118140960795 + 3298596 * 2 ^ 59
def prefixEnd_3298596 : Nat := 4983230072969 + 3 ^ 40 * 3298596 * 2
def baseEnd_3298596 : Nat := 1693765232998281461680039

theorem tailTrace_3298596 : CollatzResearch.WordTrace tailWord_3298596 prefixEnd_3298596 1693765232998281461680039 := by
  unfold tailWord_3298596
  simp only [CollatzResearch.WordTrace]
  refine ⟨60154839978878761095449821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80206453305171681460599761 60154839978878761095449821)
  ·
    refine ⟨22558064992079535410793683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60154839978878761095449821 22558064992079535410793683)
    ·
      refine ⟨33837097488119303116190525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22558064992079535410793683 33837097488119303116190525)
      ·
        refine ⟨12688911558044738668571447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33837097488119303116190525 12688911558044738668571447)
        ·
          refine ⟨19033367337067108002857171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12688911558044738668571447 19033367337067108002857171)
          ·
            refine ⟨28550051005600662004285757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19033367337067108002857171 28550051005600662004285757)
            ·
              refine ⟨10706269127100248251607159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28550051005600662004285757 10706269127100248251607159)
              ·
                refine ⟨16059403690650372377410739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10706269127100248251607159 16059403690650372377410739)
                ·
                  refine ⟨24089105535975558566116109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16059403690650372377410739 24089105535975558566116109)
                  ·
                    refine ⟨9033414575990834462293541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24089105535975558566116109 9033414575990834462293541)
                    ·
                      refine ⟨1693765232998281461680039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9033414575990834462293541 1693765232998281461680039)
                      ·
                        rfl

theorem cell23_3298596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_3298596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3298596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3298596 prefixEnd_3298596 := by exact prefixLift 3298596
  have htrace : WordTrace (prefixWord ++ tailWord_3298596) baseStart_3298596 baseEnd_3298596 := by
    simpa [prefixWord, tailWord_3298596, baseEnd_3298596] using wordTrace_append hprefix tailTrace_3298596
  have hstable : (prefixWord ++ tailWord_3298596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3298596).length < 2 ^ (prefixWord ++ tailWord_3298596).sum := by decide
  have hdescent : baseEnd_3298596 < baseStart_3298596 := by decide
  rcases family_descends (prefixWord ++ tailWord_3298596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3298613 : List Nat := [1, 3, 3, 1, 2, 2, 1, 2, 2, 4, 2]
def baseStart_3298613 : Nat := 118140960795 + 3298613 * 2 ^ 59
def prefixEnd_3298613 : Nat := 4983230072969 + 3 ^ 40 * 3298613 * 2
def baseEnd_3298613 : Nat := 1693773962169407895167461

theorem tailTrace_3298613 : CollatzResearch.WordTrace tailWord_3298613 prefixEnd_3298613 1693773962169407895167461 := by
  unfold tailWord_3298613
  simp only [CollatzResearch.WordTrace]
  refine ⟨120310299998695934094268493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80206866665797289396178995 120310299998695934094268493)
  ·
    refine ⟨45116362499510975285350685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120310299998695934094268493 45116362499510975285350685)
    ·
      refine ⟨16918635937316615732006507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45116362499510975285350685 16918635937316615732006507)
      ·
        refine ⟨25377953905974923598009761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16918635937316615732006507 25377953905974923598009761)
        ·
          refine ⟨19033465429481192698507321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25377953905974923598009761 19033465429481192698507321)
          ·
            refine ⟨14275099072110894523880491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19033465429481192698507321 14275099072110894523880491)
            ·
              refine ⟨21412648608166341785820737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14275099072110894523880491 21412648608166341785820737)
              ·
                refine ⟨16059486456124756339365553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21412648608166341785820737 16059486456124756339365553)
                ·
                  refine ⟨12044614842093567254524165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16059486456124756339365553 12044614842093567254524165)
                  ·
                    refine ⟨2258365282892543860223281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12044614842093567254524165 2258365282892543860223281)
                    ·
                      refine ⟨1693773962169407895167461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2258365282892543860223281 1693773962169407895167461)
                      ·
                        rfl

theorem cell23_3298613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 2, 2, 4, 2].length) (baseStart_3298613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3298613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3298613 prefixEnd_3298613 := by exact prefixLift 3298613
  have htrace : WordTrace (prefixWord ++ tailWord_3298613) baseStart_3298613 baseEnd_3298613 := by
    simpa [prefixWord, tailWord_3298613, baseEnd_3298613] using wordTrace_append hprefix tailTrace_3298613
  have hstable : (prefixWord ++ tailWord_3298613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3298613).length < 2 ^ (prefixWord ++ tailWord_3298613).sum := by decide
  have hdescent : baseEnd_3298613 < baseStart_3298613 := by decide
  rcases family_descends (prefixWord ++ tailWord_3298613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3298616 : List Nat := [2, 1, 2, 1, 3, 1, 1, 3, 4, 2, 3]
def baseStart_3298616 : Nat := 118140960795 + 3298616 * 2 ^ 59
def prefixEnd_3298616 : Nat := 4983230072969 + 3 ^ 40 * 3298616 * 2
def baseEnd_3298616 : Nat := 1693775502611371383429947

theorem tailTrace_3298616 : CollatzResearch.WordTrace tailWord_3298616 prefixEnd_3298616 1693775502611371383429947 := by
  unfold tailWord_3298616
  simp only [CollatzResearch.WordTrace]
  refine ⟨60155204708842532803313851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80206939611790043737751801 60155204708842532803313851)
  ·
    refine ⟨90232807063263799204970777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60155204708842532803313851 90232807063263799204970777)
    ·
      refine ⟨67674605297447849403728083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90232807063263799204970777 67674605297447849403728083)
      ·
        refine ⟨101511907946171774105592125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67674605297447849403728083 101511907946171774105592125)
        ·
          refine ⟨38066965479814415289597047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101511907946171774105592125 38066965479814415289597047)
          ·
            refine ⟨57100448219721622934395571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38066965479814415289597047 57100448219721622934395571)
            ·
              refine ⟨85650672329582434401593357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57100448219721622934395571 85650672329582434401593357)
              ·
                refine ⟨32119002123593412900597509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85650672329582434401593357 32119002123593412900597509)
                ·
                  refine ⟨6022312898173764918862033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32119002123593412900597509 6022312898173764918862033)
                  ·
                    refine ⟨4516734673630323689146525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6022312898173764918862033 4516734673630323689146525)
                    ·
                      refine ⟨1693775502611371383429947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4516734673630323689146525 1693775502611371383429947)
                      ·
                        rfl

theorem cell23_3298616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 3, 4, 2, 3].length) (baseStart_3298616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3298616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3298616 prefixEnd_3298616 := by exact prefixLift 3298616
  have htrace : WordTrace (prefixWord ++ tailWord_3298616) baseStart_3298616 baseEnd_3298616 := by
    simpa [prefixWord, tailWord_3298616, baseEnd_3298616] using wordTrace_append hprefix tailTrace_3298616
  have hstable : (prefixWord ++ tailWord_3298616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3298616).length < 2 ^ (prefixWord ++ tailWord_3298616).sum := by decide
  have hdescent : baseEnd_3298616 < baseStart_3298616 := by decide
  rcases family_descends (prefixWord ++ tailWord_3298616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3298623 : List Nat := [1, 1, 2, 2, 4, 3, 2, 1, 3, 4]
def baseStart_3298623 : Nat := 118140960795 + 3298623 * 2 ^ 59
def prefixEnd_3298623 : Nat := 4983230072969 + 3 ^ 40 * 3298623 * 2
def baseEnd_3298623 : Nat := 564593032325317618680805

theorem tailTrace_3298623 : CollatzResearch.WordTrace tailWord_3298623 prefixEnd_3298623 564593032325317618680805 := by
  unfold tailWord_3298623
  simp only [CollatzResearch.WordTrace]
  refine ⟨120310664728659705802132523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80207109819106470534755015 120310664728659705802132523)
  ·
    refine ⟨180465997092989558703198785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120310664728659705802132523 180465997092989558703198785)
    ·
      refine ⟨135349497819742169027399089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180465997092989558703198785 135349497819742169027399089)
      ·
        refine ⟨101512123364806626770549317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135349497819742169027399089 101512123364806626770549317)
        ·
          refine ⟨19033523130901242519477997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101512123364806626770549317 19033523130901242519477997)
          ·
            refine ⟨7137571174087965944804249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19033523130901242519477997 7137571174087965944804249)
            ·
              refine ⟨5353178380565974458603187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7137571174087965944804249 5353178380565974458603187)
              ·
                refine ⟨8029767570848961687904781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5353178380565974458603187 8029767570848961687904781)
                ·
                  refine ⟨3011162839068360632964293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8029767570848961687904781 3011162839068360632964293)
                  ·
                    refine ⟨564593032325317618680805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3011162839068360632964293 564593032325317618680805)
                    ·
                      rfl

theorem cell23_3298623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2, 1, 3, 4].length) (baseStart_3298623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3298623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3298623 prefixEnd_3298623 := by exact prefixLift 3298623
  have htrace : WordTrace (prefixWord ++ tailWord_3298623) baseStart_3298623 baseEnd_3298623 := by
    simpa [prefixWord, tailWord_3298623, baseEnd_3298623] using wordTrace_append hprefix tailTrace_3298623
  have hstable : (prefixWord ++ tailWord_3298623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3298623).length < 2 ^ (prefixWord ++ tailWord_3298623).sum := by decide
  have hdescent : baseEnd_3298623 < baseStart_3298623 := by decide
  rcases family_descends (prefixWord ++ tailWord_3298623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3298673 : List Nat := [1, 2, 2, 2, 1, 2, 3, 1, 4, 3, 2]
def baseStart_3298673 : Nat := 118140960795 + 3298673 * 2 ^ 59
def prefixEnd_3298673 : Nat := 4983230072969 + 3 ^ 40 * 3298673 * 2
def baseEnd_3298673 : Nat := 1693804771008677660417185

theorem tailTrace_3298673 : CollatzResearch.WordTrace tailWord_3298673 prefixEnd_3298673 1693804771008677660417185 := by
  unfold tailWord_3298673
  simp only [CollatzResearch.WordTrace]
  refine ⟨120312488378478564341452673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80208325585652376227635115 120312488378478564341452673)
  ·
    refine ⟨90234366283858923256089505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120312488378478564341452673 90234366283858923256089505)
    ·
      refine ⟨67675774712894192442067129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90234366283858923256089505 67675774712894192442067129)
      ·
        refine ⟨50756831034670644331550347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67675774712894192442067129 50756831034670644331550347)
        ·
          refine ⟨76135246552005966497325521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50756831034670644331550347 76135246552005966497325521)
          ·
            refine ⟨57101434914004474872994141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76135246552005966497325521 57101434914004474872994141)
            ·
              refine ⟨21413038092751678077372803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57101434914004474872994141 21413038092751678077372803)
              ·
                refine ⟨32119557139127517116059205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21413038092751678077372803 32119557139127517116059205)
                ·
                  refine ⟨6022416963586409459261101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32119557139127517116059205 6022416963586409459261101)
                  ·
                    refine ⟨2258406361344903547222913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6022416963586409459261101 2258406361344903547222913)
                    ·
                      refine ⟨1693804771008677660417185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2258406361344903547222913 1693804771008677660417185)
                      ·
                        rfl

theorem cell23_3298673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 1, 4, 3, 2].length) (baseStart_3298673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3298673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3298673 prefixEnd_3298673 := by exact prefixLift 3298673
  have htrace : WordTrace (prefixWord ++ tailWord_3298673) baseStart_3298673 baseEnd_3298673 := by
    simpa [prefixWord, tailWord_3298673, baseEnd_3298673] using wordTrace_append hprefix tailTrace_3298673
  have hstable : (prefixWord ++ tailWord_3298673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3298673).length < 2 ^ (prefixWord ++ tailWord_3298673).sum := by decide
  have hdescent : baseEnd_3298673 < baseStart_3298673 := by decide
  rcases family_descends (prefixWord ++ tailWord_3298673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3298720 : List Nat := [2, 1, 1, 4, 1, 2, 5, 1, 1, 1, 4]
def baseStart_3298720 : Nat := 118140960795 + 3298720 * 2 ^ 59
def prefixEnd_3298720 : Nat := 4983230072969 + 3 ^ 40 * 3298720 * 2
def baseEnd_3298720 : Nat := 1693828904599438976529469

theorem tailTrace_3298720 : CollatzResearch.WordTrace tailWord_3298720 prefixEnd_3298720 1693828904599438976529469 := by
  unfold tailWord_3298720
  simp only [CollatzResearch.WordTrace]
  refine ⟨60157101304654145684206807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80209468406205527578942409 60157101304654145684206807)
  ·
    refine ⟨90235651956981218526310211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60157101304654145684206807 90235651956981218526310211)
    ·
      refine ⟨135353477935471827789465317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90235651956981218526310211 135353477935471827789465317)
      ·
        refine ⟨25378777112900967710524747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 135353477935471827789465317 25378777112900967710524747)
        ·
          refine ⟨38068165669351451565787121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25378777112900967710524747 38068165669351451565787121)
          ·
            refine ⟨28551124252013588674340341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38068165669351451565787121 28551124252013588674340341)
            ·
              refine ⟨2676667898626273938219407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28551124252013588674340341 2676667898626273938219407)
              ·
                refine ⟨4015001847939410907329111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2676667898626273938219407 4015001847939410907329111)
                ·
                  refine ⟨6022502771909116360993667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4015001847939410907329111 6022502771909116360993667)
                  ·
                    refine ⟨9033754157863674541490501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6022502771909116360993667 9033754157863674541490501)
                    ·
                      refine ⟨1693828904599438976529469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9033754157863674541490501 1693828904599438976529469)
                      ·
                        rfl

theorem cell23_3298720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 5, 1, 1, 1, 4].length) (baseStart_3298720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3298720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3298720 prefixEnd_3298720 := by exact prefixLift 3298720
  have htrace : WordTrace (prefixWord ++ tailWord_3298720) baseStart_3298720 baseEnd_3298720 := by
    simpa [prefixWord, tailWord_3298720, baseEnd_3298720] using wordTrace_append hprefix tailTrace_3298720
  have hstable : (prefixWord ++ tailWord_3298720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3298720).length < 2 ^ (prefixWord ++ tailWord_3298720).sum := by decide
  have hdescent : baseEnd_3298720 < baseStart_3298720 := by decide
  rcases family_descends (prefixWord ++ tailWord_3298720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3298774 : List Nat := [5, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3]
def baseStart_3298774 : Nat := 118140960795 + 3298774 * 2 ^ 59
def prefixEnd_3298774 : Nat := 4983230072969 + 3 ^ 40 * 3298774 * 2
def baseEnd_3298774 : Nat := 1693856632554781765254221

theorem tailTrace_3298774 : CollatzResearch.WordTrace tailWord_3298774 prefixEnd_3298774 1693856632554781765254221 := by
  unfold tailWord_3298774
  simp only [CollatzResearch.WordTrace]
  refine ⟨7519760759444541161929961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 80210781434075105727252917 7519760759444541161929961)
  ·
    refine ⟨5639820569583405871447471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7519760759444541161929961 5639820569583405871447471)
    ·
      refine ⟨8459730854375108807171207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5639820569583405871447471 8459730854375108807171207)
      ·
        refine ⟨12689596281562663210756811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8459730854375108807171207 12689596281562663210756811)
        ·
          refine ⟨19034394422343994816135217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12689596281562663210756811 19034394422343994816135217)
          ·
            refine ⟨14275795816757996112101413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19034394422343994816135217 14275795816757996112101413)
            ·
              refine ⟨2676711715642124271019015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14275795816757996112101413 2676711715642124271019015)
              ·
                refine ⟨4015067573463186406528523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2676711715642124271019015 4015067573463186406528523)
                ·
                  refine ⟨6022601360194779609792785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4015067573463186406528523 6022601360194779609792785)
                  ·
                    refine ⟨4516951020146084707344589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6022601360194779609792785 4516951020146084707344589)
                    ·
                      refine ⟨1693856632554781765254221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4516951020146084707344589 1693856632554781765254221)
                      ·
                        rfl

theorem cell23_3298774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3].length) (baseStart_3298774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3298774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3298774 prefixEnd_3298774 := by exact prefixLift 3298774
  have htrace : WordTrace (prefixWord ++ tailWord_3298774) baseStart_3298774 baseEnd_3298774 := by
    simpa [prefixWord, tailWord_3298774, baseEnd_3298774] using wordTrace_append hprefix tailTrace_3298774
  have hstable : (prefixWord ++ tailWord_3298774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3298774).length < 2 ^ (prefixWord ++ tailWord_3298774).sum := by decide
  have hdescent : baseEnd_3298774 < baseStart_3298774 := by decide
  rcases family_descends (prefixWord ++ tailWord_3298774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3298787 : List Nat := [1, 1, 1, 6, 2, 1, 3, 2, 2, 1, 3]
def baseStart_3298787 : Nat := 118140960795 + 3298787 * 2 ^ 59
def prefixEnd_3298787 : Nat := 4983230072969 + 3 ^ 40 * 3298787 * 2
def baseEnd_3298787 : Nat := 1693863307803290214391661

theorem tailTrace_3298787 : CollatzResearch.WordTrace tailWord_3298787 prefixEnd_3298787 1693863307803290214391661 := by
  unfold tailWord_3298787
  simp only [CollatzResearch.WordTrace]
  refine ⟨120316646300065561811102615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80211097533377041207401743 120316646300065561811102615)
  ·
    refine ⟨180474969450098342716653923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120316646300065561811102615 180474969450098342716653923)
    ·
      refine ⟨270712454175147514074980885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180474969450098342716653923 270712454175147514074980885)
      ·
        refine ⟨12689646289460039722264729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 270712454175147514074980885 12689646289460039722264729)
        ·
          refine ⟨9517234717095029791698547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12689646289460039722264729 9517234717095029791698547)
          ·
            refine ⟨14275852075642544687547821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9517234717095029791698547 14275852075642544687547821)
            ·
              refine ⟨5353444528365954257830433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14275852075642544687547821 5353444528365954257830433)
              ·
                refine ⟨4015083396274465693372825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5353444528365954257830433 4015083396274465693372825)
                ·
                  refine ⟨3011312547205849270029619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4015083396274465693372825 3011312547205849270029619)
                  ·
                    refine ⟨4516968820808773905044429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3011312547205849270029619 4516968820808773905044429)
                    ·
                      refine ⟨1693863307803290214391661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4516968820808773905044429 1693863307803290214391661)
                      ·
                        rfl

theorem cell23_3298787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3, 2, 2, 1, 3].length) (baseStart_3298787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3298787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3298787 prefixEnd_3298787 := by exact prefixLift 3298787
  have htrace : WordTrace (prefixWord ++ tailWord_3298787) baseStart_3298787 baseEnd_3298787 := by
    simpa [prefixWord, tailWord_3298787, baseEnd_3298787] using wordTrace_append hprefix tailTrace_3298787
  have hstable : (prefixWord ++ tailWord_3298787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3298787).length < 2 ^ (prefixWord ++ tailWord_3298787).sum := by decide
  have hdescent : baseEnd_3298787 < baseStart_3298787 := by decide
  rcases family_descends (prefixWord ++ tailWord_3298787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3298796 : List Nat := [2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 5]
def baseStart_3298796 : Nat := 118140960795 + 3298796 * 2 ^ 59
def prefixEnd_3298796 : Nat := 4983230072969 + 3 ^ 40 * 3298796 * 2
def baseEnd_3298796 : Nat := 1693867929129180679179119

theorem tailTrace_3298796 : CollatzResearch.WordTrace tailWord_3298796 prefixEnd_3298796 1693867929129180679179119 := by
  unfold tailWord_3298796
  simp only [CollatzResearch.WordTrace]
  refine ⟨60158487278516478174090121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80211316371355304232120161 60158487278516478174090121)
  ·
    refine ⟨45118865458887358630567591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60158487278516478174090121 45118865458887358630567591)
    ·
      refine ⟨67678298188331037945851387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45118865458887358630567591 67678298188331037945851387)
      ·
        refine ⟨101517447282496556918777081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67678298188331037945851387 101517447282496556918777081)
        ·
          refine ⟨76138085461872417689082811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101517447282496556918777081 76138085461872417689082811)
          ·
            refine ⟨114207128192808626533624217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76138085461872417689082811 114207128192808626533624217)
            ·
              refine ⟨85655346144606469900218163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114207128192808626533624217 85655346144606469900218163)
              ·
                refine ⟨128483019216909704850327245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85655346144606469900218163 128483019216909704850327245)
                ·
                  refine ⟨48181132206341139318872717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 128483019216909704850327245 48181132206341139318872717)
                  ·
                    refine ⟨18067924577377927244577269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48181132206341139318872717 18067924577377927244577269)
                    ·
                      refine ⟨1693867929129180679179119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18067924577377927244577269 1693867929129180679179119)
                      ·
                        rfl

theorem cell23_3298796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 5].length) (baseStart_3298796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3298796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3298796 prefixEnd_3298796 := by exact prefixLift 3298796
  have htrace : WordTrace (prefixWord ++ tailWord_3298796) baseStart_3298796 baseEnd_3298796 := by
    simpa [prefixWord, tailWord_3298796, baseEnd_3298796] using wordTrace_append hprefix tailTrace_3298796
  have hstable : (prefixWord ++ tailWord_3298796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3298796).length < 2 ^ (prefixWord ++ tailWord_3298796).sum := by decide
  have hdescent : baseEnd_3298796 < baseStart_3298796 := by decide
  rcases family_descends (prefixWord ++ tailWord_3298796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3298822 : List Nat := [6, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2]
def baseStart_3298822 : Nat := 118140960795 + 3298822 * 2 ^ 59
def prefixEnd_3298822 : Nat := 4983230072969 + 3 ^ 40 * 3298822 * 2
def baseEnd_3298822 : Nat := 1693881279626197577454001

theorem tailTrace_3298822 : CollatzResearch.WordTrace tailWord_3298822 prefixEnd_3298822 1693881279626197577454001 := by
  unfold tailWord_3298822
  simp only [CollatzResearch.WordTrace]
  refine ⟨3759935089216836337144585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 80211948569959175192417813 3759935089216836337144585)
  ·
    refine ⟨2819951316912627252858439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3759935089216836337144585 2819951316912627252858439)
    ·
      refine ⟨4229926975368940879287659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2819951316912627252858439 4229926975368940879287659)
      ·
        refine ⟨6344890463053411318931489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4229926975368940879287659 6344890463053411318931489)
        ·
          refine ⟨4758667847290058489198617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6344890463053411318931489 4758667847290058489198617)
          ·
            refine ⟨3569000885467543866898963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4758667847290058489198617 3569000885467543866898963)
            ·
              refine ⟨5353501328201315800348445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3569000885467543866898963 5353501328201315800348445)
              ·
                refine ⟨2007562998075493425130667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5353501328201315800348445 2007562998075493425130667)
                ·
                  refine ⟨3011344497113240137696001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2007562998075493425130667 3011344497113240137696001)
                  ·
                    refine ⟨2258508372834930103272001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3011344497113240137696001 2258508372834930103272001)
                    ·
                      refine ⟨1693881279626197577454001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2258508372834930103272001 1693881279626197577454001)
                      ·
                        rfl

theorem cell23_3298822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2].length) (baseStart_3298822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3298822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3298822 prefixEnd_3298822 := by exact prefixLift 3298822
  have htrace : WordTrace (prefixWord ++ tailWord_3298822) baseStart_3298822 baseEnd_3298822 := by
    simpa [prefixWord, tailWord_3298822, baseEnd_3298822] using wordTrace_append hprefix tailTrace_3298822
  have hstable : (prefixWord ++ tailWord_3298822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3298822).length < 2 ^ (prefixWord ++ tailWord_3298822).sum := by decide
  have hdescent : baseEnd_3298822 < baseStart_3298822 := by decide
  rcases family_descends (prefixWord ++ tailWord_3298822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3298830 : List Nat := [4, 1, 1, 2, 4, 1, 1, 1, 2, 1, 5]
def baseStart_3298830 : Nat := 118140960795 + 3298830 * 2 ^ 59
def prefixEnd_3298830 : Nat := 4983230072969 + 3 ^ 40 * 3298830 * 2
def baseEnd_3298830 : Nat := 1693885387471433546153963

theorem tailTrace_3298830 : CollatzResearch.WordTrace tailWord_3298830 prefixEnd_3298830 1693885387471433546153963 := by
  unfold tailWord_3298830
  simp only [CollatzResearch.WordTrace]
  refine ⟨15039776829863722519364743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80212143092606520103278629 15039776829863722519364743)
  ·
    refine ⟨22559665244795583779047115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15039776829863722519364743 22559665244795583779047115)
    ·
      refine ⟨33839497867193375668570673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22559665244795583779047115 33839497867193375668570673)
      ·
        refine ⟨25379623400395031751428005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33839497867193375668570673 25379623400395031751428005)
        ·
          refine ⟨4758679387574068453392751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25379623400395031751428005 4758679387574068453392751)
          ·
            refine ⟨7138019081361102680089127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4758679387574068453392751 7138019081361102680089127)
            ·
              refine ⟨10707028622041654020133691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7138019081361102680089127 10707028622041654020133691)
              ·
                refine ⟨16060542933062481030200537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10707028622041654020133691 16060542933062481030200537)
                ·
                  refine ⟨12045407199796860772650403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16060542933062481030200537 12045407199796860772650403)
                  ·
                    refine ⟨18068110799695291158975605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12045407199796860772650403 18068110799695291158975605)
                    ·
                      refine ⟨1693885387471433546153963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18068110799695291158975605 1693885387471433546153963)
                      ·
                        rfl

theorem cell23_3298830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 1, 2, 1, 5].length) (baseStart_3298830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3298830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3298830 prefixEnd_3298830 := by exact prefixLift 3298830
  have htrace : WordTrace (prefixWord ++ tailWord_3298830) baseStart_3298830 baseEnd_3298830 := by
    simpa [prefixWord, tailWord_3298830, baseEnd_3298830] using wordTrace_append hprefix tailTrace_3298830
  have hstable : (prefixWord ++ tailWord_3298830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3298830).length < 2 ^ (prefixWord ++ tailWord_3298830).sum := by decide
  have hdescent : baseEnd_3298830 < baseStart_3298830 := by decide
  rcases family_descends (prefixWord ++ tailWord_3298830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3298850 : List Nat := [3, 3, 1, 1, 1, 1, 2, 6, 5]
def baseStart_3298850 : Nat := 118140960795 + 3298850 * 2 ^ 59
def prefixEnd_3298850 : Nat := 4983230072969 + 3 ^ 40 * 3298850 * 2
def baseEnd_3298850 : Nat := 188210628564947051989319

theorem tailTrace_3298850 : CollatzResearch.WordTrace tailWord_3298850 prefixEnd_3298850 188210628564947051989319 := by
  unfold tailWord_3298850
  simp only [CollatzResearch.WordTrace]
  refine ⟨30079736024709330892661501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80212629399224882380430669 30079736024709330892661501)
  ·
    refine ⟨11279901009265999084748063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30079736024709330892661501 11279901009265999084748063)
    ·
      refine ⟨16919851513898998627122095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11279901009265999084748063 16919851513898998627122095)
      ·
        refine ⟨25379777270848497940683143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16919851513898998627122095 25379777270848497940683143)
        ·
          refine ⟨38069665906272746911024715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25379777270848497940683143 38069665906272746911024715)
          ·
            refine ⟨57104498859409120366537073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38069665906272746911024715 57104498859409120366537073)
            ·
              refine ⟨42828374144556840274902805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57104498859409120366537073 42828374144556840274902805)
              ·
                refine ⟨2007580038026101887886069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 42828374144556840274902805 2007580038026101887886069)
                ·
                  refine ⟨188210628564947051989319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2007580038026101887886069 188210628564947051989319)
                  ·
                    rfl

theorem cell23_3298850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 6, 5].length) (baseStart_3298850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3298850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3298850 prefixEnd_3298850 := by exact prefixLift 3298850
  have htrace : WordTrace (prefixWord ++ tailWord_3298850) baseStart_3298850 baseEnd_3298850 := by
    simpa [prefixWord, tailWord_3298850, baseEnd_3298850] using wordTrace_append hprefix tailTrace_3298850
  have hstable : (prefixWord ++ tailWord_3298850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3298850).length < 2 ^ (prefixWord ++ tailWord_3298850).sum := by decide
  have hdescent : baseEnd_3298850 < baseStart_3298850 := by decide
  rcases family_descends (prefixWord ++ tailWord_3298850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3298900 : List Nat := [2, 4, 1, 1, 1, 2, 1, 4, 2, 1, 4]
def baseStart_3298900 : Nat := 118140960795 + 3298900 * 2 ^ 59
def prefixEnd_3298900 : Nat := 4983230072969 + 3 ^ 40 * 3298900 * 2
def baseEnd_3298900 : Nat := 1693921331117248272278641

theorem tailTrace_3298900 : CollatzResearch.WordTrace tailWord_3298900 prefixEnd_3298900 1693921331117248272278641 := by
  unfold tailWord_3298900
  simp only [CollatzResearch.WordTrace]
  refine ⟨60160383874328091054983077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80213845165770788073310769 60160383874328091054983077)
  ·
    refine ⟨11280071976436517072809327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60160383874328091054983077 11280071976436517072809327)
    ·
      refine ⟨16920107964654775609213991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11280071976436517072809327 16920107964654775609213991)
      ·
        refine ⟨25380161946982163413820987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16920107964654775609213991 25380161946982163413820987)
        ·
          refine ⟨38070242920473245120731481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25380161946982163413820987 38070242920473245120731481)
          ·
            refine ⟨28552682190354933840548611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38070242920473245120731481 28552682190354933840548611)
            ·
              refine ⟨42829023285532400760822917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28552682190354933840548611 42829023285532400760822917)
              ·
                refine ⟨8030441866037325142654297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42829023285532400760822917 8030441866037325142654297)
                ·
                  refine ⟨6022831399527993856990723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8030441866037325142654297 6022831399527993856990723)
                  ·
                    refine ⟨9034247099291990785486085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6022831399527993856990723 9034247099291990785486085)
                    ·
                      refine ⟨1693921331117248272278641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9034247099291990785486085 1693921331117248272278641)
                      ·
                        rfl

theorem cell23_3298900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 4, 2, 1, 4].length) (baseStart_3298900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3298900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3298900 prefixEnd_3298900 := by exact prefixLift 3298900
  have htrace : WordTrace (prefixWord ++ tailWord_3298900) baseStart_3298900 baseEnd_3298900 := by
    simpa [prefixWord, tailWord_3298900, baseEnd_3298900] using wordTrace_append hprefix tailTrace_3298900
  have hstable : (prefixWord ++ tailWord_3298900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3298900).length < 2 ^ (prefixWord ++ tailWord_3298900).sum := by decide
  have hdescent : baseEnd_3298900 < baseStart_3298900 := by decide
  rcases family_descends (prefixWord ++ tailWord_3298900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3298917 : List Nat := [1, 3, 1, 3, 3, 2, 1, 1, 2, 4, 2]
def baseStart_3298917 : Nat := 118140960795 + 3298917 * 2 ^ 59
def prefixEnd_3298917 : Nat := 4983230072969 + 3 ^ 40 * 3298917 * 2
def baseEnd_3298917 : Nat := 1693930060288374705766063

theorem tailTrace_3298917 : CollatzResearch.WordTrace tailWord_3298917 prefixEnd_3298917 1693930060288374705766063 := by
  unfold tailWord_3298917
  simp only [CollatzResearch.WordTrace]
  refine ⟨120321387789594594013335005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80214258526396396008890003 120321387789594594013335005)
  ·
    refine ⟨45120520421097972755000627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120321387789594594013335005 45120520421097972755000627)
    ·
      refine ⟨67680780631646959132500941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45120520421097972755000627 67680780631646959132500941)
      ·
        refine ⟨25380292736867609674687853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67680780631646959132500941 25380292736867609674687853)
        ·
          refine ⟨9517609776325353628007945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25380292736867609674687853 9517609776325353628007945)
          ·
            refine ⟨7138207332244015221005959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9517609776325353628007945 7138207332244015221005959)
            ·
              refine ⟨10707310998366022831508939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7138207332244015221005959 10707310998366022831508939)
              ·
                refine ⟨16060966497549034247263409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10707310998366022831508939 16060966497549034247263409)
                ·
                  refine ⟨12045724873161775685447557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16060966497549034247263409 12045724873161775685447557)
                  ·
                    refine ⟨2258573413717832941021417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12045724873161775685447557 2258573413717832941021417)
                    ·
                      refine ⟨1693930060288374705766063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2258573413717832941021417 1693930060288374705766063)
                      ·
                        rfl

theorem cell23_3298917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 1, 2, 4, 2].length) (baseStart_3298917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3298917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3298917 prefixEnd_3298917 := by exact prefixLift 3298917
  have htrace : WordTrace (prefixWord ++ tailWord_3298917) baseStart_3298917 baseEnd_3298917 := by
    simpa [prefixWord, tailWord_3298917, baseEnd_3298917] using wordTrace_append hprefix tailTrace_3298917
  have hstable : (prefixWord ++ tailWord_3298917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3298917).length < 2 ^ (prefixWord ++ tailWord_3298917).sum := by decide
  have hdescent : baseEnd_3298917 < baseStart_3298917 := by decide
  rcases family_descends (prefixWord ++ tailWord_3298917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3298934 : List Nat := [5, 1, 1, 2, 2, 3, 1, 1, 2, 1, 4]
def baseStart_3298934 : Nat := 118140960795 + 3298934 * 2 ^ 59
def prefixEnd_3298934 : Nat := 4983230072969 + 3 ^ 40 * 3298934 * 2
def baseEnd_3298934 : Nat := 1693938789459501139253485

theorem tailTrace_3298934 : CollatzResearch.WordTrace tailWord_3298934 prefixEnd_3298934 1693938789459501139253485 := by
  unfold tailWord_3298934
  simp only [CollatzResearch.WordTrace]
  refine ⟨7520125489408312869793991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 80214671887022003944469237 7520125489408312869793991)
  ·
    refine ⟨11280188234112469304690987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7520125489408312869793991 11280188234112469304690987)
    ·
      refine ⟨16920282351168703957036481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11280188234112469304690987 16920282351168703957036481)
      ·
        refine ⟨12690211763376527967777361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16920282351168703957036481 12690211763376527967777361)
        ·
          refine ⟨9517658822532395975833021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12690211763376527967777361 9517658822532395975833021)
          ·
            refine ⟨3569122058449648490937383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9517658822532395975833021 3569122058449648490937383)
            ·
              refine ⟨5353683087674472736406075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3569122058449648490937383 5353683087674472736406075)
              ·
                refine ⟨8030524631511709104609113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5353683087674472736406075 8030524631511709104609113)
                ·
                  refine ⟨6022893473633781828456835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8030524631511709104609113 6022893473633781828456835)
                  ·
                    refine ⟨9034340210450672742685253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6022893473633781828456835 9034340210450672742685253)
                    ·
                      refine ⟨1693938789459501139253485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9034340210450672742685253 1693938789459501139253485)
                      ·
                        rfl

theorem cell23_3298934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 1, 1, 2, 1, 4].length) (baseStart_3298934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3298934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3298934 prefixEnd_3298934 := by exact prefixLift 3298934
  have htrace : WordTrace (prefixWord ++ tailWord_3298934) baseStart_3298934 baseEnd_3298934 := by
    simpa [prefixWord, tailWord_3298934, baseEnd_3298934] using wordTrace_append hprefix tailTrace_3298934
  have hstable : (prefixWord ++ tailWord_3298934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3298934).length < 2 ^ (prefixWord ++ tailWord_3298934).sum := by decide
  have hdescent : baseEnd_3298934 < baseStart_3298934 := by decide
  rcases family_descends (prefixWord ++ tailWord_3298934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3298967 : List Nat := [1, 1, 3, 3, 2, 2, 1, 3, 3, 1, 3]
def baseStart_3298967 : Nat := 118140960795 + 3298967 * 2 ^ 59
def prefixEnd_3298967 : Nat := 4983230072969 + 3 ^ 40 * 3298967 * 2
def baseEnd_3298967 : Nat := 1693955734321099510140833

theorem tailTrace_3298967 : CollatzResearch.WordTrace tailWord_3298967 prefixEnd_3298967 1693955734321099510140833 := by
  unfold tailWord_3298967
  simp only [CollatzResearch.WordTrace]
  refine ⟨120323211439413452552655155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80215474292942301701770103 120323211439413452552655155)
  ·
    refine ⟨180484817159120178828982733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120323211439413452552655155 180484817159120178828982733)
    ·
      refine ⟨67681806434670067060868525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180484817159120178828982733 67681806434670067060868525)
      ·
        refine ⟨25380677413001275147825697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67681806434670067060868525 25380677413001275147825697)
        ·
          refine ⟨19035508059750956360869273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25380677413001275147825697 19035508059750956360869273)
          ·
            refine ⟨14276631044813217270651955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19035508059750956360869273 14276631044813217270651955)
            ·
              refine ⟨21414946567219825905977933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14276631044813217270651955 21414946567219825905977933)
              ·
                refine ⟨8030604962707434714741725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21414946567219825905977933 8030604962707434714741725)
                ·
                  refine ⟨3011476861015288018028147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8030604962707434714741725 3011476861015288018028147)
                  ·
                    refine ⟨4517215291522932027042221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3011476861015288018028147 4517215291522932027042221)
                    ·
                      refine ⟨1693955734321099510140833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4517215291522932027042221 1693955734321099510140833)
                      ·
                        rfl

theorem cell23_3298967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 3, 3, 1, 3].length) (baseStart_3298967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3298967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3298967 prefixEnd_3298967 := by exact prefixLift 3298967
  have htrace : WordTrace (prefixWord ++ tailWord_3298967) baseStart_3298967 baseEnd_3298967 := by
    simpa [prefixWord, tailWord_3298967, baseEnd_3298967] using wordTrace_append hprefix tailTrace_3298967
  have hstable : (prefixWord ++ tailWord_3298967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3298967).length < 2 ^ (prefixWord ++ tailWord_3298967).sum := by decide
  have hdescent : baseEnd_3298967 < baseStart_3298967 := by decide
  rcases family_descends (prefixWord ++ tailWord_3298967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3298974 : List Nat := [4, 3, 1, 1, 1, 3, 3, 1, 6]
def baseStart_3298974 : Nat := 118140960795 + 3298974 * 2 ^ 59
def prefixEnd_3298974 : Nat := 4983230072969 + 3 ^ 40 * 3298974 * 2
def baseEnd_3298974 : Nat := 188217703187297886972589

theorem tailTrace_3298974 : CollatzResearch.WordTrace tailWord_3298974 prefixEnd_3298974 188217703187297886972589 := by
  unfold tailWord_3298974
  simp only [CollatzResearch.WordTrace]
  refine ⟨15040433343798511593519997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80215644500258728498773317 15040433343798511593519997)
  ·
    refine ⟨5640162503924441847569999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15040433343798511593519997 5640162503924441847569999)
    ·
      refine ⟨8460243755886662771354999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5640162503924441847569999 8460243755886662771354999)
      ·
        refine ⟨12690365633829994157032499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8460243755886662771354999 12690365633829994157032499)
        ·
          refine ⟨19035548450744991235548749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12690365633829994157032499 19035548450744991235548749)
          ·
            refine ⟨7138330669029371713330781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19035548450744991235548749 7138330669029371713330781)
            ·
              refine ⟨2676874000886014392499043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7138330669029371713330781 2676874000886014392499043)
              ·
                refine ⟨4015311001329021588748565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2676874000886014392499043 4015311001329021588748565)
                ·
                  refine ⟨188217703187297886972589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4015311001329021588748565 188217703187297886972589)
                  ·
                    rfl

theorem cell23_3298974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 3, 1, 6].length) (baseStart_3298974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3298974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3298974 prefixEnd_3298974 := by exact prefixLift 3298974
  have htrace : WordTrace (prefixWord ++ tailWord_3298974) baseStart_3298974 baseEnd_3298974 := by
    simpa [prefixWord, tailWord_3298974, baseEnd_3298974] using wordTrace_append hprefix tailTrace_3298974
  have hstable : (prefixWord ++ tailWord_3298974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3298974).length < 2 ^ (prefixWord ++ tailWord_3298974).sum := by decide
  have hdescent : baseEnd_3298974 < baseStart_3298974 := by decide
  rcases family_descends (prefixWord ++ tailWord_3298974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3298977 : List Nat := [1, 2, 3, 3, 2, 1, 1, 2, 1, 5, 2]
def baseStart_3298977 : Nat := 118140960795 + 3298977 * 2 ^ 59
def prefixEnd_3298977 : Nat := 4983230072969 + 3 ^ 40 * 3298977 * 2
def baseEnd_3298977 : Nat := 1693960869127644471015787

theorem tailTrace_3298977 : CollatzResearch.WordTrace tailWord_3298977 prefixEnd_3298977 1693960869127644471015787 := by
  unfold tailWord_3298977
  simp only [CollatzResearch.WordTrace]
  refine ⟨120323576169377224260519185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80215717446251482840346123 120323576169377224260519185)
  ·
    refine ⟨90242682127032918195389389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120323576169377224260519185 90242682127032918195389389)
    ·
      refine ⟨33841005797637344323271021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90242682127032918195389389 33841005797637344323271021)
      ·
        refine ⟨12690377174114004121226633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33841005797637344323271021 12690377174114004121226633)
        ·
          refine ⟨9517782880585503090919975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12690377174114004121226633 9517782880585503090919975)
          ·
            refine ⟨14276674320878254636379963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9517782880585503090919975 14276674320878254636379963)
            ·
              refine ⟨21415011481317381954569945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14276674320878254636379963 21415011481317381954569945)
              ·
                refine ⟨16061258610988036465927459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21415011481317381954569945 16061258610988036465927459)
                ·
                  refine ⟨24091887916482054698891189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16061258610988036465927459 24091887916482054698891189)
                  ·
                    refine ⟨2258614492170192628021049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24091887916482054698891189 2258614492170192628021049)
                    ·
                      refine ⟨1693960869127644471015787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2258614492170192628021049 1693960869127644471015787)
                      ·
                        rfl

theorem cell23_3298977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 2, 1, 5, 2].length) (baseStart_3298977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3298977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3298977 prefixEnd_3298977 := by exact prefixLift 3298977
  have htrace : WordTrace (prefixWord ++ tailWord_3298977) baseStart_3298977 baseEnd_3298977 := by
    simpa [prefixWord, tailWord_3298977, baseEnd_3298977] using wordTrace_append hprefix tailTrace_3298977
  have hstable : (prefixWord ++ tailWord_3298977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3298977).length < 2 ^ (prefixWord ++ tailWord_3298977).sum := by decide
  have hdescent : baseEnd_3298977 < baseStart_3298977 := by decide
  rcases family_descends (prefixWord ++ tailWord_3298977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3299018 : List Nat := [3, 1, 2, 1, 5, 1, 3, 2, 1, 1, 3]
def baseStart_3299018 : Nat := 118140960795 + 3299018 * 2 ^ 59
def prefixEnd_3299018 : Nat := 4983230072969 + 3 ^ 40 * 3299018 * 2
def baseEnd_3299018 : Nat := 1693981921834478810603099

theorem tailTrace_3299018 : CollatzResearch.WordTrace tailWord_3299018 prefixEnd_3299018 1693981921834478810603099 := by
  unfold tailWord_3299018
  simp only [CollatzResearch.WordTrace]
  refine ⟨30081267890557172065690427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80216714374819125508507805 30081267890557172065690427)
  ·
    refine ⟨45121901835835758098535641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30081267890557172065690427 45121901835835758098535641)
    ·
      refine ⟨33841426376876818573901731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45121901835835758098535641 33841426376876818573901731)
      ·
        refine ⟨50762139565315227860852597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33841426376876818573901731 50762139565315227860852597)
        ·
          refine ⟨4758950584248302611954931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 50762139565315227860852597 4758950584248302611954931)
          ·
            refine ⟨7138425876372453917932397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4758950584248302611954931 7138425876372453917932397)
            ·
              refine ⟨2676909703639670219224649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7138425876372453917932397 2676909703639670219224649)
              ·
                refine ⟨2007682277729752664418487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2676909703639670219224649 2007682277729752664418487)
                ·
                  refine ⟨3011523416594628996627731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2007682277729752664418487 3011523416594628996627731)
                  ·
                    refine ⟨4517285124891943494941597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3011523416594628996627731 4517285124891943494941597)
                    ·
                      refine ⟨1693981921834478810603099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4517285124891943494941597 1693981921834478810603099)
                      ·
                        rfl

theorem cell23_3299018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 3, 2, 1, 1, 3].length) (baseStart_3299018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3299018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3299018 prefixEnd_3299018 := by exact prefixLift 3299018
  have htrace : WordTrace (prefixWord ++ tailWord_3299018) baseStart_3299018 baseEnd_3299018 := by
    simpa [prefixWord, tailWord_3299018, baseEnd_3299018] using wordTrace_append hprefix tailTrace_3299018
  have hstable : (prefixWord ++ tailWord_3299018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3299018).length < 2 ^ (prefixWord ++ tailWord_3299018).sum := by decide
  have hdescent : baseEnd_3299018 < baseStart_3299018 := by decide
  rcases family_descends (prefixWord ++ tailWord_3299018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3299034 : List Nat := [3, 1, 1, 2, 2, 3, 4, 1, 2, 4]
def baseStart_3299034 : Nat := 118140960795 + 3299034 * 2 ^ 59
def prefixEnd_3299034 : Nat := 4983230072969 + 3 ^ 40 * 3299034 * 2
def baseEnd_3299034 : Nat := 564663379174983582667675

theorem tailTrace_3299034 : CollatzResearch.WordTrace tailWord_3299034 prefixEnd_3299034 564663379174983582667675 := by
  unfold tailWord_3299034
  simp only [CollatzResearch.WordTrace]
  refine ⟨30081413782542680748836039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80217103420113815330229437 30081413782542680748836039)
  ·
    refine ⟨45122120673814021123254059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30081413782542680748836039 45122120673814021123254059)
    ·
      refine ⟨67683181010721031684881089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45122120673814021123254059 67683181010721031684881089)
      ·
        refine ⟨50762385758040773763660817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67683181010721031684881089 50762385758040773763660817)
        ·
          refine ⟨38071789318530580322745613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50762385758040773763660817 38071789318530580322745613)
          ·
            refine ⟨14276920994448967621029605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38071789318530580322745613 14276920994448967621029605)
            ·
              refine ⟨2676922686459181428943051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14276920994448967621029605 2676922686459181428943051)
              ·
                refine ⟨4015384029688772143414577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2676922686459181428943051 4015384029688772143414577)
                ·
                  refine ⟨3011538022266579107560933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4015384029688772143414577 3011538022266579107560933)
                  ·
                    refine ⟨564663379174983582667675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3011538022266579107560933 564663379174983582667675)
                    ·
                      rfl

theorem cell23_3299034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 4, 1, 2, 4].length) (baseStart_3299034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3299034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3299034 prefixEnd_3299034 := by exact prefixLift 3299034
  have htrace : WordTrace (prefixWord ++ tailWord_3299034) baseStart_3299034 baseEnd_3299034 := by
    simpa [prefixWord, tailWord_3299034, baseEnd_3299034] using wordTrace_append hprefix tailTrace_3299034
  have hstable : (prefixWord ++ tailWord_3299034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3299034).length < 2 ^ (prefixWord ++ tailWord_3299034).sum := by decide
  have hdescent : baseEnd_3299034 < baseStart_3299034 := by decide
  rcases family_descends (prefixWord ++ tailWord_3299034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3299041 : List Nat := [1, 2, 3, 1, 6, 1, 1, 2, 1, 1, 4]
def baseStart_3299041 : Nat := 118140960795 + 3299041 * 2 ^ 59
def prefixEnd_3299041 : Nat := 4983230072969 + 3 ^ 40 * 3299041 * 2
def baseEnd_3299041 : Nat := 1693993731889532220615493

theorem tailTrace_3299041 : CollatzResearch.WordTrace tailWord_3299041 prefixEnd_3299041 1693993731889532220615493 := by
  unfold tailWord_3299041
  simp only [CollatzResearch.WordTrace]
  refine ⟨120325910441145363190848977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80217273627430242127232651 120325910441145363190848977)
  ·
    refine ⟨90244432830859022393136733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120325910441145363190848977 90244432830859022393136733)
    ·
      refine ⟨33841662311572133397426275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90244432830859022393136733 33841662311572133397426275)
      ·
        refine ⟨50762493467358200096139413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33841662311572133397426275 50762493467358200096139413)
        ·
          refine ⟨2379491881282415629506535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 50762493467358200096139413 2379491881282415629506535)
          ·
            refine ⟨3569237821923623444259803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2379491881282415629506535 3569237821923623444259803)
            ·
              refine ⟨5353856732885435166389705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3569237821923623444259803 5353856732885435166389705)
              ·
                refine ⟨4015392549664076374792279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5353856732885435166389705 4015392549664076374792279)
                ·
                  refine ⟨6023088824496114562188419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4015392549664076374792279 6023088824496114562188419)
                  ·
                    refine ⟨9034633236744171843282629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6023088824496114562188419 9034633236744171843282629)
                    ·
                      refine ⟨1693993731889532220615493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9034633236744171843282629 1693993731889532220615493)
                      ·
                        rfl

theorem cell23_3299041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 1, 2, 1, 1, 4].length) (baseStart_3299041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3299041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3299041 prefixEnd_3299041 := by exact prefixLift 3299041
  have htrace : WordTrace (prefixWord ++ tailWord_3299041) baseStart_3299041 baseEnd_3299041 := by
    simpa [prefixWord, tailWord_3299041, baseEnd_3299041] using wordTrace_append hprefix tailTrace_3299041
  have hstable : (prefixWord ++ tailWord_3299041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3299041).length < 2 ^ (prefixWord ++ tailWord_3299041).sum := by decide
  have hdescent : baseEnd_3299041 < baseStart_3299041 := by decide
  rcases family_descends (prefixWord ++ tailWord_3299041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3299057 : List Nat := [1, 2, 2, 2, 2, 4, 1, 2, 1, 3, 3]
def baseStart_3299057 : Nat := 118140960795 + 3299057 * 2 ^ 59
def prefixEnd_3299057 : Nat := 4983230072969 + 3 ^ 40 * 3299057 * 2
def baseEnd_3299057 : Nat := 1694001947580004158015419

theorem tailTrace_3299057 : CollatzResearch.WordTrace tailWord_3299057 prefixEnd_3299057 1694001947580004158015419 := by
  unfold tailWord_3299057
  simp only [CollatzResearch.WordTrace]
  refine ⟨120326494009087397923431425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80217662672724931948954283 120326494009087397923431425)
  ·
    refine ⟨90244870506815548442573569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120326494009087397923431425 90244870506815548442573569)
    ·
      refine ⟨67683652880111661331930177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90244870506815548442573569 67683652880111661331930177)
      ·
        refine ⟨50762739660083745998947633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67683652880111661331930177 50762739660083745998947633)
        ·
          refine ⟨38072054745062809499210725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50762739660083745998947633 38072054745062809499210725)
          ·
            refine ⟨7138510264699276781102011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38072054745062809499210725 7138510264699276781102011)
            ·
              refine ⟨10707765397048915171653017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7138510264699276781102011 10707765397048915171653017)
              ·
                refine ⟨8030824047786686378739763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10707765397048915171653017 8030824047786686378739763)
                ·
                  refine ⟨12046236071680029568109645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8030824047786686378739763 12046236071680029568109645)
                  ·
                    refine ⟨4517338526880011088041117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12046236071680029568109645 4517338526880011088041117)
                    ·
                      refine ⟨1694001947580004158015419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4517338526880011088041117 1694001947580004158015419)
                      ·
                        rfl

theorem cell23_3299057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 2, 1, 3, 3].length) (baseStart_3299057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3299057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3299057 prefixEnd_3299057 := by exact prefixLift 3299057
  have htrace : WordTrace (prefixWord ++ tailWord_3299057) baseStart_3299057 baseEnd_3299057 := by
    simpa [prefixWord, tailWord_3299057, baseEnd_3299057] using wordTrace_append hprefix tailTrace_3299057
  have hstable : (prefixWord ++ tailWord_3299057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3299057).length < 2 ^ (prefixWord ++ tailWord_3299057).sum := by decide
  have hdescent : baseEnd_3299057 < baseStart_3299057 := by decide
  rcases family_descends (prefixWord ++ tailWord_3299057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3299080 : List Nat := [2, 1, 3, 2, 2, 1, 1, 1, 1, 5, 4]
def baseStart_3299080 : Nat := 118140960795 + 3299080 * 2 ^ 59
def prefixEnd_3299080 : Nat := 4983230072969 + 3 ^ 40 * 3299080 * 2
def baseEnd_3299080 : Nat := 1694013757635057568027813

theorem tailTrace_3299080 : CollatzResearch.WordTrace tailWord_3299080 prefixEnd_3299080 1694013757635057568027813 := by
  unfold tailWord_3299080
  simp only [CollatzResearch.WordTrace]
  refine ⟨60163666444002036425759347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80218221925336048567679129 60163666444002036425759347)
  ·
    refine ⟨90245499666003054638639021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60163666444002036425759347 90245499666003054638639021)
    ·
      refine ⟨33842062374751145489489633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90245499666003054638639021 33842062374751145489489633)
      ·
        refine ⟨25381546781063359117117225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33842062374751145489489633 25381546781063359117117225)
        ·
          refine ⟨19036160085797519337837919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25381546781063359117117225 19036160085797519337837919)
          ·
            refine ⟨28554240128696279006756879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19036160085797519337837919 28554240128696279006756879)
            ·
              refine ⟨42831360193044418510135319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28554240128696279006756879 42831360193044418510135319)
              ·
                refine ⟨64247040289566627765202979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42831360193044418510135319 64247040289566627765202979)
                ·
                  refine ⟨96370560434349941647804469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64247040289566627765202979 96370560434349941647804469)
                  ·
                    refine ⟨9034740040720307029481669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 96370560434349941647804469 9034740040720307029481669)
                    ·
                      refine ⟨1694013757635057568027813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9034740040720307029481669 1694013757635057568027813)
                      ·
                        rfl

theorem cell23_3299080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 1, 5, 4].length) (baseStart_3299080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3299080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3299080 prefixEnd_3299080 := by exact prefixLift 3299080
  have htrace : WordTrace (prefixWord ++ tailWord_3299080) baseStart_3299080 baseEnd_3299080 := by
    simpa [prefixWord, tailWord_3299080, baseEnd_3299080] using wordTrace_append hprefix tailTrace_3299080
  have hstable : (prefixWord ++ tailWord_3299080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3299080).length < 2 ^ (prefixWord ++ tailWord_3299080).sum := by decide
  have hdescent : baseEnd_3299080 < baseStart_3299080 := by decide
  rcases family_descends (prefixWord ++ tailWord_3299080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3299118 : List Nat := [4, 1, 3, 2, 2, 1, 1, 3, 1, 3, 2]
def baseStart_3299118 : Nat := 118140960795 + 3299118 * 2 ^ 59
def prefixEnd_3299118 : Nat := 4983230072969 + 3 ^ 40 * 3299118 * 2
def baseEnd_3299118 : Nat := 1694033269899928419352639

theorem tailTrace_3299118 : CollatzResearch.WordTrace tailWord_3299118 prefixEnd_3299118 1694033269899928419352639 := by
  unfold tailWord_3299118
  simp only [CollatzResearch.WordTrace]
  refine ⟨15041089857733300667675251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80219145907910936894268005 15041089857733300667675251)
  ·
    refine ⟨22561634786599951001512877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15041089857733300667675251 22561634786599951001512877)
    ·
      refine ⟨8460613044974981625567329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22561634786599951001512877 8460613044974981625567329)
      ·
        refine ⟨6345459783731236219175497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8460613044974981625567329 6345459783731236219175497)
        ·
          refine ⟨4759094837798427164381623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6345459783731236219175497 4759094837798427164381623)
          ·
            refine ⟨7138642256697640746572435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4759094837798427164381623 7138642256697640746572435)
            ·
              refine ⟨10707963385046461119858653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7138642256697640746572435 10707963385046461119858653)
              ·
                refine ⟨4015486269392422919946995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10707963385046461119858653 4015486269392422919946995)
                ·
                  refine ⟨6023229404088634379920493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4015486269392422919946995 6023229404088634379920493)
                  ·
                    refine ⟨2258711026533237892470185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6023229404088634379920493 2258711026533237892470185)
                    ·
                      refine ⟨1694033269899928419352639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2258711026533237892470185 1694033269899928419352639)
                      ·
                        rfl

theorem cell23_3299118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 3, 1, 3, 2].length) (baseStart_3299118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3299118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3299118 prefixEnd_3299118 := by exact prefixLift 3299118
  have htrace : WordTrace (prefixWord ++ tailWord_3299118) baseStart_3299118 baseEnd_3299118 := by
    simpa [prefixWord, tailWord_3299118, baseEnd_3299118] using wordTrace_append hprefix tailTrace_3299118
  have hstable : (prefixWord ++ tailWord_3299118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3299118).length < 2 ^ (prefixWord ++ tailWord_3299118).sum := by decide
  have hdescent : baseEnd_3299118 < baseStart_3299118 := by decide
  rcases family_descends (prefixWord ++ tailWord_3299118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3299148 : List Nat := [2, 2, 1, 3, 5, 1, 1, 1, 1, 4, 2]
def baseStart_3299148 : Nat := 118140960795 + 3299148 * 2 ^ 59
def prefixEnd_3299148 : Nat := 4983230072969 + 3 ^ 40 * 3299148 * 2
def baseEnd_3299148 : Nat := 1694048674319563301977501

theorem tailTrace_3299148 : CollatzResearch.WordTrace tailWord_3299148 prefixEnd_3299148 1694048674319563301977501 := by
  unfold tailWord_3299148
  simp only [CollatzResearch.WordTrace]
  refine ⟨60164906525878860232497049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80219875367838480309996065 60164906525878860232497049)
  ·
    refine ⟨45123679894409145174372787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60164906525878860232497049 45123679894409145174372787)
    ·
      refine ⟨67685519841613717761559181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45123679894409145174372787 67685519841613717761559181)
      ·
        refine ⟨25382069940605144160584693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67685519841613717761559181 25382069940605144160584693)
        ·
          refine ⟨2379569056931732265054815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25382069940605144160584693 2379569056931732265054815)
          ·
            refine ⟨3569353585397598397582223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2379569056931732265054815 3569353585397598397582223)
            ·
              refine ⟨5354030378096397596373335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3569353585397598397582223 5354030378096397596373335)
              ·
                refine ⟨8031045567144596394560003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5354030378096397596373335 8031045567144596394560003)
                ·
                  refine ⟨12046568350716894591840005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8031045567144596394560003 12046568350716894591840005)
                  ·
                    refine ⟨2258731565759417735970001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12046568350716894591840005 2258731565759417735970001)
                    ·
                      refine ⟨1694048674319563301977501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2258731565759417735970001 1694048674319563301977501)
                      ·
                        rfl

theorem cell23_3299148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 1, 1, 1, 4, 2].length) (baseStart_3299148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3299148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3299148 prefixEnd_3299148 := by exact prefixLift 3299148
  have htrace : WordTrace (prefixWord ++ tailWord_3299148) baseStart_3299148 baseEnd_3299148 := by
    simpa [prefixWord, tailWord_3299148, baseEnd_3299148] using wordTrace_append hprefix tailTrace_3299148
  have hstable : (prefixWord ++ tailWord_3299148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3299148).length < 2 ^ (prefixWord ++ tailWord_3299148).sum := by decide
  have hdescent : baseEnd_3299148 < baseStart_3299148 := by decide
  rcases family_descends (prefixWord ++ tailWord_3299148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3299160 : List Nat := [2, 1, 2, 2, 1, 1, 1, 1, 5, 2, 5]
def baseStart_3299160 : Nat := 118140960795 + 3299160 * 2 ^ 59
def prefixEnd_3299160 : Nat := 4983230072969 + 3 ^ 40 * 3299160 * 2
def baseEnd_3299160 : Nat := 1694054836087417255027445

theorem tailTrace_3299160 : CollatzResearch.WordTrace tailWord_3299160 prefixEnd_3299160 1694054836087417255027445 := by
  unfold tailWord_3299160
  simp only [CollatzResearch.WordTrace]
  refine ⟨60165125363857123257215467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80220167151809497676287289 60165125363857123257215467)
  ·
    refine ⟨90247688045785684885823201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60165125363857123257215467 90247688045785684885823201)
    ·
      refine ⟨67685766034339263664367401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90247688045785684885823201 67685766034339263664367401)
      ·
        refine ⟨50764324525754447748275551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67685766034339263664367401 50764324525754447748275551)
        ·
          refine ⟨76146486788631671622413327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50764324525754447748275551 76146486788631671622413327)
          ·
            refine ⟨114219730182947507433619991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76146486788631671622413327 114219730182947507433619991)
            ·
              refine ⟨171329595274421261150429987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114219730182947507433619991 171329595274421261150429987)
              ·
                refine ⟨256994392911631891725644981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 171329595274421261150429987 256994392911631891725644981)
                ·
                  refine ⟨24093224335465489849279217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 256994392911631891725644981 24093224335465489849279217)
                  ·
                    refine ⟨18069918251599117386959413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24093224335465489849279217 18069918251599117386959413)
                    ·
                      refine ⟨1694054836087417255027445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18069918251599117386959413 1694054836087417255027445)
                      ·
                        rfl

theorem cell23_3299160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 5, 2, 5].length) (baseStart_3299160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3299160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3299160 prefixEnd_3299160 := by exact prefixLift 3299160
  have htrace : WordTrace (prefixWord ++ tailWord_3299160) baseStart_3299160 baseEnd_3299160 := by
    simpa [prefixWord, tailWord_3299160, baseEnd_3299160] using wordTrace_append hprefix tailTrace_3299160
  have hstable : (prefixWord ++ tailWord_3299160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3299160).length < 2 ^ (prefixWord ++ tailWord_3299160).sum := by decide
  have hdescent : baseEnd_3299160 < baseStart_3299160 := by decide
  rcases family_descends (prefixWord ++ tailWord_3299160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3299171 : List Nat := [1, 1, 1, 5, 4, 2, 1, 3, 5]
def baseStart_3299171 : Nat := 118140960795 + 3299171 * 2 ^ 59
def prefixEnd_3299171 : Nat := 4983230072969 + 3 ^ 40 * 3299171 * 2
def baseEnd_3299171 : Nat := 188228942708290745776655

theorem tailTrace_3299171 : CollatzResearch.WordTrace tailWord_3299171 prefixEnd_3299171 188228942708290745776655 := by
  unfold tailWord_3299171
  simp only [CollatzResearch.WordTrace]
  refine ⟨120330651930674395393081367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80220434620449596928720911 120330651930674395393081367)
  ·
    refine ⟨180495977896011593089622051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120330651930674395393081367 180495977896011593089622051)
    ·
      refine ⟨270743966844017389634433077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180495977896011593089622051 270743966844017389634433077)
      ·
        refine ⟨25382246891626630278228101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 270743966844017389634433077 25382246891626630278228101)
        ·
          refine ⟨4759171292179993177167769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25382246891626630278228101 4759171292179993177167769)
          ·
            refine ⟨3569378469134994882875827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4759171292179993177167769 3569378469134994882875827)
            ·
              refine ⟨5354067703702492324313741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3569378469134994882875827 5354067703702492324313741)
              ·
                refine ⟨2007775388888434621617653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5354067703702492324313741 2007775388888434621617653)
                ·
                  refine ⟨188228942708290745776655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2007775388888434621617653 188228942708290745776655)
                  ·
                    rfl

theorem cell23_3299171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 1, 3, 5].length) (baseStart_3299171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3299171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3299171 prefixEnd_3299171 := by exact prefixLift 3299171
  have htrace : WordTrace (prefixWord ++ tailWord_3299171) baseStart_3299171 baseEnd_3299171 := by
    simpa [prefixWord, tailWord_3299171, baseEnd_3299171] using wordTrace_append hprefix tailTrace_3299171
  have hstable : (prefixWord ++ tailWord_3299171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3299171).length < 2 ^ (prefixWord ++ tailWord_3299171).sum := by decide
  have hdescent : baseEnd_3299171 < baseStart_3299171 := by decide
  rcases family_descends (prefixWord ++ tailWord_3299171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3299204 : List Nat := [2, 3, 2, 1, 1, 1, 2, 3, 2, 4, 2]
def baseStart_3299204 : Nat := 118140960795 + 3299204 * 2 ^ 59
def prefixEnd_3299204 : Nat := 4983230072969 + 3 ^ 40 * 3299204 * 2
def baseEnd_3299204 : Nat := 1694077429236215082877243

theorem tailTrace_3299204 : CollatzResearch.WordTrace tailWord_3299204 prefixEnd_3299204 1694077429236215082877243 := by
  unfold tailWord_3299204
  simp only [CollatzResearch.WordTrace]
  refine ⟨60165927769777421014516333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80221237026369894686021777 60165927769777421014516333)
  ·
    refine ⟨22562222913666532880443625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60165927769777421014516333 22562222913666532880443625)
    ·
      refine ⟨16921667185249899660332719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22562222913666532880443625 16921667185249899660332719)
      ·
        refine ⟨25382500777874849490499079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16921667185249899660332719 25382500777874849490499079)
        ·
          refine ⟨38073751166812274235748619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25382500777874849490499079 38073751166812274235748619)
          ·
            refine ⟨57110626750218411353622929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38073751166812274235748619 57110626750218411353622929)
            ·
              refine ⟨42832970062663808515217197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57110626750218411353622929 42832970062663808515217197)
              ·
                refine ⟨16062363773498928193206449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42832970062663808515217197 16062363773498928193206449)
                ·
                  refine ⟨12046772830124196144904837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16062363773498928193206449 12046772830124196144904837)
                  ·
                    refine ⟨2258769905648286777169657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12046772830124196144904837 2258769905648286777169657)
                    ·
                      refine ⟨1694077429236215082877243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2258769905648286777169657 1694077429236215082877243)
                      ·
                        rfl

theorem cell23_3299204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 3, 2, 4, 2].length) (baseStart_3299204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3299204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3299204 prefixEnd_3299204 := by exact prefixLift 3299204
  have htrace : WordTrace (prefixWord ++ tailWord_3299204) baseStart_3299204 baseEnd_3299204 := by
    simpa [prefixWord, tailWord_3299204, baseEnd_3299204] using wordTrace_append hprefix tailTrace_3299204
  have hstable : (prefixWord ++ tailWord_3299204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3299204).length < 2 ^ (prefixWord ++ tailWord_3299204).sum := by decide
  have hdescent : baseEnd_3299204 < baseStart_3299204 := by decide
  rcases family_descends (prefixWord ++ tailWord_3299204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3299257 : List Nat := [1, 2, 1, 4, 2, 1, 1, 1, 5, 5]
def baseStart_3299257 : Nat := 118140960795 + 3299257 * 2 ^ 59
def prefixEnd_3299257 : Nat := 4983230072969 + 3 ^ 40 * 3299257 * 2
def baseEnd_3299257 : Nat := 564701547903634458504833

theorem tailTrace_3299257 : CollatzResearch.WordTrace tailWord_3299257 prefixEnd_3299257 564701547903634458504833 := by
  unfold tailWord_3299257
  simp only [CollatzResearch.WordTrace]
  refine ⟨120333788608362832080712025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80222525738908554720474683 120333788608362832080712025)
  ·
    refine ⟨90250341456272124060534019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120333788608362832080712025 90250341456272124060534019)
    ·
      refine ⟨135375512184408186090801029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90250341456272124060534019 135375512184408186090801029)
      ·
        refine ⟨25382908534576534892025193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 135375512184408186090801029 25382908534576534892025193)
        ·
          refine ⟨19037181400932401169018895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25382908534576534892025193 19037181400932401169018895)
          ·
            refine ⟨28555772101398601753528343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19037181400932401169018895 28555772101398601753528343)
            ·
              refine ⟨42833658152097902630292515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28555772101398601753528343 42833658152097902630292515)
              ·
                refine ⟨64250487228146853945438773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42833658152097902630292515 64250487228146853945438773)
                ·
                  refine ⟨6023483177638767557384885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 64250487228146853945438773 6023483177638767557384885)
                  ·
                    refine ⟨564701547903634458504833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6023483177638767557384885 564701547903634458504833)
                    ·
                      rfl

theorem cell23_3299257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 5, 5].length) (baseStart_3299257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3299257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3299257 prefixEnd_3299257 := by exact prefixLift 3299257
  have htrace : WordTrace (prefixWord ++ tailWord_3299257) baseStart_3299257 baseEnd_3299257 := by
    simpa [prefixWord, tailWord_3299257, baseEnd_3299257] using wordTrace_append hprefix tailTrace_3299257
  have hstable : (prefixWord ++ tailWord_3299257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3299257).length < 2 ^ (prefixWord ++ tailWord_3299257).sum := by decide
  have hdescent : baseEnd_3299257 < baseStart_3299257 := by decide
  rcases family_descends (prefixWord ++ tailWord_3299257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3299264 : List Nat := [2, 1, 1, 2, 3, 2, 2, 2, 1, 5, 2]
def baseStart_3299264 : Nat := 118140960795 + 3299264 * 2 ^ 59
def prefixEnd_3299264 : Nat := 4983230072969 + 3 ^ 40 * 3299264 * 2
def baseEnd_3299264 : Nat := 1694108238075484848126967

theorem tailTrace_3299264 : CollatzResearch.WordTrace tailWord_3299264 prefixEnd_3299264 1694108238075484848126967 := by
  unfold tailWord_3299264
  simp only [CollatzResearch.WordTrace]
  refine ⟨60167021959668736138108423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80222695946224981517477897 60167021959668736138108423)
  ·
    refine ⟨90250532939503104207162635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60167021959668736138108423 90250532939503104207162635)
    ·
      refine ⟨135375799409254656310743953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90250532939503104207162635 135375799409254656310743953)
      ·
        refine ⟨101531849556940992233057965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135375799409254656310743953 101531849556940992233057965)
        ·
          refine ⟨38074443583852872087396737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101531849556940992233057965 38074443583852872087396737)
          ·
            refine ⟨28555832687889654065547553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38074443583852872087396737 28555832687889654065547553)
            ·
              refine ⟨21416874515917240549160665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28555832687889654065547553 21416874515917240549160665)
              ·
                refine ⟨16062655886937930411870499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21416874515917240549160665 16062655886937930411870499)
                ·
                  refine ⟨24093983830406895617805749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16062655886937930411870499 24093983830406895617805749)
                  ·
                    refine ⟨2258810984100646464169289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24093983830406895617805749 2258810984100646464169289)
                    ·
                      refine ⟨1694108238075484848126967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2258810984100646464169289 1694108238075484848126967)
                      ·
                        rfl

theorem cell23_3299264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 2, 1, 5, 2].length) (baseStart_3299264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3299264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3299264 prefixEnd_3299264 := by exact prefixLift 3299264
  have htrace : WordTrace (prefixWord ++ tailWord_3299264) baseStart_3299264 baseEnd_3299264 := by
    simpa [prefixWord, tailWord_3299264, baseEnd_3299264] using wordTrace_append hprefix tailTrace_3299264
  have hstable : (prefixWord ++ tailWord_3299264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3299264).length < 2 ^ (prefixWord ++ tailWord_3299264).sum := by decide
  have hdescent : baseEnd_3299264 < baseStart_3299264 := by decide
  rcases family_descends (prefixWord ++ tailWord_3299264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3299287 : List Nat := [1, 1, 3, 2, 1, 1, 3, 4, 1, 6]
def baseStart_3299287 : Nat := 118140960795 + 3299287 * 2 ^ 59
def prefixEnd_3299287 : Nat := 4983230072969 + 3 ^ 40 * 3299287 * 2
def baseEnd_3299287 : Nat := 564706682710179419379787

theorem tailTrace_3299287 : CollatzResearch.WordTrace tailWord_3299287 prefixEnd_3299287 564706682710179419379787 := by
  unfold tailWord_3299287
  simp only [CollatzResearch.WordTrace]
  refine ⟨120334882798254147204304115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80223255198836098136202743 120334882798254147204304115)
  ·
    refine ⟨180502324197381220806456173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120334882798254147204304115 180502324197381220806456173)
    ·
      refine ⟨67688371574017957802421065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180502324197381220806456173 67688371574017957802421065)
      ·
        refine ⟨50766278680513468351815799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67688371574017957802421065 50766278680513468351815799)
        ·
          refine ⟨76149418020770202527723699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50766278680513468351815799 76149418020770202527723699)
          ·
            refine ⟨114224127031155303791585549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76149418020770202527723699 114224127031155303791585549)
            ·
              refine ⟨42834047636683238921844581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 114224127031155303791585549 42834047636683238921844581)
              ·
                refine ⟨8031383931878107297845859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42834047636683238921844581 8031383931878107297845859)
                ·
                  refine ⟨12047075897817160946768789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8031383931878107297845859 12047075897817160946768789)
                  ·
                    refine ⟨564706682710179419379787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12047075897817160946768789 564706682710179419379787)
                    ·
                      rfl

theorem cell23_3299287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 4, 1, 6].length) (baseStart_3299287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3299287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3299287 prefixEnd_3299287 := by exact prefixLift 3299287
  have htrace : WordTrace (prefixWord ++ tailWord_3299287) baseStart_3299287 baseEnd_3299287 := by
    simpa [prefixWord, tailWord_3299287, baseEnd_3299287] using wordTrace_append hprefix tailTrace_3299287
  have hstable : (prefixWord ++ tailWord_3299287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3299287).length < 2 ^ (prefixWord ++ tailWord_3299287).sum := by decide
  have hdescent : baseEnd_3299287 < baseStart_3299287 := by decide
  rcases family_descends (prefixWord ++ tailWord_3299287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3299288 : List Nat := [2, 1, 2, 2, 2, 2, 4, 3, 1, 1, 3]
def baseStart_3299288 : Nat := 118140960795 + 3299288 * 2 ^ 59
def prefixEnd_3299288 : Nat := 4983230072969 + 3 ^ 40 * 3299288 * 2
def baseEnd_3299288 : Nat := 1694120561611192754226857

theorem tailTrace_3299288 : CollatzResearch.WordTrace tailWord_3299288 prefixEnd_3299288 1694120561611192754226857 := by
  unfold tailWord_3299288
  simp only [CollatzResearch.WordTrace]
  refine ⟨60167459635625262187545259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80223279514167016250060345 60167459635625262187545259)
  ·
    refine ⟨90251189453437893281317889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60167459635625262187545259 90251189453437893281317889)
    ·
      refine ⟨67688392090078419960988417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90251189453437893281317889 67688392090078419960988417)
      ·
        refine ⟨50766294067558814970741313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67688392090078419960988417 50766294067558814970741313)
        ·
          refine ⟨38074720550669111228055985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50766294067558814970741313 38074720550669111228055985)
          ·
            refine ⟨28556040413001833421041989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38074720550669111228055985 28556040413001833421041989)
            ·
              refine ⟨5354257577437843766445373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28556040413001833421041989 5354257577437843766445373)
              ·
                refine ⟨2007846591539191412417015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5354257577437843766445373 2007846591539191412417015)
                ·
                  refine ⟨3011769887308787118625523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2007846591539191412417015 3011769887308787118625523)
                  ·
                    refine ⟨4517654830963180677938285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3011769887308787118625523 4517654830963180677938285)
                    ·
                      refine ⟨1694120561611192754226857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4517654830963180677938285 1694120561611192754226857)
                      ·
                        rfl

theorem cell23_3299288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4, 3, 1, 1, 3].length) (baseStart_3299288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3299288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3299288 prefixEnd_3299288 := by exact prefixLift 3299288
  have htrace : WordTrace (prefixWord ++ tailWord_3299288) baseStart_3299288 baseEnd_3299288 := by
    simpa [prefixWord, tailWord_3299288, baseEnd_3299288] using wordTrace_append hprefix tailTrace_3299288
  have hstable : (prefixWord ++ tailWord_3299288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3299288).length < 2 ^ (prefixWord ++ tailWord_3299288).sum := by decide
  have hdescent : baseEnd_3299288 < baseStart_3299288 := by decide
  rcases family_descends (prefixWord ++ tailWord_3299288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3299307 : List Nat := [1, 1, 1, 1, 2, 3, 1, 4, 3, 2, 4]
def baseStart_3299307 : Nat := 118140960795 + 3299307 * 2 ^ 59
def prefixEnd_3299307 : Nat := 4983230072969 + 3 ^ 40 * 3299307 * 2
def baseEnd_3299307 : Nat := 1694130317743628179889269

theorem tailTrace_3299307 : CollatzResearch.WordTrace tailWord_3299307 prefixEnd_3299307 1694130317743628179889269 := by
  unfold tailWord_3299307
  simp only [CollatzResearch.WordTrace]
  refine ⟨120335612258181690620032175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80223741505454460413354783 120335612258181690620032175)
  ·
    refine ⟨180503418387272535930048263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120335612258181690620032175 180503418387272535930048263)
    ·
      refine ⟨270755127580908803895072395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180503418387272535930048263 270755127580908803895072395)
      ·
        refine ⟨406132691371363205842608593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270755127580908803895072395 406132691371363205842608593)
        ·
          refine ⟨304599518528522404381956445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 406132691371363205842608593 304599518528522404381956445)
          ·
            refine ⟨114224819448195901643233667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 304599518528522404381956445 114224819448195901643233667)
            ·
              refine ⟨171337229172293852464850501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114224819448195901643233667 171337229172293852464850501)
              ·
                refine ⟨32125730469805097337159469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 171337229172293852464850501 32125730469805097337159469)
                ·
                  refine ⟨12047148926176911501434801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32125730469805097337159469 12047148926176911501434801)
                  ·
                    refine ⟨9035361694632683626076101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12047148926176911501434801 9035361694632683626076101)
                    ·
                      refine ⟨1694130317743628179889269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9035361694632683626076101 1694130317743628179889269)
                      ·
                        rfl

theorem cell23_3299307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 4, 3, 2, 4].length) (baseStart_3299307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3299307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3299307 prefixEnd_3299307 := by exact prefixLift 3299307
  have htrace : WordTrace (prefixWord ++ tailWord_3299307) baseStart_3299307 baseEnd_3299307 := by
    simpa [prefixWord, tailWord_3299307, baseEnd_3299307] using wordTrace_append hprefix tailTrace_3299307
  have hstable : (prefixWord ++ tailWord_3299307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3299307).length < 2 ^ (prefixWord ++ tailWord_3299307).sum := by decide
  have hdescent : baseEnd_3299307 < baseStart_3299307 := by decide
  rcases family_descends (prefixWord ++ tailWord_3299307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3299351 : List Nat := [1, 1, 3, 5, 3, 1, 9]
def baseStart_3299351 : Nat := 118140960795 + 3299351 * 2 ^ 59
def prefixEnd_3299351 : Nat := 4983230072969 + 3 ^ 40 * 3299351 * 2
def baseEnd_3299351 : Nat := 20915468035708963058507

theorem tailTrace_3299351 : CollatzResearch.WordTrace tailWord_3299351 prefixEnd_3299351 20915468035708963058507 := by
  unfold tailWord_3299351
  simp only [CollatzResearch.WordTrace]
  refine ⟨120337217070022286134633907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80224811380014857423089271 120337217070022286134633907)
  ·
    refine ⟨180505825605033429201950861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120337217070022286134633907 180505825605033429201950861)
    ·
      refine ⟨67689684601887535950731573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180505825605033429201950861 67689684601887535950731573)
      ·
        refine ⟨6345907931426956495381085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 67689684601887535950731573 6345907931426956495381085)
        ·
          refine ⟨2379715474285108685767907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6345907931426956495381085 2379715474285108685767907)
          ·
            refine ⟨3569573211427663028651861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2379715474285108685767907 3569573211427663028651861)
            ·
              refine ⟨20915468035708963058507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3569573211427663028651861 20915468035708963058507)
              ·
                rfl

theorem cell23_3299351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 9].length) (baseStart_3299351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3299351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3299351 prefixEnd_3299351 := by exact prefixLift 3299351
  have htrace : WordTrace (prefixWord ++ tailWord_3299351) baseStart_3299351 baseEnd_3299351 := by
    simpa [prefixWord, tailWord_3299351, baseEnd_3299351] using wordTrace_append hprefix tailTrace_3299351
  have hstable : (prefixWord ++ tailWord_3299351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3299351).length < 2 ^ (prefixWord ++ tailWord_3299351).sum := by decide
  have hdescent : baseEnd_3299351 < baseStart_3299351 := by decide
  rcases family_descends (prefixWord ++ tailWord_3299351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3299362 : List Nat := [3, 3, 1, 1, 1, 2, 5, 2, 1, 2, 2]
def baseStart_3299362 : Nat := 118140960795 + 3299362 * 2 ^ 59
def prefixEnd_3299362 : Nat := 4983230072969 + 3 ^ 40 * 3299362 * 2
def baseEnd_3299362 : Nat := 1694158559179625464701517

theorem tailTrace_3299362 : CollatzResearch.WordTrace tailWord_3299362 prefixEnd_3299362 1694158559179625464701517 := by
  unfold tailWord_3299362
  simp only [CollatzResearch.WordTrace]
  refine ⟨30084404568245608753321085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80225078848654956675522893 30084404568245608753321085)
  ·
    refine ⟨11281651713092103282495407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30084404568245608753321085 11281651713092103282495407)
    ·
      refine ⟨16922477569638154923743111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11281651713092103282495407 16922477569638154923743111)
      ·
        refine ⟨25383716354457232385614667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16922477569638154923743111 25383716354457232385614667)
        ·
          refine ⟨38075574531685848578422001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25383716354457232385614667 38075574531685848578422001)
          ·
            refine ⟨28556680898764386433816501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38075574531685848578422001 28556680898764386433816501)
            ·
              refine ⟨2677188834259161228170297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28556680898764386433816501 2677188834259161228170297)
              ·
                refine ⟨2007891625694370921127723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2677188834259161228170297 2007891625694370921127723)
                ·
                  refine ⟨3011837438541556381691585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2007891625694370921127723 3011837438541556381691585)
                  ·
                    refine ⟨2258878078906167286268689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3011837438541556381691585 2258878078906167286268689)
                    ·
                      refine ⟨1694158559179625464701517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2258878078906167286268689 1694158559179625464701517)
                      ·
                        rfl

theorem cell23_3299362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 5, 2, 1, 2, 2].length) (baseStart_3299362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3299362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3299362 prefixEnd_3299362 := by exact prefixLift 3299362
  have htrace : WordTrace (prefixWord ++ tailWord_3299362) baseStart_3299362 baseEnd_3299362 := by
    simpa [prefixWord, tailWord_3299362, baseEnd_3299362] using wordTrace_append hprefix tailTrace_3299362
  have hstable : (prefixWord ++ tailWord_3299362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3299362).length < 2 ^ (prefixWord ++ tailWord_3299362).sum := by decide
  have hdescent : baseEnd_3299362 < baseStart_3299362 := by decide
  rcases family_descends (prefixWord ++ tailWord_3299362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3299378 : List Nat := [3, 2, 1, 1, 2, 4, 1, 3, 2, 1, 3]
def baseStart_3299378 : Nat := 118140960795 + 3299378 * 2 ^ 59
def prefixEnd_3299378 : Nat := 4983230072969 + 3 ^ 40 * 3299378 * 2
def baseEnd_3299378 : Nat := 1694166774870097402101443

theorem tailTrace_3299378 : CollatzResearch.WordTrace tailWord_3299378 prefixEnd_3299378 1694166774870097402101443 := by
  unfold tailWord_3299378
  simp only [CollatzResearch.WordTrace]
  refine ⟨30084550460231117436466697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80225467893949646497244525 30084550460231117436466697)
  ·
    refine ⟨22563412845173338077350023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30084550460231117436466697 22563412845173338077350023)
    ·
      refine ⟨33845119267760007116025035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22563412845173338077350023 33845119267760007116025035)
      ·
        refine ⟨50767678901640010674037553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33845119267760007116025035 50767678901640010674037553)
        ·
          refine ⟨38075759176230008005528165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50767678901640010674037553 38075759176230008005528165)
          ·
            refine ⟨7139204845543126501036531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38075759176230008005528165 7139204845543126501036531)
            ·
              refine ⟨10708807268314689751554797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7139204845543126501036531 10708807268314689751554797)
              ·
                refine ⟨4015802725618008656833049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10708807268314689751554797 4015802725618008656833049)
                ·
                  refine ⟨3011852044213506492624787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4015802725618008656833049 3011852044213506492624787)
                  ·
                    refine ⟨4517778066320259738937181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3011852044213506492624787 4517778066320259738937181)
                    ·
                      refine ⟨1694166774870097402101443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4517778066320259738937181 1694166774870097402101443)
                      ·
                        rfl

theorem cell23_3299378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 3, 2, 1, 3].length) (baseStart_3299378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3299378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3299378 prefixEnd_3299378 := by exact prefixLift 3299378
  have htrace : WordTrace (prefixWord ++ tailWord_3299378) baseStart_3299378 baseEnd_3299378 := by
    simpa [prefixWord, tailWord_3299378, baseEnd_3299378] using wordTrace_append hprefix tailTrace_3299378
  have hstable : (prefixWord ++ tailWord_3299378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3299378).length < 2 ^ (prefixWord ++ tailWord_3299378).sum := by decide
  have hdescent : baseEnd_3299378 < baseStart_3299378 := by decide
  rcases family_descends (prefixWord ++ tailWord_3299378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3299387 : List Nat := [1, 1, 1, 1, 1, 2, 1, 4, 3, 3, 5]
def baseStart_3299387 : Nat := 118140960795 + 3299387 * 2 ^ 59
def prefixEnd_3299387 : Nat := 4983230072969 + 3 ^ 40 * 3299387 * 2
def baseEnd_3299387 : Nat := 1694171396195987866888901

theorem tailTrace_3299387 : CollatzResearch.WordTrace tailWord_3299387 prefixEnd_3299387 1694171396195987866888901 := by
  unfold tailWord_3299387
  simp only [CollatzResearch.WordTrace]
  refine ⟨120338530097891864282944415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80225686731927909521962943 120338530097891864282944415)
  ·
    refine ⟨180507795146837796424416623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120338530097891864282944415 180507795146837796424416623)
    ·
      refine ⟨270761692720256694636624935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180507795146837796424416623 270761692720256694636624935)
      ·
        refine ⟨406142539080385041954937403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270761692720256694636624935 406142539080385041954937403)
        ·
          refine ⟨609213808620577562932406105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 406142539080385041954937403 609213808620577562932406105)
          ·
            refine ⟨456910356465433172199304579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 609213808620577562932406105 456910356465433172199304579)
            ·
              refine ⟨685365534698149758298956869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 456910356465433172199304579 685365534698149758298956869)
              ·
                refine ⟨128506037755903079681054413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 685365534698149758298956869 128506037755903079681054413)
                ·
                  refine ⟨48189764158463654880395405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 128506037755903079681054413 48189764158463654880395405)
                  ·
                    refine ⟨18071161559423870580148277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48189764158463654880395405 18071161559423870580148277)
                    ·
                      refine ⟨1694171396195987866888901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18071161559423870580148277 1694171396195987866888901)
                      ·
                        rfl

theorem cell23_3299387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 3, 3, 5].length) (baseStart_3299387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3299387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3299387 prefixEnd_3299387 := by exact prefixLift 3299387
  have htrace : WordTrace (prefixWord ++ tailWord_3299387) baseStart_3299387 baseEnd_3299387 := by
    simpa [prefixWord, tailWord_3299387, baseEnd_3299387] using wordTrace_append hprefix tailTrace_3299387
  have hstable : (prefixWord ++ tailWord_3299387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3299387).length < 2 ^ (prefixWord ++ tailWord_3299387).sum := by decide
  have hdescent : baseEnd_3299387 < baseStart_3299387 := by decide
  rcases family_descends (prefixWord ++ tailWord_3299387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3299401 : List Nat := [1, 2, 1, 1, 2, 2, 5, 2, 1, 4, 2]
def baseStart_3299401 : Nat := 118140960795 + 3299401 * 2 ^ 59
def prefixEnd_3299401 : Nat := 4983230072969 + 3 ^ 40 * 3299401 * 2
def baseEnd_3299401 : Nat := 1694178584925150812113837

theorem tailTrace_3299401 : CollatzResearch.WordTrace tailWord_3299401 prefixEnd_3299401 1694178584925150812113837 := by
  unfold tailWord_3299401
  simp only [CollatzResearch.WordTrace]
  refine ⟨120339040719841144673954057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80226027146560763115969371 120339040719841144673954057)
  ·
    refine ⟨90254280539880858505465543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120339040719841144673954057 90254280539880858505465543)
    ·
      refine ⟨135381420809821287758198315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90254280539880858505465543 135381420809821287758198315)
      ·
        refine ⟨203072131214731931637297473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135381420809821287758198315 203072131214731931637297473)
        ·
          refine ⟨152304098411048948727973105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203072131214731931637297473 152304098411048948727973105)
          ·
            refine ⟨114228073808286711545979829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152304098411048948727973105 114228073808286711545979829)
            ·
              refine ⟨10708881919526879207435609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 114228073808286711545979829 10708881919526879207435609)
              ·
                refine ⟨8031661439645159405576707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10708881919526879207435609 8031661439645159405576707)
                ·
                  refine ⟨12047492159467739108365061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8031661439645159405576707 12047492159467739108365061)
                  ·
                    refine ⟨2258904779900201082818449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12047492159467739108365061 2258904779900201082818449)
                    ·
                      refine ⟨1694178584925150812113837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2258904779900201082818449 1694178584925150812113837)
                      ·
                        rfl

theorem cell23_3299401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 2, 1, 4, 2].length) (baseStart_3299401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3299401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3299401 prefixEnd_3299401 := by exact prefixLift 3299401
  have htrace : WordTrace (prefixWord ++ tailWord_3299401) baseStart_3299401 baseEnd_3299401 := by
    simpa [prefixWord, tailWord_3299401, baseEnd_3299401] using wordTrace_append hprefix tailTrace_3299401
  have hstable : (prefixWord ++ tailWord_3299401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3299401).length < 2 ^ (prefixWord ++ tailWord_3299401).sum := by decide
  have hdescent : baseEnd_3299401 < baseStart_3299401 := by decide
  rcases family_descends (prefixWord ++ tailWord_3299401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3299404 : List Nat := [2, 2, 1, 3, 1, 1, 4, 1, 2, 1, 5]
def baseStart_3299404 : Nat := 118140960795 + 3299404 * 2 ^ 59
def prefixEnd_3299404 : Nat := 4983230072969 + 3 ^ 40 * 3299404 * 2
def baseEnd_3299404 : Nat := 1694180125367114300376323

theorem tailTrace_3299404 : CollatzResearch.WordTrace tailWord_3299404 prefixEnd_3299404 1694180125367114300376323 := by
  unfold tailWord_3299404
  simp only [CollatzResearch.WordTrace]
  refine ⟨60169575069415138093156633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80226100092553517457542177 60169575069415138093156633)
  ·
    refine ⟨45127181302061353569867475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60169575069415138093156633 45127181302061353569867475)
    ·
      refine ⟨67690771953092030354801213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45127181302061353569867475 67690771953092030354801213)
      ·
        refine ⟨25384039482409511383050455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67690771953092030354801213 25384039482409511383050455)
        ·
          refine ⟨38076059223614267074575683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25384039482409511383050455 38076059223614267074575683)
          ·
            refine ⟨57114088835421400611863525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38076059223614267074575683 57114088835421400611863525)
            ·
              refine ⟨10708891656641512614724411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57114088835421400611863525 10708891656641512614724411)
              ·
                refine ⟨16063337484962268922086617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10708891656641512614724411 16063337484962268922086617)
                ·
                  refine ⟨12047503113721701691564963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16063337484962268922086617 12047503113721701691564963)
                  ·
                    refine ⟨18071254670582552537347445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12047503113721701691564963 18071254670582552537347445)
                    ·
                      refine ⟨1694180125367114300376323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18071254670582552537347445 1694180125367114300376323)
                      ·
                        rfl

theorem cell23_3299404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 1, 2, 1, 5].length) (baseStart_3299404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3299404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3299404 prefixEnd_3299404 := by exact prefixLift 3299404
  have htrace : WordTrace (prefixWord ++ tailWord_3299404) baseStart_3299404 baseEnd_3299404 := by
    simpa [prefixWord, tailWord_3299404, baseEnd_3299404] using wordTrace_append hprefix tailTrace_3299404
  have hstable : (prefixWord ++ tailWord_3299404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3299404).length < 2 ^ (prefixWord ++ tailWord_3299404).sum := by decide
  have hdescent : baseEnd_3299404 < baseStart_3299404 := by decide
  rcases family_descends (prefixWord ++ tailWord_3299404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3299407 : List Nat := [1, 1, 2, 1, 1, 2, 2, 4, 9]
def baseStart_3299407 : Nat := 118140960795 + 3299407 * 2 ^ 59
def prefixEnd_3299407 : Nat := 4983230072969 + 3 ^ 40 * 3299407 * 2
def baseEnd_3299407 : Nat := 188242407312119754293201

theorem tailTrace_3299407 : CollatzResearch.WordTrace tailWord_3299407 prefixEnd_3299407 188242407312119754293201 := by
  unfold tailWord_3299407
  simp only [CollatzResearch.WordTrace]
  refine ⟨120339259557819407698672475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80226173038546271799114983 120339259557819407698672475)
  ·
    refine ⟨180508889336729111548008713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120339259557819407698672475 180508889336729111548008713)
    ·
      refine ⟨135381667002546833661006535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180508889336729111548008713 135381667002546833661006535)
      ·
        refine ⟨203072500503820250491509803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135381667002546833661006535 203072500503820250491509803)
        ·
          refine ⟨304608750755730375737264705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203072500503820250491509803 304608750755730375737264705)
          ·
            refine ⟨228456563066797781802948529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 304608750755730375737264705 228456563066797781802948529)
            ·
              refine ⟨171342422300098336352211397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 228456563066797781802948529 171342422300098336352211397)
              ·
                refine ⟨32126704181268438066039637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 171342422300098336352211397 32126704181268438066039637)
                ·
                  refine ⟨188242407312119754293201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 32126704181268438066039637 188242407312119754293201)
                  ·
                    rfl

theorem cell23_3299407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 4, 9].length) (baseStart_3299407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3299407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3299407 prefixEnd_3299407 := by exact prefixLift 3299407
  have htrace : WordTrace (prefixWord ++ tailWord_3299407) baseStart_3299407 baseEnd_3299407 := by
    simpa [prefixWord, tailWord_3299407, baseEnd_3299407] using wordTrace_append hprefix tailTrace_3299407
  have hstable : (prefixWord ++ tailWord_3299407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3299407).length < 2 ^ (prefixWord ++ tailWord_3299407).sum := by decide
  have hdescent : baseEnd_3299407 < baseStart_3299407 := by decide
  rcases family_descends (prefixWord ++ tailWord_3299407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3299511 : List Nat := [1, 1, 3, 1, 4, 2, 2, 1, 1, 4, 3]
def baseStart_3299511 : Nat := 118140960795 + 3299511 * 2 ^ 59
def prefixEnd_3299511 : Nat := 4983230072969 + 3 ^ 40 * 3299511 * 2
def baseEnd_3299511 : Nat := 1694235067797145381738331

theorem tailTrace_3299511 : CollatzResearch.WordTrace tailWord_3299511 prefixEnd_3299511 1694235067797145381738331 := by
  unfold tailWord_3299511
  simp only [CollatzResearch.WordTrace]
  refine ⟨120343052749442633460458387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80228701832961755640305591 120343052749442633460458387)
  ·
    refine ⟨180514579124163950190687581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120343052749442633460458387 180514579124163950190687581)
    ·
      refine ⟨67692967171561481321507843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180514579124163950190687581 67692967171561481321507843)
      ·
        refine ⟨101539450757342221982261765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67692967171561481321507843 101539450757342221982261765)
        ·
          refine ⟨19038647017001666621674081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101539450757342221982261765 19038647017001666621674081)
          ·
            refine ⟨14278985262751249966255561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19038647017001666621674081 14278985262751249966255561)
            ·
              refine ⟨10709238947063437474691671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14278985262751249966255561 10709238947063437474691671)
              ·
                refine ⟨16063858420595156212037507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10709238947063437474691671 16063858420595156212037507)
                ·
                  refine ⟨24095787630892734318056261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16063858420595156212037507 24095787630892734318056261)
                  ·
                    refine ⟨4517960180792387684635549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24095787630892734318056261 4517960180792387684635549)
                    ·
                      refine ⟨1694235067797145381738331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4517960180792387684635549 1694235067797145381738331)
                      ·
                        rfl

theorem cell23_3299511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 1, 1, 4, 3].length) (baseStart_3299511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3299511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3299511 prefixEnd_3299511 := by exact prefixLift 3299511
  have htrace : WordTrace (prefixWord ++ tailWord_3299511) baseStart_3299511 baseEnd_3299511 := by
    simpa [prefixWord, tailWord_3299511, baseEnd_3299511] using wordTrace_append hprefix tailTrace_3299511
  have hstable : (prefixWord ++ tailWord_3299511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3299511).length < 2 ^ (prefixWord ++ tailWord_3299511).sum := by decide
  have hdescent : baseEnd_3299511 < baseStart_3299511 := by decide
  rcases family_descends (prefixWord ++ tailWord_3299511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3299514 : List Nat := [3, 1, 1, 1, 2, 2, 3, 2, 8]
def baseStart_3299514 : Nat := 118140960795 + 3299514 * 2 ^ 59
def prefixEnd_3299514 : Nat := 4983230072969 + 3 ^ 40 * 3299514 * 2
def baseEnd_3299514 : Nat := 188248512026567652222313

theorem tailTrace_3299514 : CollatzResearch.WordTrace tailWord_3299514 prefixEnd_3299514 188248512026567652222313 := by
  unfold tailWord_3299514
  simp only [CollatzResearch.WordTrace]
  refine ⟨30085790542107941243204399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80228774778954509981878397 30085790542107941243204399)
  ·
    refine ⟨45128685813161911864806599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30085790542107941243204399 45128685813161911864806599)
    ·
      refine ⟨67693028719742867797209899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45128685813161911864806599 67693028719742867797209899)
      ·
        refine ⟨101539543079614301695814849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67693028719742867797209899 101539543079614301695814849)
        ·
          refine ⟨76154657309710726271861137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101539543079614301695814849 76154657309710726271861137)
          ·
            refine ⟨57115992982283044703895853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76154657309710726271861137 57115992982283044703895853)
            ·
              refine ⟨21418497368356141763960945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57115992982283044703895853 21418497368356141763960945)
              ·
                refine ⟨16063873026267106322970709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21418497368356141763960945 16063873026267106322970709)
                ·
                  refine ⟨188248512026567652222313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16063873026267106322970709 188248512026567652222313)
                  ·
                    rfl

theorem cell23_3299514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 2, 8].length) (baseStart_3299514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3299514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3299514 prefixEnd_3299514 := by exact prefixLift 3299514
  have htrace : WordTrace (prefixWord ++ tailWord_3299514) baseStart_3299514 baseEnd_3299514 := by
    simpa [prefixWord, tailWord_3299514, baseEnd_3299514] using wordTrace_append hprefix tailTrace_3299514
  have hstable : (prefixWord ++ tailWord_3299514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3299514).length < 2 ^ (prefixWord ++ tailWord_3299514).sum := by decide
  have hdescent : baseEnd_3299514 < baseStart_3299514 := by decide
  rcases family_descends (prefixWord ++ tailWord_3299514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3299535 : List Nat := [1, 1, 2, 1, 1, 3, 7, 2, 1, 4]
def baseStart_3299535 : Nat := 118140960795 + 3299535 * 2 ^ 59
def prefixEnd_3299535 : Nat := 4983230072969 + 3 ^ 40 * 3299535 * 2
def baseEnd_3299535 : Nat := 564749130444284429279407

theorem tailTrace_3299535 : CollatzResearch.WordTrace tailWord_3299535 prefixEnd_3299535 564749130444284429279407 := by
  unfold tailWord_3299535
  simp only [CollatzResearch.WordTrace]
  refine ⟨120343928101355685559332059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80229285400903790372888039 120343928101355685559332059)
  ·
    refine ⟨180515892152033528338998089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120343928101355685559332059 180515892152033528338998089)
    ·
      refine ⟨135386919114025146254248567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180515892152033528338998089 135386919114025146254248567)
      ·
        refine ⟨203080378671037719381372851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135386919114025146254248567 203080378671037719381372851)
        ·
          refine ⟨304620568006556579072059277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203080378671037719381372851 304620568006556579072059277)
          ·
            refine ⟨114232713002458717152022229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 304620568006556579072059277 114232713002458717152022229)
            ·
              refine ⟨2677329210995126183250521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 114232713002458717152022229 2677329210995126183250521)
              ·
                refine ⟨2007996908246344637437891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2677329210995126183250521 2007996908246344637437891)
                ·
                  refine ⟨3011995362369516956156837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2007996908246344637437891 3011995362369516956156837)
                  ·
                    refine ⟨564749130444284429279407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3011995362369516956156837 564749130444284429279407)
                    ·
                      rfl

theorem cell23_3299535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 7, 2, 1, 4].length) (baseStart_3299535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3299535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3299535 prefixEnd_3299535 := by exact prefixLift 3299535
  have htrace : WordTrace (prefixWord ++ tailWord_3299535) baseStart_3299535 baseEnd_3299535 := by
    simpa [prefixWord, tailWord_3299535, baseEnd_3299535] using wordTrace_append hprefix tailTrace_3299535
  have hstable : (prefixWord ++ tailWord_3299535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3299535).length < 2 ^ (prefixWord ++ tailWord_3299535).sum := by decide
  have hdescent : baseEnd_3299535 < baseStart_3299535 := by decide
  rcases family_descends (prefixWord ++ tailWord_3299535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3299592 : List Nat := [2, 1, 3, 2, 3, 2, 1, 4, 1, 1, 3]
def baseStart_3299592 : Nat := 118140960795 + 3299592 * 2 ^ 59
def prefixEnd_3299592 : Nat := 4983230072969 + 3 ^ 40 * 3299592 * 2
def baseEnd_3299592 : Nat := 1694276659730159564825459

theorem tailTrace_3299592 : CollatzResearch.WordTrace tailWord_3299592 prefixEnd_3299592 1694276659730159564825459 := by
  unfold tailWord_3299592
  simp only [CollatzResearch.WordTrace]
  refine ⟨60173003531074592147078515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80230671374766122862771353 60173003531074592147078515)
  ·
    refine ⟨90259505296611888220617773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60173003531074592147078515 90259505296611888220617773)
    ·
      refine ⟨33847314486229458082731665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90259505296611888220617773 33847314486229458082731665)
      ·
        refine ⟨25385485864672093562048749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33847314486229458082731665 25385485864672093562048749)
        ·
          refine ⟨9519557199252035085768281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25385485864672093562048749 9519557199252035085768281)
          ·
            refine ⟨7139667899439026314326211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9519557199252035085768281 7139667899439026314326211)
            ·
              refine ⟨10709501849158539471489317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7139667899439026314326211 10709501849158539471489317)
              ·
                refine ⟨2008031596717226150904247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10709501849158539471489317 2008031596717226150904247)
                ·
                  refine ⟨3012047395075839226356371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2008031596717226150904247 3012047395075839226356371)
                  ·
                    refine ⟨4518071092613758839534557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3012047395075839226356371 4518071092613758839534557)
                    ·
                      refine ⟨1694276659730159564825459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4518071092613758839534557 1694276659730159564825459)
                      ·
                        rfl

theorem cell23_3299592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 4, 1, 1, 3].length) (baseStart_3299592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3299592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3299592 prefixEnd_3299592 := by exact prefixLift 3299592
  have htrace : WordTrace (prefixWord ++ tailWord_3299592) baseStart_3299592 baseEnd_3299592 := by
    simpa [prefixWord, tailWord_3299592, baseEnd_3299592] using wordTrace_append hprefix tailTrace_3299592
  have hstable : (prefixWord ++ tailWord_3299592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3299592).length < 2 ^ (prefixWord ++ tailWord_3299592).sum := by decide
  have hdescent : baseEnd_3299592 < baseStart_3299592 := by decide
  rcases family_descends (prefixWord ++ tailWord_3299592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3299608 : List Nat := [2, 1, 2, 3, 1, 2, 1, 5, 2, 4]
def baseStart_3299608 : Nat := 118140960795 + 3299608 * 2 ^ 59
def prefixEnd_3299608 : Nat := 4983230072969 + 3 ^ 40 * 3299608 * 2
def baseEnd_3299608 : Nat := 564761625140210500741795

theorem tailTrace_3299608 : CollatzResearch.WordTrace tailWord_3299608 prefixEnd_3299608 564761625140210500741795 := by
  unfold tailWord_3299608
  simp only [CollatzResearch.WordTrace]
  refine ⟨60173295315045609513369739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80231060420060812684492985 60173295315045609513369739)
  ·
    refine ⟨90259942972568414270054609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60173295315045609513369739 90259942972568414270054609)
    ·
      refine ⟨67694957229426310702540957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90259942972568414270054609 67694957229426310702540957)
      ·
        refine ⟨25385608961034866513452859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67694957229426310702540957 25385608961034866513452859)
        ·
          refine ⟨38078413441552299770179289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25385608961034866513452859 38078413441552299770179289)
          ·
            refine ⟨28558810081164224827634467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38078413441552299770179289 28558810081164224827634467)
            ·
              refine ⟨42838215121746337241451701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28558810081164224827634467 42838215121746337241451701)
              ·
                refine ⟨4016082667663719116386097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42838215121746337241451701 4016082667663719116386097)
                ·
                  refine ⟨3012062000747789337289573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4016082667663719116386097 3012062000747789337289573)
                  ·
                    refine ⟨564761625140210500741795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3012062000747789337289573 564761625140210500741795)
                    ·
                      rfl

theorem cell23_3299608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 5, 2, 4].length) (baseStart_3299608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3299608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3299608 prefixEnd_3299608 := by exact prefixLift 3299608
  have htrace : WordTrace (prefixWord ++ tailWord_3299608) baseStart_3299608 baseEnd_3299608 := by
    simpa [prefixWord, tailWord_3299608, baseEnd_3299608] using wordTrace_append hprefix tailTrace_3299608
  have hstable : (prefixWord ++ tailWord_3299608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3299608).length < 2 ^ (prefixWord ++ tailWord_3299608).sum := by decide
  have hdescent : baseEnd_3299608 < baseStart_3299608 := by decide
  rcases family_descends (prefixWord ++ tailWord_3299608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3299611 : List Nat := [1, 1, 1, 1, 1, 1, 7, 3, 1, 2, 4]
def baseStart_3299611 : Nat := 118140960795 + 3299611 * 2 ^ 59
def prefixEnd_3299611 : Nat := 4983230072969 + 3 ^ 40 * 3299611 * 2
def baseEnd_3299611 : Nat := 1694286415862594990487871

theorem tailTrace_3299611 : CollatzResearch.WordTrace tailWord_3299611 prefixEnd_3299611 1694286415862594990487871 := by
  unfold tailWord_3299611
  simp only [CollatzResearch.WordTrace]
  refine ⟨120346700049080350539098687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80231133366053567026065791 120346700049080350539098687)
  ·
    refine ⟨180520050073620525808648031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120346700049080350539098687 180520050073620525808648031)
    ·
      refine ⟨270780075110430788712972047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180520050073620525808648031 270780075110430788712972047)
      ·
        refine ⟨406170112665646183069458071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270780075110430788712972047 406170112665646183069458071)
        ·
          refine ⟨609255168998469274604187107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 406170112665646183069458071 609255168998469274604187107)
          ·
            refine ⟨913882753497703911906280661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 609255168998469274604187107 913882753497703911906280661)
            ·
              refine ⟨21419127035102435435303453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 913882753497703911906280661 21419127035102435435303453)
              ·
                refine ⟨8032172638163413288238795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21419127035102435435303453 8032172638163413288238795)
                ·
                  refine ⟨12048258957245119932358193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8032172638163413288238795 12048258957245119932358193)
                  ·
                    refine ⟨9036194217933839949268645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12048258957245119932358193 9036194217933839949268645)
                    ·
                      refine ⟨1694286415862594990487871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9036194217933839949268645 1694286415862594990487871)
                      ·
                        rfl

theorem cell23_3299611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 3, 1, 2, 4].length) (baseStart_3299611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3299611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3299611 prefixEnd_3299611 := by exact prefixLift 3299611
  have htrace : WordTrace (prefixWord ++ tailWord_3299611) baseStart_3299611 baseEnd_3299611 := by
    simpa [prefixWord, tailWord_3299611, baseEnd_3299611] using wordTrace_append hprefix tailTrace_3299611
  have hstable : (prefixWord ++ tailWord_3299611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3299611).length < 2 ^ (prefixWord ++ tailWord_3299611).sum := by decide
  have hdescent : baseEnd_3299611 < baseStart_3299611 := by decide
  rcases family_descends (prefixWord ++ tailWord_3299611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3299615 : List Nat := [1, 1, 2, 4, 3, 1, 1, 1, 5, 2, 2]
def baseStart_3299615 : Nat := 118140960795 + 3299615 * 2 ^ 59
def prefixEnd_3299615 : Nat := 4983230072969 + 3 ^ 40 * 3299615 * 2
def baseEnd_3299615 : Nat := 1694288469785212974837853

theorem tailTrace_3299615 : CollatzResearch.WordTrace tailWord_3299615 prefixEnd_3299615 1694288469785212974837853 := by
  unfold tailWord_3299615
  simp only [CollatzResearch.WordTrace]
  refine ⟨120346845941065859222244299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80231230627377239481496199 120346845941065859222244299)
  ·
    refine ⟨180520268911598788833366449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120346845941065859222244299 180520268911598788833366449)
    ·
      refine ⟨135390201683699091625024837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180520268911598788833366449 135390201683699091625024837)
      ·
        refine ⟨25385662815693579679692157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 135390201683699091625024837 25385662815693579679692157)
        ·
          refine ⟨9519623555885092379884559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25385662815693579679692157 9519623555885092379884559)
          ·
            refine ⟨14279435333827638569826839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9519623555885092379884559 14279435333827638569826839)
            ·
              refine ⟨21419153000741457854740259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14279435333827638569826839 21419153000741457854740259)
              ·
                refine ⟨32128729501112186782110389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21419153000741457854740259 32128729501112186782110389)
                ·
                  refine ⟨3012068390729267510822849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32128729501112186782110389 3012068390729267510822849)
                  ·
                    refine ⟨2259051293046950633117137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3012068390729267510822849 2259051293046950633117137)
                    ·
                      refine ⟨1694288469785212974837853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2259051293046950633117137 1694288469785212974837853)
                      ·
                        rfl

theorem cell23_3299615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 1, 5, 2, 2].length) (baseStart_3299615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3299615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3299615 prefixEnd_3299615 := by exact prefixLift 3299615
  have htrace : WordTrace (prefixWord ++ tailWord_3299615) baseStart_3299615 baseEnd_3299615 := by
    simpa [prefixWord, tailWord_3299615, baseEnd_3299615] using wordTrace_append hprefix tailTrace_3299615
  have hstable : (prefixWord ++ tailWord_3299615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3299615).length < 2 ^ (prefixWord ++ tailWord_3299615).sum := by decide
  have hdescent : baseEnd_3299615 < baseStart_3299615 := by decide
  rcases family_descends (prefixWord ++ tailWord_3299615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3299629 : List Nat := [1, 5, 3, 1, 2, 2, 2, 1, 1, 5]
def baseStart_3299629 : Nat := 118140960795 + 3299629 * 2 ^ 59
def prefixEnd_3299629 : Nat := 4983230072969 + 3 ^ 40 * 3299629 * 2
def baseEnd_3299629 : Nat := 564765219504791973354263

theorem tailTrace_3299629 : CollatzResearch.WordTrace tailWord_3299629 prefixEnd_3299629 564765219504791973354263 := by
  unfold tailWord_3299629
  simp only [CollatzResearch.WordTrace]
  refine ⟨120347356563015139613253941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80231571042010093075502627 120347356563015139613253941)
  ·
    refine ⟨11282564677782669338742557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 120347356563015139613253941 11282564677782669338742557)
    ·
      refine ⟨4230961754168501002028459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11282564677782669338742557 4230961754168501002028459)
      ·
        refine ⟨6346442631252751503042689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4230961754168501002028459 6346442631252751503042689)
        ·
          refine ⟨4759831973439563627282017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6346442631252751503042689 4759831973439563627282017)
          ·
            refine ⟨3569873980079672720461513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4759831973439563627282017 3569873980079672720461513)
            ·
              refine ⟨2677405485059754540346135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3569873980079672720461513 2677405485059754540346135)
              ·
                refine ⟨4016108227589631810519203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2677405485059754540346135 4016108227589631810519203)
                ·
                  refine ⟨6024162341384447715778805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4016108227589631810519203 6024162341384447715778805)
                  ·
                    refine ⟨564765219504791973354263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6024162341384447715778805 564765219504791973354263)
                    ·
                      rfl

theorem cell23_3299629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_3299629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3299629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3299629 prefixEnd_3299629 := by exact prefixLift 3299629
  have htrace : WordTrace (prefixWord ++ tailWord_3299629) baseStart_3299629 baseEnd_3299629 := by
    simpa [prefixWord, tailWord_3299629, baseEnd_3299629] using wordTrace_append hprefix tailTrace_3299629
  have hstable : (prefixWord ++ tailWord_3299629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3299629).length < 2 ^ (prefixWord ++ tailWord_3299629).sum := by decide
  have hdescent : baseEnd_3299629 < baseStart_3299629 := by decide
  rcases family_descends (prefixWord ++ tailWord_3299629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3299649 : List Nat := [1, 2, 5, 2, 2, 1, 2, 1, 3, 2, 2]
def baseStart_3299649 : Nat := 118140960795 + 3299649 * 2 ^ 59
def prefixEnd_3299649 : Nat := 4983230072969 + 3 ^ 40 * 3299649 * 2
def baseEnd_3299649 : Nat := 1694305928127465841812697

theorem tailTrace_3299649 : CollatzResearch.WordTrace tailWord_3299649 prefixEnd_3299649 1694305928127465841812697 := by
  unfold tailWord_3299649
  simp only [CollatzResearch.WordTrace]
  refine ⟨120348086022942683028982001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80232057348628455352654667 120348086022942683028982001)
  ·
    refine ⟨90261064517207012271736501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120348086022942683028982001 90261064517207012271736501)
    ·
      refine ⟨8461974798488157400475297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 90261064517207012271736501 8461974798488157400475297)
      ·
        refine ⟨6346481098866118050356473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8461974798488157400475297 6346481098866118050356473)
        ·
          refine ⟨4759860824149588537767355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6346481098866118050356473 4759860824149588537767355)
          ·
            refine ⟨7139791236224382806651033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4759860824149588537767355 7139791236224382806651033)
            ·
              refine ⟨5354843427168287104988275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7139791236224382806651033 5354843427168287104988275)
              ·
                refine ⟨8032265140752430657482413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5354843427168287104988275 8032265140752430657482413)
                ·
                  refine ⟨3012099427782161496555905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8032265140752430657482413 3012099427782161496555905)
                  ·
                    refine ⟨2259074570836621122416929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3012099427782161496555905 2259074570836621122416929)
                    ·
                      refine ⟨1694305928127465841812697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2259074570836621122416929 1694305928127465841812697)
                      ·
                        rfl

theorem cell23_3299649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 2, 1, 3, 2, 2].length) (baseStart_3299649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3299649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3299649 prefixEnd_3299649 := by exact prefixLift 3299649
  have htrace : WordTrace (prefixWord ++ tailWord_3299649) baseStart_3299649 baseEnd_3299649 := by
    simpa [prefixWord, tailWord_3299649, baseEnd_3299649] using wordTrace_append hprefix tailTrace_3299649
  have hstable : (prefixWord ++ tailWord_3299649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3299649).length < 2 ^ (prefixWord ++ tailWord_3299649).sum := by decide
  have hdescent : baseEnd_3299649 < baseStart_3299649 := by decide
  rcases family_descends (prefixWord ++ tailWord_3299649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3299665 : List Nat := [1, 2, 2, 1, 4, 4, 1, 1, 1, 3, 3]
def baseStart_3299665 : Nat := 118140960795 + 3299665 * 2 ^ 59
def prefixEnd_3299665 : Nat := 4983230072969 + 3 ^ 40 * 3299665 * 2
def baseEnd_3299665 : Nat := 1694314143817937779212623

theorem tailTrace_3299665 : CollatzResearch.WordTrace tailWord_3299665 prefixEnd_3299665 1694314143817937779212623 := by
  unfold tailWord_3299665
  simp only [CollatzResearch.WordTrace]
  refine ⟨120348669590884717761564449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80232446393923145174376299 120348669590884717761564449)
  ·
    refine ⟨90261502193163538321173337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120348669590884717761564449 90261502193163538321173337)
    ·
      refine ⟨67696126644872653740880003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90261502193163538321173337 67696126644872653740880003)
      ·
        refine ⟨101544189967308980611320005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67696126644872653740880003 101544189967308980611320005)
        ·
          refine ⟨19039535618870433864622501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101544189967308980611320005 19039535618870433864622501)
          ·
            refine ⟨3569912928538206349616719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19039535618870433864622501 3569912928538206349616719)
            ·
              refine ⟨5354869392807309524425079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3569912928538206349616719 5354869392807309524425079)
              ·
                refine ⟨8032304089210964286637619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5354869392807309524425079 8032304089210964286637619)
                ·
                  refine ⟨12048456133816446429956429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8032304089210964286637619 12048456133816446429956429)
                  ·
                    refine ⟨4518171050181167411233661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12048456133816446429956429 4518171050181167411233661)
                    ·
                      refine ⟨1694314143817937779212623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4518171050181167411233661 1694314143817937779212623)
                      ·
                        rfl

theorem cell23_3299665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 1, 1, 1, 3, 3].length) (baseStart_3299665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3299665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3299665 prefixEnd_3299665 := by exact prefixLift 3299665
  have htrace : WordTrace (prefixWord ++ tailWord_3299665) baseStart_3299665 baseEnd_3299665 := by
    simpa [prefixWord, tailWord_3299665, baseEnd_3299665] using wordTrace_append hprefix tailTrace_3299665
  have hstable : (prefixWord ++ tailWord_3299665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3299665).length < 2 ^ (prefixWord ++ tailWord_3299665).sum := by decide
  have hdescent : baseEnd_3299665 < baseStart_3299665 := by decide
  rcases family_descends (prefixWord ++ tailWord_3299665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3299691 : List Nat := [1, 1, 1, 1, 2, 2, 2, 5, 2, 1, 5]
def baseStart_3299691 : Nat := 118140960795 + 3299691 * 2 ^ 59
def prefixEnd_3299691 : Nat := 4983230072969 + 3 ^ 40 * 3299691 * 2
def baseEnd_3299691 : Nat := 1694327494314954677487503

theorem tailTrace_3299691 : CollatzResearch.WordTrace tailWord_3299691 prefixEnd_3299691 1694327494314954677487503 := by
  unfold tailWord_3299691
  simp only [CollatzResearch.WordTrace]
  refine ⟨120349617888790524202010927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80233078592527016134673951 120349617888790524202010927)
  ·
    refine ⟨180524426833185786303016391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120349617888790524202010927 180524426833185786303016391)
    ·
      refine ⟨270786640249778679454524587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180524426833185786303016391 270786640249778679454524587)
      ·
        refine ⟨406179960374668019181786881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270786640249778679454524587 406179960374668019181786881)
        ·
          refine ⟨304634970281001014386340161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 406179960374668019181786881 304634970281001014386340161)
          ·
            refine ⟨228476227710750760789755121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 304634970281001014386340161 228476227710750760789755121)
            ·
              refine ⟨171357170783063070592316341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 228476227710750760789755121 171357170783063070592316341)
              ·
                refine ⟨16064734760912162868029657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 171357170783063070592316341 16064734760912162868029657)
                ·
                  refine ⟨12048551070684122151022243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16064734760912162868029657 12048551070684122151022243)
                  ·
                    refine ⟨18072826606026183226533365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12048551070684122151022243 18072826606026183226533365)
                    ·
                      refine ⟨1694327494314954677487503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18072826606026183226533365 1694327494314954677487503)
                      ·
                        rfl

theorem cell23_3299691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 5, 2, 1, 5].length) (baseStart_3299691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3299691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3299691 prefixEnd_3299691 := by exact prefixLift 3299691
  have htrace : WordTrace (prefixWord ++ tailWord_3299691) baseStart_3299691 baseEnd_3299691 := by
    simpa [prefixWord, tailWord_3299691, baseEnd_3299691] using wordTrace_append hprefix tailTrace_3299691
  have hstable : (prefixWord ++ tailWord_3299691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3299691).length < 2 ^ (prefixWord ++ tailWord_3299691).sum := by decide
  have hdescent : baseEnd_3299691 < baseStart_3299691 := by decide
  rcases family_descends (prefixWord ++ tailWord_3299691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3299805 : List Nat := [1, 4, 3, 1, 1, 1, 1, 2, 5, 4]
def baseStart_3299805 : Nat := 118140960795 + 3299805 * 2 ^ 59
def prefixEnd_3299805 : Nat := 4983230072969 + 3 ^ 40 * 3299805 * 2
def baseEnd_3299805 : Nat := 564795343703189077153993

theorem tailTrace_3299805 : CollatzResearch.WordTrace tailWord_3299805 prefixEnd_3299805 564795343703189077153993 := by
  unfold tailWord_3299805
  simp only [CollatzResearch.WordTrace]
  refine ⟨120353775810377521671660869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80235850540251681114440579 120353775810377521671660869)
  ·
    refine ⟨22566332964445785313436413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120353775810377521671660869 22566332964445785313436413)
    ·
      refine ⟨8462374861667169492538655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22566332964445785313436413 8462374861667169492538655)
      ·
        refine ⟨12693562292500754238807983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8462374861667169492538655 12693562292500754238807983)
        ·
          refine ⟨19040343438751131358211975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12693562292500754238807983 19040343438751131358211975)
          ·
            refine ⟨28560515158126697037317963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19040343438751131358211975 28560515158126697037317963)
            ·
              refine ⟨42840772737190045555976945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28560515158126697037317963 42840772737190045555976945)
              ·
                refine ⟨32130579552892534166982709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42840772737190045555976945 32130579552892534166982709)
                ·
                  refine ⟨3012241833083675078154629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32130579552892534166982709 3012241833083675078154629)
                  ·
                    refine ⟨564795343703189077153993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3012241833083675078154629 564795343703189077153993)
                    ·
                      rfl

theorem cell23_3299805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 2, 5, 4].length) (baseStart_3299805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3299805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3299805 prefixEnd_3299805 := by exact prefixLift 3299805
  have htrace : WordTrace (prefixWord ++ tailWord_3299805) baseStart_3299805 baseEnd_3299805 := by
    simpa [prefixWord, tailWord_3299805, baseEnd_3299805] using wordTrace_append hprefix tailTrace_3299805
  have hstable : (prefixWord ++ tailWord_3299805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3299805).length < 2 ^ (prefixWord ++ tailWord_3299805).sum := by decide
  have hdescent : baseEnd_3299805 < baseStart_3299805 := by decide
  rcases family_descends (prefixWord ++ tailWord_3299805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3299815 : List Nat := [1, 1, 5, 2, 1, 1, 2, 1, 4, 2, 3]
def baseStart_3299815 : Nat := 118140960795 + 3299815 * 2 ^ 59
def prefixEnd_3299815 : Nat := 4983230072969 + 3 ^ 40 * 3299815 * 2
def baseEnd_3299815 : Nat := 1694391165916112192336933

theorem tailTrace_3299815 : CollatzResearch.WordTrace tailWord_3299815 prefixEnd_3299815 1694391165916112192336933 := by
  unfold tailWord_3299815
  simp only [CollatzResearch.WordTrace]
  refine ⟨120354140540341293379524899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80236093693560862253016599 120354140540341293379524899)
  ·
    refine ⟨180531210810511940069287349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120354140540341293379524899 180531210810511940069287349)
    ·
      refine ⟨16924801013485494381495689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 180531210810511940069287349 16924801013485494381495689)
      ·
        refine ⟨12693600760114120786121767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16924801013485494381495689 12693600760114120786121767)
        ·
          refine ⟨19040401140171181179182651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12693600760114120786121767 19040401140171181179182651)
          ·
            refine ⟨28560601710256771768773977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19040401140171181179182651 28560601710256771768773977)
            ·
              refine ⟨21420451282692578826580483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28560601710256771768773977 21420451282692578826580483)
              ·
                refine ⟨32130676924038868239870725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21420451282692578826580483 32130676924038868239870725)
                ·
                  refine ⟨6024501923257287794975761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32130676924038868239870725 6024501923257287794975761)
                  ·
                    refine ⟨4518376442442965846231821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6024501923257287794975761 4518376442442965846231821)
                    ·
                      refine ⟨1694391165916112192336933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4518376442442965846231821 1694391165916112192336933)
                      ·
                        rfl

theorem cell23_3299815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 1, 4, 2, 3].length) (baseStart_3299815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3299815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3299815 prefixEnd_3299815 := by exact prefixLift 3299815
  have htrace : WordTrace (prefixWord ++ tailWord_3299815) baseStart_3299815 baseEnd_3299815 := by
    simpa [prefixWord, tailWord_3299815, baseEnd_3299815] using wordTrace_append hprefix tailTrace_3299815
  have hstable : (prefixWord ++ tailWord_3299815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3299815).length < 2 ^ (prefixWord ++ tailWord_3299815).sum := by decide
  have hdescent : baseEnd_3299815 < baseStart_3299815 := by decide
  rcases family_descends (prefixWord ++ tailWord_3299815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3299822 : List Nat := [4, 1, 2, 1, 2, 3, 2, 1, 3, 4]
def baseStart_3299822 : Nat := 118140960795 + 3299822 * 2 ^ 59
def prefixEnd_3299822 : Nat := 4983230072969 + 3 ^ 40 * 3299822 * 2
def baseEnd_3299822 : Nat := 564798253426897888316467

theorem tailTrace_3299822 : CollatzResearch.WordTrace tailWord_3299822 prefixEnd_3299822 564798253426897888316467 := by
  unfold tailWord_3299822
  simp only [CollatzResearch.WordTrace]
  refine ⟨15044299481414491696878715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80236263900877289050019813 15044299481414491696878715)
  ·
    refine ⟨22566449222121737545318073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15044299481414491696878715 22566449222121737545318073)
    ·
      refine ⟨16924836916591303158988555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22566449222121737545318073 16924836916591303158988555)
      ·
        refine ⟨25387255374886954738482833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16924836916591303158988555 25387255374886954738482833)
        ·
          refine ⟨19040441531165216053862125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25387255374886954738482833 19040441531165216053862125)
          ·
            refine ⟨7140165574186956020198297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19040441531165216053862125 7140165574186956020198297)
            ·
              refine ⟨5355124180640217015148723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7140165574186956020198297 5355124180640217015148723)
              ·
                refine ⟨8032686270960325522723085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5355124180640217015148723 8032686270960325522723085)
                ·
                  refine ⟨3012257351610122071021157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8032686270960325522723085 3012257351610122071021157)
                  ·
                    refine ⟨564798253426897888316467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3012257351610122071021157 564798253426897888316467)
                    ·
                      rfl

theorem cell23_3299822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2, 1, 3, 4].length) (baseStart_3299822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3299822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3299822 prefixEnd_3299822 := by exact prefixLift 3299822
  have htrace : WordTrace (prefixWord ++ tailWord_3299822) baseStart_3299822 baseEnd_3299822 := by
    simpa [prefixWord, tailWord_3299822, baseEnd_3299822] using wordTrace_append hprefix tailTrace_3299822
  have hstable : (prefixWord ++ tailWord_3299822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3299822).length < 2 ^ (prefixWord ++ tailWord_3299822).sum := by decide
  have hdescent : baseEnd_3299822 < baseStart_3299822 := by decide
  rcases family_descends (prefixWord ++ tailWord_3299822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3299886 : List Nat := [4, 1, 3, 1, 4, 1, 2, 1, 6]
def baseStart_3299886 : Nat := 118140960795 + 3299886 * 2 ^ 59
def prefixEnd_3299886 : Nat := 4983230072969 + 3 ^ 40 * 3299886 * 2
def baseEnd_3299886 : Nat := 188269735893620157172123

theorem tailTrace_3299886 : CollatzResearch.WordTrace tailWord_3299886 prefixEnd_3299886 188269735893620157172123 := by
  unfold tailWord_3299886
  simp only [CollatzResearch.WordTrace]
  refine ⟨15044591265385509063169939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80237820082056048336906341 15044591265385509063169939)
  ·
    refine ⟨22566886898078263594754909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15044591265385509063169939 22566886898078263594754909)
    ·
      refine ⟨8462582586779348848033091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22566886898078263594754909 8462582586779348848033091)
      ·
        refine ⟨12693873880169023272049637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8462582586779348848033091 12693873880169023272049637)
        ·
          refine ⟨2380101352531691863509307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12693873880169023272049637 2380101352531691863509307)
          ·
            refine ⟨3570152028797537795263961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2380101352531691863509307 3570152028797537795263961)
            ·
              refine ⟨2677614021598153346447971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3570152028797537795263961 2677614021598153346447971)
              ·
                refine ⟨4016421032397230019671957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2677614021598153346447971 4016421032397230019671957)
                ·
                  refine ⟨188269735893620157172123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4016421032397230019671957 188269735893620157172123)
                  ·
                    rfl

theorem cell23_3299886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 2, 1, 6].length) (baseStart_3299886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3299886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3299886 prefixEnd_3299886 := by exact prefixLift 3299886
  have htrace : WordTrace (prefixWord ++ tailWord_3299886) baseStart_3299886 baseEnd_3299886 := by
    simpa [prefixWord, tailWord_3299886, baseEnd_3299886] using wordTrace_append hprefix tailTrace_3299886
  have hstable : (prefixWord ++ tailWord_3299886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3299886).length < 2 ^ (prefixWord ++ tailWord_3299886).sum := by decide
  have hdescent : baseEnd_3299886 < baseStart_3299886 := by decide
  rcases family_descends (prefixWord ++ tailWord_3299886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3299986 : List Nat := [3, 2, 3, 1, 2, 1, 3, 2, 2, 1, 3]
def baseStart_3299986 : Nat := 118140960795 + 3299986 * 2 ^ 59
def prefixEnd_3299986 : Nat := 4983230072969 + 3 ^ 40 * 3299986 * 2
def baseEnd_3299986 : Nat := 1694478971108031023298647

theorem tailTrace_3299986 : CollatzResearch.WordTrace tailWord_3299986 prefixEnd_3299986 1694478971108031023298647 := by
  unfold tailWord_3299986
  simp only [CollatzResearch.WordTrace]
  refine ⟨30090094355680447395999953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80240251615147859722666541 30090094355680447395999953)
  ·
    refine ⟨22567570766760335546999965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30090094355680447395999953 22567570766760335546999965)
    ·
      refine ⟨8462839037535125830124987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22567570766760335546999965 8462839037535125830124987)
      ·
        refine ⟨12694258556302688745187481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8462839037535125830124987 12694258556302688745187481)
        ·
          refine ⟨9520693917227016558890611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12694258556302688745187481 9520693917227016558890611)
          ·
            refine ⟨14281040875840524838335917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9520693917227016558890611 14281040875840524838335917)
            ·
              refine ⟨5355390328440196814375969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14281040875840524838335917 5355390328440196814375969)
              ·
                refine ⟨4016542746330147610781977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5355390328440196814375969 4016542746330147610781977)
                ·
                  refine ⟨3012407059747610708086483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4016542746330147610781977 3012407059747610708086483)
                  ·
                    refine ⟨4518610589621416062129725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3012407059747610708086483 4518610589621416062129725)
                    ·
                      refine ⟨1694478971108031023298647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4518610589621416062129725 1694478971108031023298647)
                      ·
                        rfl

theorem cell23_3299986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3, 2, 2, 1, 3].length) (baseStart_3299986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3299986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3299986 prefixEnd_3299986 := by exact prefixLift 3299986
  have htrace : WordTrace (prefixWord ++ tailWord_3299986) baseStart_3299986 baseEnd_3299986 := by
    simpa [prefixWord, tailWord_3299986, baseEnd_3299986] using wordTrace_append hprefix tailTrace_3299986
  have hstable : (prefixWord ++ tailWord_3299986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3299986).length < 2 ^ (prefixWord ++ tailWord_3299986).sum := by decide
  have hdescent : baseEnd_3299986 < baseStart_3299986 := by decide
  rcases family_descends (prefixWord ++ tailWord_3299986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3300015 : List Nat := [1, 1, 2, 1, 2, 5, 2, 2, 7]
def baseStart_3300015 : Nat := 118140960795 + 3300015 * 2 ^ 59
def prefixEnd_3300015 : Nat := 4983230072969 + 3 ^ 40 * 3300015 * 2
def baseEnd_3300015 : Nat := 188277095783001267759557

theorem tailTrace_3300015 : CollatzResearch.WordTrace tailWord_3300015 prefixEnd_3300015 188277095783001267759557 := by
  unfold tailWord_3300015
  simp only [CollatzResearch.WordTrace]
  refine ⟨120361435139616727536805499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80240956759744485024536999 120361435139616727536805499)
  ·
    refine ⟨180542152709425091305208249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120361435139616727536805499 180542152709425091305208249)
    ·
      refine ⟨135406614532068818478906187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180542152709425091305208249 135406614532068818478906187)
      ·
        refine ⟨203109921798103227718359281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135406614532068818478906187 203109921798103227718359281)
        ·
          refine ⟨152332441348577420788769461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203109921798103227718359281 152332441348577420788769461)
          ·
            refine ⟨14281166376429133198947137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 152332441348577420788769461 14281166376429133198947137)
            ·
              refine ⟨10710874782321849899210353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14281166376429133198947137 10710874782321849899210353)
              ·
                refine ⟨8033156086741387424407765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10710874782321849899210353 8033156086741387424407765)
                ·
                  refine ⟨188277095783001267759557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8033156086741387424407765 188277095783001267759557)
                  ·
                    rfl

theorem cell23_3300015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 2, 7].length) (baseStart_3300015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3300015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3300015 prefixEnd_3300015 := by exact prefixLift 3300015
  have htrace : WordTrace (prefixWord ++ tailWord_3300015) baseStart_3300015 baseEnd_3300015 := by
    simpa [prefixWord, tailWord_3300015, baseEnd_3300015] using wordTrace_append hprefix tailTrace_3300015
  have hstable : (prefixWord ++ tailWord_3300015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3300015).length < 2 ^ (prefixWord ++ tailWord_3300015).sum := by decide
  have hdescent : baseEnd_3300015 < baseStart_3300015 := by decide
  rcases family_descends (prefixWord ++ tailWord_3300015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3300049 : List Nat := [1, 2, 2, 1, 2, 3, 5, 2, 5]
def baseStart_3300049 : Nat := 118140960795 + 3300049 * 2 ^ 59
def prefixEnd_3300049 : Nat := 4983230072969 + 3 ^ 40 * 3300049 * 2
def baseEnd_3300049 : Nat := 188279035598807141867873

theorem tailTrace_3300049 : CollatzResearch.WordTrace tailWord_3300049 prefixEnd_3300049 188279035598807141867873 := by
  unfold tailWord_3300049
  simp only [CollatzResearch.WordTrace]
  refine ⟨120362675221493551343543201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80241783480995700895695467 120362675221493551343543201)
  ·
    refine ⟨90272006416120163507657401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120362675221493551343543201 90272006416120163507657401)
    ·
      refine ⟨67704004812090122630743051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90272006416120163507657401 67704004812090122630743051)
      ·
        refine ⟨101556007218135183946114577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67704004812090122630743051 101556007218135183946114577)
        ·
          refine ⟨76167005413601387959585933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101556007218135183946114577 76167005413601387959585933)
          ·
            refine ⟨28562627030100520484844725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76167005413601387959585933 28562627030100520484844725)
            ·
              refine ⟨2677746284071923795454193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28562627030100520484844725 2677746284071923795454193)
              ·
                refine ⟨2008309713053942846590645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2677746284071923795454193 2008309713053942846590645)
                ·
                  refine ⟨188279035598807141867873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2008309713053942846590645 188279035598807141867873)
                  ·
                    rfl

theorem cell23_3300049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 5, 2, 5].length) (baseStart_3300049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3300049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3300049 prefixEnd_3300049 := by exact prefixLift 3300049
  have htrace : WordTrace (prefixWord ++ tailWord_3300049) baseStart_3300049 baseEnd_3300049 := by
    simpa [prefixWord, tailWord_3300049, baseEnd_3300049] using wordTrace_append hprefix tailTrace_3300049
  have hstable : (prefixWord ++ tailWord_3300049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3300049).length < 2 ^ (prefixWord ++ tailWord_3300049).sum := by decide
  have hdescent : baseEnd_3300049 < baseStart_3300049 := by decide
  rcases family_descends (prefixWord ++ tailWord_3300049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3300055 : List Nat := [1, 1, 3, 2, 1, 4, 1, 1, 1, 1, 7]
def baseStart_3300055 : Nat := 118140960795 + 3300055 * 2 ^ 59
def prefixEnd_3300055 : Nat := 4983230072969 + 3 ^ 40 * 3300055 * 2
def baseEnd_3300055 : Nat := 1694514401273191253335829

theorem tailTrace_3300055 : CollatzResearch.WordTrace tailWord_3300055 prefixEnd_3300055 1694514401273191253335829 := by
  unfold tailWord_3300055
  simp only [CollatzResearch.WordTrace]
  refine ⟨120362894059471814368261619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80241929372981209578841079 120362894059471814368261619)
  ·
    refine ⟨180544341089207721552392429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120362894059471814368261619 180544341089207721552392429)
    ·
      refine ⟨67704127908452895582147161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180544341089207721552392429 67704127908452895582147161)
      ·
        refine ⟨50778095931339671686610371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67704127908452895582147161 50778095931339671686610371)
        ·
          refine ⟨76167143897009507529915557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50778095931339671686610371 76167143897009507529915557)
          ·
            refine ⟨14281339480689282661859167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76167143897009507529915557 14281339480689282661859167)
            ·
              refine ⟨21422009221033923992788751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14281339480689282661859167 21422009221033923992788751)
              ·
                refine ⟨32133013831550885989183127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21422009221033923992788751 32133013831550885989183127)
                ·
                  refine ⟨48199520747326328983774691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32133013831550885989183127 48199520747326328983774691)
                  ·
                    refine ⟨72299281120989493475662037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48199520747326328983774691 72299281120989493475662037)
                    ·
                      refine ⟨1694514401273191253335829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 72299281120989493475662037 1694514401273191253335829)
                      ·
                        rfl

theorem cell23_3300055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 1, 1, 1, 7].length) (baseStart_3300055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3300055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3300055 prefixEnd_3300055 := by exact prefixLift 3300055
  have htrace : WordTrace (prefixWord ++ tailWord_3300055) baseStart_3300055 baseEnd_3300055 := by
    simpa [prefixWord, tailWord_3300055, baseEnd_3300055] using wordTrace_append hprefix tailTrace_3300055
  have hstable : (prefixWord ++ tailWord_3300055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3300055).length < 2 ^ (prefixWord ++ tailWord_3300055).sum := by decide
  have hdescent : baseEnd_3300055 < baseStart_3300055 := by decide
  rcases family_descends (prefixWord ++ tailWord_3300055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3300060 : List Nat := [2, 2, 5, 1, 1, 1, 4, 1, 2, 2, 2]
def baseStart_3300060 : Nat := 118140960795 + 3300060 * 2 ^ 59
def prefixEnd_3300060 : Nat := 4983230072969 + 3 ^ 40 * 3300060 * 2
def baseEnd_3300060 : Nat := 1694516968676463733773307

theorem tailTrace_3300060 : CollatzResearch.WordTrace tailWord_3300060 prefixEnd_3300060 1694516968676463733773307 := by
  unfold tailWord_3300060
  simp only [CollatzResearch.WordTrace]
  refine ⟨60181538212226850111096817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80242050949635800148129089 60181538212226850111096817)
  ·
    refine ⟨45136153659170137583322613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60181538212226850111096817 45136153659170137583322613)
    ·
      refine ⟨4231514405547200398436495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 45136153659170137583322613 4231514405547200398436495)
      ·
        refine ⟨6347271608320800597654743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4231514405547200398436495 6347271608320800597654743)
        ·
          refine ⟨9520907412481200896482115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6347271608320800597654743 9520907412481200896482115)
          ·
            refine ⟨14281361118721801344723173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9520907412481200896482115 14281361118721801344723173)
            ·
              refine ⟨2677755209760337752135595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14281361118721801344723173 2677755209760337752135595)
              ·
                refine ⟨4016632814640506628203393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2677755209760337752135595 4016632814640506628203393)
                ·
                  refine ⟨3012474610980379971152545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4016632814640506628203393 3012474610980379971152545)
                  ·
                    refine ⟨2259355958235284978364409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3012474610980379971152545 2259355958235284978364409)
                    ·
                      refine ⟨1694516968676463733773307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2259355958235284978364409 1694516968676463733773307)
                      ·
                        rfl

theorem cell23_3300060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 4, 1, 2, 2, 2].length) (baseStart_3300060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3300060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3300060 prefixEnd_3300060 := by exact prefixLift 3300060
  have htrace : WordTrace (prefixWord ++ tailWord_3300060) baseStart_3300060 baseEnd_3300060 := by
    simpa [prefixWord, tailWord_3300060, baseEnd_3300060] using wordTrace_append hprefix tailTrace_3300060
  have hstable : (prefixWord ++ tailWord_3300060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3300060).length < 2 ^ (prefixWord ++ tailWord_3300060).sum := by decide
  have hdescent : baseEnd_3300060 < baseStart_3300060 := by decide
  rcases family_descends (prefixWord ++ tailWord_3300060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3300095 : List Nat := [1, 1, 2, 2, 1, 3, 1, 3, 2, 1, 6]
def baseStart_3300095 : Nat := 118140960795 + 3300095 * 2 ^ 59
def prefixEnd_3300095 : Nat := 4983230072969 + 3 ^ 40 * 3300095 * 2
def baseEnd_3300095 : Nat := 1694534940499371096835645

theorem tailTrace_3300095 : CollatzResearch.WordTrace tailWord_3300095 prefixEnd_3300095 1694534940499371096835645 := by
  unfold tailWord_3300095
  simp only [CollatzResearch.WordTrace]
  refine ⟨120364352979326901199717739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80242901986217934133145159 120364352979326901199717739)
  ·
    refine ⟨180546529468990351799576609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120364352979326901199717739 180546529468990351799576609)
    ·
      refine ⟨135409897101742763849682457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180546529468990351799576609 135409897101742763849682457)
      ·
        refine ⟨101557422826307072887261843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135409897101742763849682457 101557422826307072887261843)
        ·
          refine ⟨152336134239460609330892765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101557422826307072887261843 152336134239460609330892765)
          ·
            refine ⟨57126050339797728499084787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 152336134239460609330892765 57126050339797728499084787)
            ·
              refine ⟨85689075509696592748627181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57126050339797728499084787 85689075509696592748627181)
              ·
                refine ⟨32133403316136222280735193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85689075509696592748627181 32133403316136222280735193)
                ·
                  refine ⟨24100052487102166710551395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32133403316136222280735193 24100052487102166710551395)
                  ·
                    refine ⟨36150078730653250065827093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24100052487102166710551395 36150078730653250065827093)
                    ·
                      refine ⟨1694534940499371096835645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36150078730653250065827093 1694534940499371096835645)
                      ·
                        rfl

theorem cell23_3300095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 3, 2, 1, 6].length) (baseStart_3300095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3300095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3300095 prefixEnd_3300095 := by exact prefixLift 3300095
  have htrace : WordTrace (prefixWord ++ tailWord_3300095) baseStart_3300095 baseEnd_3300095 := by
    simpa [prefixWord, tailWord_3300095, baseEnd_3300095] using wordTrace_append hprefix tailTrace_3300095
  have hstable : (prefixWord ++ tailWord_3300095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3300095).length < 2 ^ (prefixWord ++ tailWord_3300095).sum := by decide
  have hdescent : baseEnd_3300095 < baseStart_3300095 := by decide
  rcases family_descends (prefixWord ++ tailWord_3300095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3300105 : List Nat := [1, 2, 1, 1, 3, 2, 2, 3, 8]
def baseStart_3300105 : Nat := 118140960795 + 3300105 * 2 ^ 59
def prefixEnd_3300105 : Nat := 4983230072969 + 3 ^ 40 * 3300105 * 2
def baseEnd_3300105 : Nat := 188282230589546228634511

theorem tailTrace_3300105 : CollatzResearch.WordTrace tailWord_3300105 prefixEnd_3300105 188282230589546228634511 := by
  unfold tailWord_3300105
  simp only [CollatzResearch.WordTrace]
  refine ⟨120364717709290672907581769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80243145139527115271721179 120364717709290672907581769)
  ·
    refine ⟨90273538281968004680686327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120364717709290672907581769 90273538281968004680686327)
    ·
      refine ⟨135410307422952007021029491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90273538281968004680686327 135410307422952007021029491)
      ·
        refine ⟨203115461134428010531544237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135410307422952007021029491 203115461134428010531544237)
        ·
          refine ⟨76168297925410503949329089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 203115461134428010531544237 76168297925410503949329089)
          ·
            refine ⟨57126223444057877961996817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76168297925410503949329089 57126223444057877961996817)
            ·
              refine ⟨42844667583043408471497613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57126223444057877961996817 42844667583043408471497613)
              ·
                refine ⟨16066750343641278176811605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42844667583043408471497613 16066750343641278176811605)
                ·
                  refine ⟨188282230589546228634511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16066750343641278176811605 188282230589546228634511)
                  ·
                    rfl

theorem cell23_3300105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 3, 8].length) (baseStart_3300105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3300105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3300105 prefixEnd_3300105 := by exact prefixLift 3300105
  have htrace : WordTrace (prefixWord ++ tailWord_3300105) baseStart_3300105 baseEnd_3300105 := by
    simpa [prefixWord, tailWord_3300105, baseEnd_3300105] using wordTrace_append hprefix tailTrace_3300105
  have hstable : (prefixWord ++ tailWord_3300105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3300105).length < 2 ^ (prefixWord ++ tailWord_3300105).sum := by decide
  have hdescent : baseEnd_3300105 < baseStart_3300105 := by decide
  rcases family_descends (prefixWord ++ tailWord_3300105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3300122 : List Nat := [3, 1, 1, 3, 2, 1, 1, 5, 6]
def baseStart_3300122 : Nat := 118140960795 + 3300122 * 2 ^ 59
def prefixEnd_3300122 : Nat := 4983230072969 + 3 ^ 40 * 3300122 * 2
def baseEnd_3300122 : Nat := 188283200497449165688669

theorem tailTrace_3300122 : CollatzResearch.WordTrace tailWord_3300122 prefixEnd_3300122 188283200497449165688669 := by
  unfold tailWord_3300122
  simp only [CollatzResearch.WordTrace]
  refine ⟨30091334437557271202737655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80243558500152723207300413 30091334437557271202737655)
  ·
    refine ⟨45137001656335906804106483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30091334437557271202737655 45137001656335906804106483)
    ·
      refine ⟨67705502484503860206159725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45137001656335906804106483 67705502484503860206159725)
      ·
        refine ⟨25389563431688947577309897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67705502484503860206159725 25389563431688947577309897)
        ·
          refine ⟨19042172573766710682982423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25389563431688947577309897 19042172573766710682982423)
          ·
            refine ⟨28563258860650066024473635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19042172573766710682982423 28563258860650066024473635)
            ·
              refine ⟨42844888290975099036710453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28563258860650066024473635 42844888290975099036710453)
              ·
                refine ⟨4016708277278915534691605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42844888290975099036710453 4016708277278915534691605)
                ·
                  refine ⟨188283200497449165688669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4016708277278915534691605 188283200497449165688669)
                  ·
                    rfl

theorem cell23_3300122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 5, 6].length) (baseStart_3300122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3300122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3300122 prefixEnd_3300122 := by exact prefixLift 3300122
  have htrace : WordTrace (prefixWord ++ tailWord_3300122) baseStart_3300122 baseEnd_3300122 := by
    simpa [prefixWord, tailWord_3300122, baseEnd_3300122] using wordTrace_append hprefix tailTrace_3300122
  have hstable : (prefixWord ++ tailWord_3300122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3300122).length < 2 ^ (prefixWord ++ tailWord_3300122).sum := by decide
  have hdescent : baseEnd_3300122 < baseStart_3300122 := by decide
  rcases family_descends (prefixWord ++ tailWord_3300122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3300173 : List Nat := [1, 6, 1, 2, 2, 1, 3, 1, 6]
def baseStart_3300173 : Nat := 118140960795 + 3300173 * 2 ^ 59
def prefixEnd_3300173 : Nat := 4983230072969 + 3 ^ 40 * 3300173 * 2
def baseEnd_3300173 : Nat := 188286110221157976851143

theorem tailTrace_3300173 : CollatzResearch.WordTrace tailWord_3300173 prefixEnd_3300173 188286110221157976851143 := by
  unfold tailWord_3300173
  simp only [CollatzResearch.WordTrace]
  refine ⟨120367197873044320521057173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80244798582029547014038115 120367197873044320521057173)
  ·
    refine ⟨5642212400298952524424555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 120367197873044320521057173 5642212400298952524424555)
    ·
      refine ⟨8463318600448428786636833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5642212400298952524424555 8463318600448428786636833)
      ·
        refine ⟨6347488950336321589977625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8463318600448428786636833 6347488950336321589977625)
        ·
          refine ⟨4760616712752241192483219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6347488950336321589977625 4760616712752241192483219)
          ·
            refine ⟨7140925069128361788724829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4760616712752241192483219 7140925069128361788724829)
            ·
              refine ⟨2677846900923135670771811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7140925069128361788724829 2677846900923135670771811)
              ·
                refine ⟨4016770351384703506157717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2677846900923135670771811 4016770351384703506157717)
                ·
                  refine ⟨188286110221157976851143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4016770351384703506157717 188286110221157976851143)
                  ·
                    rfl

theorem cell23_3300173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 3, 1, 6].length) (baseStart_3300173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3300173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3300173 prefixEnd_3300173 := by exact prefixLift 3300173
  have htrace : WordTrace (prefixWord ++ tailWord_3300173) baseStart_3300173 baseEnd_3300173 := by
    simpa [prefixWord, tailWord_3300173, baseEnd_3300173] using wordTrace_append hprefix tailTrace_3300173
  have hstable : (prefixWord ++ tailWord_3300173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3300173).length < 2 ^ (prefixWord ++ tailWord_3300173).sum := by decide
  have hdescent : baseEnd_3300173 < baseStart_3300173 := by decide
  rcases family_descends (prefixWord ++ tailWord_3300173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3300192 : List Nat := [2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 5]
def baseStart_3300192 : Nat := 118140960795 + 3300192 * 2 ^ 59
def prefixEnd_3300192 : Nat := 4983230072969 + 3 ^ 40 * 3300192 * 2
def baseEnd_3300192 : Nat := 1694584748122857217322699

theorem tailTrace_3300192 : CollatzResearch.WordTrace tailWord_3300192 prefixEnd_3300192 1694584748122857217322699 := by
  unfold tailWord_3300192
  simp only [CollatzResearch.WordTrace]
  refine ⟨60183945429987743382999415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80245260573316991177332553 60183945429987743382999415)
  ·
    refine ⟨90275918144981615074499123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60183945429987743382999415 90275918144981615074499123)
    ·
      refine ⟨135413877217472422611748685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90275918144981615074499123 135413877217472422611748685)
      ·
        refine ⟨50780203956552158479405757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135413877217472422611748685 50780203956552158479405757)
        ·
          refine ⟨19042576483707059429777159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50780203956552158479405757 19042576483707059429777159)
          ·
            refine ⟨28563864725560589144665739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19042576483707059429777159 28563864725560589144665739)
            ·
              refine ⟨42845797088340883716998609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28563864725560589144665739 42845797088340883716998609)
              ·
                refine ⟨32134347816255662787748957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42845797088340883716998609 32134347816255662787748957)
                ·
                  refine ⟨12050380431095873545405859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32134347816255662787748957 12050380431095873545405859)
                  ·
                    refine ⟨18075570646643810318108789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12050380431095873545405859 18075570646643810318108789)
                    ·
                      refine ⟨1694584748122857217322699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18075570646643810318108789 1694584748122857217322699)
                      ·
                        rfl

theorem cell23_3300192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 5].length) (baseStart_3300192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3300192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3300192 prefixEnd_3300192 := by exact prefixLift 3300192
  have htrace : WordTrace (prefixWord ++ tailWord_3300192) baseStart_3300192 baseEnd_3300192 := by
    simpa [prefixWord, tailWord_3300192, baseEnd_3300192] using wordTrace_append hprefix tailTrace_3300192
  have hstable : (prefixWord ++ tailWord_3300192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3300192).length < 2 ^ (prefixWord ++ tailWord_3300192).sum := by decide
  have hdescent : baseEnd_3300192 < baseStart_3300192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3300192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3300199 : List Nat := [1, 1, 5, 1, 2, 2, 1, 2, 4, 4]
def baseStart_3300199 : Nat := 118140960795 + 3300199 * 2 ^ 59
def prefixEnd_3300199 : Nat := 4983230072969 + 3 ^ 40 * 3300199 * 2
def baseEnd_3300199 : Nat := 564862780829146229978389

theorem tailTrace_3300199 : CollatzResearch.WordTrace tailWord_3300199 prefixEnd_3300199 564862780829146229978389 := by
  unfold tailWord_3300199
  simp only [CollatzResearch.WordTrace]
  refine ⟨120368146170950126961503651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80245430780633417974335767 120368146170950126961503651)
  ·
    refine ⟨180552219256425190442255477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120368146170950126961503651 180552219256425190442255477)
    ·
      refine ⟨16926770555289861603961451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 180552219256425190442255477 16926770555289861603961451)
      ·
        refine ⟨25390155832934792405942177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16926770555289861603961451 25390155832934792405942177)
        ·
          refine ⟨19042616874701094304456633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25390155832934792405942177 19042616874701094304456633)
          ·
            refine ⟨14281962656025820728342475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19042616874701094304456633 14281962656025820728342475)
            ·
              refine ⟨21422943984038731092513713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14281962656025820728342475 21422943984038731092513713)
              ·
                refine ⟨16067207988029048319385285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21422943984038731092513713 16067207988029048319385285)
                ·
                  refine ⟨3012601497755446559884741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16067207988029048319385285 3012601497755446559884741)
                  ·
                    refine ⟨564862780829146229978389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3012601497755446559884741 564862780829146229978389)
                    ·
                      rfl

theorem cell23_3300199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 2, 4, 4].length) (baseStart_3300199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3300199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3300199 prefixEnd_3300199 := by exact prefixLift 3300199
  have htrace : WordTrace (prefixWord ++ tailWord_3300199) baseStart_3300199 baseEnd_3300199 := by
    simpa [prefixWord, tailWord_3300199, baseEnd_3300199] using wordTrace_append hprefix tailTrace_3300199
  have hstable : (prefixWord ++ tailWord_3300199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3300199).length < 2 ^ (prefixWord ++ tailWord_3300199).sum := by decide
  have hdescent : baseEnd_3300199 < baseStart_3300199 := by decide
  rcases family_descends (prefixWord ++ tailWord_3300199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3300200 : List Nat := [2, 1, 4, 2, 1, 4, 1, 3, 1, 1, 3]
def baseStart_3300200 : Nat := 118140960795 + 3300200 * 2 ^ 59
def prefixEnd_3300200 : Nat := 4983230072969 + 3 ^ 40 * 3300200 * 2
def baseEnd_3300200 : Nat := 1694588855968093186022663

theorem tailTrace_3300200 : CollatzResearch.WordTrace tailWord_3300200 prefixEnd_3300200 1694588855968093186022663 := by
  unfold tailWord_3300200
  simp only [CollatzResearch.WordTrace]
  refine ⟨60184091321973252066145027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80245455095964336088193369 60184091321973252066145027)
  ·
    refine ⟨90276136982959878099217541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60184091321973252066145027 90276136982959878099217541)
    ·
      refine ⟨16926775684304977143603289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90276136982959878099217541 16926775684304977143603289)
      ·
        refine ⟨12695081763228732857702467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16926775684304977143603289 12695081763228732857702467)
        ·
          refine ⟨19042622644843099286553701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12695081763228732857702467 19042622644843099286553701)
          ·
            refine ⟨3570491745908081116228819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19042622644843099286553701 3570491745908081116228819)
            ·
              refine ⟨5355737618862121674343229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3570491745908081116228819 5355737618862121674343229)
              ·
                refine ⟨2008401607073295627878711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5355737618862121674343229 2008401607073295627878711)
                ·
                  refine ⟨3012602410609943441818067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2008401607073295627878711 3012602410609943441818067)
                  ·
                    refine ⟨4518903615914915162727101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3012602410609943441818067 4518903615914915162727101)
                    ·
                      refine ⟨1694588855968093186022663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4518903615914915162727101 1694588855968093186022663)
                      ·
                        rfl

theorem cell23_3300200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 1, 3, 1, 1, 3].length) (baseStart_3300200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3300200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3300200 prefixEnd_3300200 := by exact prefixLift 3300200
  have htrace : WordTrace (prefixWord ++ tailWord_3300200) baseStart_3300200 baseEnd_3300200 := by
    simpa [prefixWord, tailWord_3300200, baseEnd_3300200] using wordTrace_append hprefix tailTrace_3300200
  have hstable : (prefixWord ++ tailWord_3300200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3300200).length < 2 ^ (prefixWord ++ tailWord_3300200).sum := by decide
  have hdescent : baseEnd_3300200 < baseStart_3300200 := by decide
  rcases family_descends (prefixWord ++ tailWord_3300200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3300209 : List Nat := [1, 2, 2, 2, 1, 5, 2, 1, 1, 1, 5]
def baseStart_3300209 : Nat := 118140960795 + 3300209 * 2 ^ 59
def prefixEnd_3300209 : Nat := 4983230072969 + 3 ^ 40 * 3300209 * 2
def baseEnd_3300209 : Nat := 1694593477293983650810121

theorem tailTrace_3300209 : CollatzResearch.WordTrace tailWord_3300209 prefixEnd_3300209 1694593477293983650810121 := by
  unfold tailWord_3300209
  simp only [CollatzResearch.WordTrace]
  refine ⟨120368510900913898669367681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80245673933942599112911787 120368510900913898669367681)
  ·
    refine ⟨90276383175685424002025761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120368510900913898669367681 90276383175685424002025761)
    ·
      refine ⟨67707287381764068001519321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90276383175685424002025761 67707287381764068001519321)
      ·
        refine ⟨50780465536323051001139491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67707287381764068001519321 50780465536323051001139491)
        ·
          refine ⟨76170698304484576501709237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50780465536323051001139491 76170698304484576501709237)
          ·
            refine ⟨7141002966045429047035241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 76170698304484576501709237 7141002966045429047035241)
            ·
              refine ⟨5355752224534071785276431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7141002966045429047035241 5355752224534071785276431)
              ·
                refine ⟨8033628336801107677914647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5355752224534071785276431 8033628336801107677914647)
                ·
                  refine ⟨12050442505201661516871971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8033628336801107677914647 12050442505201661516871971)
                  ·
                    refine ⟨18075663757802492275307957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12050442505201661516871971 18075663757802492275307957)
                    ·
                      refine ⟨1694593477293983650810121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18075663757802492275307957 1694593477293983650810121)
                      ·
                        rfl

theorem cell23_3300209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2, 1, 1, 1, 5].length) (baseStart_3300209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3300209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3300209 prefixEnd_3300209 := by exact prefixLift 3300209
  have htrace : WordTrace (prefixWord ++ tailWord_3300209) baseStart_3300209 baseEnd_3300209 := by
    simpa [prefixWord, tailWord_3300209, baseEnd_3300209] using wordTrace_append hprefix tailTrace_3300209
  have hstable : (prefixWord ++ tailWord_3300209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3300209).length < 2 ^ (prefixWord ++ tailWord_3300209).sum := by decide
  have hdescent : baseEnd_3300209 < baseStart_3300209 := by decide
  rcases family_descends (prefixWord ++ tailWord_3300209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3300223 : List Nat := [1, 1, 2, 2, 1, 1, 4, 6, 1, 2, 2]
def baseStart_3300223 : Nat := 118140960795 + 3300223 * 2 ^ 59
def prefixEnd_3300223 : Nat := 4983230072969 + 3 ^ 40 * 3300223 * 2
def baseEnd_3300223 : Nat := 1694600666023146596035057

theorem tailTrace_3300223 : CollatzResearch.WordTrace tailWord_3300223 prefixEnd_3300223 1694600666023146596035057 := by
  unfold tailWord_3300223
  simp only [CollatzResearch.WordTrace]
  refine ⟨120369021522863179060377323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80246014348575452706918215 120369021522863179060377323)
  ·
    refine ⟨180553532284294768590565985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120369021522863179060377323 180553532284294768590565985)
    ·
      refine ⟨135415149213221076442924489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180553532284294768590565985 135415149213221076442924489)
      ·
        refine ⟨101561361909915807332193367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135415149213221076442924489 101561361909915807332193367)
        ·
          refine ⟨152342042864873710998290051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101561361909915807332193367 152342042864873710998290051)
          ·
            refine ⟨228513064297310566497435077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152342042864873710998290051 228513064297310566497435077)
            ·
              refine ⟨42846199555745731218269077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 228513064297310566497435077 42846199555745731218269077)
              ·
                refine ⟨2008415604175581150856363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 42846199555745731218269077 2008415604175581150856363)
                ·
                  refine ⟨3012623406263371726284545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2008415604175581150856363 3012623406263371726284545)
                  ·
                    refine ⟨2259467554697528794713409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3012623406263371726284545 2259467554697528794713409)
                    ·
                      refine ⟨1694600666023146596035057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2259467554697528794713409 1694600666023146596035057)
                      ·
                        rfl

theorem cell23_3300223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 6, 1, 2, 2].length) (baseStart_3300223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3300223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3300223 prefixEnd_3300223 := by exact prefixLift 3300223
  have htrace : WordTrace (prefixWord ++ tailWord_3300223) baseStart_3300223 baseEnd_3300223 := by
    simpa [prefixWord, tailWord_3300223, baseEnd_3300223] using wordTrace_append hprefix tailTrace_3300223
  have hstable : (prefixWord ++ tailWord_3300223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3300223).length < 2 ^ (prefixWord ++ tailWord_3300223).sum := by decide
  have hdescent : baseEnd_3300223 < baseStart_3300223 := by decide
  rcases family_descends (prefixWord ++ tailWord_3300223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3300233 : List Nat := [1, 2, 1, 1, 5, 4, 2, 1, 2, 4]
def baseStart_3300233 : Nat := 118140960795 + 3300233 * 2 ^ 59
def prefixEnd_3300233 : Nat := 4983230072969 + 3 ^ 40 * 3300233 * 2
def baseEnd_3300233 : Nat := 564868600276563852303337

theorem tailTrace_3300233 : CollatzResearch.WordTrace tailWord_3300233 prefixEnd_3300233 564868600276563852303337 := by
  unfold tailWord_3300233
  simp only [CollatzResearch.WordTrace]
  refine ⟨120369386252826950768241353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80246257501884633845494235 120369386252826950768241353)
  ·
    refine ⟨90277039689620213076181015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120369386252826950768241353 90277039689620213076181015)
    ·
      refine ⟨135415559534430319614271523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90277039689620213076181015 135415559534430319614271523)
      ·
        refine ⟨203123339301645479421407285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135415559534430319614271523 203123339301645479421407285)
        ·
          refine ⟨19042813059529263695756933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 203123339301645479421407285 19042813059529263695756933)
          ·
            refine ⟨3570527448661736942954425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19042813059529263695756933 3570527448661736942954425)
            ·
              refine ⟨2677895586496302707215819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3570527448661736942954425 2677895586496302707215819)
              ·
                refine ⟨4016843379744454060823729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2677895586496302707215819 4016843379744454060823729)
                ·
                  refine ⟨3012632534808340545617797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4016843379744454060823729 3012632534808340545617797)
                  ·
                    refine ⟨564868600276563852303337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3012632534808340545617797 564868600276563852303337)
                    ·
                      rfl

theorem cell23_3300233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 2, 1, 2, 4].length) (baseStart_3300233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3300233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3300233 prefixEnd_3300233 := by exact prefixLift 3300233
  have htrace : WordTrace (prefixWord ++ tailWord_3300233) baseStart_3300233 baseEnd_3300233 := by
    simpa [prefixWord, tailWord_3300233, baseEnd_3300233] using wordTrace_append hprefix tailTrace_3300233
  have hstable : (prefixWord ++ tailWord_3300233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3300233).length < 2 ^ (prefixWord ++ tailWord_3300233).sum := by decide
  have hdescent : baseEnd_3300233 < baseStart_3300233 := by decide
  rcases family_descends (prefixWord ++ tailWord_3300233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3300276 : List Nat := [2, 5, 2, 1, 1, 1, 1, 1, 2, 7]
def baseStart_3300276 : Nat := 118140960795 + 3300276 * 2 ^ 59
def prefixEnd_3300276 : Nat := 4983230072969 + 3 ^ 40 * 3300276 * 2
def baseEnd_3300276 : Nat := 564875960165944962890771

theorem tailTrace_3300276 : CollatzResearch.WordTrace tailWord_3300276 prefixEnd_3300276 564875960165944962890771 := by
  unfold tailWord_3300276
  simp only [CollatzResearch.WordTrace]
  refine ⟨60185477295835584556028341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80247303061114112741371121 60185477295835584556028341)
  ·
    refine ⟨5642388496484586052127657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 60185477295835584556028341 5642388496484586052127657)
    ·
      refine ⟨4231791372363439539095743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5642388496484586052127657 4231791372363439539095743)
      ·
        refine ⟨6347687058545159308643615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4231791372363439539095743 6347687058545159308643615)
        ·
          refine ⟨9521530587817738962965423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6347687058545159308643615 9521530587817738962965423)
          ·
            refine ⟨14282295881726608444448135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9521530587817738962965423 14282295881726608444448135)
            ·
              refine ⟨21423443822589912666672203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14282295881726608444448135 21423443822589912666672203)
              ·
                refine ⟨32135165733884869000008305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21423443822589912666672203 32135165733884869000008305)
                ·
                  refine ⟨24101374300413651750006229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32135165733884869000008305 24101374300413651750006229)
                  ·
                    refine ⟨564875960165944962890771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24101374300413651750006229 564875960165944962890771)
                    ·
                      rfl

theorem cell23_3300276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_3300276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3300276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3300276 prefixEnd_3300276 := by exact prefixLift 3300276
  have htrace : WordTrace (prefixWord ++ tailWord_3300276) baseStart_3300276 baseEnd_3300276 := by
    simpa [prefixWord, tailWord_3300276, baseEnd_3300276] using wordTrace_append hprefix tailTrace_3300276
  have hstable : (prefixWord ++ tailWord_3300276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3300276).length < 2 ^ (prefixWord ++ tailWord_3300276).sum := by decide
  have hdescent : baseEnd_3300276 < baseStart_3300276 := by decide
  rcases family_descends (prefixWord ++ tailWord_3300276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3300317 : List Nat := [1, 4, 3, 1, 2, 3, 2, 1, 1, 3, 2]
def baseStart_3300317 : Nat := 118140960795 + 3300317 * 2 ^ 59
def prefixEnd_3300317 : Nat := 4983230072969 + 3 ^ 40 * 3300317 * 2
def baseEnd_3300317 : Nat := 1694648933204669228259625

theorem tailTrace_3300317 : CollatzResearch.WordTrace tailWord_3300317 prefixEnd_3300317 1694648933204669228259625 := by
  unfold tailWord_3300317
  simp only [CollatzResearch.WordTrace]
  refine ⟨120372449984522633114299205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80248299989681755409532803 120372449984522633114299205)
  ·
    refine ⟨22569834372097993708931101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120372449984522633114299205 22569834372097993708931101)
    ·
      refine ⟨8463687889536747640849163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22569834372097993708931101 8463687889536747640849163)
      ·
        refine ⟨12695531834305121461273745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8463687889536747640849163 12695531834305121461273745)
        ·
          refine ⟨9521648875728841095955309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12695531834305121461273745 9521648875728841095955309)
          ·
            refine ⟨3570618328398315410983241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9521648875728841095955309 3570618328398315410983241)
            ·
              refine ⟨2677963746298736558237431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3570618328398315410983241 2677963746298736558237431)
              ·
                refine ⟨4016945619448104837356147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2677963746298736558237431 4016945619448104837356147)
                ·
                  refine ⟨6025418429172157256034221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4016945619448104837356147 6025418429172157256034221)
                  ·
                    refine ⟨2259531910939558971012833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6025418429172157256034221 2259531910939558971012833)
                    ·
                      refine ⟨1694648933204669228259625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2259531910939558971012833 1694648933204669228259625)
                      ·
                        rfl

theorem cell23_3300317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 2, 1, 1, 3, 2].length) (baseStart_3300317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3300317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3300317 prefixEnd_3300317 := by exact prefixLift 3300317
  have htrace : WordTrace (prefixWord ++ tailWord_3300317) baseStart_3300317 baseEnd_3300317 := by
    simpa [prefixWord, tailWord_3300317, baseEnd_3300317] using wordTrace_append hprefix tailTrace_3300317
  have hstable : (prefixWord ++ tailWord_3300317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3300317).length < 2 ^ (prefixWord ++ tailWord_3300317).sum := by decide
  have hdescent : baseEnd_3300317 < baseStart_3300317 := by decide
  rcases family_descends (prefixWord ++ tailWord_3300317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3300330 : List Nat := [3, 1, 3, 1, 2, 2, 3, 2, 2, 2, 2]
def baseStart_3300330 : Nat := 118140960795 + 3300330 * 2 ^ 59
def prefixEnd_3300330 : Nat := 4983230072969 + 3 ^ 40 * 3300330 * 2
def baseEnd_3300330 : Nat := 1694655608453177677397065

theorem tailTrace_3300330 : CollatzResearch.WordTrace tailWord_3300330 prefixEnd_3300330 1694655608453177677397065 := by
  unfold tailWord_3300330
  simp only [CollatzResearch.WordTrace]
  refine ⟨30093231033368884083630611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80248616088983690889681629 30093231033368884083630611)
  ·
    refine ⟨45139846550053326125445917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30093231033368884083630611 45139846550053326125445917)
    ·
      refine ⟨16927442456269997297042219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45139846550053326125445917 16927442456269997297042219)
      ·
        refine ⟨25391163684404995945563329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16927442456269997297042219 25391163684404995945563329)
        ·
          refine ⟨19043372763303746959172497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25391163684404995945563329 19043372763303746959172497)
          ·
            refine ⟨14282529572477810219379373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19043372763303746959172497 14282529572477810219379373)
            ·
              refine ⟨5355948589679178832267265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14282529572477810219379373 5355948589679178832267265)
              ·
                refine ⟨4016961442259384124200449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5355948589679178832267265 4016961442259384124200449)
                ·
                  refine ⟨3012721081694538093150337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4016961442259384124200449 3012721081694538093150337)
                  ·
                    refine ⟨2259540811270903569862753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3012721081694538093150337 2259540811270903569862753)
                    ·
                      refine ⟨1694655608453177677397065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2259540811270903569862753 1694655608453177677397065)
                      ·
                        rfl

theorem cell23_3300330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3, 2, 2, 2, 2].length) (baseStart_3300330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3300330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3300330 prefixEnd_3300330 := by exact prefixLift 3300330
  have htrace : WordTrace (prefixWord ++ tailWord_3300330) baseStart_3300330 baseEnd_3300330 := by
    simpa [prefixWord, tailWord_3300330, baseEnd_3300330] using wordTrace_append hprefix tailTrace_3300330
  have hstable : (prefixWord ++ tailWord_3300330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3300330).length < 2 ^ (prefixWord ++ tailWord_3300330).sum := by decide
  have hdescent : baseEnd_3300330 < baseStart_3300330 := by decide
  rcases family_descends (prefixWord ++ tailWord_3300330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3300369 : List Nat := [1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 4]
def baseStart_3300369 : Nat := 118140960795 + 3300369 * 2 ^ 59
def prefixEnd_3300369 : Nat := 4983230072969 + 3 ^ 40 * 3300369 * 2
def baseEnd_3300369 : Nat := 1694675634198703024809385

theorem tailTrace_3300369 : CollatzResearch.WordTrace tailWord_3300369 prefixEnd_3300369 1694675634198703024809385 := by
  unfold tailWord_3300369
  simp only [CollatzResearch.WordTrace]
  refine ⟨120374346580334245995192161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80249564386889497330128107 120374346580334245995192161)
  ·
    refine ⟨90280759935250684496394121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120374346580334245995192161 90280759935250684496394121)
    ·
      refine ⟨67710569951438013372295591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90280759935250684496394121 67710569951438013372295591)
      ·
        refine ⟨101565854927157020058443387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67710569951438013372295591 101565854927157020058443387)
        ·
          refine ⟨152348782390735530087665081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101565854927157020058443387 152348782390735530087665081)
          ·
            refine ⟨114261586793051647565748811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152348782390735530087665081 114261586793051647565748811)
            ·
              refine ⟨171392380189577471348623217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114261586793051647565748811 171392380189577471348623217)
              ·
                refine ⟨128544285142183103511467413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 171392380189577471348623217 128544285142183103511467413)
                ·
                  refine ⟨6025513366039832977100035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 128544285142183103511467413 6025513366039832977100035)
                  ·
                    refine ⟨9038270049059749465650053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6025513366039832977100035 9038270049059749465650053)
                    ·
                      refine ⟨1694675634198703024809385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9038270049059749465650053 1694675634198703024809385)
                      ·
                        rfl

theorem cell23_3300369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 4].length) (baseStart_3300369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3300369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3300369 prefixEnd_3300369 := by exact prefixLift 3300369
  have htrace : WordTrace (prefixWord ++ tailWord_3300369) baseStart_3300369 baseEnd_3300369 := by
    simpa [prefixWord, tailWord_3300369, baseEnd_3300369] using wordTrace_append hprefix tailTrace_3300369
  have hstable : (prefixWord ++ tailWord_3300369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3300369).length < 2 ^ (prefixWord ++ tailWord_3300369).sum := by decide
  have hdescent : baseEnd_3300369 < baseStart_3300369 := by decide
  rcases family_descends (prefixWord ++ tailWord_3300369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3300386 : List Nat := [3, 3, 1, 1, 1, 3, 1, 1, 4, 1, 4]
def baseStart_3300386 : Nat := 118140960795 + 3300386 * 2 ^ 59
def prefixEnd_3300386 : Nat := 4983230072969 + 3 ^ 40 * 3300386 * 2
def baseEnd_3300386 : Nat := 1694684363369829458296807

theorem tailTrace_3300386 : CollatzResearch.WordTrace tailWord_3300386 prefixEnd_3300386 1694684363369829458296807 := by
  unfold tailWord_3300386
  simp only [CollatzResearch.WordTrace]
  refine ⟨30093741655318164474640253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80249977747515105265707341 30093741655318164474640253)
  ·
    refine ⟨11285153120744311677990095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30093741655318164474640253 11285153120744311677990095)
    ·
      refine ⟨16927729681116467516985143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11285153120744311677990095 16927729681116467516985143)
      ·
        refine ⟨25391594521674701275477715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16927729681116467516985143 25391594521674701275477715)
        ·
          refine ⟨38087391782512051913216573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25391594521674701275477715 38087391782512051913216573)
          ·
            refine ⟨14282771918442019467456215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38087391782512051913216573 14282771918442019467456215)
            ·
              refine ⟨21424157877663029201184323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14282771918442019467456215 21424157877663029201184323)
              ·
                refine ⟨32136236816494543801776485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21424157877663029201184323 32136236816494543801776485)
                ·
                  refine ⟨6025544403092726962833091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32136236816494543801776485 6025544403092726962833091)
                  ·
                    refine ⟨9038316604639090444249637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6025544403092726962833091 9038316604639090444249637)
                    ·
                      refine ⟨1694684363369829458296807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9038316604639090444249637 1694684363369829458296807)
                      ·
                        rfl

theorem cell23_3300386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 1, 4, 1, 4].length) (baseStart_3300386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3300386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3300386 prefixEnd_3300386 := by exact prefixLift 3300386
  have htrace : WordTrace (prefixWord ++ tailWord_3300386) baseStart_3300386 baseEnd_3300386 := by
    simpa [prefixWord, tailWord_3300386, baseEnd_3300386] using wordTrace_append hprefix tailTrace_3300386
  have hstable : (prefixWord ++ tailWord_3300386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3300386).length < 2 ^ (prefixWord ++ tailWord_3300386).sum := by decide
  have hdescent : baseEnd_3300386 < baseStart_3300386 := by decide
  rcases family_descends (prefixWord ++ tailWord_3300386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3300423 : List Nat := [1, 1, 4, 1, 3, 3, 2, 1, 2, 2, 3]
def baseStart_3300423 : Nat := 118140960795 + 3300423 * 2 ^ 59
def prefixEnd_3300423 : Nat := 4983230072969 + 3 ^ 40 * 3300423 * 2
def baseEnd_3300423 : Nat := 1694703362154045813534137

theorem tailTrace_3300423 : CollatzResearch.WordTrace tailWord_3300423 prefixEnd_3300423 1694703362154045813534137 := by
  unfold tailWord_3300423
  simp only [CollatzResearch.WordTrace]
  refine ⟨120376316122138613217657923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80250877414759075478438615 120376316122138613217657923)
  ·
    refine ⟨180564474183207919826486885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120376316122138613217657923 180564474183207919826486885)
    ·
      refine ⟨33855838909351484967466291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 180564474183207919826486885 33855838909351484967466291)
      ·
        refine ⟨50783758364027227451199437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33855838909351484967466291 50783758364027227451199437)
        ·
          refine ⟨19043909386510210294199789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50783758364027227451199437 19043909386510210294199789)
          ·
            refine ⟨7141466019941328860324921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19043909386510210294199789 7141466019941328860324921)
            ·
              refine ⟨5356099514955996645243691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7141466019941328860324921 5356099514955996645243691)
              ·
                refine ⟨8034149272433994967865537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5356099514955996645243691 8034149272433994967865537)
                ·
                  refine ⟨6025611954325496225899153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8034149272433994967865537 6025611954325496225899153)
                  ·
                    refine ⟨4519208965744122169424365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6025611954325496225899153 4519208965744122169424365)
                    ·
                      refine ⟨1694703362154045813534137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4519208965744122169424365 1694703362154045813534137)
                      ·
                        rfl

theorem cell23_3300423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2, 1, 2, 2, 3].length) (baseStart_3300423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3300423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3300423 prefixEnd_3300423 := by exact prefixLift 3300423
  have htrace : WordTrace (prefixWord ++ tailWord_3300423) baseStart_3300423 baseEnd_3300423 := by
    simpa [prefixWord, tailWord_3300423, baseEnd_3300423] using wordTrace_append hprefix tailTrace_3300423
  have hstable : (prefixWord ++ tailWord_3300423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3300423).length < 2 ^ (prefixWord ++ tailWord_3300423).sum := by decide
  have hdescent : baseEnd_3300423 < baseStart_3300423 := by decide
  rcases family_descends (prefixWord ++ tailWord_3300423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3300453 : List Nat := [1, 3, 1, 3, 2, 1, 2, 3, 3, 1, 3]
def baseStart_3300453 : Nat := 118140960795 + 3300453 * 2 ^ 59
def prefixEnd_3300453 : Nat := 4983230072969 + 3 ^ 40 * 3300453 * 2
def baseEnd_3300453 : Nat := 1694718766573680696158999

theorem tailTrace_3300453 : CollatzResearch.WordTrace tailWord_3300453 prefixEnd_3300453 1694718766573680696158999 := by
  unfold tailWord_3300453
  simp only [CollatzResearch.WordTrace]
  refine ⟨120377410312029928341250013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80251606874686618894166675 120377410312029928341250013)
  ·
    refine ⟨45141528867011223127968755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120377410312029928341250013 45141528867011223127968755)
    ·
      refine ⟨67712293300516834691953133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45141528867011223127968755 67712293300516834691953133)
      ·
        refine ⟨25392109987693813009482425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67712293300516834691953133 25392109987693813009482425)
        ·
          refine ⟨19044082490770359757111819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25392109987693813009482425 19044082490770359757111819)
          ·
            refine ⟨28566123736155539635667729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19044082490770359757111819 28566123736155539635667729)
            ·
              refine ⟨21424592802116654726750797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28566123736155539635667729 21424592802116654726750797)
              ·
                refine ⟨8034222300793745522531549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21424592802116654726750797 8034222300793745522531549)
                ·
                  refine ⟨3012833362797654570949331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8034222300793745522531549 3012833362797654570949331)
                  ·
                    refine ⟨4519250044196481856423997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3012833362797654570949331 4519250044196481856423997)
                    ·
                      refine ⟨1694718766573680696158999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4519250044196481856423997 1694718766573680696158999)
                      ·
                        rfl

theorem cell23_3300453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 3, 3, 1, 3].length) (baseStart_3300453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3300453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3300453 prefixEnd_3300453 := by exact prefixLift 3300453
  have htrace : WordTrace (prefixWord ++ tailWord_3300453) baseStart_3300453 baseEnd_3300453 := by
    simpa [prefixWord, tailWord_3300453, baseEnd_3300453] using wordTrace_append hprefix tailTrace_3300453
  have hstable : (prefixWord ++ tailWord_3300453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3300453).length < 2 ^ (prefixWord ++ tailWord_3300453).sum := by decide
  have hdescent : baseEnd_3300453 < baseStart_3300453 := by decide
  rcases family_descends (prefixWord ++ tailWord_3300453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3300470 : List Nat := [5, 1, 1, 2, 1, 1, 3, 2, 3, 1, 3]
def baseStart_3300470 : Nat := 118140960795 + 3300470 * 2 ^ 59
def prefixEnd_3300470 : Nat := 4983230072969 + 3 ^ 40 * 3300470 * 2
def baseEnd_3300470 : Nat := 1694727495744807129646421

theorem tailTrace_3300470 : CollatzResearch.WordTrace tailWord_3300470 prefixEnd_3300470 1694727495744807129646421 := by
  unfold tailWord_3300470
  simp only [CollatzResearch.WordTrace]
  refine ⟨7523626897060521265288679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 80252020235312226829745909 7523626897060521265288679)
  ·
    refine ⟨11285440345590781897933019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7523626897060521265288679 11285440345590781897933019)
    ·
      refine ⟨16928160518386172846899529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11285440345590781897933019 16928160518386172846899529)
      ·
        refine ⟨12696120388789629635174647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16928160518386172846899529 12696120388789629635174647)
        ·
          refine ⟨19044180583184444452761971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12696120388789629635174647 19044180583184444452761971)
          ·
            refine ⟨28566270874776666679142957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19044180583184444452761971 28566270874776666679142957)
            ·
              refine ⟨10712351578041250004678609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28566270874776666679142957 10712351578041250004678609)
              ·
                refine ⟨8034263683530937503508957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10712351578041250004678609 8034263683530937503508957)
                ·
                  refine ⟨3012848881324101563815859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8034263683530937503508957 3012848881324101563815859)
                  ·
                    refine ⟨4519273321986152345723789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3012848881324101563815859 4519273321986152345723789)
                    ·
                      refine ⟨1694727495744807129646421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4519273321986152345723789 1694727495744807129646421)
                      ·
                        rfl

theorem cell23_3300470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 2, 3, 1, 3].length) (baseStart_3300470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3300470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3300470 prefixEnd_3300470 := by exact prefixLift 3300470
  have htrace : WordTrace (prefixWord ++ tailWord_3300470) baseStart_3300470 baseEnd_3300470 := by
    simpa [prefixWord, tailWord_3300470, baseEnd_3300470] using wordTrace_append hprefix tailTrace_3300470
  have hstable : (prefixWord ++ tailWord_3300470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3300470).length < 2 ^ (prefixWord ++ tailWord_3300470).sum := by decide
  have hdescent : baseEnd_3300470 < baseStart_3300470 := by decide
  rcases family_descends (prefixWord ++ tailWord_3300470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3300476 : List Nat := [2, 2, 2, 1, 1, 3, 1, 3, 3, 1, 4]
def baseStart_3300476 : Nat := 118140960795 + 3300476 * 2 ^ 59
def prefixEnd_3300476 : Nat := 4983230072969 + 3 ^ 40 * 3300476 * 2
def baseEnd_3300476 : Nat := 1694730576628734106171393

theorem tailTrace_3300476 : CollatzResearch.WordTrace tailWord_3300476 prefixEnd_3300476 1694730576628734106171393 := by
  unfold tailWord_3300476
  simp only [CollatzResearch.WordTrace]
  refine ⟨60189124595473301634668641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80252166127297735512891521 60189124595473301634668641)
  ·
    refine ⟨45141843446604976226001481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60189124595473301634668641 45141843446604976226001481)
    ·
      refine ⟨33856382584953732169501111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45141843446604976226001481 33856382584953732169501111)
      ·
        refine ⟨50784573877430598254251667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33856382584953732169501111 50784573877430598254251667)
        ·
          refine ⟨76176860816145897381377501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50784573877430598254251667 76176860816145897381377501)
          ·
            refine ⟨28566322806054711518016563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76176860816145897381377501 28566322806054711518016563)
            ·
              refine ⟨42849484209082067277024845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28566322806054711518016563 42849484209082067277024845)
              ·
                refine ⟨16068556578405775228884317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42849484209082067277024845 16068556578405775228884317)
                ·
                  refine ⟨6025708716902165710831619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16068556578405775228884317 6025708716902165710831619)
                  ·
                    refine ⟨9038563075353248566247429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6025708716902165710831619 9038563075353248566247429)
                    ·
                      refine ⟨1694730576628734106171393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9038563075353248566247429 1694730576628734106171393)
                      ·
                        rfl

theorem cell23_3300476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 3, 3, 1, 4].length) (baseStart_3300476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3300476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3300476 prefixEnd_3300476 := by exact prefixLift 3300476
  have htrace : WordTrace (prefixWord ++ tailWord_3300476) baseStart_3300476 baseEnd_3300476 := by
    simpa [prefixWord, tailWord_3300476, baseEnd_3300476] using wordTrace_append hprefix tailTrace_3300476
  have hstable : (prefixWord ++ tailWord_3300476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3300476).length < 2 ^ (prefixWord ++ tailWord_3300476).sum := by decide
  have hdescent : baseEnd_3300476 < baseStart_3300476 := by decide
  rcases family_descends (prefixWord ++ tailWord_3300476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3300496 : List Nat := [2, 1, 1, 1, 1, 1, 4, 2, 5, 2, 3]
def baseStart_3300496 : Nat := 118140960795 + 3300496 * 2 ^ 59
def prefixEnd_3300496 : Nat := 4983230072969 + 3 ^ 40 * 3300496 * 2
def baseEnd_3300496 : Nat := 1694740846241824027921301

theorem tailTrace_3300496 : CollatzResearch.WordTrace tailWord_3300496 prefixEnd_3300496 1694740846241824027921301 := by
  unfold tailWord_3300496
  simp only [CollatzResearch.WordTrace]
  refine ⟨60189489325437073342532671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80252652433916097790043561 60189489325437073342532671)
  ·
    refine ⟨90284233988155610013799007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60189489325437073342532671 90284233988155610013799007)
    ·
      refine ⟨135426350982233415020698511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90284233988155610013799007 135426350982233415020698511)
      ·
        refine ⟨203139526473350122531047767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135426350982233415020698511 203139526473350122531047767)
        ·
          refine ⟨304709289710025183796571651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203139526473350122531047767 304709289710025183796571651)
          ·
            refine ⟨457063934565037775694857477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 304709289710025183796571651 457063934565037775694857477)
            ·
              refine ⟨85699487730944582942785777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 457063934565037775694857477 85699487730944582942785777)
              ·
                refine ⟨64274615798208437207089333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85699487730944582942785777 64274615798208437207089333)
                ·
                  refine ⟨6025745231082040988164625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 64274615798208437207089333 6025745231082040988164625)
                  ·
                    refine ⟨4519308923311530741123469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6025745231082040988164625 4519308923311530741123469)
                    ·
                      refine ⟨1694740846241824027921301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4519308923311530741123469 1694740846241824027921301)
                      ·
                        rfl

theorem cell23_3300496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 5, 2, 3].length) (baseStart_3300496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3300496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3300496 prefixEnd_3300496 := by exact prefixLift 3300496
  have htrace : WordTrace (prefixWord ++ tailWord_3300496) baseStart_3300496 baseEnd_3300496 := by
    simpa [prefixWord, tailWord_3300496, baseEnd_3300496] using wordTrace_append hprefix tailTrace_3300496
  have hstable : (prefixWord ++ tailWord_3300496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3300496).length < 2 ^ (prefixWord ++ tailWord_3300496).sum := by decide
  have hdescent : baseEnd_3300496 < baseStart_3300496 := by decide
  rcases family_descends (prefixWord ++ tailWord_3300496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3300503 : List Nat := [1, 1, 3, 3, 3, 2, 1, 1, 4, 4]
def baseStart_3300503 : Nat := 118140960795 + 3300503 * 2 ^ 59
def prefixEnd_3300503 : Nat := 4983230072969 + 3 ^ 40 * 3300503 * 2
def baseEnd_3300503 : Nat := 564914813535468500177923

theorem tailTrace_3300503 : CollatzResearch.WordTrace tailWord_3300503 prefixEnd_3300503 564914813535468500177923 := by
  unfold tailWord_3300503
  simp only [CollatzResearch.WordTrace]
  refine ⟨120379233961848786880570163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80252822641232524587046775 120379233961848786880570163)
  ·
    refine ⟨180568850942773180320855245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120379233961848786880570163 180568850942773180320855245)
    ·
      refine ⟨67713319103539942620320717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180568850942773180320855245 67713319103539942620320717)
      ·
        refine ⟨25392494663827478482620269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67713319103539942620320717 25392494663827478482620269)
        ·
          refine ⟨9522185498935304430982601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25392494663827478482620269 9522185498935304430982601)
          ·
            refine ⟨7141639124201478323236951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9522185498935304430982601 7141639124201478323236951)
            ·
              refine ⟨10712458686302217484855427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7141639124201478323236951 10712458686302217484855427)
              ·
                refine ⟨16068688029453326227283141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10712458686302217484855427 16068688029453326227283141)
                ·
                  refine ⟨3012879005522498667615589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16068688029453326227283141 3012879005522498667615589)
                  ·
                    refine ⟨564914813535468500177923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3012879005522498667615589 564914813535468500177923)
                    ·
                      rfl

theorem cell23_3300503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 1, 4, 4].length) (baseStart_3300503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3300503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3300503 prefixEnd_3300503 := by exact prefixLift 3300503
  have htrace : WordTrace (prefixWord ++ tailWord_3300503) baseStart_3300503 baseEnd_3300503 := by
    simpa [prefixWord, tailWord_3300503, baseEnd_3300503] using wordTrace_append hprefix tailTrace_3300503
  have hstable : (prefixWord ++ tailWord_3300503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3300503).length < 2 ^ (prefixWord ++ tailWord_3300503).sum := by decide
  have hdescent : baseEnd_3300503 < baseStart_3300503 := by decide
  rcases family_descends (prefixWord ++ tailWord_3300503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3300530 : List Nat := [3, 2, 1, 1, 1, 5, 2, 2, 1, 2, 3]
def baseStart_3300530 : Nat := 118140960795 + 3300530 * 2 ^ 59
def prefixEnd_3300530 : Nat := 4983230072969 + 3 ^ 40 * 3300530 * 2
def baseEnd_3300530 : Nat := 1694758304584076894896145

theorem tailTrace_3300530 : CollatzResearch.WordTrace tailWord_3300530 prefixEnd_3300530 1694758304584076894896145 := by
  unfold tailWord_3300530
  simp only [CollatzResearch.WordTrace]
  refine ⟨30095054683187742622950761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80253479155167313661202029 30095054683187742622950761)
  ·
    refine ⟨22571291012390806967213071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30095054683187742622950761 22571291012390806967213071)
    ·
      refine ⟨33856936518586210450819607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22571291012390806967213071 33856936518586210450819607)
      ·
        refine ⟨50785404777879315676229411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33856936518586210450819607 50785404777879315676229411)
        ·
          refine ⟨76178107166818973514344117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50785404777879315676229411 76178107166818973514344117)
          ·
            refine ⟨7141697546889278766969761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 76178107166818973514344117 7141697546889278766969761)
            ·
              refine ⟨5356273160166959075227321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7141697546889278766969761 5356273160166959075227321)
              ·
                refine ⟨4017204870125219306420491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5356273160166959075227321 4017204870125219306420491)
                ·
                  refine ⟨6025807305187828959630737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4017204870125219306420491 6025807305187828959630737)
                  ·
                    refine ⟨4519355478890871719723053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6025807305187828959630737 4519355478890871719723053)
                    ·
                      refine ⟨1694758304584076894896145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4519355478890871719723053 1694758304584076894896145)
                      ·
                        rfl

theorem cell23_3300530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2, 2, 1, 2, 3].length) (baseStart_3300530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3300530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3300530 prefixEnd_3300530 := by exact prefixLift 3300530
  have htrace : WordTrace (prefixWord ++ tailWord_3300530) baseStart_3300530 baseEnd_3300530 := by
    simpa [prefixWord, tailWord_3300530, baseEnd_3300530] using wordTrace_append hprefix tailTrace_3300530
  have hstable : (prefixWord ++ tailWord_3300530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3300530).length < 2 ^ (prefixWord ++ tailWord_3300530).sum := by decide
  have hdescent : baseEnd_3300530 < baseStart_3300530 := by decide
  rcases family_descends (prefixWord ++ tailWord_3300530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3300543 : List Nat := [1, 1, 2, 2, 2, 2, 3, 2, 4, 1, 3]
def baseStart_3300543 : Nat := 118140960795 + 3300543 * 2 ^ 59
def prefixEnd_3300543 : Nat := 4983230072969 + 3 ^ 40 * 3300543 * 2
def baseEnd_3300543 : Nat := 1694764979832585344033585

theorem tailTrace_3300543 : CollatzResearch.WordTrace tailWord_3300543 prefixEnd_3300543 1694764979832585344033585 := by
  unfold tailWord_3300543
  simp only [CollatzResearch.WordTrace]
  refine ⟨120380692881703873712026283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80253795254469249141350855 120380692881703873712026283)
  ·
    refine ⟨180571039322555810568039425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120380692881703873712026283 180571039322555810568039425)
    ·
      refine ⟨135428279491916857926029569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180571039322555810568039425 135428279491916857926029569)
      ·
        refine ⟨101571209618937643444522177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135428279491916857926029569 101571209618937643444522177)
        ·
          refine ⟨76178407214203232583391633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101571209618937643444522177 76178407214203232583391633)
          ·
            refine ⟨57133805410652424437543725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76178407214203232583391633 57133805410652424437543725)
            ·
              refine ⟨21425177028994659164078897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57133805410652424437543725 21425177028994659164078897)
              ·
                refine ⟨16068882771745994373059173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21425177028994659164078897 16068882771745994373059173)
                ·
                  refine ⟨3012915519702373944948595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16068882771745994373059173 3012915519702373944948595)
                  ·
                    refine ⟨4519373279553560917422893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3012915519702373944948595 4519373279553560917422893)
                    ·
                      refine ⟨1694764979832585344033585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4519373279553560917422893 1694764979832585344033585)
                      ·
                        rfl

theorem cell23_3300543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 2, 4, 1, 3].length) (baseStart_3300543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3300543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3300543 prefixEnd_3300543 := by exact prefixLift 3300543
  have htrace : WordTrace (prefixWord ++ tailWord_3300543) baseStart_3300543 baseEnd_3300543 := by
    simpa [prefixWord, tailWord_3300543, baseEnd_3300543] using wordTrace_append hprefix tailTrace_3300543
  have hstable : (prefixWord ++ tailWord_3300543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3300543).length < 2 ^ (prefixWord ++ tailWord_3300543).sum := by decide
  have hdescent : baseEnd_3300543 < baseStart_3300543 := by decide
  rcases family_descends (prefixWord ++ tailWord_3300543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3300577 : List Nat := [1, 2, 3, 1, 3, 2, 4, 1, 2, 1, 3]
def baseStart_3300577 : Nat := 118140960795 + 3300577 * 2 ^ 59
def prefixEnd_3300577 : Nat := 4983230072969 + 3 ^ 40 * 3300577 * 2
def baseEnd_3300577 : Nat := 1694782438174838211008429

theorem tailTrace_3300577 : CollatzResearch.WordTrace tailWord_3300577 prefixEnd_3300577 1694782438174838211008429 := by
  unfold tailWord_3300577
  simp only [CollatzResearch.WordTrace]
  refine ⟨120381932963580697518763985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80254621975720465012509323 120381932963580697518763985)
  ·
    refine ⟨90286449722685523139072989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120381932963580697518763985 90286449722685523139072989)
    ·
      refine ⟨33857418646007071177152371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90286449722685523139072989 33857418646007071177152371)
      ·
        refine ⟨50786127969010606765728557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33857418646007071177152371 50786127969010606765728557)
        ·
          refine ⟨19044797988378977537148209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50786127969010606765728557 19044797988378977537148209)
          ·
            refine ⟨14283598491284233152861157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19044797988378977537148209 14283598491284233152861157)
            ·
              refine ⟨2678174717115793716161467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14283598491284233152861157 2678174717115793716161467)
              ·
                refine ⟨4017262075673690574242201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2678174717115793716161467 4017262075673690574242201)
                ·
                  refine ⟨3012946556755267930681651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4017262075673690574242201 3012946556755267930681651)
                  ·
                    refine ⟨4519419835132901896022477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3012946556755267930681651 4519419835132901896022477)
                    ·
                      refine ⟨1694782438174838211008429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4519419835132901896022477 1694782438174838211008429)
                      ·
                        rfl

theorem cell23_3300577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 4, 1, 2, 1, 3].length) (baseStart_3300577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3300577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3300577 prefixEnd_3300577 := by exact prefixLift 3300577
  have htrace : WordTrace (prefixWord ++ tailWord_3300577) baseStart_3300577 baseEnd_3300577 := by
    simpa [prefixWord, tailWord_3300577, baseEnd_3300577] using wordTrace_append hprefix tailTrace_3300577
  have hstable : (prefixWord ++ tailWord_3300577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3300577).length < 2 ^ (prefixWord ++ tailWord_3300577).sum := by decide
  have hdescent : baseEnd_3300577 < baseStart_3300577 := by decide
  rcases family_descends (prefixWord ++ tailWord_3300577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3300587 : List Nat := [1, 1, 1, 1, 2, 8, 1, 2, 1, 3, 2]
def baseStart_3300587 : Nat := 118140960795 + 3300587 * 2 ^ 59
def prefixEnd_3300587 : Nat := 4983230072969 + 3 ^ 40 * 3300587 * 2
def baseEnd_3300587 : Nat := 1694787572981383171883383

theorem tailTrace_3300587 : CollatzResearch.WordTrace tailWord_3300587 prefixEnd_3300587 1694787572981383171883383 := by
  unfold tailWord_3300587
  simp only [CollatzResearch.WordTrace]
  refine ⟨120382297693544469226628015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80254865129029646151085343 120382297693544469226628015)
  ·
    refine ⟨180573446540316703839942023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120382297693544469226628015 180573446540316703839942023)
    ·
      refine ⟨270860169810475055759913035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180573446540316703839942023 270860169810475055759913035)
      ·
        refine ⟨406290254715712583639869553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270860169810475055759913035 406290254715712583639869553)
        ·
          refine ⟨304717691036784437729902165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 406290254715712583639869553 304717691036784437729902165)
          ·
            refine ⟨3570910441837317629647291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 304717691036784437729902165 3570910441837317629647291)
            ·
              refine ⟨5356365662755976444470937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3570910441837317629647291 5356365662755976444470937)
              ·
                refine ⟨4017274247066982333353203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5356365662755976444470937 4017274247066982333353203)
                ·
                  refine ⟨6025911370600473500029805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4017274247066982333353203 6025911370600473500029805)
                  ·
                    refine ⟨2259716763975177562511177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6025911370600473500029805 2259716763975177562511177)
                    ·
                      refine ⟨1694787572981383171883383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2259716763975177562511177 1694787572981383171883383)
                      ·
                        rfl

theorem cell23_3300587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 1, 2, 1, 3, 2].length) (baseStart_3300587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3300587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3300587 prefixEnd_3300587 := by exact prefixLift 3300587
  have htrace : WordTrace (prefixWord ++ tailWord_3300587) baseStart_3300587 baseEnd_3300587 := by
    simpa [prefixWord, tailWord_3300587, baseEnd_3300587] using wordTrace_append hprefix tailTrace_3300587
  have hstable : (prefixWord ++ tailWord_3300587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3300587).length < 2 ^ (prefixWord ++ tailWord_3300587).sum := by decide
  have hdescent : baseEnd_3300587 < baseStart_3300587 := by decide
  rcases family_descends (prefixWord ++ tailWord_3300587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3300604 : List Nat := [2, 2, 2, 1, 5, 1, 3, 1, 1, 3, 2]
def baseStart_3300604 : Nat := 118140960795 + 3300604 * 2 ^ 59
def prefixEnd_3300604 : Nat := 4983230072969 + 3 ^ 40 * 3300604 * 2
def baseEnd_3300604 : Nat := 1694796302152509605370805

theorem tailTrace_3300604 : CollatzResearch.WordTrace tailWord_3300604 prefixEnd_3300604 1694796302152509605370805 := by
  unfold tailWord_3300604
  simp only [CollatzResearch.WordTrace]
  refine ⟨60191458867241440564998433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80255278489655254086664577 60191458867241440564998433)
  ·
    refine ⟨45143594150431080423748825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60191458867241440564998433 45143594150431080423748825)
    ·
      refine ⟨33857695612823310317811619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45143594150431080423748825 33857695612823310317811619)
      ·
        refine ⟨50786543419234965476717429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33857695612823310317811619 50786543419234965476717429)
        ·
          refine ⟨4761238445553278013442259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 50786543419234965476717429 4761238445553278013442259)
          ·
            refine ⟨7141857668329917020163389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4761238445553278013442259 7141857668329917020163389)
            ·
              refine ⟨2678196625623718882561271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7141857668329917020163389 2678196625623718882561271)
              ·
                refine ⟨4017294938435578323841907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2678196625623718882561271 4017294938435578323841907)
                ·
                  refine ⟨6025942407653367485762861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4017294938435578323841907 6025942407653367485762861)
                  ·
                    refine ⟨2259728402870012807161073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6025942407653367485762861 2259728402870012807161073)
                    ·
                      refine ⟨1694796302152509605370805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2259728402870012807161073 1694796302152509605370805)
                      ·
                        rfl

theorem cell23_3300604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 3, 1, 1, 3, 2].length) (baseStart_3300604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3300604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3300604 prefixEnd_3300604 := by exact prefixLift 3300604
  have htrace : WordTrace (prefixWord ++ tailWord_3300604) baseStart_3300604 baseEnd_3300604 := by
    simpa [prefixWord, tailWord_3300604, baseEnd_3300604] using wordTrace_append hprefix tailTrace_3300604
  have hstable : (prefixWord ++ tailWord_3300604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3300604).length < 2 ^ (prefixWord ++ tailWord_3300604).sum := by decide
  have hdescent : baseEnd_3300604 < baseStart_3300604 := by decide
  rcases family_descends (prefixWord ++ tailWord_3300604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3300617 : List Nat := [1, 2, 1, 1, 3, 3, 4, 2, 2, 2, 2]
def baseStart_3300617 : Nat := 118140960795 + 3300617 * 2 ^ 59
def prefixEnd_3300617 : Nat := 4983230072969 + 3 ^ 40 * 3300617 * 2
def baseEnd_3300617 : Nat := 1694802977401018054508245

theorem tailTrace_3300617 : CollatzResearch.WordTrace tailWord_3300617 prefixEnd_3300617 1694802977401018054508245 := by
  unfold tailWord_3300617
  simp only [CollatzResearch.WordTrace]
  refine ⟨120383391883435784350220105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80255594588957189566813403 120383391883435784350220105)
  ·
    refine ⟨90287543912576838262665079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120383391883435784350220105 90287543912576838262665079)
    ·
      refine ⟨135431315868865257393997619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90287543912576838262665079 135431315868865257393997619)
      ·
        refine ⟨203146973803297886090996429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135431315868865257393997619 203146973803297886090996429)
        ·
          refine ⟨76180115176236707284123661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 203146973803297886090996429 76180115176236707284123661)
          ·
            refine ⟨28567543191088765231546373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76180115176236707284123661 28567543191088765231546373)
            ·
              refine ⟨5356414348329143480914945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28567543191088765231546373 5356414348329143480914945)
              ·
                refine ⟨4017310761246857610686209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5356414348329143480914945 4017310761246857610686209)
                ·
                  refine ⟨3012983070935143208014657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4017310761246857610686209 3012983070935143208014657)
                  ·
                    refine ⟨2259737303201357406010993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3012983070935143208014657 2259737303201357406010993)
                    ·
                      refine ⟨1694802977401018054508245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2259737303201357406010993 1694802977401018054508245)
                      ·
                        rfl

theorem cell23_3300617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4, 2, 2, 2, 2].length) (baseStart_3300617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3300617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3300617 prefixEnd_3300617 := by exact prefixLift 3300617
  have htrace : WordTrace (prefixWord ++ tailWord_3300617) baseStart_3300617 baseEnd_3300617 := by
    simpa [prefixWord, tailWord_3300617, baseEnd_3300617] using wordTrace_append hprefix tailTrace_3300617
  have hstable : (prefixWord ++ tailWord_3300617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3300617).length < 2 ^ (prefixWord ++ tailWord_3300617).sum := by decide
  have hdescent : baseEnd_3300617 < baseStart_3300617 := by decide
  rcases family_descends (prefixWord ++ tailWord_3300617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3300763 : List Nat := [1, 1, 1, 1, 1, 1, 2, 1, 9, 1, 4]
def baseStart_3300763 : Nat := 118140960795 + 3300763 * 2 ^ 59
def prefixEnd_3300763 : Nat := 4983230072969 + 3 ^ 40 * 3300763 * 2
def baseEnd_3300763 : Nat := 1694877945576574483282573

theorem tailTrace_3300763 : CollatzResearch.WordTrace tailWord_3300763 prefixEnd_3300763 1694877945576574483282573 := by
  unfold tailWord_3300763
  simp only [CollatzResearch.WordTrace]
  refine ⟨120388716940906851285034943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80259144627271234190023295 120388716940906851285034943)
  ·
    refine ⟨180583075411360276927552415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120388716940906851285034943 180583075411360276927552415)
    ·
      refine ⟨270874613117040415391328623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180583075411360276927552415 270874613117040415391328623)
      ·
        refine ⟨406311919675560623086992935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270874613117040415391328623 406311919675560623086992935)
        ·
          refine ⟨609467879513340934630489403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 406311919675560623086992935 609467879513340934630489403)
          ·
            refine ⟨914201819270011401945734105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 609467879513340934630489403 914201819270011401945734105)
            ·
              refine ⟨685651364452508551459300579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 914201819270011401945734105 685651364452508551459300579)
              ·
                refine ⟨1028477046678762827188950869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 685651364452508551459300579 1028477046678762827188950869)
                ·
                  refine ⟨6026232695383375940560259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 1028477046678762827188950869 6026232695383375940560259)
                  ·
                    refine ⟨9039349043075063910840389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6026232695383375940560259 9039349043075063910840389)
                    ·
                      refine ⟨1694877945576574483282573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9039349043075063910840389 1694877945576574483282573)
                      ·
                        rfl

theorem cell23_3300763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 9, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 9, 1, 4].length) (baseStart_3300763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3300763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3300763 prefixEnd_3300763 := by exact prefixLift 3300763
  have htrace : WordTrace (prefixWord ++ tailWord_3300763) baseStart_3300763 baseEnd_3300763 := by
    simpa [prefixWord, tailWord_3300763, baseEnd_3300763] using wordTrace_append hprefix tailTrace_3300763
  have hstable : (prefixWord ++ tailWord_3300763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3300763).length < 2 ^ (prefixWord ++ tailWord_3300763).sum := by decide
  have hdescent : baseEnd_3300763 < baseStart_3300763 := by decide
  rcases family_descends (prefixWord ++ tailWord_3300763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3300767 : List Nat := [1, 1, 2, 5, 1, 2, 1, 3, 2, 3, 2]
def baseStart_3300767 : Nat := 118140960795 + 3300767 * 2 ^ 59
def prefixEnd_3300767 : Nat := 4983230072969 + 3 ^ 40 * 3300767 * 2
def baseEnd_3300767 : Nat := 1694879999499192467632555

theorem tailTrace_3300767 : CollatzResearch.WordTrace tailWord_3300767 prefixEnd_3300767 1694879999499192467632555 := by
  unfold tailWord_3300767
  simp only [CollatzResearch.WordTrace]
  refine ⟨120388862832892359968180555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80259241888594906645453703 120388862832892359968180555)
  ·
    refine ⟨180583294249338539952270833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120388862832892359968180555 180583294249338539952270833)
    ·
      refine ⟨135437470687003904964203125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180583294249338539952270833 135437470687003904964203125)
      ·
        refine ⟨12697262876906616090394043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 135437470687003904964203125 12697262876906616090394043)
        ·
          refine ⟨19045894315359924135591065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12697262876906616090394043 19045894315359924135591065)
          ·
            refine ⟨14284420736519943101693299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19045894315359924135591065 14284420736519943101693299)
            ·
              refine ⟨21426631104779914652539949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14284420736519943101693299 21426631104779914652539949)
              ·
                refine ⟨8034986664292467994702481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21426631104779914652539949 8034986664292467994702481)
                ·
                  refine ⟨6026239998219350996026861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8034986664292467994702481 6026239998219350996026861)
                  ·
                    refine ⟨2259839999332256623510073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6026239998219350996026861 2259839999332256623510073)
                    ·
                      refine ⟨1694879999499192467632555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2259839999332256623510073 1694879999499192467632555)
                      ·
                        rfl

theorem cell23_3300767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 3, 2, 3, 2].length) (baseStart_3300767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3300767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3300767 prefixEnd_3300767 := by exact prefixLift 3300767
  have htrace : WordTrace (prefixWord ++ tailWord_3300767) baseStart_3300767 baseEnd_3300767 := by
    simpa [prefixWord, tailWord_3300767, baseEnd_3300767] using wordTrace_append hprefix tailTrace_3300767
  have hstable : (prefixWord ++ tailWord_3300767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3300767).length < 2 ^ (prefixWord ++ tailWord_3300767).sum := by decide
  have hdescent : baseEnd_3300767 < baseStart_3300767 := by decide
  rcases family_descends (prefixWord ++ tailWord_3300767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3300780 : List Nat := [2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 4]
def baseStart_3300780 : Nat := 118140960795 + 3300780 * 2 ^ 59
def prefixEnd_3300780 : Nat := 4983230072969 + 3 ^ 40 * 3300780 * 2
def baseEnd_3300780 : Nat := 1694886674747700916769995

theorem tailTrace_3300780 : CollatzResearch.WordTrace tailWord_3300780 prefixEnd_3300780 1694886674747700916769995 := by
  unfold tailWord_3300780
  simp only [CollatzResearch.WordTrace]
  refine ⟨60194668490922631594201897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80259557987896842125602529 60194668490922631594201897)
  ·
    refine ⟨45146001368191973695651423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60194668490922631594201897 45146001368191973695651423)
    ·
      refine ⟨67719002052287960543477135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45146001368191973695651423 67719002052287960543477135)
      ·
        refine ⟨101578503078431940815215703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67719002052287960543477135 101578503078431940815215703)
        ·
          refine ⟨152367754617647911222823555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101578503078431940815215703 152367754617647911222823555)
          ·
            refine ⟨228551631926471866834235333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152367754617647911222823555 228551631926471866834235333)
            ·
              refine ⟨42853430986213475031419125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 228551631926471866834235333 42853430986213475031419125)
              ·
                refine ⟨4017509154957513284195543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42853430986213475031419125 4017509154957513284195543)
                ·
                  refine ⟨6026263732436269926293315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4017509154957513284195543 6026263732436269926293315)
                  ·
                    refine ⟨9039395598654404889439973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6026263732436269926293315 9039395598654404889439973)
                    ·
                      refine ⟨1694886674747700916769995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9039395598654404889439973 1694886674747700916769995)
                      ·
                        rfl

theorem cell23_3300780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 4].length) (baseStart_3300780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3300780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3300780 prefixEnd_3300780 := by exact prefixLift 3300780
  have htrace : WordTrace (prefixWord ++ tailWord_3300780) baseStart_3300780 baseEnd_3300780 := by
    simpa [prefixWord, tailWord_3300780, baseEnd_3300780] using wordTrace_append hprefix tailTrace_3300780
  have hstable : (prefixWord ++ tailWord_3300780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3300780).length < 2 ^ (prefixWord ++ tailWord_3300780).sum := by decide
  have hdescent : baseEnd_3300780 < baseStart_3300780 := by decide
  rcases family_descends (prefixWord ++ tailWord_3300780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3300800 : List Nat := [2, 1, 1, 2, 3, 1, 3, 2, 3, 2, 3]
def baseStart_3300800 : Nat := 118140960795 + 3300800 * 2 ^ 59
def prefixEnd_3300800 : Nat := 4983230072969 + 3 ^ 40 * 3300800 * 2
def baseEnd_3300800 : Nat := 1694896944360790838519903

theorem tailTrace_3300800 : CollatzResearch.WordTrace tailWord_3300800 prefixEnd_3300800 1694896944360790838519903 := by
  unfold tailWord_3300800
  simp only [CollatzResearch.WordTrace]
  refine ⟨60195033220886403302065927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80260044294515204402754569 60195033220886403302065927)
  ·
    refine ⟨90292549831329604953098891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60195033220886403302065927 90292549831329604953098891)
    ·
      refine ⟨135438824746994407429648337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90292549831329604953098891 135438824746994407429648337)
      ·
        refine ⟨101579118560245805572236253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135438824746994407429648337 101579118560245805572236253)
        ·
          refine ⟨38092169460092177089588595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101579118560245805572236253 38092169460092177089588595)
          ·
            refine ⟨57138254190138265634382893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38092169460092177089588595 57138254190138265634382893)
            ·
              refine ⟨21426845321301849612893585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57138254190138265634382893 21426845321301849612893585)
              ·
                refine ⟨16070133990976387209670189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21426845321301849612893585 16070133990976387209670189)
                ·
                  refine ⟨6026300246616145203626321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16070133990976387209670189 6026300246616145203626321)
                  ·
                    refine ⟨4519725184962108902719741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6026300246616145203626321 4519725184962108902719741)
                    ·
                      refine ⟨1694896944360790838519903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4519725184962108902719741 1694896944360790838519903)
                      ·
                        rfl

theorem cell23_3300800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 2, 3, 2, 3].length) (baseStart_3300800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3300800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3300800 prefixEnd_3300800 := by exact prefixLift 3300800
  have htrace : WordTrace (prefixWord ++ tailWord_3300800) baseStart_3300800 baseEnd_3300800 := by
    simpa [prefixWord, tailWord_3300800, baseEnd_3300800] using wordTrace_append hprefix tailTrace_3300800
  have hstable : (prefixWord ++ tailWord_3300800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3300800).length < 2 ^ (prefixWord ++ tailWord_3300800).sum := by decide
  have hdescent : baseEnd_3300800 < baseStart_3300800 := by decide
  rcases family_descends (prefixWord ++ tailWord_3300800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3300803 : List Nat := [1, 1, 1, 3, 1, 1, 7, 8]
def baseStart_3300803 : Nat := 118140960795 + 3300803 * 2 ^ 59
def prefixEnd_3300803 : Nat := 4983230072969 + 3 ^ 40 * 3300803 * 2
def baseEnd_3300803 : Nat := 62774017955657567658607

theorem tailTrace_3300803 : CollatzResearch.WordTrace tailWord_3300803 prefixEnd_3300803 62774017955657567658607 := by
  unfold tailWord_3300803
  simp only [CollatzResearch.WordTrace]
  refine ⟨120390175860761938116491063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80260117240507958744327375 120390175860761938116491063)
  ·
    refine ⟨180585263791142907174736595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120390175860761938116491063 180585263791142907174736595)
    ·
      refine ⟨270877895686714360762104893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180585263791142907174736595 270877895686714360762104893)
      ·
        refine ⟨101579210882517885285789335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 270877895686714360762104893 101579210882517885285789335)
        ·
          refine ⟨152368816323776827928684003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101579210882517885285789335 152368816323776827928684003)
          ·
            refine ⟨228553224485665241893026005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152368816323776827928684003 228553224485665241893026005)
            ·
              refine ⟨5356716198882779106867797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 228553224485665241893026005 5356716198882779106867797)
              ·
                refine ⟨62774017955657567658607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5356716198882779106867797 62774017955657567658607)
                ·
                  rfl

theorem cell23_3300803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7, 8].length) (baseStart_3300803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3300803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3300803 prefixEnd_3300803 := by exact prefixLift 3300803
  have htrace : WordTrace (prefixWord ++ tailWord_3300803) baseStart_3300803 baseEnd_3300803 := by
    simpa [prefixWord, tailWord_3300803, baseEnd_3300803] using wordTrace_append hprefix tailTrace_3300803
  have hstable : (prefixWord ++ tailWord_3300803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3300803).length < 2 ^ (prefixWord ++ tailWord_3300803).sum := by decide
  have hdescent : baseEnd_3300803 < baseStart_3300803 := by decide
  rcases family_descends (prefixWord ++ tailWord_3300803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3300810 : List Nat := [3, 1, 2, 1, 2, 3, 1, 3, 1, 2, 4]
def baseStart_3300810 : Nat := 118140960795 + 3300810 * 2 ^ 59
def prefixEnd_3300810 : Nat := 4983230072969 + 3 ^ 40 * 3300810 * 2
def baseEnd_3300810 : Nat := 1694902079167335799394857

theorem tailTrace_3300810 : CollatzResearch.WordTrace tailWord_3300810 prefixEnd_3300810 1694902079167335799394857 := by
  unfold tailWord_3300810
  simp only [CollatzResearch.WordTrace]
  refine ⟨30097607792934144577998971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80260287447824385541330589 30097607792934144577998971)
  ·
    refine ⟨45146411689401216866998457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30097607792934144577998971 45146411689401216866998457)
    ·
      refine ⟨33859808767050912650248843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45146411689401216866998457 33859808767050912650248843)
      ·
        refine ⟨50789713150576368975373265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33859808767050912650248843 50789713150576368975373265)
        ·
          refine ⟨38092284862932276731529949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50789713150576368975373265 38092284862932276731529949)
          ·
            refine ⟨14284606823599603774323731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38092284862932276731529949 14284606823599603774323731)
            ·
              refine ⟨21426910235399405661485597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14284606823599603774323731 21426910235399405661485597)
              ·
                refine ⟨8035091338274777123057099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21426910235399405661485597 8035091338274777123057099)
                ·
                  refine ⟨12052637007412165684585649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8035091338274777123057099 12052637007412165684585649)
                  ·
                    refine ⟨9039477755559124263439237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12052637007412165684585649 9039477755559124263439237)
                    ·
                      refine ⟨1694902079167335799394857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9039477755559124263439237 1694902079167335799394857)
                      ·
                        rfl

theorem cell23_3300810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 3, 1, 2, 4].length) (baseStart_3300810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3300810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3300810 prefixEnd_3300810 := by exact prefixLift 3300810
  have htrace : WordTrace (prefixWord ++ tailWord_3300810) baseStart_3300810 baseEnd_3300810 := by
    simpa [prefixWord, tailWord_3300810, baseEnd_3300810] using wordTrace_append hprefix tailTrace_3300810
  have hstable : (prefixWord ++ tailWord_3300810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3300810).length < 2 ^ (prefixWord ++ tailWord_3300810).sum := by decide
  have hdescent : baseEnd_3300810 < baseStart_3300810 := by decide
  rcases family_descends (prefixWord ++ tailWord_3300810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3300831 : List Nat := [1, 1, 2, 3, 3, 1, 4, 3, 1, 2, 2]
def baseStart_3300831 : Nat := 118140960795 + 3300831 * 2 ^ 59
def prefixEnd_3300831 : Nat := 4983230072969 + 3 ^ 40 * 3300831 * 2
def baseEnd_3300831 : Nat := 1694912862261080217232261

theorem tailTrace_3300831 : CollatzResearch.WordTrace tailWord_3300831 prefixEnd_3300831 1694912862261080217232261 := by
  unfold tailWord_3300831
  simp only [CollatzResearch.WordTrace]
  refine ⟨120391197104660498898510347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80260798069773665932340231 120391197104660498898510347)
  ·
    refine ⟨180586795656990748347765521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120391197104660498898510347 180586795656990748347765521)
    ·
      refine ⟨135440096742743061260824141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180586795656990748347765521 135440096742743061260824141)
      ·
        refine ⟨50790036278528647972809053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135440096742743061260824141 50790036278528647972809053)
        ·
          refine ⟨19046263604448242989803395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50790036278528647972809053 19046263604448242989803395)
          ·
            refine ⟨28569395406672364484705093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19046263604448242989803395 28569395406672364484705093)
            ·
              refine ⟨5356761638751068340882205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28569395406672364484705093 5356761638751068340882205)
              ·
                refine ⟨2008785614531650627830827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5356761638751068340882205 2008785614531650627830827)
                ·
                  refine ⟨3013178421797475941746241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2008785614531650627830827 3013178421797475941746241)
                  ·
                    refine ⟨2259883816348106956309681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3013178421797475941746241 2259883816348106956309681)
                    ·
                      refine ⟨1694912862261080217232261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2259883816348106956309681 1694912862261080217232261)
                      ·
                        rfl

theorem cell23_3300831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4, 3, 1, 2, 2].length) (baseStart_3300831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3300831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3300831 prefixEnd_3300831 := by exact prefixLift 3300831
  have htrace : WordTrace (prefixWord ++ tailWord_3300831) baseStart_3300831 baseEnd_3300831 := by
    simpa [prefixWord, tailWord_3300831, baseEnd_3300831] using wordTrace_append hprefix tailTrace_3300831
  have hstable : (prefixWord ++ tailWord_3300831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3300831).length < 2 ^ (prefixWord ++ tailWord_3300831).sum := by decide
  have hdescent : baseEnd_3300831 < baseStart_3300831 := by decide
  rcases family_descends (prefixWord ++ tailWord_3300831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3300843 : List Nat := [1, 1, 1, 1, 2, 3, 2, 1, 4, 2, 5]
def baseStart_3300843 : Nat := 118140960795 + 3300843 * 2 ^ 59
def prefixEnd_3300843 : Nat := 4983230072969 + 3 ^ 40 * 3300843 * 2
def baseEnd_3300843 : Nat := 1694919024028934170282205

theorem tailTrace_3300843 : CollatzResearch.WordTrace tailWord_3300843 prefixEnd_3300843 1694919024028934170282205 := by
  unfold tailWord_3300843
  simp only [CollatzResearch.WordTrace]
  refine ⟨120391634780617024947947183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80261089853744683298631455 120391634780617024947947183)
  ·
    refine ⟨180587452170925537421920775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120391634780617024947947183 180587452170925537421920775)
    ·
      refine ⟨270881178256388306132881163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180587452170925537421920775 270881178256388306132881163)
      ·
        refine ⟨406321767384582459199321745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270881178256388306132881163 406321767384582459199321745)
        ·
          refine ⟨304741325538436844399491309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 406321767384582459199321745 304741325538436844399491309)
          ·
            refine ⟨114277997076913816649809241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 304741325538436844399491309 114277997076913816649809241)
            ·
              refine ⟨85708497807685362487356931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114277997076913816649809241 85708497807685362487356931)
              ·
                refine ⟨128562746711528043731035397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85708497807685362487356931 128562746711528043731035397)
                ·
                  refine ⟨24105515008411508199569137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 128562746711528043731035397 24105515008411508199569137)
                  ·
                    refine ⟨18079136256308631149676853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24105515008411508199569137 18079136256308631149676853)
                    ·
                      refine ⟨1694919024028934170282205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18079136256308631149676853 1694919024028934170282205)
                      ·
                        rfl

theorem cell23_3300843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 4, 2, 5].length) (baseStart_3300843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3300843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3300843 prefixEnd_3300843 := by exact prefixLift 3300843
  have htrace : WordTrace (prefixWord ++ tailWord_3300843) baseStart_3300843 baseEnd_3300843 := by
    simpa [prefixWord, tailWord_3300843, baseEnd_3300843] using wordTrace_append hprefix tailTrace_3300843
  have hstable : (prefixWord ++ tailWord_3300843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3300843).length < 2 ^ (prefixWord ++ tailWord_3300843).sum := by decide
  have hdescent : baseEnd_3300843 < baseStart_3300843 := by decide
  rcases family_descends (prefixWord ++ tailWord_3300843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3300863 : List Nat := [1, 1, 2, 2, 1, 2, 2, 3, 1, 8]
def baseStart_3300863 : Nat := 118140960795 + 3300863 * 2 ^ 59
def prefixEnd_3300863 : Nat := 4983230072969 + 3 ^ 40 * 3300863 * 2
def baseEnd_3300863 : Nat := 564976431214008030677371

theorem tailTrace_3300863 : CollatzResearch.WordTrace tailWord_3300863 prefixEnd_3300863 564976431214008030677371 := by
  unfold tailWord_3300863
  simp only [CollatzResearch.WordTrace]
  refine ⟨120392364240544568363675243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80261576160363045575783495 120392364240544568363675243)
  ·
    refine ⟨180588546360816852545512865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120392364240544568363675243 180588546360816852545512865)
    ·
      refine ⟨135441409770612639409134649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180588546360816852545512865 135441409770612639409134649)
      ·
        refine ⟨101581057327959479556850987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135441409770612639409134649 101581057327959479556850987)
        ·
          refine ⟨152371585991939219335276481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101581057327959479556850987 152371585991939219335276481)
          ·
            refine ⟨114278689493954414501457361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152371585991939219335276481 114278689493954414501457361)
            ·
              refine ⟨85709017120465810876093021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114278689493954414501457361 85709017120465810876093021)
              ·
                refine ⟨32140881420174679078534883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85709017120465810876093021 32140881420174679078534883)
                ·
                  refine ⟨48211322130262018617802325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32140881420174679078534883 48211322130262018617802325)
                  ·
                    refine ⟨564976431214008030677371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 48211322130262018617802325 564976431214008030677371)
                    ·
                      rfl

theorem cell23_3300863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 3, 1, 8].length) (baseStart_3300863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3300863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3300863 prefixEnd_3300863 := by exact prefixLift 3300863
  have htrace : WordTrace (prefixWord ++ tailWord_3300863) baseStart_3300863 baseEnd_3300863 := by
    simpa [prefixWord, tailWord_3300863, baseEnd_3300863] using wordTrace_append hprefix tailTrace_3300863
  have hstable : (prefixWord ++ tailWord_3300863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3300863).length < 2 ^ (prefixWord ++ tailWord_3300863).sum := by decide
  have hdescent : baseEnd_3300863 < baseStart_3300863 := by decide
  rcases family_descends (prefixWord ++ tailWord_3300863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3300874 : List Nat := [3, 1, 2, 2, 2, 2, 1, 4, 1, 3, 2]
def baseStart_3300874 : Nat := 118140960795 + 3300874 * 2 ^ 59
def prefixEnd_3300874 : Nat := 4983230072969 + 3 ^ 40 * 3300874 * 2
def baseEnd_3300874 : Nat := 1694934941929223548994563

theorem tailTrace_3300874 : CollatzResearch.WordTrace tailWord_3300874 prefixEnd_3300874 1694934941929223548994563 := by
  unfold tailWord_3300874
  simp only [CollatzResearch.WordTrace]
  refine ⟨30098191360876179310581419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80261843629003144828217117 30098191360876179310581419)
  ·
    refine ⟨45147287041314268965872129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30098191360876179310581419 45147287041314268965872129)
    ·
      refine ⟨33860465280985701724404097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45147287041314268965872129 33860465280985701724404097)
      ·
        refine ⟨25395348960739276293303073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33860465280985701724404097 25395348960739276293303073)
        ·
          refine ⟨19046511720554457219977305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25395348960739276293303073 19046511720554457219977305)
          ·
            refine ⟨14284883790415842914982979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19046511720554457219977305 14284883790415842914982979)
            ·
              refine ⟨21427325685623764372474469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14284883790415842914982979 21427325685623764372474469)
              ·
                refine ⟨4017623566054455819838963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21427325685623764372474469 4017623566054455819838963)
                ·
                  refine ⟨6026435349081683729758445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4017623566054455819838963 6026435349081683729758445)
                  ·
                    refine ⟨2259913255905631398659417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6026435349081683729758445 2259913255905631398659417)
                    ·
                      refine ⟨1694934941929223548994563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2259913255905631398659417 1694934941929223548994563)
                      ·
                        rfl

theorem cell23_3300874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 4, 1, 3, 2].length) (baseStart_3300874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3300874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3300874 prefixEnd_3300874 := by exact prefixLift 3300874
  have htrace : WordTrace (prefixWord ++ tailWord_3300874) baseStart_3300874 baseEnd_3300874 := by
    simpa [prefixWord, tailWord_3300874, baseEnd_3300874] using wordTrace_append hprefix tailTrace_3300874
  have hstable : (prefixWord ++ tailWord_3300874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3300874).length < 2 ^ (prefixWord ++ tailWord_3300874).sum := by decide
  have hdescent : baseEnd_3300874 < baseStart_3300874 := by decide
  rcases family_descends (prefixWord ++ tailWord_3300874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3300890 : List Nat := [3, 1, 1, 3, 1, 1, 1, 2, 1, 6, 3]
def baseStart_3300890 : Nat := 118140960795 + 3300890 * 2 ^ 59
def prefixEnd_3300890 : Nat := 4983230072969 + 3 ^ 40 * 3300890 * 2
def baseEnd_3300890 : Nat := 1694943157619695486394489

theorem tailTrace_3300890 : CollatzResearch.WordTrace tailWord_3300890 prefixEnd_3300890 1694943157619695486394489 := by
  unfold tailWord_3300890
  simp only [CollatzResearch.WordTrace]
  refine ⟨30098337252861687993727031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80262232674297834649938749 30098337252861687993727031)
  ·
    refine ⟨45147505879292531990590547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30098337252861687993727031 45147505879292531990590547)
    ·
      refine ⟨67721258818938797985885821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45147505879292531990590547 67721258818938797985885821)
      ·
        refine ⟨25395472057102049244707183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67721258818938797985885821 25395472057102049244707183)
        ·
          refine ⟨38093208085653073867060775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25395472057102049244707183 38093208085653073867060775)
          ·
            refine ⟨57139812128479610800591163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38093208085653073867060775 57139812128479610800591163)
            ·
              refine ⟨85709718192719416200886745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57139812128479610800591163 85709718192719416200886745)
              ·
                refine ⟨64282288644539562150665059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85709718192719416200886745 64282288644539562150665059)
                ·
                  refine ⟨96423432966809343225997589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64282288644539562150665059 96423432966809343225997589)
                  ·
                    refine ⟨4519848420319187963718637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 96423432966809343225997589 4519848420319187963718637)
                    ·
                      refine ⟨1694943157619695486394489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4519848420319187963718637 1694943157619695486394489)
                      ·
                        rfl

theorem cell23_3300890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 1, 6, 3].length) (baseStart_3300890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3300890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3300890 prefixEnd_3300890 := by exact prefixLift 3300890
  have htrace : WordTrace (prefixWord ++ tailWord_3300890) baseStart_3300890 baseEnd_3300890 := by
    simpa [prefixWord, tailWord_3300890, baseEnd_3300890] using wordTrace_append hprefix tailTrace_3300890
  have hstable : (prefixWord ++ tailWord_3300890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3300890).length < 2 ^ (prefixWord ++ tailWord_3300890).sum := by decide
  have hdescent : baseEnd_3300890 < baseStart_3300890 := by decide
  rcases family_descends (prefixWord ++ tailWord_3300890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3300921 : List Nat := [1, 2, 1, 5, 1, 3, 1, 3, 2, 2, 2]
def baseStart_3300921 : Nat := 118140960795 + 3300921 * 2 ^ 59
def prefixEnd_3300921 : Nat := 4983230072969 + 3 ^ 40 * 3300921 * 2
def baseEnd_3300921 : Nat := 1694959075519984865106847

theorem tailTrace_3300921 : CollatzResearch.WordTrace tailWord_3300921 prefixEnd_3300921 1694959075519984865106847 := by
  unfold tailWord_3300921
  simp only [CollatzResearch.WordTrace]
  refine ⟨120394479674334444269286617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80262986449556296179524411 120394479674334444269286617)
  ·
    refine ⟨90295859755750833201964963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120394479674334444269286617 90295859755750833201964963)
    ·
      refine ⟨135443789633626249802947445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90295859755750833201964963 135443789633626249802947445)
      ·
        refine ⟨12697855278152460919026323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 135443789633626249802947445 12697855278152460919026323)
        ·
          refine ⟨19046782917228691378539485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12697855278152460919026323 19046782917228691378539485)
          ·
            refine ⟨7142543593960759266952307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19046782917228691378539485 7142543593960759266952307)
            ·
              refine ⟨10713815390941138900428461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7142543593960759266952307 10713815390941138900428461)
              ·
                refine ⟨4017680771602927087660673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10713815390941138900428461 4017680771602927087660673)
                ·
                  refine ⟨3013260578702195315745505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4017680771602927087660673 3013260578702195315745505)
                  ·
                    refine ⟨2259945434026646486809129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3013260578702195315745505 2259945434026646486809129)
                    ·
                      refine ⟨1694959075519984865106847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2259945434026646486809129 1694959075519984865106847)
                      ·
                        rfl

theorem cell23_3300921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 3, 2, 2, 2].length) (baseStart_3300921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3300921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3300921 prefixEnd_3300921 := by exact prefixLift 3300921
  have htrace : WordTrace (prefixWord ++ tailWord_3300921) baseStart_3300921 baseEnd_3300921 := by
    simpa [prefixWord, tailWord_3300921, baseEnd_3300921] using wordTrace_append hprefix tailTrace_3300921
  have hstable : (prefixWord ++ tailWord_3300921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3300921).length < 2 ^ (prefixWord ++ tailWord_3300921).sum := by decide
  have hdescent : baseEnd_3300921 < baseStart_3300921 := by decide
  rcases family_descends (prefixWord ++ tailWord_3300921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3300960 : List Nat := [2, 1, 1, 3, 2, 1, 1, 2, 3, 3, 4]
def baseStart_3300960 : Nat := 118140960795 + 3300960 * 2 ^ 59
def prefixEnd_3300960 : Nat := 4983230072969 + 3 ^ 40 * 3300960 * 2
def baseEnd_3300960 : Nat := 1694979101265510212519167

theorem tailTrace_3300960 : CollatzResearch.WordTrace tailWord_3300960 prefixEnd_3300960 1694979101265510212519167 := by
  unfold tailWord_3300960
  simp only [CollatzResearch.WordTrace]
  refine ⟨60197951060596576964978167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80263934747462102619970889 60197951060596576964978167)
  ·
    refine ⟨90296926590894865447467251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60197951060596576964978167 90296926590894865447467251)
    ·
      refine ⟨135445389886342298171200877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90296926590894865447467251 135445389886342298171200877)
      ·
        refine ⟨50792021207378361814200329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135445389886342298171200877 50792021207378361814200329)
        ·
          refine ⟨38094015905533771360650247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50792021207378361814200329 38094015905533771360650247)
          ·
            refine ⟨57141023858300657040975371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38094015905533771360650247 57141023858300657040975371)
            ·
              refine ⟨85711535787450985561463057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57141023858300657040975371 85711535787450985561463057)
              ·
                refine ⟨64283651840588239171097293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85711535787450985561463057 64283651840588239171097293)
                ·
                  refine ⟨24106369440220589689161485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64283651840588239171097293 24106369440220589689161485)
                  ·
                    refine ⟨9039888540082721133435557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24106369440220589689161485 9039888540082721133435557)
                    ·
                      refine ⟨1694979101265510212519167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9039888540082721133435557 1694979101265510212519167)
                      ·
                        rfl

theorem cell23_3300960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3, 4].length) (baseStart_3300960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3300960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3300960 prefixEnd_3300960 := by exact prefixLift 3300960
  have htrace : WordTrace (prefixWord ++ tailWord_3300960) baseStart_3300960 baseEnd_3300960 := by
    simpa [prefixWord, tailWord_3300960, baseEnd_3300960] using wordTrace_append hprefix tailTrace_3300960
  have hstable : (prefixWord ++ tailWord_3300960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3300960).length < 2 ^ (prefixWord ++ tailWord_3300960).sum := by decide
  have hdescent : baseEnd_3300960 < baseStart_3300960 := by decide
  rcases family_descends (prefixWord ++ tailWord_3300960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3300987 : List Nat := [1, 1, 1, 1, 1, 4, 5, 2, 3, 4]
def baseStart_3300987 : Nat := 118140960795 + 3300987 * 2 ^ 59
def prefixEnd_3300987 : Nat := 4983230072969 + 3 ^ 40 * 3300987 * 2
def baseEnd_3300987 : Nat := 564997655081060535627181

theorem tailTrace_3300987 : CollatzResearch.WordTrace tailWord_3300987 prefixEnd_3300987 564997655081060535627181 := by
  unfold tailWord_3300987
  simp only [CollatzResearch.WordTrace]
  refine ⟨120396886892095337541189215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80264591261396891694126143 120396886892095337541189215)
  ·
    refine ⟨180595330338143006311783823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120396886892095337541189215 180595330338143006311783823)
    ·
      refine ⟨270892995507214509467675735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180595330338143006311783823 270892995507214509467675735)
      ·
        refine ⟨406339493260821764201513603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270892995507214509467675735 406339493260821764201513603)
        ·
          refine ⟨609509239891232646302270405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 406339493260821764201513603 609509239891232646302270405)
          ·
            refine ⟨114282982479606121181675701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 609509239891232646302270405 114282982479606121181675701)
            ·
              refine ⟨10714029607463073860782097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 114282982479606121181675701 10714029607463073860782097)
              ·
                refine ⟨8035522205597305395586573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10714029607463073860782097 8035522205597305395586573)
                ·
                  refine ⟨3013320827098989523344965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8035522205597305395586573 3013320827098989523344965)
                  ·
                    refine ⟨564997655081060535627181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3013320827098989523344965 564997655081060535627181)
                    ·
                      rfl

theorem cell23_3300987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 2, 3, 4].length) (baseStart_3300987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3300987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3300987 prefixEnd_3300987 := by exact prefixLift 3300987
  have htrace : WordTrace (prefixWord ++ tailWord_3300987) baseStart_3300987 baseEnd_3300987 := by
    simpa [prefixWord, tailWord_3300987, baseEnd_3300987] using wordTrace_append hprefix tailTrace_3300987
  have hstable : (prefixWord ++ tailWord_3300987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3300987).length < 2 ^ (prefixWord ++ tailWord_3300987).sum := by decide
  have hdescent : baseEnd_3300987 < baseStart_3300987 := by decide
  rcases family_descends (prefixWord ++ tailWord_3300987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3300997 : List Nat := [1, 3, 1, 1, 4, 1, 3, 1, 1, 4, 3]
def baseStart_3300997 : Nat := 118140960795 + 3300997 * 2 ^ 59
def prefixEnd_3300997 : Nat := 4983230072969 + 3 ^ 40 * 3300997 * 2
def baseEnd_3300997 : Nat := 1694998100049726567756497

theorem tailTrace_3300997 : CollatzResearch.WordTrace tailWord_3300997 prefixEnd_3300997 1694998100049726567756497 := by
  unfold tailWord_3300997
  simp only [CollatzResearch.WordTrace]
  refine ⟨120397251622059109249053245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80264834414706072832702163 120397251622059109249053245)
  ·
    refine ⟨45148969358272165968394967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120397251622059109249053245 45148969358272165968394967)
    ·
      refine ⟨67723454037408248952592451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45148969358272165968394967 67723454037408248952592451)
      ·
        refine ⟨101585181056112373428888677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67723454037408248952592451 101585181056112373428888677)
        ·
          refine ⟨19047221448021070017916627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101585181056112373428888677 19047221448021070017916627)
          ·
            refine ⟨28570832172031605026874941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19047221448021070017916627 28570832172031605026874941)
            ·
              refine ⟨10714062064511851885078103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28570832172031605026874941 10714062064511851885078103)
              ·
                refine ⟨16071093096767777827617155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10714062064511851885078103 16071093096767777827617155)
                ·
                  refine ⟨24106639645151666741425733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16071093096767777827617155 24106639645151666741425733)
                  ·
                    refine ⟨4519994933465937514017325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24106639645151666741425733 4519994933465937514017325)
                    ·
                      refine ⟨1694998100049726567756497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4519994933465937514017325 1694998100049726567756497)
                      ·
                        rfl

theorem cell23_3300997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 1, 1, 4, 3].length) (baseStart_3300997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3300997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3300997 prefixEnd_3300997 := by exact prefixLift 3300997
  have htrace : WordTrace (prefixWord ++ tailWord_3300997) baseStart_3300997 baseEnd_3300997 := by
    simpa [prefixWord, tailWord_3300997, baseEnd_3300997] using wordTrace_append hprefix tailTrace_3300997
  have hstable : (prefixWord ++ tailWord_3300997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3300997).length < 2 ^ (prefixWord ++ tailWord_3300997).sum := by decide
  have hdescent : baseEnd_3300997 < baseStart_3300997 := by decide
  rcases family_descends (prefixWord ++ tailWord_3300997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3301037 : List Nat := [1, 5, 2, 1, 1, 1, 1, 2, 1, 2, 6]
def baseStart_3301037 : Nat := 118140960795 + 3301037 * 2 ^ 59
def prefixEnd_3301037 : Nat := 4983230072969 + 3 ^ 40 * 3301037 * 2
def baseEnd_3301037 : Nat := 1695018639275906411256313

theorem tailTrace_3301037 : CollatzResearch.WordTrace tailWord_3301037 prefixEnd_3301037 1695018639275906411256313 := by
  unfold tailWord_3301037
  simp only [CollatzResearch.WordTrace]
  refine ⟨120398710541914196080509365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80265807027942797387006243 120398710541914196080509365)
  ·
    refine ⟨11287379113304455882547753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 120398710541914196080509365 11287379113304455882547753)
    ·
      refine ⟨8465534334978341911910815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11287379113304455882547753 8465534334978341911910815)
      ·
        refine ⟨12698301502467512867866223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8465534334978341911910815 12698301502467512867866223)
        ·
          refine ⟨19047452253701269301799335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12698301502467512867866223 19047452253701269301799335)
          ·
            refine ⟨28571178380551903952699003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19047452253701269301799335 28571178380551903952699003)
            ·
              refine ⟨42856767570827855929048505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28571178380551903952699003 42856767570827855929048505)
              ·
                refine ⟨32142575678120891946786379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42856767570827855929048505 32142575678120891946786379)
                ·
                  refine ⟨48213863517181337920179569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32142575678120891946786379 48213863517181337920179569)
                  ·
                    refine ⟨36160397637886003440134677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48213863517181337920179569 36160397637886003440134677)
                    ·
                      refine ⟨1695018639275906411256313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36160397637886003440134677 1695018639275906411256313)
                      ·
                        rfl

theorem cell23_3301037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_3301037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3301037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3301037 prefixEnd_3301037 := by exact prefixLift 3301037
  have htrace : WordTrace (prefixWord ++ tailWord_3301037) baseStart_3301037 baseEnd_3301037 := by
    simpa [prefixWord, tailWord_3301037, baseEnd_3301037] using wordTrace_append hprefix tailTrace_3301037
  have hstable : (prefixWord ++ tailWord_3301037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3301037).length < 2 ^ (prefixWord ++ tailWord_3301037).sum := by decide
  have hdescent : baseEnd_3301037 < baseStart_3301037 := by decide
  rcases family_descends (prefixWord ++ tailWord_3301037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3301040 : List Nat := [2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 7]
def baseStart_3301040 : Nat := 118140960795 + 3301040 * 2 ^ 59
def prefixEnd_3301040 : Nat := 4983230072969 + 3 ^ 40 * 3301040 * 2
def baseEnd_3301040 : Nat := 1695020179717869899518799

theorem tailTrace_3301040 : CollatzResearch.WordTrace tailWord_3301040 prefixEnd_3301040 1695020179717869899518799 := by
  unfold tailWord_3301040
  simp only [CollatzResearch.WordTrace]
  refine ⟨60199409980451663796434287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80265879973935551728579049 60199409980451663796434287)
  ·
    refine ⟨90299114970677495694651431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60199409980451663796434287 90299114970677495694651431)
    ·
      refine ⟨135448672456016243541977147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90299114970677495694651431 135448672456016243541977147)
      ·
        refine ⟨203173008684024365312965721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135448672456016243541977147 203173008684024365312965721)
        ·
          refine ⟨152379756513018273984724291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203173008684024365312965721 152379756513018273984724291)
          ·
            refine ⟨228569634769527410977086437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152379756513018273984724291 228569634769527410977086437)
            ·
              refine ⟨42856806519286389558203707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 228569634769527410977086437 42856806519286389558203707)
              ·
                refine ⟨64285209778929584337305561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42856806519286389558203707 64285209778929584337305561)
                ·
                  refine ⟨48213907334197188252979171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64285209778929584337305561 48213907334197188252979171)
                  ·
                    refine ⟨72320861001295782379468757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48213907334197188252979171 72320861001295782379468757)
                    ·
                      refine ⟨1695020179717869899518799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 72320861001295782379468757 1695020179717869899518799)
                      ·
                        rfl

theorem cell23_3301040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 7].length) (baseStart_3301040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3301040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3301040 prefixEnd_3301040 := by exact prefixLift 3301040
  have htrace : WordTrace (prefixWord ++ tailWord_3301040) baseStart_3301040 baseEnd_3301040 := by
    simpa [prefixWord, tailWord_3301040, baseEnd_3301040] using wordTrace_append hprefix tailTrace_3301040
  have hstable : (prefixWord ++ tailWord_3301040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3301040).length < 2 ^ (prefixWord ++ tailWord_3301040).sum := by decide
  have hdescent : baseEnd_3301040 < baseStart_3301040 := by decide
  rcases family_descends (prefixWord ++ tailWord_3301040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3301085 : List Nat := [1, 4, 3, 3, 2, 1, 2, 1, 6]
def baseStart_3301085 : Nat := 118140960795 + 3301085 * 2 ^ 59
def prefixEnd_3301085 : Nat := 4983230072969 + 3 ^ 40 * 3301085 * 2
def baseEnd_3301085 : Nat := 188338142927480247050677

theorem tailTrace_3301085 : CollatzResearch.WordTrace tailWord_3301085 prefixEnd_3301085 188338142927480247050677 := by
  unfold tailWord_3301085
  simp only [CollatzResearch.WordTrace]
  refine ⟨120400461245740300278256709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80266974163826866852171139 120400461245740300278256709)
  ·
    refine ⟨22575086483576306302173133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120400461245740300278256709 22575086483576306302173133)
    ·
      refine ⟨8465657431341114863314925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22575086483576306302173133 8465657431341114863314925)
      ·
        refine ⟨3174621536752918073743097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8465657431341114863314925 3174621536752918073743097)
        ·
          refine ⟨2380966152564688555307323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3174621536752918073743097 2380966152564688555307323)
          ·
            refine ⟨3571449228847032832960985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2380966152564688555307323 3571449228847032832960985)
            ·
              refine ⟨2678586921635274624720739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3571449228847032832960985 2678586921635274624720739)
              ·
                refine ⟨4017880382452911937081109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2678586921635274624720739 4017880382452911937081109)
                ·
                  refine ⟨188338142927480247050677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4017880382452911937081109 188338142927480247050677)
                  ·
                    rfl

theorem cell23_3301085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 2, 1, 6].length) (baseStart_3301085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3301085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3301085 prefixEnd_3301085 := by exact prefixLift 3301085
  have htrace : WordTrace (prefixWord ++ tailWord_3301085) baseStart_3301085 baseEnd_3301085 := by
    simpa [prefixWord, tailWord_3301085, baseEnd_3301085] using wordTrace_append hprefix tailTrace_3301085
  have hstable : (prefixWord ++ tailWord_3301085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3301085).length < 2 ^ (prefixWord ++ tailWord_3301085).sum := by decide
  have hdescent : baseEnd_3301085 < baseStart_3301085 := by decide
  rcases family_descends (prefixWord ++ tailWord_3301085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3301087 : List Nat := [1, 1, 2, 3, 2, 2, 1, 4, 1, 1, 5]
def baseStart_3301087 : Nat := 118140960795 + 3301087 * 2 ^ 59
def prefixEnd_3301087 : Nat := 4983230072969 + 3 ^ 40 * 3301087 * 2
def baseEnd_3301087 : Nat := 1695044313308631215631083

theorem tailTrace_3301087 : CollatzResearch.WordTrace tailWord_3301087 prefixEnd_3301087 1695044313308631215631083 := by
  unfold tailWord_3301087
  simp only [CollatzResearch.WordTrace]
  refine ⟨120400534191733054619829515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80267022794488703079886343 120400534191733054619829515)
  ·
    refine ⟨180600801287599581929744273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120400534191733054619829515 180600801287599581929744273)
    ·
      refine ⟨135450600965699686447308205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180600801287599581929744273 135450600965699686447308205)
      ·
        refine ⟨50793975362137382417740577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135450600965699686447308205 50793975362137382417740577)
        ·
          refine ⟨38095481521603036813305433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50793975362137382417740577 38095481521603036813305433)
          ·
            refine ⟨28571611141202277609979075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38095481521603036813305433 28571611141202277609979075)
            ·
              refine ⟨42857416711803416414968613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28571611141202277609979075 42857416711803416414968613)
              ·
                refine ⟨8035765633463140577806615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42857416711803416414968613 8035765633463140577806615)
                ·
                  refine ⟨12053648450194710866709923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8035765633463140577806615 12053648450194710866709923)
                  ·
                    refine ⟨18080472675292066300064885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12053648450194710866709923 18080472675292066300064885)
                    ·
                      refine ⟨1695044313308631215631083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18080472675292066300064885 1695044313308631215631083)
                      ·
                        rfl

theorem cell23_3301087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 4, 1, 1, 5].length) (baseStart_3301087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3301087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3301087 prefixEnd_3301087 := by exact prefixLift 3301087
  have htrace : WordTrace (prefixWord ++ tailWord_3301087) baseStart_3301087 baseEnd_3301087 := by
    simpa [prefixWord, tailWord_3301087, baseEnd_3301087] using wordTrace_append hprefix tailTrace_3301087
  have hstable : (prefixWord ++ tailWord_3301087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3301087).length < 2 ^ (prefixWord ++ tailWord_3301087).sum := by decide
  have hdescent : baseEnd_3301087 < baseStart_3301087 := by decide
  rcases family_descends (prefixWord ++ tailWord_3301087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3301097 : List Nat := [1, 2, 1, 1, 1, 2, 3, 5, 1, 2, 4]
def baseStart_3301097 : Nat := 118140960795 + 3301097 * 2 ^ 59
def prefixEnd_3301097 : Nat := 4983230072969 + 3 ^ 40 * 3301097 * 2
def baseEnd_3301097 : Nat := 1695049448115176176506037

theorem tailTrace_3301097 : CollatzResearch.WordTrace tailWord_3301097 prefixEnd_3301097 1695049448115176176506037 := by
  unfold tailWord_3301097
  simp only [CollatzResearch.WordTrace]
  refine ⟨120400898921696826327693545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80267265947797884218462363 120400898921696826327693545)
  ·
    refine ⟨90300674191272619745770159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120400898921696826327693545 90300674191272619745770159)
    ·
      refine ⟨135451011286908929618655239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90300674191272619745770159 135451011286908929618655239)
      ·
        refine ⟨203176516930363394427982859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135451011286908929618655239 203176516930363394427982859)
        ·
          refine ⟨304764775395545091641974289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203176516930363394427982859 304764775395545091641974289)
          ·
            refine ⟨228573581546658818731480717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 304764775395545091641974289 228573581546658818731480717)
            ·
              refine ⟨85715093079997057024305269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 228573581546658818731480717 85715093079997057024305269)
              ·
                refine ⟨8035789976249724096028619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 85715093079997057024305269 8035789976249724096028619)
                ·
                  refine ⟨12053684964374586144042929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8035789976249724096028619 12053684964374586144042929)
                  ·
                    refine ⟨9040263723280939608032197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12053684964374586144042929 9040263723280939608032197)
                    ·
                      refine ⟨1695049448115176176506037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9040263723280939608032197 1695049448115176176506037)
                      ·
                        rfl

theorem cell23_3301097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 5, 1, 2, 4].length) (baseStart_3301097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3301097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3301097 prefixEnd_3301097 := by exact prefixLift 3301097
  have htrace : WordTrace (prefixWord ++ tailWord_3301097) baseStart_3301097 baseEnd_3301097 := by
    simpa [prefixWord, tailWord_3301097, baseEnd_3301097] using wordTrace_append hprefix tailTrace_3301097
  have hstable : (prefixWord ++ tailWord_3301097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3301097).length < 2 ^ (prefixWord ++ tailWord_3301097).sum := by decide
  have hdescent : baseEnd_3301097 < baseStart_3301097 := by decide
  rcases family_descends (prefixWord ++ tailWord_3301097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3301101 : List Nat := [1, 5, 1, 2, 1, 2, 3, 2, 1, 1, 4]
def baseStart_3301101 : Nat := 118140960795 + 3301101 * 2 ^ 59
def prefixEnd_3301101 : Nat := 4983230072969 + 3 ^ 40 * 3301101 * 2
def baseEnd_3301101 : Nat := 1695051502037794160856019

theorem tailTrace_3301101 : CollatzResearch.WordTrace tailWord_3301101 prefixEnd_3301101 1695051502037794160856019 := by
  unfold tailWord_3301101
  simp only [CollatzResearch.WordTrace]
  refine ⟨120401044813682335010839157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80267363209121556673892771 120401044813682335010839157)
  ·
    refine ⟨11287597951282718907266171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 120401044813682335010839157 11287597951282718907266171)
    ·
      refine ⟨16931396926924078360899257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11287597951282718907266171 16931396926924078360899257)
      ·
        refine ⟨12698547695193058770674443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16931396926924078360899257 12698547695193058770674443)
        ·
          refine ⟨19047821542789588156011665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12698547695193058770674443 19047821542789588156011665)
          ·
            refine ⟨14285866157092191117008749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19047821542789588156011665 14285866157092191117008749)
            ·
              refine ⟨5357199808909571668878281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14285866157092191117008749 5357199808909571668878281)
              ·
                refine ⟨4017899856682178751658711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5357199808909571668878281 4017899856682178751658711)
                ·
                  refine ⟨6026849785023268127488067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4017899856682178751658711 6026849785023268127488067)
                  ·
                    refine ⟨9040274677534902191232101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6026849785023268127488067 9040274677534902191232101)
                    ·
                      refine ⟨1695051502037794160856019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9040274677534902191232101 1695051502037794160856019)
                      ·
                        rfl

theorem cell23_3301101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3, 2, 1, 1, 4].length) (baseStart_3301101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3301101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3301101 prefixEnd_3301101 := by exact prefixLift 3301101
  have htrace : WordTrace (prefixWord ++ tailWord_3301101) baseStart_3301101 baseEnd_3301101 := by
    simpa [prefixWord, tailWord_3301101, baseEnd_3301101] using wordTrace_append hprefix tailTrace_3301101
  have hstable : (prefixWord ++ tailWord_3301101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3301101).length < 2 ^ (prefixWord ++ tailWord_3301101).sum := by decide
  have hdescent : baseEnd_3301101 < baseStart_3301101 := by decide
  rcases family_descends (prefixWord ++ tailWord_3301101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3301104 : List Nat := [2, 1, 1, 1, 3, 1, 2, 6, 1, 2, 3]
def baseStart_3301104 : Nat := 118140960795 + 3301104 * 2 ^ 59
def prefixEnd_3301104 : Nat := 4983230072969 + 3 ^ 40 * 3301104 * 2
def baseEnd_3301104 : Nat := 1695053042479757649118505

theorem tailTrace_3301104 : CollatzResearch.WordTrace tailWord_3301104 prefixEnd_3301104 1695053042479757649118505 := by
  unfold tailWord_3301104
  simp only [CollatzResearch.WordTrace]
  refine ⟨60200577116335733261599183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80267436155114311015465577 60200577116335733261599183)
  ·
    refine ⟨90300865674503599892398775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60200577116335733261599183 90300865674503599892398775)
    ·
      refine ⟨135451298511755399838598163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90300865674503599892398775 135451298511755399838598163)
      ·
        refine ⟨203176947767633099757897245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135451298511755399838598163 203176947767633099757897245)
        ·
          refine ⟨76191355412862412409211467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 203176947767633099757897245 76191355412862412409211467)
          ·
            refine ⟨114287033119293618613817201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76191355412862412409211467 114287033119293618613817201)
            ·
              refine ⟨85715274839470213960362901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114287033119293618613817201 85715274839470213960362901)
              ·
                refine ⟨4017903508100166279392011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 85715274839470213960362901 4017903508100166279392011)
                ·
                  refine ⟨6026855262150249419088017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4017903508100166279392011 6026855262150249419088017)
                  ·
                    refine ⟨4520141446612687064316013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6026855262150249419088017 4520141446612687064316013)
                    ·
                      refine ⟨1695053042479757649118505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4520141446612687064316013 1695053042479757649118505)
                      ·
                        rfl

theorem cell23_3301104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 6, 1, 2, 3].length) (baseStart_3301104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3301104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3301104 prefixEnd_3301104 := by exact prefixLift 3301104
  have htrace : WordTrace (prefixWord ++ tailWord_3301104) baseStart_3301104 baseEnd_3301104 := by
    simpa [prefixWord, tailWord_3301104, baseEnd_3301104] using wordTrace_append hprefix tailTrace_3301104
  have hstable : (prefixWord ++ tailWord_3301104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3301104).length < 2 ^ (prefixWord ++ tailWord_3301104).sum := by decide
  have hdescent : baseEnd_3301104 < baseStart_3301104 := by decide
  rcases family_descends (prefixWord ++ tailWord_3301104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3301151 : List Nat := [1, 1, 2, 4, 2, 1, 1, 5, 2, 1, 3]
def baseStart_3301151 : Nat := 118140960795 + 3301151 * 2 ^ 59
def prefixEnd_3301151 : Nat := 4983230072969 + 3 ^ 40 * 3301151 * 2
def baseEnd_3301151 : Nat := 1695077176070518965230789

theorem tailTrace_3301151 : CollatzResearch.WordTrace tailWord_3301151 prefixEnd_3301151 1695077176070518965230789 := by
  unfold tailWord_3301151
  simp only [CollatzResearch.WordTrace]
  refine ⟨120402868463501193550159307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80268578975667462366772871 120402868463501193550159307)
  ·
    refine ⟨180604302695251790325238961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120402868463501193550159307 180604302695251790325238961)
    ·
      refine ⟨135453227021438842743929221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180604302695251790325238961 135453227021438842743929221)
      ·
        refine ⟨25397480066519783014486729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 135453227021438842743929221 25397480066519783014486729)
        ·
          refine ⟨19048110049889837260865047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25397480066519783014486729 19048110049889837260865047)
          ·
            refine ⟨28572165074834755891297571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19048110049889837260865047 28572165074834755891297571)
            ·
              refine ⟨42858247612252133836946357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28572165074834755891297571 42858247612252133836946357)
              ·
                refine ⟨4017960713648637547213721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42858247612252133836946357 4017960713648637547213721)
                ·
                  refine ⟨3013470535236478160410291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4017960713648637547213721 3013470535236478160410291)
                  ·
                    refine ⟨4520205802854717240615437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3013470535236478160410291 4520205802854717240615437)
                    ·
                      refine ⟨1695077176070518965230789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4520205802854717240615437 1695077176070518965230789)
                      ·
                        rfl

theorem cell23_3301151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 5, 2, 1, 3].length) (baseStart_3301151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3301151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3301151 prefixEnd_3301151 := by exact prefixLift 3301151
  have htrace : WordTrace (prefixWord ++ tailWord_3301151) baseStart_3301151 baseEnd_3301151 := by
    simpa [prefixWord, tailWord_3301151, baseEnd_3301151] using wordTrace_append hprefix tailTrace_3301151
  have hstable : (prefixWord ++ tailWord_3301151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3301151).length < 2 ^ (prefixWord ++ tailWord_3301151).sum := by decide
  have hdescent : baseEnd_3301151 < baseStart_3301151 := by decide
  rcases family_descends (prefixWord ++ tailWord_3301151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3301178 : List Nat := [3, 1, 1, 1, 5, 2, 1, 3, 1, 3, 2]
def baseStart_3301178 : Nat := 118140960795 + 3301178 * 2 ^ 59
def prefixEnd_3301178 : Nat := 4983230072969 + 3 ^ 40 * 3301178 * 2
def baseEnd_3301178 : Nat := 1695091040048190359593165

theorem tailTrace_3301178 : CollatzResearch.WordTrace tailWord_3301178 prefixEnd_3301178 1695091040048190359593165 := by
  unfold tailWord_3301178
  simp only [CollatzResearch.WordTrace]
  refine ⟨30100963308600844290348047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80269235489602251440928125 30100963308600844290348047)
  ·
    refine ⟨45151444962901266435522071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30100963308600844290348047 45151444962901266435522071)
    ·
      refine ⟨67727167444351899653283107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45151444962901266435522071 67727167444351899653283107)
      ·
        refine ⟨101590751166527849479924661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67727167444351899653283107 101590751166527849479924661)
        ·
          refine ⟨9524132921861985888742937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 101590751166527849479924661 9524132921861985888742937)
          ·
            refine ⟨7143099691396489416557203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9524132921861985888742937 7143099691396489416557203)
            ·
              refine ⟨10714649537094734124835805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7143099691396489416557203 10714649537094734124835805)
              ·
                refine ⟨4017993576410525296813427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10714649537094734124835805 4017993576410525296813427)
                ·
                  refine ⟨6026990364615787945220141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4017993576410525296813427 6026990364615787945220141)
                  ·
                    refine ⟨2260121386730920479457553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6026990364615787945220141 2260121386730920479457553)
                    ·
                      refine ⟨1695091040048190359593165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2260121386730920479457553 1695091040048190359593165)
                      ·
                        rfl

theorem cell23_3301178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 3, 1, 3, 2].length) (baseStart_3301178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3301178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3301178 prefixEnd_3301178 := by exact prefixLift 3301178
  have htrace : WordTrace (prefixWord ++ tailWord_3301178) baseStart_3301178 baseEnd_3301178 := by
    simpa [prefixWord, tailWord_3301178, baseEnd_3301178] using wordTrace_append hprefix tailTrace_3301178
  have hstable : (prefixWord ++ tailWord_3301178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3301178).length < 2 ^ (prefixWord ++ tailWord_3301178).sum := by decide
  have hdescent : baseEnd_3301178 < baseStart_3301178 := by decide
  rcases family_descends (prefixWord ++ tailWord_3301178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3301267 : List Nat := [1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 9]
def baseStart_3301267 : Nat := 118140960795 + 3301267 * 2 ^ 59
def prefixEnd_3301267 : Nat := 4983230072969 + 3 ^ 40 * 3301267 * 2
def baseEnd_3301267 : Nat := 1695136739826440511380255

theorem tailTrace_3301267 : CollatzResearch.WordTrace tailWord_3301267 prefixEnd_3301267 1695136739826440511380255 := by
  unfold tailWord_3301267
  simp only [CollatzResearch.WordTrace]
  refine ⟨120407099331080945361382055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80271399554053963574254703 120407099331080945361382055)
  ·
    refine ⟨180610648996621418042073083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120407099331080945361382055 180610648996621418042073083)
    ·
      refine ⟨270915973494932127063109625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180610648996621418042073083 270915973494932127063109625)
      ·
        refine ⟨203186980121199095297332219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 270915973494932127063109625 203186980121199095297332219)
        ·
          refine ⟨304780470181798642945998329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203186980121199095297332219 304780470181798642945998329)
          ·
            refine ⟨228585352636348982209498747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 304780470181798642945998329 228585352636348982209498747)
            ·
              refine ⟨342878028954523473314248121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 228585352636348982209498747 342878028954523473314248121)
              ·
                refine ⟨257158521715892604985686091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 342878028954523473314248121 257158521715892604985686091)
                ·
                  refine ⟨385737782573838907478529137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 257158521715892604985686091 385737782573838907478529137)
                  ·
                    refine ⟨289303336930379180608896853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 385737782573838907478529137 289303336930379180608896853)
                    ·
                      refine ⟨1695136739826440511380255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 289303336930379180608896853 1695136739826440511380255)
                      ·
                        rfl

theorem cell23_3301267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 9].length) (baseStart_3301267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3301267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3301267 prefixEnd_3301267 := by exact prefixLift 3301267
  have htrace : WordTrace (prefixWord ++ tailWord_3301267) baseStart_3301267 baseEnd_3301267 := by
    simpa [prefixWord, tailWord_3301267, baseEnd_3301267] using wordTrace_append hprefix tailTrace_3301267
  have hstable : (prefixWord ++ tailWord_3301267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3301267).length < 2 ^ (prefixWord ++ tailWord_3301267).sum := by decide
  have hdescent : baseEnd_3301267 < baseStart_3301267 := by decide
  rcases family_descends (prefixWord ++ tailWord_3301267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3301381 : List Nat := [1, 3, 1, 1, 2, 4, 3, 1, 1, 6]
def baseStart_3301381 : Nat := 118140960795 + 3301381 * 2 ^ 59
def prefixEnd_3301381 : Nat := 4983230072969 + 3 ^ 40 * 3301381 * 2
def baseEnd_3301381 : Nat := 565065092207017688451577

theorem tailTrace_3301381 : CollatzResearch.WordTrace tailWord_3301381 prefixEnd_3301381 565065092207017688451577 := by
  unfold tailWord_3301381
  simp only [CollatzResearch.WordTrace]
  refine ⟨120411257252667942831031997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80274171501778628554021331 120411257252667942831031997)
  ·
    refine ⟨45154221469750478561636999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120411257252667942831031997 45154221469750478561636999)
    ·
      refine ⟨67731332204625717842455499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45154221469750478561636999 67731332204625717842455499)
      ·
        refine ⟨101596998306938576763683249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67731332204625717842455499 101596998306938576763683249)
        ·
          refine ⟨76197748730203932572762437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101596998306938576763683249 76197748730203932572762437)
          ·
            refine ⟨14287077886913237357392957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76197748730203932572762437 14287077886913237357392957)
            ·
              refine ⟨5357654207592464009022359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14287077886913237357392957 5357654207592464009022359)
              ·
                refine ⟨8036481311388696013533539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5357654207592464009022359 8036481311388696013533539)
                ·
                  refine ⟨12054721967083044020300309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8036481311388696013533539 12054721967083044020300309)
                  ·
                    refine ⟨565065092207017688451577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12054721967083044020300309 565065092207017688451577)
                    ·
                      rfl

theorem cell23_3301381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 6].length) (baseStart_3301381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3301381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3301381 prefixEnd_3301381 := by exact prefixLift 3301381
  have htrace : WordTrace (prefixWord ++ tailWord_3301381) baseStart_3301381 baseEnd_3301381 := by
    simpa [prefixWord, tailWord_3301381, baseEnd_3301381] using wordTrace_append hprefix tailTrace_3301381
  have hstable : (prefixWord ++ tailWord_3301381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3301381).length < 2 ^ (prefixWord ++ tailWord_3301381).sum := by decide
  have hdescent : baseEnd_3301381 < baseStart_3301381 := by decide
  rcases family_descends (prefixWord ++ tailWord_3301381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3301388 : List Nat := [2, 2, 1, 2, 3, 1, 4, 2, 1, 1, 4]
def baseStart_3301388 : Nat := 118140960795 + 3301388 * 2 ^ 59
def prefixEnd_3301388 : Nat := 4983230072969 + 3 ^ 40 * 3301388 * 2
def baseEnd_3301388 : Nat := 1695198870985634537967199

theorem tailTrace_3301388 : CollatzResearch.WordTrace tailWord_3301388 prefixEnd_3301388 1695198870985634537967199 := by
  unfold tailWord_3301388
  simp only [CollatzResearch.WordTrace]
  refine ⟨60205756281821291513268409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80274341709095055351024545 60205756281821291513268409)
  ·
    refine ⟨45154317211365968634951307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60205756281821291513268409 45154317211365968634951307)
    ·
      refine ⟨67731475817048952952426961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45154317211365968634951307 67731475817048952952426961)
      ·
        refine ⟨50798606862786714714320221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67731475817048952952426961 50798606862786714714320221)
        ·
          refine ⟨19049477573545018017870083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50798606862786714714320221 19049477573545018017870083)
          ·
            refine ⟨28574216360317527026805125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19049477573545018017870083 28574216360317527026805125)
            ·
              refine ⟨5357665567559536317525961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28574216360317527026805125 5357665567559536317525961)
              ·
                refine ⟨4018249175669652238144471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5357665567559536317525961 4018249175669652238144471)
                ·
                  refine ⟨6027373763504478357216707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4018249175669652238144471 6027373763504478357216707)
                  ·
                    refine ⟨9041060645256717535825061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6027373763504478357216707 9041060645256717535825061)
                    ·
                      refine ⟨1695198870985634537967199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9041060645256717535825061 1695198870985634537967199)
                      ·
                        rfl

theorem cell23_3301388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4, 2, 1, 1, 4].length) (baseStart_3301388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3301388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3301388 prefixEnd_3301388 := by exact prefixLift 3301388
  have htrace : WordTrace (prefixWord ++ tailWord_3301388) baseStart_3301388 baseEnd_3301388 := by
    simpa [prefixWord, tailWord_3301388, baseEnd_3301388] using wordTrace_append hprefix tailTrace_3301388
  have hstable : (prefixWord ++ tailWord_3301388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3301388).length < 2 ^ (prefixWord ++ tailWord_3301388).sum := by decide
  have hdescent : baseEnd_3301388 < baseStart_3301388 := by decide
  rcases family_descends (prefixWord ++ tailWord_3301388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3301399 : List Nat := [1, 1, 3, 5, 2, 2, 1, 3, 1, 1, 3]
def baseStart_3301399 : Nat := 118140960795 + 3301399 * 2 ^ 59
def prefixEnd_3301399 : Nat := 4983230072969 + 3 ^ 40 * 3301399 * 2
def baseEnd_3301399 : Nat := 1695204519272833994929649

theorem tailTrace_3301399 : CollatzResearch.WordTrace tailWord_3301399 prefixEnd_3301399 1695204519272833994929649 := by
  unfold tailWord_3301399
  simp only [CollatzResearch.WordTrace]
  refine ⟨120411913766602731905187251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80274609177735154603458167 120411913766602731905187251)
  ·
    refine ⟨180617870649904097857780877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120411913766602731905187251 180617870649904097857780877)
    ·
      refine ⟨67731701493714036696667829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180617870649904097857780877 67731701493714036696667829)
      ·
        refine ⟨6349847015035690940312609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 67731701493714036696667829 6349847015035690940312609)
        ·
          refine ⟨4762385261276768205234457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6349847015035690940312609 4762385261276768205234457)
          ·
            refine ⟨3571788945957576153925843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4762385261276768205234457 3571788945957576153925843)
            ·
              refine ⟨5357683418936364230888765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3571788945957576153925843 5357683418936364230888765)
              ·
                refine ⟨2009131282101136586583287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5357683418936364230888765 2009131282101136586583287)
                ·
                  refine ⟨3013696923151704879874931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2009131282101136586583287 3013696923151704879874931)
                  ·
                    refine ⟨4520545384727557319812397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3013696923151704879874931 4520545384727557319812397)
                    ·
                      refine ⟨1695204519272833994929649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4520545384727557319812397 1695204519272833994929649)
                      ·
                        rfl

theorem cell23_3301399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 1, 3, 1, 1, 3].length) (baseStart_3301399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3301399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3301399 prefixEnd_3301399 := by exact prefixLift 3301399
  have htrace : WordTrace (prefixWord ++ tailWord_3301399) baseStart_3301399 baseEnd_3301399 := by
    simpa [prefixWord, tailWord_3301399, baseEnd_3301399] using wordTrace_append hprefix tailTrace_3301399
  have hstable : (prefixWord ++ tailWord_3301399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3301399).length < 2 ^ (prefixWord ++ tailWord_3301399).sum := by decide
  have hdescent : baseEnd_3301399 < baseStart_3301399 := by decide
  rcases family_descends (prefixWord ++ tailWord_3301399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3301416 : List Nat := [2, 1, 5, 3, 1, 1, 3, 2, 1, 1, 3]
def baseStart_3301416 : Nat := 118140960795 + 3301416 * 2 ^ 59
def prefixEnd_3301416 : Nat := 4983230072969 + 3 ^ 40 * 3301416 * 2
def baseEnd_3301416 : Nat := 1695213248443960428417071

theorem tailTrace_3301416 : CollatzResearch.WordTrace tailWord_3301416 prefixEnd_3301416 1695213248443960428417071 := by
  unfold tailWord_3301416
  simp only [CollatzResearch.WordTrace]
  refine ⟨60206266903770571904278051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80275022538360762539037401 60206266903770571904278051)
  ·
    refine ⟨90309400355655857856417077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60206266903770571904278051 90309400355655857856417077)
    ·
      refine ⟨8466506283342736674039101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 90309400355655857856417077 8466506283342736674039101)
      ·
        refine ⟨3174939856253526252764663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8466506283342736674039101 3174939856253526252764663)
        ·
          refine ⟨4762409784380289379146995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3174939856253526252764663 4762409784380289379146995)
          ·
            refine ⟨7143614676570434068720493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4762409784380289379146995 7143614676570434068720493)
            ·
              refine ⟨2678855503713912775770185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7143614676570434068720493 2678855503713912775770185)
              ·
                refine ⟨2009141627785434581827639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2678855503713912775770185 2009141627785434581827639)
                ·
                  refine ⟨3013712441678151872741459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2009141627785434581827639 3013712441678151872741459)
                  ·
                    refine ⟨4520568662517227809112189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3013712441678151872741459 4520568662517227809112189)
                    ·
                      refine ⟨1695213248443960428417071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4520568662517227809112189 1695213248443960428417071)
                      ·
                        rfl

theorem cell23_3301416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_3301416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3301416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3301416 prefixEnd_3301416 := by exact prefixLift 3301416
  have htrace : WordTrace (prefixWord ++ tailWord_3301416) baseStart_3301416 baseEnd_3301416 := by
    simpa [prefixWord, tailWord_3301416, baseEnd_3301416] using wordTrace_append hprefix tailTrace_3301416
  have hstable : (prefixWord ++ tailWord_3301416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3301416).length < 2 ^ (prefixWord ++ tailWord_3301416).sum := by decide
  have hdescent : baseEnd_3301416 < baseStart_3301416 := by decide
  rcases family_descends (prefixWord ++ tailWord_3301416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3301422 : List Nat := [4, 1, 3, 1, 1, 2, 3, 1, 3, 2, 2]
def baseStart_3301422 : Nat := 118140960795 + 3301422 * 2 ^ 59
def prefixEnd_3301422 : Nat := 4983230072969 + 3 ^ 40 * 3301422 * 2
def baseEnd_3301422 : Nat := 1695216329327887404942043

theorem tailTrace_3301422 : CollatzResearch.WordTrace tailWord_3301422 prefixEnd_3301422 1695216329327887404942043 := by
  unfold tailWord_3301422
  simp only [CollatzResearch.WordTrace]
  refine ⟨15051594080689925854159315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80275168430346271222183013 15051594080689925854159315)
  ·
    refine ⟨22577391121034888781238973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15051594080689925854159315 22577391121034888781238973)
    ·
      refine ⟨8466521670388083292964615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22577391121034888781238973 8466521670388083292964615)
      ·
        refine ⟨12699782505582124939446923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8466521670388083292964615 12699782505582124939446923)
        ·
          refine ⟨19049673758373187409170385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12699782505582124939446923 19049673758373187409170385)
          ·
            refine ⟨14287255318779890556877789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19049673758373187409170385 14287255318779890556877789)
            ·
              refine ⟨5357720744542458958829171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14287255318779890556877789 5357720744542458958829171)
              ·
                refine ⟨8036581116813688438243757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5357720744542458958829171 8036581116813688438243757)
                ·
                  refine ⟨3013717918805133164341409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8036581116813688438243757 3013717918805133164341409)
                  ·
                    refine ⟨2260288439103849873256057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3013717918805133164341409 2260288439103849873256057)
                    ·
                      refine ⟨1695216329327887404942043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2260288439103849873256057 1695216329327887404942043)
                      ·
                        rfl

theorem cell23_3301422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3, 1, 3, 2, 2].length) (baseStart_3301422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3301422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3301422 prefixEnd_3301422 := by exact prefixLift 3301422
  have htrace : WordTrace (prefixWord ++ tailWord_3301422) baseStart_3301422 baseEnd_3301422 := by
    simpa [prefixWord, tailWord_3301422, baseEnd_3301422] using wordTrace_append hprefix tailTrace_3301422
  have hstable : (prefixWord ++ tailWord_3301422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3301422).length < 2 ^ (prefixWord ++ tailWord_3301422).sum := by decide
  have hdescent : baseEnd_3301422 < baseStart_3301422 := by decide
  rcases family_descends (prefixWord ++ tailWord_3301422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3301432 : List Nat := [2, 1, 2, 1, 6, 2, 2, 1, 2, 4]
def baseStart_3301432 : Nat := 118140960795 + 3301432 * 2 ^ 59
def prefixEnd_3301432 : Nat := 4983230072969 + 3 ^ 40 * 3301432 * 2
def baseEnd_3301432 : Nat := 565073821378144121938999

theorem tailTrace_3301432 : CollatzResearch.WordTrace tailWord_3301432 prefixEnd_3301432 565073821378144121938999 := by
  unfold tailWord_3301432
  simp only [CollatzResearch.WordTrace]
  refine ⟨60206558687741589270569275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80275411583655452360759033 60206558687741589270569275)
  ·
    refine ⟨90309838031612383905853913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60206558687741589270569275 90309838031612383905853913)
    ·
      refine ⟨67732378523709287929390435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90309838031612383905853913 67732378523709287929390435)
      ·
        refine ⟨101598567785563931894085653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67732378523709287929390435 101598567785563931894085653)
        ·
          refine ⟨4762432864948309307535265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 101598567785563931894085653 4762432864948309307535265)
          ·
            refine ⟨3571824648711231980651449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4762432864948309307535265 3571824648711231980651449)
            ·
              refine ⟨2678868486533423985488587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3571824648711231980651449 2678868486533423985488587)
              ·
                refine ⟨4018302729800135978232881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2678868486533423985488587 4018302729800135978232881)
                ·
                  refine ⟨3013727047350101983674661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4018302729800135978232881 3013727047350101983674661)
                  ·
                    refine ⟨565073821378144121938999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3013727047350101983674661 565073821378144121938999)
                    ·
                      rfl

theorem cell23_3301432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 2, 1, 2, 4].length) (baseStart_3301432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3301432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3301432 prefixEnd_3301432 := by exact prefixLift 3301432
  have htrace : WordTrace (prefixWord ++ tailWord_3301432) baseStart_3301432 baseEnd_3301432 := by
    simpa [prefixWord, tailWord_3301432, baseEnd_3301432] using wordTrace_append hprefix tailTrace_3301432
  have hstable : (prefixWord ++ tailWord_3301432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3301432).length < 2 ^ (prefixWord ++ tailWord_3301432).sum := by decide
  have hdescent : baseEnd_3301432 < baseStart_3301432 := by decide
  rcases family_descends (prefixWord ++ tailWord_3301432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3301481 : List Nat := [1, 2, 1, 1, 1, 5, 1, 1, 1, 6, 3]
def baseStart_3301481 : Nat := 118140960795 + 3301481 * 2 ^ 59
def prefixEnd_3301481 : Nat := 4983230072969 + 3 ^ 40 * 3301481 * 2
def baseEnd_3301481 : Nat := 1695246624686502674104271

theorem tailTrace_3301481 : CollatzResearch.WordTrace tailWord_3301481 prefixEnd_3301481 1695246624686502674104271 := by
  unfold tailWord_3301481
  simp only [CollatzResearch.WordTrace]
  refine ⟨120414904552305659909672297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80276603034870439939781531 120414904552305659909672297)
  ·
    refine ⟨90311178414229244932254223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120414904552305659909672297 90311178414229244932254223)
    ·
      refine ⟨135466767621343867398381335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90311178414229244932254223 135466767621343867398381335)
      ·
        refine ⟨203200151432015801097572003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135466767621343867398381335 203200151432015801097572003)
        ·
          refine ⟨304800227148023701646358005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203200151432015801097572003 304800227148023701646358005)
          ·
            refine ⟨28575021295127222029346063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 304800227148023701646358005 28575021295127222029346063)
            ·
              refine ⟨42862531942690833044019095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28575021295127222029346063 42862531942690833044019095)
              ·
                refine ⟨64293797914036249566028643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42862531942690833044019095 64293797914036249566028643)
                ·
                  refine ⟨96440696871054374349042965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64293797914036249566028643 96440696871054374349042965)
                  ·
                    refine ⟨4520657665830673797611389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 96440696871054374349042965 4520657665830673797611389)
                    ·
                      refine ⟨1695246624686502674104271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4520657665830673797611389 1695246624686502674104271)
                      ·
                        rfl

theorem cell23_3301481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 6, 3].length) (baseStart_3301481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3301481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3301481 prefixEnd_3301481 := by exact prefixLift 3301481
  have htrace : WordTrace (prefixWord ++ tailWord_3301481) baseStart_3301481 baseEnd_3301481 := by
    simpa [prefixWord, tailWord_3301481, baseEnd_3301481] using wordTrace_append hprefix tailTrace_3301481
  have hstable : (prefixWord ++ tailWord_3301481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3301481).length < 2 ^ (prefixWord ++ tailWord_3301481).sum := by decide
  have hdescent : baseEnd_3301481 < baseStart_3301481 := by decide
  rcases family_descends (prefixWord ++ tailWord_3301481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3301495 : List Nat := [1, 1, 3, 1, 1, 6, 2, 1, 1, 4, 2]
def baseStart_3301495 : Nat := 118140960795 + 3301495 * 2 ^ 59
def prefixEnd_3301495 : Nat := 4983230072969 + 3 ^ 40 * 3301495 * 2
def baseEnd_3301495 : Nat := 1695253813415665619329207

theorem tailTrace_3301495 : CollatzResearch.WordTrace tailWord_3301495 prefixEnd_3301495 1695253813415665619329207 := by
  unfold tailWord_3301495
  simp only [CollatzResearch.WordTrace]
  refine ⟨120415415174254940300681939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80276943449503293533787959 120415415174254940300681939)
  ·
    refine ⟨180623122761382410451022909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120415415174254940300681939 180623122761382410451022909)
    ·
      refine ⟨67733671035518403919133591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180623122761382410451022909 67733671035518403919133591)
      ·
        refine ⟨101600506553277605878700387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67733671035518403919133591 101600506553277605878700387)
        ·
          refine ⟨152400759829916408818050581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101600506553277605878700387 152400759829916408818050581)
          ·
            refine ⟨7143785617027331663346121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 152400759829916408818050581 7143785617027331663346121)
            ·
              refine ⟨5357839212770498747509591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7143785617027331663346121 5357839212770498747509591)
              ·
                refine ⟨8036758819155748121264387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5357839212770498747509591 8036758819155748121264387)
                ·
                  refine ⟨12055138228733622181896581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8036758819155748121264387 12055138228733622181896581)
                  ·
                    refine ⟨2260338417887554159105609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12055138228733622181896581 2260338417887554159105609)
                    ·
                      refine ⟨1695253813415665619329207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2260338417887554159105609 1695253813415665619329207)
                      ·
                        rfl

theorem cell23_3301495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2, 1, 1, 4, 2].length) (baseStart_3301495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3301495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3301495 prefixEnd_3301495 := by exact prefixLift 3301495
  have htrace : WordTrace (prefixWord ++ tailWord_3301495) baseStart_3301495 baseEnd_3301495 := by
    simpa [prefixWord, tailWord_3301495, baseEnd_3301495] using wordTrace_append hprefix tailTrace_3301495
  have hstable : (prefixWord ++ tailWord_3301495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3301495).length < 2 ^ (prefixWord ++ tailWord_3301495).sum := by decide
  have hdescent : baseEnd_3301495 < baseStart_3301495 := by decide
  rcases family_descends (prefixWord ++ tailWord_3301495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3301501 : List Nat := [1, 4, 1, 1, 3, 2, 1, 1, 9]
def baseStart_3301501 : Nat := 118140960795 + 3301501 * 2 ^ 59
def prefixEnd_3301501 : Nat := 4983230072969 + 3 ^ 40 * 3301501 * 2
def baseEnd_3301501 : Nat := 188361877144399177317131

theorem tailTrace_3301501 : CollatzResearch.WordTrace tailWord_3301501 prefixEnd_3301501 188361877144399177317131 := by
  unfold tailWord_3301501
  simp only [CollatzResearch.WordTrace]
  refine ⟨120415634012233203325400357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80277089341488802216933571 120415634012233203325400357)
  ·
    refine ⟨22577931377293725623512567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120415634012233203325400357 22577931377293725623512567)
    ·
      refine ⟨33866897065940588435268851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22577931377293725623512567 33866897065940588435268851)
      ·
        refine ⟨50800345598910882652903277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33866897065940588435268851 50800345598910882652903277)
        ·
          refine ⟨19050129599591580994838729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50800345598910882652903277 19050129599591580994838729)
          ·
            refine ⟨14287597199693685746129047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19050129599591580994838729 14287597199693685746129047)
            ·
              refine ⟨21431395799540528619193571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14287597199693685746129047 21431395799540528619193571)
              ·
                refine ⟨32147093699310792928790357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21431395799540528619193571 32147093699310792928790357)
                ·
                  refine ⟨188361877144399177317131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 32147093699310792928790357 188361877144399177317131)
                  ·
                    rfl

theorem cell23_3301501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 1, 9].length) (baseStart_3301501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3301501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3301501 prefixEnd_3301501 := by exact prefixLift 3301501
  have htrace : WordTrace (prefixWord ++ tailWord_3301501) baseStart_3301501 baseEnd_3301501 := by
    simpa [prefixWord, tailWord_3301501, baseEnd_3301501] using wordTrace_append hprefix tailTrace_3301501
  have hstable : (prefixWord ++ tailWord_3301501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3301501).length < 2 ^ (prefixWord ++ tailWord_3301501).sum := by decide
  have hdescent : baseEnd_3301501 < baseStart_3301501 := by decide
  rcases family_descends (prefixWord ++ tailWord_3301501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3301535 : List Nat := [1, 1, 2, 6, 1, 1, 2, 4, 5]
def baseStart_3301535 : Nat := 118140960795 + 3301535 * 2 ^ 59
def prefixEnd_3301535 : Nat := 4983230072969 + 3 ^ 40 * 3301535 * 2
def baseEnd_3301535 : Nat := 188363816960205051425447

theorem tailTrace_3301535 : CollatzResearch.WordTrace tailWord_3301535 prefixEnd_3301535 188363816960205051425447 := by
  unfold tailWord_3301535
  simp only [CollatzResearch.WordTrace]
  refine ⟨120416874094110027132138059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80277916062740018088092039 120416874094110027132138059)
  ·
    refine ⟨180625311141165040698207089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120416874094110027132138059 180625311141165040698207089)
    ·
      refine ⟨135468983355873780523655317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180625311141165040698207089 135468983355873780523655317)
      ·
        refine ⟨6350108594806583462046343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 135468983355873780523655317 6350108594806583462046343)
        ·
          refine ⟨9525162892209875193069515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6350108594806583462046343 9525162892209875193069515)
          ·
            refine ⟨14287744338314812789604273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9525162892209875193069515 14287744338314812789604273)
            ·
              refine ⟨10715808253736109592203205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14287744338314812789604273 10715808253736109592203205)
              ·
                refine ⟨2009214047575520548538101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10715808253736109592203205 2009214047575520548538101)
                ·
                  refine ⟨188363816960205051425447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2009214047575520548538101 188363816960205051425447)
                  ·
                    rfl

theorem cell23_3301535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 4, 5].length) (baseStart_3301535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3301535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3301535 prefixEnd_3301535 := by exact prefixLift 3301535
  have htrace : WordTrace (prefixWord ++ tailWord_3301535) baseStart_3301535 baseEnd_3301535 := by
    simpa [prefixWord, tailWord_3301535, baseEnd_3301535] using wordTrace_append hprefix tailTrace_3301535
  have hstable : (prefixWord ++ tailWord_3301535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3301535).length < 2 ^ (prefixWord ++ tailWord_3301535).sum := by decide
  have hdescent : baseEnd_3301535 < baseStart_3301535 := by decide
  rcases family_descends (prefixWord ++ tailWord_3301535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3301541 : List Nat := [1, 3, 1, 2, 1, 3, 2, 1, 1, 1, 7]
def baseStart_3301541 : Nat := 118140960795 + 3301541 * 2 ^ 59
def prefixEnd_3301541 : Nat := 4983230072969 + 3 ^ 40 * 3301541 * 2
def baseEnd_3301541 : Nat := 1695277433525772439353995

theorem tailTrace_3301541 : CollatzResearch.WordTrace tailWord_3301541 prefixEnd_3301541 1695277433525772439353995 := by
  unfold tailWord_3301541
  simp only [CollatzResearch.WordTrace]
  refine ⟨120417092932088290156856477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80278061954725526771237651 120417092932088290156856477)
  ·
    refine ⟨45156409849533108808821179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120417092932088290156856477 45156409849533108808821179)
    ·
      refine ⟨67734614774299663213231769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45156409849533108808821179 67734614774299663213231769)
      ·
        refine ⟨50800961080724747409923827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67734614774299663213231769 50800961080724747409923827)
        ·
          refine ⟨76201441621087121114885741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50800961080724747409923827 76201441621087121114885741)
          ·
            refine ⟨28575540607907670418082153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76201441621087121114885741 28575540607907670418082153)
            ·
              refine ⟨21431655455930752813561615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28575540607907670418082153 21431655455930752813561615)
              ·
                refine ⟨32147483183896129220342423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21431655455930752813561615 32147483183896129220342423)
                ·
                  refine ⟨48221224775844193830513635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32147483183896129220342423 48221224775844193830513635)
                  ·
                    refine ⟨72331837163766290745770453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48221224775844193830513635 72331837163766290745770453)
                    ·
                      refine ⟨1695277433525772439353995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 72331837163766290745770453 1695277433525772439353995)
                      ·
                        rfl

theorem cell23_3301541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 1, 1, 1, 7].length) (baseStart_3301541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3301541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3301541 prefixEnd_3301541 := by exact prefixLift 3301541
  have htrace : WordTrace (prefixWord ++ tailWord_3301541) baseStart_3301541 baseEnd_3301541 := by
    simpa [prefixWord, tailWord_3301541, baseEnd_3301541] using wordTrace_append hprefix tailTrace_3301541
  have hstable : (prefixWord ++ tailWord_3301541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3301541).length < 2 ^ (prefixWord ++ tailWord_3301541).sum := by decide
  have hdescent : baseEnd_3301541 < baseStart_3301541 := by decide
  rcases family_descends (prefixWord ++ tailWord_3301541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3301546 : List Nat := [3, 1, 5, 1, 3, 1, 1, 1, 1, 4, 2]
def baseStart_3301546 : Nat := 118140960795 + 3301546 * 2 ^ 59
def prefixEnd_3301546 : Nat := 4983230072969 + 3 ^ 40 * 3301546 * 2
def baseEnd_3301546 : Nat := 1695280000929044919791473

theorem tailTrace_3301546 : CollatzResearch.WordTrace tailWord_3301546 prefixEnd_3301546 1695280000929044919791473 := by
  unfold tailWord_3301546
  simp only [CollatzResearch.WordTrace]
  refine ⟨30104318824267544002697123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80278183531380117340525661 30104318824267544002697123)
  ·
    refine ⟨45156478236401316004045685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30104318824267544002697123 45156478236401316004045685)
    ·
      refine ⟨4233419834662623375379283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 45156478236401316004045685 4233419834662623375379283)
      ·
        refine ⟨6350129751993935063068925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4233419834662623375379283 6350129751993935063068925)
        ·
          refine ⟨2381298656997725648650847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6350129751993935063068925 2381298656997725648650847)
          ·
            refine ⟨3571947985496588472976271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2381298656997725648650847 3571947985496588472976271)
            ·
              refine ⟨5357921978244882709464407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3571947985496588472976271 5357921978244882709464407)
              ·
                refine ⟨8036882967367324064196611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5357921978244882709464407 8036882967367324064196611)
                ·
                  refine ⟨12055324451050986096294917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8036882967367324064196611 12055324451050986096294917)
                  ·
                    refine ⟨2260373334572059893055297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12055324451050986096294917 2260373334572059893055297)
                    ·
                      refine ⟨1695280000929044919791473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2260373334572059893055297 1695280000929044919791473)
                      ·
                        rfl

theorem cell23_3301546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 1, 1, 1, 4, 2].length) (baseStart_3301546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3301546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3301546 prefixEnd_3301546 := by exact prefixLift 3301546
  have htrace : WordTrace (prefixWord ++ tailWord_3301546) baseStart_3301546 baseEnd_3301546 := by
    simpa [prefixWord, tailWord_3301546, baseEnd_3301546] using wordTrace_append hprefix tailTrace_3301546
  have hstable : (prefixWord ++ tailWord_3301546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3301546).length < 2 ^ (prefixWord ++ tailWord_3301546).sum := by decide
  have hdescent : baseEnd_3301546 < baseStart_3301546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3301546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3301561 : List Nat := [1, 2, 1, 4, 1, 2, 1, 1, 2, 8]
def baseStart_3301561 : Nat := 118140960795 + 3301561 * 2 ^ 59
def prefixEnd_3301561 : Nat := 4983230072969 + 3 ^ 40 * 3301561 * 2
def baseEnd_3301561 : Nat := 565095901046287453701301

theorem tailTrace_3301561 : CollatzResearch.WordTrace tailWord_3301561 prefixEnd_3301561 565095901046287453701301 := by
  unfold tailWord_3301561
  simp only [CollatzResearch.WordTrace]
  refine ⟨120417822392015833572584537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80278548261343889048389691 120417822392015833572584537)
  ·
    refine ⟨90313366794011875179438403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120417822392015833572584537 90313366794011875179438403)
    ·
      refine ⟨135470050191017812769157605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90313366794011875179438403 135470050191017812769157605)
      ·
        refine ⟨25400634410815839894217051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 135470050191017812769157605 25400634410815839894217051)
        ·
          refine ⟨38100951616223759841325577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25400634410815839894217051 38100951616223759841325577)
          ·
            refine ⟨28575713712167819880994183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38100951616223759841325577 28575713712167819880994183)
            ·
              refine ⟨42863570568251729821491275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28575713712167819880994183 42863570568251729821491275)
              ·
                refine ⟨64295355852377594732236913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42863570568251729821491275 64295355852377594732236913)
                ·
                  refine ⟨48221516889283196049177685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64295355852377594732236913 48221516889283196049177685)
                  ·
                    refine ⟨565095901046287453701301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 48221516889283196049177685 565095901046287453701301)
                    ·
                      rfl

theorem cell23_3301561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 2, 8].length) (baseStart_3301561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3301561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3301561 prefixEnd_3301561 := by exact prefixLift 3301561
  have htrace : WordTrace (prefixWord ++ tailWord_3301561) baseStart_3301561 baseEnd_3301561 := by
    simpa [prefixWord, tailWord_3301561, baseEnd_3301561] using wordTrace_append hprefix tailTrace_3301561
  have hstable : (prefixWord ++ tailWord_3301561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3301561).length < 2 ^ (prefixWord ++ tailWord_3301561).sum := by decide
  have hdescent : baseEnd_3301561 < baseStart_3301561 := by decide
  rcases family_descends (prefixWord ++ tailWord_3301561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3301568 : List Nat := [2, 1, 1, 2, 5, 1, 2, 1, 1, 3, 4]
def baseStart_3301568 : Nat := 118140960795 + 3301568 * 2 ^ 59
def prefixEnd_3301568 : Nat := 4983230072969 + 3 ^ 40 * 3301568 * 2
def baseEnd_3301568 : Nat := 1695291297503443833716371

theorem tailTrace_3301568 : CollatzResearch.WordTrace tailWord_3301568 prefixEnd_3301568 1695291297503443833716371 := by
  unfold tailWord_3301568
  simp only [CollatzResearch.WordTrace]
  refine ⟨60209038851495236884044679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80278718468660315845392905 60209038851495236884044679)
  ·
    refine ⟨90313558277242855326067019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60209038851495236884044679 90313558277242855326067019)
    ·
      refine ⟨135470337415864282989100529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90313558277242855326067019 135470337415864282989100529)
      ·
        refine ⟨101602753061898212241825397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135470337415864282989100529 101602753061898212241825397)
        ·
          refine ⟨9525258099552957397671131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 101602753061898212241825397 9525258099552957397671131)
          ·
            refine ⟨14287887149329436096506697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9525258099552957397671131 14287887149329436096506697)
            ·
              refine ⟨10715915361997077072380023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14287887149329436096506697 10715915361997077072380023)
              ·
                refine ⟨16073873042995615608570035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10715915361997077072380023 16073873042995615608570035)
                ·
                  refine ⟨24110809564493423412855053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16073873042995615608570035 24110809564493423412855053)
                  ·
                    refine ⟨9041553586685033779820645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24110809564493423412855053 9041553586685033779820645)
                    ·
                      refine ⟨1695291297503443833716371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9041553586685033779820645 1695291297503443833716371)
                      ·
                        rfl

theorem cell23_3301568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 1, 1, 3, 4].length) (baseStart_3301568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3301568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3301568 prefixEnd_3301568 := by exact prefixLift 3301568
  have htrace : WordTrace (prefixWord ++ tailWord_3301568) baseStart_3301568 baseEnd_3301568 := by
    simpa [prefixWord, tailWord_3301568, baseEnd_3301568] using wordTrace_append hprefix tailTrace_3301568
  have hstable : (prefixWord ++ tailWord_3301568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3301568).length < 2 ^ (prefixWord ++ tailWord_3301568).sum := by decide
  have hdescent : baseEnd_3301568 < baseStart_3301568 := by decide
  rcases family_descends (prefixWord ++ tailWord_3301568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3301569 : List Nat := [1, 2, 6, 1, 2, 2, 1, 3, 5]
def baseStart_3301569 : Nat := 118140960795 + 3301569 * 2 ^ 59
def prefixEnd_3301569 : Nat := 4983230072969 + 3 ^ 40 * 3301569 * 2
def baseEnd_3301569 : Nat := 188365756776010925533763

theorem tailTrace_3301569 : CollatzResearch.WordTrace tailWord_3301569 prefixEnd_3301569 188365756776010925533763 := by
  unfold tailWord_3301569
  simp only [CollatzResearch.WordTrace]
  refine ⟨120418114175986850938875761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80278742783991233959250507 120418114175986850938875761)
  ·
    refine ⟨90313585631990138204156821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120418114175986850938875761 90313585631990138204156821)
    ·
      refine ⟨4233449326499537728319851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 90313585631990138204156821 4233449326499537728319851)
      ·
        refine ⟨6350173989749306592479777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4233449326499537728319851 6350173989749306592479777)
        ·
          refine ⟨4762630492311979944359833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6350173989749306592479777 4762630492311979944359833)
          ·
            refine ⟨3571972869233984958269875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4762630492311979944359833 3571972869233984958269875)
            ·
              refine ⟨5357959303850977437404813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3571972869233984958269875 5357959303850977437404813)
              ·
                refine ⟨2009234738944116539026805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5357959303850977437404813 2009234738944116539026805)
                ·
                  refine ⟨188365756776010925533763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2009234738944116539026805 188365756776010925533763)
                  ·
                    rfl

theorem cell23_3301569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 1, 3, 5].length) (baseStart_3301569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3301569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3301569 prefixEnd_3301569 := by exact prefixLift 3301569
  have htrace : WordTrace (prefixWord ++ tailWord_3301569) baseStart_3301569 baseEnd_3301569 := by
    simpa [prefixWord, tailWord_3301569, baseEnd_3301569] using wordTrace_append hprefix tailTrace_3301569
  have hstable : (prefixWord ++ tailWord_3301569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3301569).length < 2 ^ (prefixWord ++ tailWord_3301569).sum := by decide
  have hdescent : baseEnd_3301569 < baseStart_3301569 := by decide
  rcases family_descends (prefixWord ++ tailWord_3301569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3301685 : List Nat := [1, 3, 3, 1, 2, 1, 2, 2, 4, 4]
def baseStart_3301685 : Nat := 118140960795 + 3301685 * 2 ^ 59
def prefixEnd_3301685 : Nat := 4983230072969 + 3 ^ 40 * 3301685 * 2
def baseEnd_3301685 : Nat := 565117124913339958651111

theorem tailTrace_3301685 : CollatzResearch.WordTrace tailWord_3301685 prefixEnd_3301685 565117124913339958651111 := by
  unfold tailWord_3301685
  simp only [CollatzResearch.WordTrace]
  refine ⟨120422345043566602750098509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80281563362377735166732339 120422345043566602750098509)
  ·
    refine ⟨45158379391337476031286941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120422345043566602750098509 45158379391337476031286941)
    ·
      refine ⟨16934392271751553511732603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45158379391337476031286941 16934392271751553511732603)
      ·
        refine ⟨25401588407627330267598905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16934392271751553511732603 25401588407627330267598905)
        ·
          refine ⟨19051191305720497700699179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25401588407627330267598905 19051191305720497700699179)
          ·
            refine ⟨28576786958580746551048769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19051191305720497700699179 28576786958580746551048769)
            ·
              refine ⟨21432590218935559913286577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28576786958580746551048769 21432590218935559913286577)
              ·
                refine ⟨16074442664201669934964933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21432590218935559913286577 16074442664201669934964933)
                ·
                  refine ⟨3013957999537813112805925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16074442664201669934964933 3013957999537813112805925)
                  ·
                    refine ⟨565117124913339958651111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3013957999537813112805925 565117124913339958651111)
                    ·
                      rfl

theorem cell23_3301685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 2, 4, 4].length) (baseStart_3301685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3301685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3301685 prefixEnd_3301685 := by exact prefixLift 3301685
  have htrace : WordTrace (prefixWord ++ tailWord_3301685) baseStart_3301685 baseEnd_3301685 := by
    simpa [prefixWord, tailWord_3301685, baseEnd_3301685] using wordTrace_append hprefix tailTrace_3301685
  have hstable : (prefixWord ++ tailWord_3301685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3301685).length < 2 ^ (prefixWord ++ tailWord_3301685).sum := by decide
  have hdescent : baseEnd_3301685 < baseStart_3301685 := by decide
  rcases family_descends (prefixWord ++ tailWord_3301685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3301689 : List Nat := [1, 2, 1, 6, 1, 3, 2, 1, 1, 5]
def baseStart_3301689 : Nat := 118140960795 + 3301689 * 2 ^ 59
def prefixEnd_3301689 : Nat := 4983230072969 + 3 ^ 40 * 3301689 * 2
def baseEnd_3301689 : Nat := 565117809554212620101105

theorem tailTrace_3301689 : CollatzResearch.WordTrace tailWord_3301689 prefixEnd_3301689 565117809554212620101105 := by
  unfold tailWord_3301689
  simp only [CollatzResearch.WordTrace]
  refine ⟨120422490935552111433244121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80281660623701407622162747 120422490935552111433244121)
  ·
    refine ⟨90316868201664083574933091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120422490935552111433244121 90316868201664083574933091)
    ·
      refine ⟨135475302302496125362399637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90316868201664083574933091 135475302302496125362399637)
      ·
        refine ⟨6350404795429505876362483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 135475302302496125362399637 6350404795429505876362483)
        ·
          refine ⟨9525607193144258814543725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6350404795429505876362483 9525607193144258814543725)
          ·
            refine ⟨3572102697429097055453897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9525607193144258814543725 3572102697429097055453897)
            ·
              refine ⟨2679077023071822791590423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3572102697429097055453897 2679077023071822791590423)
              ·
                refine ⟨4018615534607734187385635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2679077023071822791590423 4018615534607734187385635)
                ·
                  refine ⟨6027923301911601281078453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4018615534607734187385635 6027923301911601281078453)
                  ·
                    refine ⟨565117809554212620101105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6027923301911601281078453 565117809554212620101105)
                    ·
                      rfl

theorem cell23_3301689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 2, 1, 1, 5].length) (baseStart_3301689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3301689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3301689 prefixEnd_3301689 := by exact prefixLift 3301689
  have htrace : WordTrace (prefixWord ++ tailWord_3301689) baseStart_3301689 baseEnd_3301689 := by
    simpa [prefixWord, tailWord_3301689, baseEnd_3301689] using wordTrace_append hprefix tailTrace_3301689
  have hstable : (prefixWord ++ tailWord_3301689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3301689).length < 2 ^ (prefixWord ++ tailWord_3301689).sum := by decide
  have hdescent : baseEnd_3301689 < baseStart_3301689 := by decide
  rcases family_descends (prefixWord ++ tailWord_3301689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3301692 : List Nat := [2, 2, 2, 2, 1, 2, 1, 2, 5, 2, 2]
def baseStart_3301692 : Nat := 118140960795 + 3301692 * 2 ^ 59
def prefixEnd_3301692 : Nat := 4983230072969 + 3 ^ 40 * 3301692 * 2
def baseEnd_3301692 : Nat := 1695354969104601348565801

theorem tailTrace_3301692 : CollatzResearch.WordTrace tailWord_3301692 prefixEnd_3301692 1695354969104601348565801 := by
  unfold tailWord_3301692
  simp only [CollatzResearch.WordTrace]
  refine ⟨60211300177270621472801665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80281733569694161963735553 60211300177270621472801665)
  ·
    refine ⟨45158475132952966104601249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60211300177270621472801665 45158475132952966104601249)
    ·
      refine ⟨33868856349714724578450937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45158475132952966104601249 33868856349714724578450937)
      ·
        refine ⟨25401642262286043433838203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33868856349714724578450937 25401642262286043433838203)
        ·
          refine ⟨38102463393429065150757305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25401642262286043433838203 38102463393429065150757305)
          ·
            refine ⟨28576847545071798863067979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38102463393429065150757305 28576847545071798863067979)
            ·
              refine ⟨42865271317607698294601969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28576847545071798863067979 42865271317607698294601969)
              ·
                refine ⟨32148953488205773720951477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42865271317607698294601969 32148953488205773720951477)
                ·
                  refine ⟨3013964389519291286339201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32148953488205773720951477 3013964389519291286339201)
                  ·
                    refine ⟨2260473292139468464754401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3013964389519291286339201 2260473292139468464754401)
                    ·
                      refine ⟨1695354969104601348565801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2260473292139468464754401 1695354969104601348565801)
                      ·
                        rfl

theorem cell23_3301692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 2, 5, 2, 2].length) (baseStart_3301692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3301692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3301692 prefixEnd_3301692 := by exact prefixLift 3301692
  have htrace : WordTrace (prefixWord ++ tailWord_3301692) baseStart_3301692 baseEnd_3301692 := by
    simpa [prefixWord, tailWord_3301692, baseEnd_3301692] using wordTrace_append hprefix tailTrace_3301692
  have hstable : (prefixWord ++ tailWord_3301692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3301692).length < 2 ^ (prefixWord ++ tailWord_3301692).sum := by decide
  have hdescent : baseEnd_3301692 < baseStart_3301692 := by decide
  rcases family_descends (prefixWord ++ tailWord_3301692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3301786 : List Nat := [3, 1, 1, 4, 1, 4, 1, 2, 1, 3, 2]
def baseStart_3301786 : Nat := 118140960795 + 3301786 * 2 ^ 59
def prefixEnd_3301786 : Nat := 4983230072969 + 3 ^ 40 * 3301786 * 2
def baseEnd_3301786 : Nat := 1695403236286123980790369

theorem tailTrace_3301786 : CollatzResearch.WordTrace tailWord_3301786 prefixEnd_3301786 1695403236286123980790369 := by
  unfold tailWord_3301786
  simp only [CollatzResearch.WordTrace]
  refine ⟨30106507204050174249881303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80284019210800464666350141 30106507204050174249881303)
  ·
    refine ⟨45159760806075261374821955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30106507204050174249881303 45159760806075261374821955)
    ·
      refine ⟨67739641209112892062232933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45159760806075261374821955 67739641209112892062232933)
      ·
        refine ⟨12701182726708667261668675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67739641209112892062232933 12701182726708667261668675)
        ·
          refine ⟨19051774090063000892503013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12701182726708667261668675 19051774090063000892503013)
          ·
            refine ⟨3572207641886812667344315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19051774090063000892503013 3572207641886812667344315)
            ·
              refine ⟨5358311462830219001016473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3572207641886812667344315 5358311462830219001016473)
              ·
                refine ⟨4018733597122664250762355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5358311462830219001016473 4018733597122664250762355)
                ·
                  refine ⟨6028100395683996376143533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4018733597122664250762355 6028100395683996376143533)
                  ·
                    refine ⟨2260537648381498641053825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6028100395683996376143533 2260537648381498641053825)
                    ·
                      refine ⟨1695403236286123980790369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2260537648381498641053825 1695403236286123980790369)
                      ·
                        rfl

theorem cell23_3301786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 1, 2, 1, 3, 2].length) (baseStart_3301786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3301786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3301786 prefixEnd_3301786 := by exact prefixLift 3301786
  have htrace : WordTrace (prefixWord ++ tailWord_3301786) baseStart_3301786 baseEnd_3301786 := by
    simpa [prefixWord, tailWord_3301786, baseEnd_3301786] using wordTrace_append hprefix tailTrace_3301786
  have hstable : (prefixWord ++ tailWord_3301786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3301786).length < 2 ^ (prefixWord ++ tailWord_3301786).sum := by decide
  have hdescent : baseEnd_3301786 < baseStart_3301786 := by decide
  rcases family_descends (prefixWord ++ tailWord_3301786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3301799 : List Nat := [1, 1, 6, 1, 1, 3, 1, 2, 1, 4, 2]
def baseStart_3301799 : Nat := 118140960795 + 3301799 * 2 ^ 59
def prefixEnd_3301799 : Nat := 4983230072969 + 3 ^ 40 * 3301799 * 2
def baseEnd_3301799 : Nat := 1695409911534632429927809

theorem tailTrace_3301799 : CollatzResearch.WordTrace tailWord_3301799 prefixEnd_3301799 1695409911534632429927809 := by
  unfold tailWord_3301799
  simp only [CollatzResearch.WordTrace]
  refine ⟨120426502965153600219748451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80284335310102400146498967 120426502965153600219748451)
  ·
    refine ⟨180639754447730400329622677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120426502965153600219748451 180639754447730400329622677)
    ·
      refine ⟨8467488489737362515451063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 180639754447730400329622677 8467488489737362515451063)
      ·
        refine ⟨12701232734606043773176595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8467488489737362515451063 12701232734606043773176595)
        ·
          refine ⟨19051849101909065659764893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12701232734606043773176595 19051849101909065659764893)
          ·
            refine ⟨7144443413215899622411835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19051849101909065659764893 7144443413215899622411835)
            ·
              refine ⟨10716665119823849433617753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7144443413215899622411835 10716665119823849433617753)
              ·
                refine ⟨8037498839867887075213315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10716665119823849433617753 8037498839867887075213315)
                ·
                  refine ⟨12056248259801830612819973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8037498839867887075213315 12056248259801830612819973)
                  ·
                    refine ⟨2260546548712843239903745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12056248259801830612819973 2260546548712843239903745)
                    ·
                      refine ⟨1695409911534632429927809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2260546548712843239903745 1695409911534632429927809)
                      ·
                        rfl

theorem cell23_3301799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 2, 1, 4, 2].length) (baseStart_3301799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3301799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3301799 prefixEnd_3301799 := by exact prefixLift 3301799
  have htrace : WordTrace (prefixWord ++ tailWord_3301799) baseStart_3301799 baseEnd_3301799 := by
    simpa [prefixWord, tailWord_3301799, baseEnd_3301799] using wordTrace_append hprefix tailTrace_3301799
  have hstable : (prefixWord ++ tailWord_3301799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3301799).length < 2 ^ (prefixWord ++ tailWord_3301799).sum := by decide
  have hdescent : baseEnd_3301799 < baseStart_3301799 := by decide
  rcases family_descends (prefixWord ++ tailWord_3301799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3301808 : List Nat := [2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 8]
def baseStart_3301808 : Nat := 118140960795 + 3301808 * 2 ^ 59
def prefixEnd_3301808 : Nat := 4983230072969 + 3 ^ 40 * 3301808 * 2
def baseEnd_3301808 : Nat := 1695414532860522894715267

theorem tailTrace_3301808 : CollatzResearch.WordTrace tailWord_3301808 prefixEnd_3301808 1695414532860522894715267 := by
  unfold tailWord_3301808
  simp only [CollatzResearch.WordTrace]
  refine ⟨60213415611060497378413039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80284554148080663171217385 60213415611060497378413039)
  ·
    refine ⟨90320123416590746067619559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60213415611060497378413039 90320123416590746067619559)
    ·
      refine ⟨135480185124886119101429339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90320123416590746067619559 135480185124886119101429339)
      ·
        refine ⟨203220277687329178652144009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135480185124886119101429339 203220277687329178652144009)
        ·
          refine ⟨152415208265496883989108007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203220277687329178652144009 152415208265496883989108007)
          ·
            refine ⟨228622812398245325983662011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152415208265496883989108007 228622812398245325983662011)
            ·
              refine ⟨342934218597367988975493017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 228622812398245325983662011 342934218597367988975493017)
              ·
                refine ⟨257200663948025991731619763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 342934218597367988975493017 257200663948025991731619763)
                ·
                  refine ⟨385800995922038987597429645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 257200663948025991731619763 385800995922038987597429645)
                  ·
                    refine ⟨144675373470764620349036117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 385800995922038987597429645 144675373470764620349036117)
                    ·
                      refine ⟨1695414532860522894715267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 144675373470764620349036117 1695414532860522894715267)
                      ·
                        rfl

theorem cell23_3301808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 8].length) (baseStart_3301808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3301808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3301808 prefixEnd_3301808 := by exact prefixLift 3301808
  have htrace : WordTrace (prefixWord ++ tailWord_3301808) baseStart_3301808 baseEnd_3301808 := by
    simpa [prefixWord, tailWord_3301808, baseEnd_3301808] using wordTrace_append hprefix tailTrace_3301808
  have hstable : (prefixWord ++ tailWord_3301808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3301808).length < 2 ^ (prefixWord ++ tailWord_3301808).sum := by decide
  have hdescent : baseEnd_3301808 < baseStart_3301808 := by decide
  rcases family_descends (prefixWord ++ tailWord_3301808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3301832 : List Nat := [2, 1, 3, 1, 3, 3, 1, 1, 2, 3, 3]
def baseStart_3301832 : Nat := 118140960795 + 3301832 * 2 ^ 59
def prefixEnd_3301832 : Nat := 4983230072969 + 3 ^ 40 * 3301832 * 2
def baseEnd_3301832 : Nat := 1695426856396230800815157

theorem tailTrace_3301832 : CollatzResearch.WordTrace tailWord_3301832 prefixEnd_3301832 1695426856396230800815157 := by
  unfold tailWord_3301832
  simp only [CollatzResearch.WordTrace]
  refine ⟨60213853287017023427849875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80285137716022697903799833 60213853287017023427849875)
  ·
    refine ⟨90320779930525535141774813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60213853287017023427849875 90320779930525535141774813)
    ·
      refine ⟨33870292473947075678165555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90320779930525535141774813 33870292473947075678165555)
      ·
        refine ⟨50805438710920613517248333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33870292473947075678165555 50805438710920613517248333)
        ·
          refine ⟨19052039516595230068968125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50805438710920613517248333 19052039516595230068968125)
          ·
            refine ⟨7144514818723211275863047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19052039516595230068968125 7144514818723211275863047)
            ·
              refine ⟨10716772228084816913794571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7144514818723211275863047 10716772228084816913794571)
              ·
                refine ⟨16075158342127225370691857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10716772228084816913794571 16075158342127225370691857)
                ·
                  refine ⟨12056368756595419028018893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16075158342127225370691857 12056368756595419028018893)
                  ·
                    refine ⟨4521138283723282135507085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12056368756595419028018893 4521138283723282135507085)
                    ·
                      refine ⟨1695426856396230800815157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4521138283723282135507085 1695426856396230800815157)
                      ·
                        rfl

theorem cell23_3301832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 1, 2, 3, 3].length) (baseStart_3301832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3301832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3301832 prefixEnd_3301832 := by exact prefixLift 3301832
  have htrace : WordTrace (prefixWord ++ tailWord_3301832) baseStart_3301832 baseEnd_3301832 := by
    simpa [prefixWord, tailWord_3301832, baseEnd_3301832] using wordTrace_append hprefix tailTrace_3301832
  have hstable : (prefixWord ++ tailWord_3301832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3301832).length < 2 ^ (prefixWord ++ tailWord_3301832).sum := by decide
  have hdescent : baseEnd_3301832 < baseStart_3301832 := by decide
  rcases family_descends (prefixWord ++ tailWord_3301832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3301872 : List Nat := [2, 1, 1, 1, 3, 3, 1, 1, 4, 4, 2]
def baseStart_3301872 : Nat := 118140960795 + 3301872 * 2 ^ 59
def prefixEnd_3301872 : Nat := 4983230072969 + 3 ^ 40 * 3301872 * 2
def baseEnd_3301872 : Nat := 1695447395622410644314973

theorem tailTrace_3301872 : CollatzResearch.WordTrace tailWord_3301872 prefixEnd_3301872 1695447395622410644314973 := by
  unfold tailWord_3301872
  simp only [CollatzResearch.WordTrace]
  refine ⟨60214582746944566843577935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80286110329259422458103913 60214582746944566843577935)
  ·
    refine ⟨90321874120416850265366903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60214582746944566843577935 90321874120416850265366903)
    ·
      refine ⟨135482811180625275398050355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90321874120416850265366903 135482811180625275398050355)
      ·
        refine ⟨203224216770937913097075533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135482811180625275398050355 203224216770937913097075533)
        ·
          refine ⟨76209081289101717411403325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 203224216770937913097075533 76209081289101717411403325)
          ·
            refine ⟨28578405483413144029276247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76209081289101717411403325 28578405483413144029276247)
            ·
              refine ⟨42867608225119716043914371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28578405483413144029276247 42867608225119716043914371)
              ·
                refine ⟨64301412337679574065871557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42867608225119716043914371 64301412337679574065871557)
                ·
                  refine ⟨12056514813314920137350917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64301412337679574065871557 12056514813314920137350917)
                  ·
                    refine ⟨2260596527496547525753297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12056514813314920137350917 2260596527496547525753297)
                    ·
                      refine ⟨1695447395622410644314973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2260596527496547525753297 1695447395622410644314973)
                      ·
                        rfl

theorem cell23_3301872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 4, 4, 2].length) (baseStart_3301872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3301872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3301872 prefixEnd_3301872 := by exact prefixLift 3301872
  have htrace : WordTrace (prefixWord ++ tailWord_3301872) baseStart_3301872 baseEnd_3301872 := by
    simpa [prefixWord, tailWord_3301872, baseEnd_3301872] using wordTrace_append hprefix tailTrace_3301872
  have hstable : (prefixWord ++ tailWord_3301872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3301872).length < 2 ^ (prefixWord ++ tailWord_3301872).sum := by decide
  have hdescent : baseEnd_3301872 < baseStart_3301872 := by decide
  rcases family_descends (prefixWord ++ tailWord_3301872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3301885 : List Nat := [1, 4, 1, 1, 1, 3, 1, 2, 2, 1, 6]
def baseStart_3301885 : Nat := 118140960795 + 3301885 * 2 ^ 59
def prefixEnd_3301885 : Nat := 4983230072969 + 3 ^ 40 * 3301885 * 2
def baseEnd_3301885 : Nat := 1695454070870919093452413

theorem tailTrace_3301885 : CollatzResearch.WordTrace tailWord_3301885 prefixEnd_3301885 1695454070870919093452413 := by
  unfold tailWord_3301885
  simp only [CollatzResearch.WordTrace]
  refine ⟨120429639642842036907379109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80286426428561357938252739 120429639642842036907379109)
  ·
    refine ⟨22580557433032881920133583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120429639642842036907379109 22580557433032881920133583)
    ·
      refine ⟨33870836149549322880200375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22580557433032881920133583 33870836149549322880200375)
      ·
        refine ⟨50806254224323984320300563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33870836149549322880200375 50806254224323984320300563)
        ·
          refine ⟨76209381336485976480450845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50806254224323984320300563 76209381336485976480450845)
          ·
            refine ⟨28578518001182241180169067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76209381336485976480450845 28578518001182241180169067)
            ·
              refine ⟨42867777001773361770253601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28578518001182241180169067 42867777001773361770253601)
              ·
                refine ⟨32150832751330021327690201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42867777001773361770253601 32150832751330021327690201)
                ·
                  refine ⟨24113124563497515995767651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32150832751330021327690201 24113124563497515995767651)
                  ·
                    refine ⟨36169686845246273993651477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24113124563497515995767651 36169686845246273993651477)
                    ·
                      refine ⟨1695454070870919093452413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36169686845246273993651477 1695454070870919093452413)
                      ·
                        rfl

theorem cell23_3301885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 2, 2, 1, 6].length) (baseStart_3301885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3301885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3301885 prefixEnd_3301885 := by exact prefixLift 3301885
  have htrace : WordTrace (prefixWord ++ tailWord_3301885) baseStart_3301885 baseEnd_3301885 := by
    simpa [prefixWord, tailWord_3301885, baseEnd_3301885] using wordTrace_append hprefix tailTrace_3301885
  have hstable : (prefixWord ++ tailWord_3301885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3301885).length < 2 ^ (prefixWord ++ tailWord_3301885).sum := by decide
  have hdescent : baseEnd_3301885 < baseStart_3301885 := by decide
  rcases family_descends (prefixWord ++ tailWord_3301885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3301889 : List Nat := [1, 2, 4, 1, 3, 1, 2, 1, 2, 4, 2]
def baseStart_3301889 : Nat := 118140960795 + 3301889 * 2 ^ 59
def prefixEnd_3301889 : Nat := 4983230072969 + 3 ^ 40 * 3301889 * 2
def baseEnd_3301889 : Nat := 1695456124793537077802395

theorem tailTrace_3301889 : CollatzResearch.WordTrace tailWord_3301889 prefixEnd_3301889 1695456124793537077802395 := by
  unfold tailWord_3301889
  simp only [CollatzResearch.WordTrace]
  refine ⟨120429785534827545590524721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80286523689885030393683147 120429785534827545590524721)
  ·
    refine ⟨90322339151120659192893541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120429785534827545590524721 90322339151120659192893541)
    ·
      refine ⟨16935438590835123598667539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90322339151120659192893541 16935438590835123598667539)
      ·
        refine ⟨25403157886252685398001309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16935438590835123598667539 25403157886252685398001309)
        ·
          refine ⟨9526184207344757024250491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25403157886252685398001309 9526184207344757024250491)
          ·
            refine ⟨14289276311017135536375737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9526184207344757024250491 14289276311017135536375737)
            ·
              refine ⟨10716957233262851652281803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14289276311017135536375737 10716957233262851652281803)
              ·
                refine ⟨16075435849894277478422705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10716957233262851652281803 16075435849894277478422705)
                ·
                  refine ⟨12056576887420708108817029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16075435849894277478422705 12056576887420708108817029)
                  ·
                    refine ⟨2260608166391382770403193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12056576887420708108817029 2260608166391382770403193)
                    ·
                      refine ⟨1695456124793537077802395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2260608166391382770403193 1695456124793537077802395)
                      ·
                        rfl

theorem cell23_3301889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 1, 2, 4, 2].length) (baseStart_3301889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3301889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3301889 prefixEnd_3301889 := by exact prefixLift 3301889
  have htrace : WordTrace (prefixWord ++ tailWord_3301889) baseStart_3301889 baseEnd_3301889 := by
    simpa [prefixWord, tailWord_3301889, baseEnd_3301889] using wordTrace_append hprefix tailTrace_3301889
  have hstable : (prefixWord ++ tailWord_3301889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3301889).length < 2 ^ (prefixWord ++ tailWord_3301889).sum := by decide
  have hdescent : baseEnd_3301889 < baseStart_3301889 := by decide
  rcases family_descends (prefixWord ++ tailWord_3301889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3301916 : List Nat := [2, 2, 3, 1, 2, 2, 3, 3, 1, 4]
def baseStart_3301916 : Nat := 118140960795 + 3301916 * 2 ^ 59
def prefixEnd_3301916 : Nat := 4983230072969 + 3 ^ 40 * 3301916 * 2
def baseEnd_3301916 : Nat := 565156662923736157388257

theorem tailTrace_3301916 : CollatzResearch.WordTrace tailWord_3301916 prefixEnd_3301916 565156662923736157388257 := by
  unfold tailWord_3301916
  simp only [CollatzResearch.WordTrace]
  refine ⟨60215385152864864600878801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80287180203819819467838401 60215385152864864600878801)
  ·
    refine ⟨45161538864648648450659101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60215385152864864600878801 45161538864648648450659101)
    ·
      refine ⟨16935577074243243168997163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45161538864648648450659101 16935577074243243168997163)
      ·
        refine ⟨25403365611364864753495745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16935577074243243168997163 25403365611364864753495745)
        ·
          refine ⟨19052524208523648565121809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25403365611364864753495745 19052524208523648565121809)
          ·
            refine ⟨14289393156392736423841357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19052524208523648565121809 14289393156392736423841357)
            ·
              refine ⟨5358522433647276158940509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14289393156392736423841357 5358522433647276158940509)
              ·
                refine ⟨2009445912617728559602691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5358522433647276158940509 2009445912617728559602691)
                ·
                  refine ⟨3014168868926592839404037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2009445912617728559602691 3014168868926592839404037)
                  ·
                    refine ⟨565156662923736157388257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3014168868926592839404037 565156662923736157388257)
                    ·
                      rfl

theorem cell23_3301916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3, 3, 1, 4].length) (baseStart_3301916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3301916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3301916 prefixEnd_3301916 := by exact prefixLift 3301916
  have htrace : WordTrace (prefixWord ++ tailWord_3301916) baseStart_3301916 baseEnd_3301916 := by
    simpa [prefixWord, tailWord_3301916, baseEnd_3301916] using wordTrace_append hprefix tailTrace_3301916
  have hstable : (prefixWord ++ tailWord_3301916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3301916).length < 2 ^ (prefixWord ++ tailWord_3301916).sum := by decide
  have hdescent : baseEnd_3301916 < baseStart_3301916 := by decide
  rcases family_descends (prefixWord ++ tailWord_3301916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3301955 : List Nat := [1, 1, 1, 3, 1, 2, 1, 2, 5, 6]
def baseStart_3301955 : Nat := 118140960795 + 3301955 * 2 ^ 59
def prefixEnd_3301955 : Nat := 4983230072969 + 3 ^ 40 * 3301955 * 2
def baseEnd_3301955 : Nat := 565163338172244606525697

theorem tailTrace_3301955 : CollatzResearch.WordTrace tailWord_3301955 prefixEnd_3301955 565163338172244606525697 := by
  unfold tailWord_3301955
  simp only [CollatzResearch.WordTrace]
  refine ⟨120432192752588438862427319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80288128501725625908284879 120432192752588438862427319)
  ·
    refine ⟨180648289128882658293640979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120432192752588438862427319 180648289128882658293640979)
    ·
      refine ⟨270972433693323987440461469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180648289128882658293640979 270972433693323987440461469)
      ·
        refine ⟨101614662634996495290173051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 270972433693323987440461469 101614662634996495290173051)
        ·
          refine ⟨152421993952494742935259577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101614662634996495290173051 152421993952494742935259577)
          ·
            refine ⟨114316495464371057201444683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152421993952494742935259577 114316495464371057201444683)
            ·
              refine ⟨171474743196556585802167025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114316495464371057201444683 171474743196556585802167025)
              ·
                refine ⟨128606057397417439351625269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 171474743196556585802167025 128606057397417439351625269)
                ·
                  refine ⟨12056817881007884939214869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 128606057397417439351625269 12056817881007884939214869)
                  ·
                    refine ⟨565163338172244606525697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12056817881007884939214869 565163338172244606525697)
                    ·
                      rfl

theorem cell23_3301955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 5, 6].length) (baseStart_3301955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3301955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3301955 prefixEnd_3301955 := by exact prefixLift 3301955
  have htrace : WordTrace (prefixWord ++ tailWord_3301955) baseStart_3301955 baseEnd_3301955 := by
    simpa [prefixWord, tailWord_3301955, baseEnd_3301955] using wordTrace_append hprefix tailTrace_3301955
  have hstable : (prefixWord ++ tailWord_3301955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3301955).length < 2 ^ (prefixWord ++ tailWord_3301955).sum := by decide
  have hdescent : baseEnd_3301955 < baseStart_3301955 := by decide
  rcases family_descends (prefixWord ++ tailWord_3301955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3301959 : List Nat := [1, 1, 4, 1, 4, 1, 3, 2, 1, 5]
def baseStart_3301959 : Nat := 118140960795 + 3301959 * 2 ^ 59
def prefixEnd_3301959 : Nat := 4983230072969 + 3 ^ 40 * 3301959 * 2
def baseEnd_3301959 : Nat := 565164022813117267975691

theorem tailTrace_3301959 : CollatzResearch.WordTrace tailWord_3301959 prefixEnd_3301959 565164022813117267975691 := by
  unfold tailWord_3301959
  simp only [CollatzResearch.WordTrace]
  refine ⟨120432338644573947545572931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80288225763049298363715287 120432338644573947545572931)
  ·
    refine ⟨180648507966860921318359397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120432338644573947545572931 180648507966860921318359397)
    ·
      refine ⟨33871595243786422747192387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 180648507966860921318359397 33871595243786422747192387)
      ·
        refine ⟨50807392865679634120788581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33871595243786422747192387 50807392865679634120788581)
        ·
          refine ⟨9526386162314931397647859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50807392865679634120788581 9526386162314931397647859)
          ·
            refine ⟨14289579243472397096471789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9526386162314931397647859 14289579243472397096471789)
            ·
              refine ⟨5358592216302148911176921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14289579243472397096471789 5358592216302148911176921)
              ·
                refine ⟨4018944162226611683382691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5358592216302148911176921 4018944162226611683382691)
                ·
                  refine ⟨6028416243339917525074037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4018944162226611683382691 6028416243339917525074037)
                  ·
                    refine ⟨565164022813117267975691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6028416243339917525074037 565164022813117267975691)
                    ·
                      rfl

theorem cell23_3301959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3, 2, 1, 5].length) (baseStart_3301959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3301959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3301959 prefixEnd_3301959 := by exact prefixLift 3301959
  have htrace : WordTrace (prefixWord ++ tailWord_3301959) baseStart_3301959 baseEnd_3301959 := by
    simpa [prefixWord, tailWord_3301959, baseEnd_3301959] using wordTrace_append hprefix tailTrace_3301959
  have hstable : (prefixWord ++ tailWord_3301959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3301959).length < 2 ^ (prefixWord ++ tailWord_3301959).sum := by decide
  have hdescent : baseEnd_3301959 < baseStart_3301959 := by decide
  rcases family_descends (prefixWord ++ tailWord_3301959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3301972 : List Nat := [2, 4, 1, 1, 1, 3, 1, 1, 3, 6]
def baseStart_3301972 : Nat := 118140960795 + 3301972 * 2 ^ 59
def prefixEnd_3301972 : Nat := 4983230072969 + 3 ^ 40 * 3301972 * 2
def baseEnd_3301972 : Nat := 565166247895953417688171

theorem tailTrace_3301972 : CollatzResearch.WordTrace tailWord_3301972 prefixEnd_3301972 565166247895953417688171 := by
  unfold tailWord_3301972
  simp only [CollatzResearch.WordTrace]
  refine ⟨60216406396763425382898085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80288541862351233843864113 60216406396763425382898085)
  ·
    refine ⟨11290576199393142259293391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60216406396763425382898085 11290576199393142259293391)
    ·
      refine ⟨16935864299089713388940087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11290576199393142259293391 16935864299089713388940087)
      ·
        refine ⟨25403796448634570083410131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16935864299089713388940087 25403796448634570083410131)
        ·
          refine ⟨38105694672951855125115197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25403796448634570083410131 38105694672951855125115197)
          ·
            refine ⟨14289635502356945671918199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38105694672951855125115197 14289635502356945671918199)
            ·
              refine ⟨21434453253535418507877299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14289635502356945671918199 21434453253535418507877299)
              ·
                refine ⟨32151679880303127761815949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21434453253535418507877299 32151679880303127761815949)
                ·
                  refine ⟨12056879955113672910680981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32151679880303127761815949 12056879955113672910680981)
                  ·
                    refine ⟨565166247895953417688171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12056879955113672910680981 565166247895953417688171)
                    ·
                      rfl

theorem cell23_3301972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 1, 3, 6].length) (baseStart_3301972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3301972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3301972 prefixEnd_3301972 := by exact prefixLift 3301972
  have htrace : WordTrace (prefixWord ++ tailWord_3301972) baseStart_3301972 baseEnd_3301972 := by
    simpa [prefixWord, tailWord_3301972, baseEnd_3301972] using wordTrace_append hprefix tailTrace_3301972
  have hstable : (prefixWord ++ tailWord_3301972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3301972).length < 2 ^ (prefixWord ++ tailWord_3301972).sum := by decide
  have hdescent : baseEnd_3301972 < baseStart_3301972 := by decide
  rcases family_descends (prefixWord ++ tailWord_3301972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3301985 : List Nat := [1, 2, 3, 1, 1, 15]
def baseStart_3301985 : Nat := 118140960795 + 3301985 * 2 ^ 59
def prefixEnd_3301985 : Nat := 4983230072969 + 3 ^ 40 * 3301985 * 2
def baseEnd_3301985 : Nat := 6977388555293698362971

theorem tailTrace_3301985 : CollatzResearch.WordTrace tailWord_3301985 prefixEnd_3301985 6977388555293698362971 := by
  unfold tailWord_3301985
  simp only [CollatzResearch.WordTrace]
  refine ⟨120433286942479753986019409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80288857961653169324012939 120433286942479753986019409)
  ·
    refine ⟨90324965206859815489514557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120433286942479753986019409 90324965206859815489514557)
    ·
      refine ⟨33871861952572430808567959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90324965206859815489514557 33871861952572430808567959)
      ·
        refine ⟨50807792928858646212851939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33871861952572430808567959 50807792928858646212851939)
        ·
          refine ⟨76211689393287969319277909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50807792928858646212851939 76211689393287969319277909)
          ·
            refine ⟨6977388555293698362971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 15 76211689393287969319277909 6977388555293698362971)
            ·
              rfl

theorem cell23_3301985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 15].length) (baseStart_3301985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3301985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3301985 prefixEnd_3301985 := by exact prefixLift 3301985
  have htrace : WordTrace (prefixWord ++ tailWord_3301985) baseStart_3301985 baseEnd_3301985 := by
    simpa [prefixWord, tailWord_3301985, baseEnd_3301985] using wordTrace_append hprefix tailTrace_3301985
  have hstable : (prefixWord ++ tailWord_3301985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3301985).length < 2 ^ (prefixWord ++ tailWord_3301985).sum := by decide
  have hdescent : baseEnd_3301985 < baseStart_3301985 := by decide
  rcases family_descends (prefixWord ++ tailWord_3301985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3301995 : List Nat := [1, 1, 1, 1, 2, 2, 1, 3, 2, 2, 7]
def baseStart_3301995 : Nat := 118140960795 + 3301995 * 2 ^ 59
def prefixEnd_3301995 : Nat := 4983230072969 + 3 ^ 40 * 3301995 * 2
def baseEnd_3301995 : Nat := 1695510553742913663076907

theorem tailTrace_3301995 : CollatzResearch.WordTrace tailWord_3301995 prefixEnd_3301995 1695510553742913663076907 := by
  unfold tailWord_3301995
  simp only [CollatzResearch.WordTrace]
  refine ⟨120433651672443525693883439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80289101114962350462588959 120433651672443525693883439)
  ·
    refine ⟨180650477508665288540825159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120433651672443525693883439 180650477508665288540825159)
    ·
      refine ⟨270975716262997932811237739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180650477508665288540825159 270975716262997932811237739)
      ·
        refine ⟨406463574394496899216856609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270975716262997932811237739 406463574394496899216856609)
        ·
          refine ⟨304847680795872674412642457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 406463574394496899216856609 304847680795872674412642457)
          ·
            refine ⟨228635760596904505809481843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 304847680795872674412642457 228635760596904505809481843)
            ·
              refine ⟨342953640895356758714222765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 228635760596904505809481843 342953640895356758714222765)
              ·
                refine ⟨128607615335758784517833537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 342953640895356758714222765 128607615335758784517833537)
                ·
                  refine ⟨96455711501819088388375153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 128607615335758784517833537 96455711501819088388375153)
                  ·
                    refine ⟨72341783626364316291281365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 96455711501819088388375153 72341783626364316291281365)
                    ·
                      refine ⟨1695510553742913663076907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 72341783626364316291281365 1695510553742913663076907)
                      ·
                        rfl

theorem cell23_3301995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 2, 7].length) (baseStart_3301995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3301995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3301995 prefixEnd_3301995 := by exact prefixLift 3301995
  have htrace : WordTrace (prefixWord ++ tailWord_3301995) baseStart_3301995 baseEnd_3301995 := by
    simpa [prefixWord, tailWord_3301995, baseEnd_3301995] using wordTrace_append hprefix tailTrace_3301995
  have hstable : (prefixWord ++ tailWord_3301995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3301995).length < 2 ^ (prefixWord ++ tailWord_3301995).sum := by decide
  have hdescent : baseEnd_3301995 < baseStart_3301995 := by decide
  rcases family_descends (prefixWord ++ tailWord_3301995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3302006 : List Nat := [5, 1, 1, 2, 3, 1, 2, 1, 1, 6]
def baseStart_3302006 : Nat := 118140960795 + 3302006 * 2 ^ 59
def prefixEnd_3302006 : Nat := 4983230072969 + 3 ^ 40 * 3302006 * 2
def baseEnd_3302006 : Nat := 565172067343371040013119

theorem tailTrace_3302006 : CollatzResearch.WordTrace tailWord_3302006 prefixEnd_3302006 565172067343371040013119 := by
  unfold tailWord_3302006
  simp only [CollatzResearch.WordTrace]
  refine ⟨7527128304712729660783367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 80289368583602449715022581 7527128304712729660783367)
  ·
    refine ⟨11290692457069094491175051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7527128304712729660783367 11290692457069094491175051)
    ·
      refine ⟨16936038685603641736762577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11290692457069094491175051 16936038685603641736762577)
      ·
        refine ⟨12702029014202731302571933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16936038685603641736762577 12702029014202731302571933)
        ·
          refine ⟨4763260880326024238464475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12702029014202731302571933 4763260880326024238464475)
          ·
            refine ⟨7144891320489036357696713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4763260880326024238464475 7144891320489036357696713)
            ·
              refine ⟨5358668490366777268272535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7144891320489036357696713 5358668490366777268272535)
              ·
                refine ⟨8038002735550165902408803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5358668490366777268272535 8038002735550165902408803)
                ·
                  refine ⟨12057004103325248853613205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8038002735550165902408803 12057004103325248853613205)
                  ·
                    refine ⟨565172067343371040013119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12057004103325248853613205 565172067343371040013119)
                    ·
                      rfl

theorem cell23_3302006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 2, 1, 1, 6].length) (baseStart_3302006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3302006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3302006 prefixEnd_3302006 := by exact prefixLift 3302006
  have htrace : WordTrace (prefixWord ++ tailWord_3302006) baseStart_3302006 baseEnd_3302006 := by
    simpa [prefixWord, tailWord_3302006, baseEnd_3302006] using wordTrace_append hprefix tailTrace_3302006
  have hstable : (prefixWord ++ tailWord_3302006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3302006).length < 2 ^ (prefixWord ++ tailWord_3302006).sum := by decide
  have hdescent : baseEnd_3302006 < baseStart_3302006 := by decide
  rcases family_descends (prefixWord ++ tailWord_3302006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3302009 : List Nat := [1, 2, 1, 3, 3, 3, 2, 1, 1, 2, 4]
def baseStart_3302009 : Nat := 118140960795 + 3302009 * 2 ^ 59
def prefixEnd_3302009 : Nat := 4983230072969 + 3 ^ 40 * 3302009 * 2
def baseEnd_3302009 : Nat := 1695517742472076608301843

theorem tailTrace_3302009 : CollatzResearch.WordTrace tailWord_3302009 prefixEnd_3302009 1695517742472076608301843 := by
  unfold tailWord_3302009
  simp only [CollatzResearch.WordTrace]
  refine ⟨120434162294392806084893081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80289441529595204056595387 120434162294392806084893081)
  ·
    refine ⟨90325621720794604563669811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120434162294392806084893081 90325621720794604563669811)
    ·
      refine ⟨135488432581191906845504717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90325621720794604563669811 135488432581191906845504717)
      ·
        refine ⟨50808162217946965067064269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135488432581191906845504717 50808162217946965067064269)
        ·
          refine ⟨19053060831730111900149101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50808162217946965067064269 19053060831730111900149101)
          ·
            refine ⟨7144897811898791962555913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19053060831730111900149101 7144897811898791962555913)
            ·
              refine ⟨5358673358924093971916935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7144897811898791962555913 5358673358924093971916935)
              ·
                refine ⟨8038010038386140957875403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5358673358924093971916935 8038010038386140957875403)
                ·
                  refine ⟨12057015057579211436813105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8038010038386140957875403 12057015057579211436813105)
                  ·
                    refine ⟨9042761293184408577609829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12057015057579211436813105 9042761293184408577609829)
                    ·
                      refine ⟨1695517742472076608301843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9042761293184408577609829 1695517742472076608301843)
                      ·
                        rfl

theorem cell23_3302009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2, 1, 1, 2, 4].length) (baseStart_3302009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3302009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3302009 prefixEnd_3302009 := by exact prefixLift 3302009
  have htrace : WordTrace (prefixWord ++ tailWord_3302009) baseStart_3302009 baseEnd_3302009 := by
    simpa [prefixWord, tailWord_3302009, baseEnd_3302009] using wordTrace_append hprefix tailTrace_3302009
  have hstable : (prefixWord ++ tailWord_3302009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3302009).length < 2 ^ (prefixWord ++ tailWord_3302009).sum := by decide
  have hdescent : baseEnd_3302009 < baseStart_3302009 := by decide
  rcases family_descends (prefixWord ++ tailWord_3302009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3302013 : List Nat := [1, 4, 1, 1, 5, 1, 1, 2, 3, 2, 2]
def baseStart_3302013 : Nat := 118140960795 + 3302013 * 2 ^ 59
def prefixEnd_3302013 : Nat := 4983230072969 + 3 ^ 40 * 3302013 * 2
def baseEnd_3302013 : Nat := 1695519796394694592651825

theorem tailTrace_3302013 : CollatzResearch.WordTrace tailWord_3302013 prefixEnd_3302013 1695519796394694592651825 := by
  unfold tailWord_3302013
  simp only [CollatzResearch.WordTrace]
  refine ⟨120434308186378314768038693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80289538790918876512025795 120434308186378314768038693)
  ·
    refine ⟨22581432784945934019007255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120434308186378314768038693 22581432784945934019007255)
    ·
      refine ⟨33872149177418901028510883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22581432784945934019007255 33872149177418901028510883)
      ·
        refine ⟨50808223766128351542766325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33872149177418901028510883 50808223766128351542766325)
        ·
          refine ⟨4763270978074532957134343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 50808223766128351542766325 4763270978074532957134343)
          ·
            refine ⟨7144906467111799435701515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4763270978074532957134343 7144906467111799435701515)
            ·
              refine ⟨10717359700667699153552273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7144906467111799435701515 10717359700667699153552273)
              ·
                refine ⟨8038019775500774365164205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10717359700667699153552273 8038019775500774365164205)
                ·
                  refine ⟨3014257415812790386936577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8038019775500774365164205 3014257415812790386936577)
                  ·
                    refine ⟨2260693061859592790202433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3014257415812790386936577 2260693061859592790202433)
                    ·
                      refine ⟨1695519796394694592651825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2260693061859592790202433 1695519796394694592651825)
                      ·
                        rfl

theorem cell23_3302013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 2, 3, 2, 2].length) (baseStart_3302013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3302013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3302013 prefixEnd_3302013 := by exact prefixLift 3302013
  have htrace : WordTrace (prefixWord ++ tailWord_3302013) baseStart_3302013 baseEnd_3302013 := by
    simpa [prefixWord, tailWord_3302013, baseEnd_3302013] using wordTrace_append hprefix tailTrace_3302013
  have hstable : (prefixWord ++ tailWord_3302013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3302013).length < 2 ^ (prefixWord ++ tailWord_3302013).sum := by decide
  have hdescent : baseEnd_3302013 < baseStart_3302013 := by decide
  rcases family_descends (prefixWord ++ tailWord_3302013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3302030 : List Nat := [4, 1, 1, 3, 1, 1, 4, 3, 1, 2, 2]
def baseStart_3302030 : Nat := 118140960795 + 3302030 * 2 ^ 59
def prefixEnd_3302030 : Nat := 4983230072969 + 3 ^ 40 * 3302030 * 2
def baseEnd_3302030 : Nat := 1695528525565821026139247

theorem tailTrace_3302030 : CollatzResearch.WordTrace tailWord_3302030 prefixEnd_3302030 1695528525565821026139247 := by
  unfold tailWord_3302030
  simp only [CollatzResearch.WordTrace]
  refine ⟨15054366028414590833925943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80289952151544484447605029 15054366028414590833925943)
  ·
    refine ⟨22581549042621886250888915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15054366028414590833925943 22581549042621886250888915)
    ·
      refine ⟨33872323563932829376333373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22581549042621886250888915 33872323563932829376333373)
      ·
        refine ⟨12702121336474811016125015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33872323563932829376333373 12702121336474811016125015)
        ·
          refine ⟨19053182004712216524187523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12702121336474811016125015 19053182004712216524187523)
          ·
            refine ⟨28579773007068324786281285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19053182004712216524187523 28579773007068324786281285)
            ·
              refine ⟨5358707438825310897427741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28579773007068324786281285 5358707438825310897427741)
              ·
                refine ⟨2009515289559491586535403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5358707438825310897427741 2009515289559491586535403)
                ·
                  refine ⟨3014272934339237379803105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2009515289559491586535403 3014272934339237379803105)
                  ·
                    refine ⟨2260704700754428034852329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3014272934339237379803105 2260704700754428034852329)
                    ·
                      refine ⟨1695528525565821026139247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2260704700754428034852329 1695528525565821026139247)
                      ·
                        rfl

theorem cell23_3302030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4, 3, 1, 2, 2].length) (baseStart_3302030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3302030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3302030 prefixEnd_3302030 := by exact prefixLift 3302030
  have htrace : WordTrace (prefixWord ++ tailWord_3302030) baseStart_3302030 baseEnd_3302030 := by
    simpa [prefixWord, tailWord_3302030, baseEnd_3302030] using wordTrace_append hprefix tailTrace_3302030
  have hstable : (prefixWord ++ tailWord_3302030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3302030).length < 2 ^ (prefixWord ++ tailWord_3302030).sum := by decide
  have hdescent : baseEnd_3302030 < baseStart_3302030 := by decide
  rcases family_descends (prefixWord ++ tailWord_3302030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3302063 : List Nat := [1, 1, 2, 1, 2, 6, 3, 1, 2, 1, 3]
def baseStart_3302063 : Nat := 118140960795 + 3302063 * 2 ^ 59
def prefixEnd_3302063 : Nat := 4983230072969 + 3 ^ 40 * 3302063 * 2
def baseEnd_3302063 : Nat := 1695545470427419397026595

theorem tailTrace_3302063 : CollatzResearch.WordTrace tailWord_3302063 prefixEnd_3302063 1695545470427419397026595 := by
  unfold tailWord_3302063
  simp only [CollatzResearch.WordTrace]
  refine ⟨120436131836197173307358843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80290754557464782204905895 120436131836197173307358843)
  ·
    refine ⟨180654197754295759961038265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120436131836197173307358843 180654197754295759961038265)
    ·
      refine ⟨135490648315721819970778699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180654197754295759961038265 135490648315721819970778699)
      ·
        refine ⟨203235972473582729956168049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135490648315721819970778699 203235972473582729956168049)
        ·
          refine ⟨152426979355187047467126037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203235972473582729956168049 152426979355187047467126037)
          ·
            refine ⟨7145014657274392850021533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 152426979355187047467126037 7145014657274392850021533)
            ·
              refine ⟨2679380496477897318758075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7145014657274392850021533 2679380496477897318758075)
              ·
                refine ⟨4019070744716845978137113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2679380496477897318758075 4019070744716845978137113)
                ·
                  refine ⟨3014303058537634483602835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4019070744716845978137113 3014303058537634483602835)
                  ·
                    refine ⟨4521454587806451725404253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3014303058537634483602835 4521454587806451725404253)
                    ·
                      refine ⟨1695545470427419397026595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4521454587806451725404253 1695545470427419397026595)
                      ·
                        rfl

theorem cell23_3302063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 3, 1, 2, 1, 3].length) (baseStart_3302063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3302063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3302063 prefixEnd_3302063 := by exact prefixLift 3302063
  have htrace : WordTrace (prefixWord ++ tailWord_3302063) baseStart_3302063 baseEnd_3302063 := by
    simpa [prefixWord, tailWord_3302063, baseEnd_3302063] using wordTrace_append hprefix tailTrace_3302063
  have hstable : (prefixWord ++ tailWord_3302063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3302063).length < 2 ^ (prefixWord ++ tailWord_3302063).sum := by decide
  have hdescent : baseEnd_3302063 < baseStart_3302063 := by decide
  rcases family_descends (prefixWord ++ tailWord_3302063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3302070 : List Nat := [5, 1, 3, 1, 3, 1, 2, 7]
def baseStart_3302070 : Nat := 118140960795 + 3302070 * 2 ^ 59
def prefixEnd_3302070 : Nat := 4983230072969 + 3 ^ 40 * 3302070 * 2
def baseEnd_3302070 : Nat := 62798113510814847023669

theorem tailTrace_3302070 : CollatzResearch.WordTrace tailWord_3302070 prefixEnd_3302070 62798113510814847023669 := by
  unfold tailWord_3302070
  simp only [CollatzResearch.WordTrace]
  refine ⟨7527274196698238343928979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 80290924764781209001909109 7527274196698238343928979)
  ·
    refine ⟨11290911295047357515893469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7527274196698238343928979 11290911295047357515893469)
    ·
      refine ⟨4234091735642759068460051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11290911295047357515893469 4234091735642759068460051)
      ·
        refine ⟨6351137603464138602690077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4234091735642759068460051 6351137603464138602690077)
        ·
          refine ⟨2381676601299051976008779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6351137603464138602690077 2381676601299051976008779)
          ·
            refine ⟨3572514901948577964013169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2381676601299051976008779 3572514901948577964013169)
            ·
              refine ⟨2679386176461433473009877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3572514901948577964013169 2679386176461433473009877)
              ·
                refine ⟨62798113510814847023669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2679386176461433473009877 62798113510814847023669)
                ·
                  rfl

theorem cell23_3302070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 2, 7].length) (baseStart_3302070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3302070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3302070 prefixEnd_3302070 := by exact prefixLift 3302070
  have htrace : WordTrace (prefixWord ++ tailWord_3302070) baseStart_3302070 baseEnd_3302070 := by
    simpa [prefixWord, tailWord_3302070, baseEnd_3302070] using wordTrace_append hprefix tailTrace_3302070
  have hstable : (prefixWord ++ tailWord_3302070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3302070).length < 2 ^ (prefixWord ++ tailWord_3302070).sum := by decide
  have hdescent : baseEnd_3302070 < baseStart_3302070 := by decide
  rcases family_descends (prefixWord ++ tailWord_3302070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3302081 : List Nat := [1, 2, 6, 2, 2, 1, 1, 3, 1, 2, 2]
def baseStart_3302081 : Nat := 118140960795 + 3302081 * 2 ^ 59
def prefixEnd_3302081 : Nat := 4983230072969 + 3 ^ 40 * 3302081 * 2
def baseEnd_3302081 : Nat := 1695554713079200326601513

theorem tailTrace_3302081 : CollatzResearch.WordTrace tailWord_3302081 prefixEnd_3302081 1695554713079200326601513 := by
  unfold tailWord_3302081
  simp only [CollatzResearch.WordTrace]
  refine ⟨120436788350131962381514097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80291192233421308254342731 120436788350131962381514097)
  ·
    refine ⟨90327591262598971786135573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120436788350131962381514097 90327591262598971786135573)
    ·
      refine ⟨4234105840434326802475105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 90327591262598971786135573 4234105840434326802475105)
      ·
        refine ⟨3175579380325745101856329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4234105840434326802475105 3175579380325745101856329)
        ·
          refine ⟨2381684535244308826392247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3175579380325745101856329 2381684535244308826392247)
          ·
            refine ⟨3572526802866463239588371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2381684535244308826392247 3572526802866463239588371)
            ·
              refine ⟨5358790204299694859382557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3572526802866463239588371 5358790204299694859382557)
              ·
                refine ⟨2009546326612385572268459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5358790204299694859382557 2009546326612385572268459)
                ·
                  refine ⟨3014319489918578358402689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2009546326612385572268459 3014319489918578358402689)
                  ·
                    refine ⟨2260739617438933768802017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3014319489918578358402689 2260739617438933768802017)
                    ·
                      refine ⟨1695554713079200326601513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2260739617438933768802017 1695554713079200326601513)
                      ·
                        rfl

theorem cell23_3302081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_3302081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3302081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3302081 prefixEnd_3302081 := by exact prefixLift 3302081
  have htrace : WordTrace (prefixWord ++ tailWord_3302081) baseStart_3302081 baseEnd_3302081 := by
    simpa [prefixWord, tailWord_3302081, baseEnd_3302081] using wordTrace_append hprefix tailTrace_3302081
  have hstable : (prefixWord ++ tailWord_3302081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3302081).length < 2 ^ (prefixWord ++ tailWord_3302081).sum := by decide
  have hdescent : baseEnd_3302081 < baseStart_3302081 := by decide
  rcases family_descends (prefixWord ++ tailWord_3302081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3302120 : List Nat := [2, 1, 4, 1, 4, 1, 1, 3, 2, 2, 2]
def baseStart_3302120 : Nat := 118140960795 + 3302120 * 2 ^ 59
def prefixEnd_3302120 : Nat := 4983230072969 + 3 ^ 40 * 3302120 * 2
def baseEnd_3302120 : Nat := 1695574738824725674013833

theorem tailTrace_3302120 : CollatzResearch.WordTrace tailWord_3302120 prefixEnd_3302120 1695574738824725674013833 := by
  unfold tailWord_3302120
  simp only [CollatzResearch.WordTrace]
  refine ⟨60219105398495336021091907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80292140531327114694789209 60219105398495336021091907)
  ·
    refine ⟨90328658097743004031637861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60219105398495336021091907 90328658097743004031637861)
    ·
      refine ⟨16936623393326813255932099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90328658097743004031637861 16936623393326813255932099)
      ·
        refine ⟨25404935089990219883898149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16936623393326813255932099 25404935089990219883898149)
        ·
          refine ⟨4763425329373166228230903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25404935089990219883898149 4763425329373166228230903)
          ·
            refine ⟨7145137994059749342346355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4763425329373166228230903 7145137994059749342346355)
            ·
              refine ⟨10717706991089624013519533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7145137994059749342346355 10717706991089624013519533)
              ·
                refine ⟨4019140121658609005069825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10717706991089624013519533 4019140121658609005069825)
                ·
                  refine ⟨3014355091243956753802369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4019140121658609005069825 3014355091243956753802369)
                  ·
                    refine ⟨2260766318432967565351777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3014355091243956753802369 2260766318432967565351777)
                    ·
                      refine ⟨1695574738824725674013833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2260766318432967565351777 1695574738824725674013833)
                      ·
                        rfl

theorem cell23_3302120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 3, 2, 2, 2].length) (baseStart_3302120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3302120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3302120 prefixEnd_3302120 := by exact prefixLift 3302120
  have htrace : WordTrace (prefixWord ++ tailWord_3302120) baseStart_3302120 baseEnd_3302120 := by
    simpa [prefixWord, tailWord_3302120, baseEnd_3302120] using wordTrace_append hprefix tailTrace_3302120
  have hstable : (prefixWord ++ tailWord_3302120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3302120).length < 2 ^ (prefixWord ++ tailWord_3302120).sum := by decide
  have hdescent : baseEnd_3302120 < baseStart_3302120 := by decide
  rcases family_descends (prefixWord ++ tailWord_3302120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3302159 : List Nat := [1, 1, 2, 1, 1, 1, 5, 4, 2, 1, 4]
def baseStart_3302159 : Nat := 118140960795 + 3302159 * 2 ^ 59
def prefixEnd_3302159 : Nat := 4983230072969 + 3 ^ 40 * 3302159 * 2
def baseEnd_3302159 : Nat := 1695594764570251021426153

theorem tailTrace_3302159 : CollatzResearch.WordTrace tailWord_3302159 prefixEnd_3302159 1695594764570251021426153 := by
  unfold tailWord_3302159
  simp only [CollatzResearch.WordTrace]
  refine ⟨120439633243849381702853531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80293088829232921135235687 120439633243849381702853531)
  ·
    refine ⟨180659449865774072554280297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120439633243849381702853531 180659449865774072554280297)
    ·
      refine ⟨135494587399330554415710223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180659449865774072554280297 135494587399330554415710223)
      ·
        refine ⟨203241881098995831623565335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135494587399330554415710223 203241881098995831623565335)
        ·
          refine ⟨304862821648493747435348003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203241881098995831623565335 304862821648493747435348003)
          ·
            refine ⟨457294232472740621153022005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 304862821648493747435348003 457294232472740621153022005)
            ·
              refine ⟨42871334294319433233095813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 457294232472740621153022005 42871334294319433233095813)
              ·
                refine ⟨8038375180184893731205465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42871334294319433233095813 8038375180184893731205465)
                ·
                  refine ⟨6028781385138670298404099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8038375180184893731205465 6028781385138670298404099)
                  ·
                    refine ⟨9043172077708005447606149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6028781385138670298404099 9043172077708005447606149)
                    ·
                      refine ⟨1695594764570251021426153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9043172077708005447606149 1695594764570251021426153)
                      ·
                        rfl

theorem cell23_3302159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 4, 2, 1, 4].length) (baseStart_3302159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3302159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3302159 prefixEnd_3302159 := by exact prefixLift 3302159
  have htrace : WordTrace (prefixWord ++ tailWord_3302159) baseStart_3302159 baseEnd_3302159 := by
    simpa [prefixWord, tailWord_3302159, baseEnd_3302159] using wordTrace_append hprefix tailTrace_3302159
  have hstable : (prefixWord ++ tailWord_3302159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3302159).length < 2 ^ (prefixWord ++ tailWord_3302159).sum := by decide
  have hdescent : baseEnd_3302159 < baseStart_3302159 := by decide
  rcases family_descends (prefixWord ++ tailWord_3302159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3302176 : List Nat := [2, 1, 1, 5, 1, 2, 1, 1, 1, 6, 2]
def baseStart_3302176 : Nat := 118140960795 + 3302176 * 2 ^ 59
def prefixEnd_3302176 : Nat := 4983230072969 + 3 ^ 40 * 3302176 * 2
def baseEnd_3302176 : Nat := 1695603493741377454913575

theorem tailTrace_3302176 : CollatzResearch.WordTrace tailWord_3302176 prefixEnd_3302176 1695603493741377454913575 := by
  unfold tailWord_3302176
  simp only [CollatzResearch.WordTrace]
  refine ⟨60220126642393896803111191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80293502189858529070814921 60220126642393896803111191)
  ·
    refine ⟨90330189963590845204666787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60220126642393896803111191 90330189963590845204666787)
    ·
      refine ⟨135495284945386267807000181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90330189963590845204666787 135495284945386267807000181)
      ·
        refine ⟨12702682963629962606906267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 135495284945386267807000181 12702682963629962606906267)
        ·
          refine ⟨19054024445444943910359401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12702682963629962606906267 19054024445444943910359401)
          ·
            refine ⟨14290518334083707932769551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19054024445444943910359401 14290518334083707932769551)
            ·
              refine ⟨21435777501125561899154327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14290518334083707932769551 21435777501125561899154327)
              ·
                refine ⟨32153666251688342848731491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21435777501125561899154327 32153666251688342848731491)
                ·
                  refine ⟨48230499377532514273097237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32153666251688342848731491 48230499377532514273097237)
                  ·
                    refine ⟨2260804658321836606551433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 48230499377532514273097237 2260804658321836606551433)
                    ·
                      refine ⟨1695603493741377454913575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2260804658321836606551433 1695603493741377454913575)
                      ·
                        rfl

theorem cell23_3302176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 1, 1, 6, 2].length) (baseStart_3302176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3302176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3302176 prefixEnd_3302176 := by exact prefixLift 3302176
  have htrace : WordTrace (prefixWord ++ tailWord_3302176) baseStart_3302176 baseEnd_3302176 := by
    simpa [prefixWord, tailWord_3302176, baseEnd_3302176] using wordTrace_append hprefix tailTrace_3302176
  have hstable : (prefixWord ++ tailWord_3302176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3302176).length < 2 ^ (prefixWord ++ tailWord_3302176).sum := by decide
  have hdescent : baseEnd_3302176 < baseStart_3302176 := by decide
  rcases family_descends (prefixWord ++ tailWord_3302176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3302179 : List Nat := [1, 1, 1, 4, 2, 1, 1, 4, 1, 4, 3]
def baseStart_3302179 : Nat := 118140960795 + 3302179 * 2 ^ 59
def prefixEnd_3302179 : Nat := 4983230072969 + 3 ^ 40 * 3302179 * 2
def baseEnd_3302179 : Nat := 1695605034183340943176061

theorem tailTrace_3302179 : CollatzResearch.WordTrace tailWord_3302179 prefixEnd_3302179 1695605034183340943176061 := by
  unfold tailWord_3302179
  simp only [CollatzResearch.WordTrace]
  refine ⟨120440362703776925118581591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80293575135851283412387727 120440362703776925118581591)
  ·
    refine ⟨180660544055665387677872387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120440362703776925118581591 180660544055665387677872387)
    ·
      refine ⟨270990816083498081516808581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180660544055665387677872387 270990816083498081516808581)
      ·
        refine ⟨50810778015655890284401609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 270990816083498081516808581 50810778015655890284401609)
        ·
          refine ⟨38108083511741917713301207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50810778015655890284401609 38108083511741917713301207)
          ·
            refine ⟨57162125267612876569951811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38108083511741917713301207 57162125267612876569951811)
            ·
              refine ⟨85743187901419314854927717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57162125267612876569951811 85743187901419314854927717)
              ·
                refine ⟨16076847731516121535298947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85743187901419314854927717 16076847731516121535298947)
                ·
                  refine ⟨24115271597274182302948421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16076847731516121535298947 24115271597274182302948421)
                  ·
                    refine ⟨4521613424488909181802829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24115271597274182302948421 4521613424488909181802829)
                    ·
                      refine ⟨1695605034183340943176061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4521613424488909181802829 1695605034183340943176061)
                      ·
                        rfl

theorem cell23_3302179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 4, 1, 4, 3].length) (baseStart_3302179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3302179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3302179 prefixEnd_3302179 := by exact prefixLift 3302179
  have htrace : WordTrace (prefixWord ++ tailWord_3302179) baseStart_3302179 baseEnd_3302179 := by
    simpa [prefixWord, tailWord_3302179, baseEnd_3302179] using wordTrace_append hprefix tailTrace_3302179
  have hstable : (prefixWord ++ tailWord_3302179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3302179).length < 2 ^ (prefixWord ++ tailWord_3302179).sum := by decide
  have hdescent : baseEnd_3302179 < baseStart_3302179 := by decide
  rcases family_descends (prefixWord ++ tailWord_3302179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3302243 : List Nat := [1, 1, 1, 5, 3, 1, 2, 2, 3, 1, 3]
def baseStart_3302243 : Nat := 118140960795 + 3302243 * 2 ^ 59
def prefixEnd_3302243 : Nat := 4983230072969 + 3 ^ 40 * 3302243 * 2
def baseEnd_3302243 : Nat := 1695637896945228692775767

theorem tailTrace_3302243 : CollatzResearch.WordTrace tailWord_3302243 prefixEnd_3302243 1695637896945228692775767 := by
  unfold tailWord_3302243
  simp only [CollatzResearch.WordTrace]
  refine ⟨120442696975545064048911383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80295131317030042699274255 120442696975545064048911383)
  ·
    refine ⟨180664045463317596073367075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120442696975545064048911383 180664045463317596073367075)
    ·
      refine ⟨270996068194976394110050613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180664045463317596073367075 270996068194976394110050613)
      ·
        refine ⟨25405881393279036947817245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 270996068194976394110050613 25405881393279036947817245)
        ·
          refine ⟨9527205522479638855431467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25405881393279036947817245 9527205522479638855431467)
          ·
            refine ⟨14290808283719458283147201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9527205522479638855431467 14290808283719458283147201)
            ·
              refine ⟨10718106212789593712360401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14290808283719458283147201 10718106212789593712360401)
              ·
                refine ⟨8038579659592195284270301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10718106212789593712360401 8038579659592195284270301)
                ·
                  refine ⟨3014467372347073231601363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8038579659592195284270301 3014467372347073231601363)
                  ·
                    refine ⟨4521701058520609847402045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3014467372347073231601363 4521701058520609847402045)
                    ·
                      refine ⟨1695637896945228692775767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4521701058520609847402045 1695637896945228692775767)
                      ·
                        rfl

theorem cell23_3302243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 2, 3, 1, 3].length) (baseStart_3302243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3302243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3302243 prefixEnd_3302243 := by exact prefixLift 3302243
  have htrace : WordTrace (prefixWord ++ tailWord_3302243) baseStart_3302243 baseEnd_3302243 := by
    simpa [prefixWord, tailWord_3302243, baseEnd_3302243] using wordTrace_append hprefix tailTrace_3302243
  have hstable : (prefixWord ++ tailWord_3302243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3302243).length < 2 ^ (prefixWord ++ tailWord_3302243).sum := by decide
  have hdescent : baseEnd_3302243 < baseStart_3302243 := by decide
  rcases family_descends (prefixWord ++ tailWord_3302243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3302253 : List Nat := [1, 5, 1, 1, 1, 1, 1, 5, 2, 3, 2]
def baseStart_3302253 : Nat := 118140960795 + 3302253 * 2 ^ 59
def prefixEnd_3302253 : Nat := 4983230072969 + 3 ^ 40 * 3302253 * 2
def baseEnd_3302253 : Nat := 1695643031751773653650721

theorem tailTrace_3302253 : CollatzResearch.WordTrace tailWord_3302253 prefixEnd_3302253 1695643031751773653650721 := by
  unfold tailWord_3302253
  simp only [CollatzResearch.WordTrace]
  refine ⟨120443061705508835756775413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80295374470339223837850275 120443061705508835756775413)
  ·
    refine ⟨11291537034891453352197695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 120443061705508835756775413 11291537034891453352197695)
    ·
      refine ⟨16937305552337180028296543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11291537034891453352197695 16937305552337180028296543)
      ·
        refine ⟨25405958328505770042444815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16937305552337180028296543 25405958328505770042444815)
        ·
          refine ⟨38108937492758655063667223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25405958328505770042444815 38108937492758655063667223)
          ·
            refine ⟨57163406239137982595500835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38108937492758655063667223 57163406239137982595500835)
            ·
              refine ⟨85745109358706973893251253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57163406239137982595500835 85745109358706973893251253)
              ·
                refine ⟨8038604002378778802492305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 85745109358706973893251253 8038604002378778802492305)
                ·
                  refine ⟨6028953001784084101869229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8038604002378778802492305 6028953001784084101869229)
                  ·
                    refine ⟨2260857375669031538200961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6028953001784084101869229 2260857375669031538200961)
                    ·
                      refine ⟨1695643031751773653650721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2260857375669031538200961 1695643031751773653650721)
                      ·
                        rfl

theorem cell23_3302253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 5, 2, 3, 2].length) (baseStart_3302253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3302253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3302253 prefixEnd_3302253 := by exact prefixLift 3302253
  have htrace : WordTrace (prefixWord ++ tailWord_3302253) baseStart_3302253 baseEnd_3302253 := by
    simpa [prefixWord, tailWord_3302253, baseEnd_3302253] using wordTrace_append hprefix tailTrace_3302253
  have hstable : (prefixWord ++ tailWord_3302253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3302253).length < 2 ^ (prefixWord ++ tailWord_3302253).sum := by decide
  have hdescent : baseEnd_3302253 < baseStart_3302253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3302253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3302254 : List Nat := [4, 1, 2, 3, 3, 1, 1, 3, 1, 4]
def baseStart_3302254 : Nat := 118140960795 + 3302254 * 2 ^ 59
def prefixEnd_3302254 : Nat := 4983230072969 + 3 ^ 40 * 3302254 * 2
def baseEnd_3302254 : Nat := 565214515077476049912739

theorem tailTrace_3302254 : CollatzResearch.WordTrace tailWord_3302254 prefixEnd_3302254 565214515077476049912739 := by
  unfold tailWord_3302254
  simp only [CollatzResearch.WordTrace]
  refine ⟨15055387272313151615945227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80295398785670141951707877 15055387272313151615945227)
  ·
    refine ⟨22583080908469727423917841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15055387272313151615945227 22583080908469727423917841)
    ·
      refine ⟨16937310681352295567938381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22583080908469727423917841 16937310681352295567938381)
      ·
        refine ⟨6351491505507110837976893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16937310681352295567938381 6351491505507110837976893)
        ·
          refine ⟨2381809314565166564241335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6351491505507110837976893 2381809314565166564241335)
          ·
            refine ⟨3572713971847749846362003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2381809314565166564241335 3572713971847749846362003)
            ·
              refine ⟨5359070957771624769543005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3572713971847749846362003 5359070957771624769543005)
              ·
                refine ⟨2009651609164359288578627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5359070957771624769543005 2009651609164359288578627)
                ·
                  refine ⟨3014477413746538932867941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2009651609164359288578627 3014477413746538932867941)
                  ·
                    refine ⟨565214515077476049912739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3014477413746538932867941 565214515077476049912739)
                    ·
                      rfl

theorem cell23_3302254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 1, 3, 1, 4].length) (baseStart_3302254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3302254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3302254 prefixEnd_3302254 := by exact prefixLift 3302254
  have htrace : WordTrace (prefixWord ++ tailWord_3302254) baseStart_3302254 baseEnd_3302254 := by
    simpa [prefixWord, tailWord_3302254, baseEnd_3302254] using wordTrace_append hprefix tailTrace_3302254
  have hstable : (prefixWord ++ tailWord_3302254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3302254).length < 2 ^ (prefixWord ++ tailWord_3302254).sum := by decide
  have hdescent : baseEnd_3302254 < baseStart_3302254 := by decide
  rcases family_descends (prefixWord ++ tailWord_3302254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3302259 : List Nat := [1, 1, 1, 2, 2, 1, 4, 4, 1, 6]
def baseStart_3302259 : Nat := 118140960795 + 3302259 * 2 ^ 59
def prefixEnd_3302259 : Nat := 4983230072969 + 3 ^ 40 * 3302259 * 2
def baseEnd_3302259 : Nat := 565215370878566876725231

theorem tailTrace_3302259 : CollatzResearch.WordTrace tailWord_3302259 prefixEnd_3302259 565215370878566876725231 := by
  unfold tailWord_3302259
  simp only [CollatzResearch.WordTrace]
  refine ⟨120443280543487098781493831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80295520362324732520995887 120443280543487098781493831)
  ·
    refine ⟨180664920815230648172240747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120443280543487098781493831 180664920815230648172240747)
    ·
      refine ⟨270997381222845972258361121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180664920815230648172240747 270997381222845972258361121)
      ·
        refine ⟨203248035917134479193770841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 270997381222845972258361121 203248035917134479193770841)
        ·
          refine ⟨152436026937850859395328131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203248035917134479193770841 152436026937850859395328131)
          ·
            refine ⟨228654040406776289092992197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152436026937850859395328131 228654040406776289092992197)
            ·
              refine ⟨42872632576270554204936037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 228654040406776289092992197 42872632576270554204936037)
              ·
                refine ⟨8038618608050728913425507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42872632576270554204936037 8038618608050728913425507)
                ·
                  refine ⟨12057927912076093370138261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8038618608050728913425507 12057927912076093370138261)
                  ·
                    refine ⟨565215370878566876725231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12057927912076093370138261 565215370878566876725231)
                    ·
                      rfl

theorem cell23_3302259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 4, 1, 6].length) (baseStart_3302259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3302259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3302259 prefixEnd_3302259 := by exact prefixLift 3302259
  have htrace : WordTrace (prefixWord ++ tailWord_3302259) baseStart_3302259 baseEnd_3302259 := by
    simpa [prefixWord, tailWord_3302259, baseEnd_3302259] using wordTrace_append hprefix tailTrace_3302259
  have hstable : (prefixWord ++ tailWord_3302259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3302259).length < 2 ^ (prefixWord ++ tailWord_3302259).sum := by decide
  have hdescent : baseEnd_3302259 < baseStart_3302259 := by decide
  rcases family_descends (prefixWord ++ tailWord_3302259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3302277 : List Nat := [1, 3, 1, 1, 3, 4, 3, 2, 1, 1, 3]
def baseStart_3302277 : Nat := 118140960795 + 3302277 * 2 ^ 59
def prefixEnd_3302277 : Nat := 4983230072969 + 3 ^ 40 * 3302277 * 2
def baseEnd_3302277 : Nat := 1695655355287481559750611

theorem tailTrace_3302277 : CollatzResearch.WordTrace tailWord_3302277 prefixEnd_3302277 1695655355287481559750611 := by
  unfold tailWord_3302277
  simp only [CollatzResearch.WordTrace]
  refine ⟨120443937057421887855649085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80295958038281258570432723 120443937057421887855649085)
  ·
    refine ⟨45166476396533207945868407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120443937057421887855649085 45166476396533207945868407)
    ·
      refine ⟨67749714594799811918802611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45166476396533207945868407 67749714594799811918802611)
      ·
        refine ⟨101624571892199717878203917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67749714594799811918802611 101624571892199717878203917)
        ·
          refine ⟨38109214459574894204326469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101624571892199717878203917 38109214459574894204326469)
          ·
            refine ⟨7145477711170292663311213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38109214459574894204326469 7145477711170292663311213)
            ·
              refine ⟨2679554141688859748741705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7145477711170292663311213 2679554141688859748741705)
              ·
                refine ⟨2009665606266644811556279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2679554141688859748741705 2009665606266644811556279)
                ·
                  refine ⟨3014498409399967217334419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2009665606266644811556279 3014498409399967217334419)
                  ·
                    refine ⟨4521747614099950826001629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3014498409399967217334419 4521747614099950826001629)
                    ·
                      refine ⟨1695655355287481559750611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4521747614099950826001629 1695655355287481559750611)
                      ·
                        rfl

theorem cell23_3302277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 3, 2, 1, 1, 3].length) (baseStart_3302277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3302277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3302277 prefixEnd_3302277 := by exact prefixLift 3302277
  have htrace : WordTrace (prefixWord ++ tailWord_3302277) baseStart_3302277 baseEnd_3302277 := by
    simpa [prefixWord, tailWord_3302277, baseEnd_3302277] using wordTrace_append hprefix tailTrace_3302277
  have hstable : (prefixWord ++ tailWord_3302277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3302277).length < 2 ^ (prefixWord ++ tailWord_3302277).sum := by decide
  have hdescent : baseEnd_3302277 < baseStart_3302277 := by decide
  rcases family_descends (prefixWord ++ tailWord_3302277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3302293 : List Nat := [1, 3, 2, 1, 1, 5, 1, 3, 2, 4]
def baseStart_3302293 : Nat := 118140960795 + 3302293 * 2 ^ 59
def prefixEnd_3302293 : Nat := 4983230072969 + 3 ^ 40 * 3302293 * 2
def baseEnd_3302293 : Nat := 565221190325984499050179

theorem tailTrace_3302293 : CollatzResearch.WordTrace tailWord_3302293 prefixEnd_3302293 565221190325984499050179 := by
  unfold tailWord_3302293
  simp only [CollatzResearch.WordTrace]
  refine ⟨120444520625363922588231533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80296347083575948392154355 120444520625363922588231533)
  ·
    refine ⟨45166695234511470970586825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120444520625363922588231533 45166695234511470970586825)
    ·
      refine ⟨33875021425883603227940119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45166695234511470970586825 33875021425883603227940119)
      ·
        refine ⟨50812532138825404841910179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33875021425883603227940119 50812532138825404841910179)
        ·
          refine ⟨76218798208238107262865269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50812532138825404841910179 76218798208238107262865269)
          ·
            refine ⟨7145512332022322555893619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 76218798208238107262865269 7145512332022322555893619)
            ·
              refine ⟨10718268498033483833840429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7145512332022322555893619 10718268498033483833840429)
              ·
                refine ⟨4019350686762556437690161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10718268498033483833840429 4019350686762556437690161)
                ·
                  refine ⟨3014513015071917328267621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4019350686762556437690161 3014513015071917328267621)
                  ·
                    refine ⟨565221190325984499050179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3014513015071917328267621 565221190325984499050179)
                    ·
                      rfl

theorem cell23_3302293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 3, 2, 4].length) (baseStart_3302293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3302293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3302293 prefixEnd_3302293 := by exact prefixLift 3302293
  have htrace : WordTrace (prefixWord ++ tailWord_3302293) baseStart_3302293 baseEnd_3302293 := by
    simpa [prefixWord, tailWord_3302293, baseEnd_3302293] using wordTrace_append hprefix tailTrace_3302293
  have hstable : (prefixWord ++ tailWord_3302293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3302293).length < 2 ^ (prefixWord ++ tailWord_3302293).sum := by decide
  have hdescent : baseEnd_3302293 < baseStart_3302293 := by decide
  rcases family_descends (prefixWord ++ tailWord_3302293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3302303 : List Nat := [1, 1, 2, 5, 2, 2, 1, 1, 3, 2, 3]
def baseStart_3302303 : Nat := 118140960795 + 3302303 * 2 ^ 59
def prefixEnd_3302303 : Nat := 4983230072969 + 3 ^ 40 * 3302303 * 2
def baseEnd_3302303 : Nat := 1695668705784498458025491

theorem tailTrace_3302303 : CollatzResearch.WordTrace tailWord_3302303 prefixEnd_3302303 1695668705784498458025491 := by
  unfold tailWord_3302303
  simp only [CollatzResearch.WordTrace]
  refine ⟨120444885355327694296095563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80296590236885129530730375 120444885355327694296095563)
  ·
    refine ⟨180667328032991541444143345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120444885355327694296095563 180667328032991541444143345)
    ·
      refine ⟨135500496024743656083107509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180667328032991541444143345 135500496024743656083107509)
      ·
        refine ⟨12703171502319717757791329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 135500496024743656083107509 12703171502319717757791329)
        ·
          refine ⟨9527378626739788318343497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12703171502319717757791329 9527378626739788318343497)
          ·
            refine ⟨7145533970054841238757623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9527378626739788318343497 7145533970054841238757623)
            ·
              refine ⟨10718300955082261858136435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7145533970054841238757623 10718300955082261858136435)
              ·
                refine ⟨16077451432623392787204653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10718300955082261858136435 16077451432623392787204653)
                ·
                  refine ⟨6029044287233772295201745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16077451432623392787204653 6029044287233772295201745)
                  ·
                    refine ⟨4521783215425329221401309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6029044287233772295201745 4521783215425329221401309)
                    ·
                      refine ⟨1695668705784498458025491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4521783215425329221401309 1695668705784498458025491)
                      ·
                        rfl

theorem cell23_3302303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 1, 3, 2, 3].length) (baseStart_3302303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3302303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3302303 prefixEnd_3302303 := by exact prefixLift 3302303
  have htrace : WordTrace (prefixWord ++ tailWord_3302303) baseStart_3302303 baseEnd_3302303 := by
    simpa [prefixWord, tailWord_3302303, baseEnd_3302303] using wordTrace_append hprefix tailTrace_3302303
  have hstable : (prefixWord ++ tailWord_3302303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3302303).length < 2 ^ (prefixWord ++ tailWord_3302303).sum := by decide
  have hdescent : baseEnd_3302303 < baseStart_3302303 := by decide
  rcases family_descends (prefixWord ++ tailWord_3302303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3302306 : List Nat := [3, 3, 1, 2, 2, 1, 2, 9]
def baseStart_3302306 : Nat := 118140960795 + 3302306 * 2 ^ 59
def prefixEnd_3302306 : Nat := 4983230072969 + 3 ^ 40 * 3302306 * 2
def baseEnd_3302306 : Nat := 62802601712091183195851

theorem tailTrace_3302306 : CollatzResearch.WordTrace tailWord_3302306 prefixEnd_3302306 62802601712091183195851 := by
  unfold tailWord_3302306
  simp only [CollatzResearch.WordTrace]
  refine ⟨30111248693579206452113693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80296663182877883872303181 30111248693579206452113693)
  ·
    refine ⟨11291718260092202419542635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30111248693579206452113693 11291718260092202419542635)
    ·
      refine ⟨16937577390138303629313953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11291718260092202419542635 16937577390138303629313953)
      ·
        refine ⟨12703183042603727721985465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16937577390138303629313953 12703183042603727721985465)
        ·
          refine ⟨9527387281952795791489099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12703183042603727721985465 9527387281952795791489099)
          ·
            refine ⟨14291080922929193687233649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9527387281952795791489099 14291080922929193687233649)
            ·
              refine ⟨10718310692196895265425237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14291080922929193687233649 10718310692196895265425237)
              ·
                refine ⟨62802601712091183195851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10718310692196895265425237 62802601712091183195851)
                ·
                  rfl

theorem cell23_3302306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 9].length) (baseStart_3302306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3302306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3302306 prefixEnd_3302306 := by exact prefixLift 3302306
  have htrace : WordTrace (prefixWord ++ tailWord_3302306) baseStart_3302306 baseEnd_3302306 := by
    simpa [prefixWord, tailWord_3302306, baseEnd_3302306] using wordTrace_append hprefix tailTrace_3302306
  have hstable : (prefixWord ++ tailWord_3302306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3302306).length < 2 ^ (prefixWord ++ tailWord_3302306).sum := by decide
  have hdescent : baseEnd_3302306 < baseStart_3302306 := by decide
  rcases family_descends (prefixWord ++ tailWord_3302306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3302316 : List Nat := [2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 3]
def baseStart_3302316 : Nat := 118140960795 + 3302316 * 2 ^ 59
def prefixEnd_3302316 : Nat := 4983230072969 + 3 ^ 40 * 3302316 * 2
def baseEnd_3302316 : Nat := 1695675381033006907162931

theorem tailTrace_3302316 : CollatzResearch.WordTrace tailWord_3302316 prefixEnd_3302316 1695675381033006907162931 := by
  unfold tailWord_3302316
  simp only [CollatzResearch.WordTrace]
  refine ⟨60222679752140298758159401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80296906336187065010879201 60222679752140298758159401)
  ·
    refine ⟨45167009814105224068619551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60222679752140298758159401 45167009814105224068619551)
    ·
      refine ⟨67750514721157836102929327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45167009814105224068619551 67750514721157836102929327)
      ·
        refine ⟨101625772081736754154393991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67750514721157836102929327 101625772081736754154393991)
        ·
          refine ⟨152438658122605131231590987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101625772081736754154393991 152438658122605131231590987)
          ·
            refine ⟨228657987183907696847386481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152438658122605131231590987 228657987183907696847386481)
            ·
              refine ⟨171493490387930772635539861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 228657987183907696847386481 171493490387930772635539861)
              ·
                refine ⟨8038757361934254967290931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 171493490387930772635539861 8038757361934254967290931)
                ·
                  refine ⟨12058136042901382450936397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8038757361934254967290931 12058136042901382450936397)
                  ·
                    refine ⟨4521801016088018419101149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12058136042901382450936397 4521801016088018419101149)
                    ·
                      refine ⟨1695675381033006907162931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4521801016088018419101149 1695675381033006907162931)
                      ·
                        rfl

theorem cell23_3302316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 3].length) (baseStart_3302316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3302316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3302316 prefixEnd_3302316 := by exact prefixLift 3302316
  have htrace : WordTrace (prefixWord ++ tailWord_3302316) baseStart_3302316 baseEnd_3302316 := by
    simpa [prefixWord, tailWord_3302316, baseEnd_3302316] using wordTrace_append hprefix tailTrace_3302316
  have hstable : (prefixWord ++ tailWord_3302316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3302316).length < 2 ^ (prefixWord ++ tailWord_3302316).sum := by decide
  have hdescent : baseEnd_3302316 < baseStart_3302316 := by decide
  rcases family_descends (prefixWord ++ tailWord_3302316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3302340 : List Nat := [2, 3, 3, 3, 1, 2, 1, 8]
def baseStart_3302340 : Nat := 118140960795 + 3302340 * 2 ^ 59
def prefixEnd_3302340 : Nat := 4983230072969 + 3 ^ 40 * 3302340 * 2
def baseEnd_3302340 : Nat := 62803248317359807898623

theorem tailTrace_3302340 : CollatzResearch.WordTrace tailWord_3302340 prefixEnd_3302340 62803248317359807898623 := by
  unfold tailWord_3302340
  simp only [CollatzResearch.WordTrace]
  refine ⟨60223117428096824807596237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80297489904129099743461649 60223117428096824807596237)
  ·
    refine ⟨22583669035536309302848589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60223117428096824807596237 22583669035536309302848589)
    ·
      refine ⟨8468875888326115988568221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22583669035536309302848589 8468875888326115988568221)
      ·
        refine ⟨3175828458122293495713083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8468875888326115988568221 3175828458122293495713083)
        ·
          refine ⟨4763742687183440243569625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3175828458122293495713083 4763742687183440243569625)
          ·
            refine ⟨3572807015387580182677219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4763742687183440243569625 3572807015387580182677219)
            ·
              refine ⟨5359210523081370274015829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3572807015387580182677219 5359210523081370274015829)
              ·
                refine ⟨62803248317359807898623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5359210523081370274015829 62803248317359807898623)
                ·
                  rfl

theorem cell23_3302340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 1, 8].length) (baseStart_3302340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3302340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3302340 prefixEnd_3302340 := by exact prefixLift 3302340
  have htrace : WordTrace (prefixWord ++ tailWord_3302340) baseStart_3302340 baseEnd_3302340 := by
    simpa [prefixWord, tailWord_3302340, baseEnd_3302340] using wordTrace_append hprefix tailTrace_3302340
  have hstable : (prefixWord ++ tailWord_3302340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3302340).length < 2 ^ (prefixWord ++ tailWord_3302340).sum := by decide
  have hdescent : baseEnd_3302340 < baseStart_3302340 := by decide
  rcases family_descends (prefixWord ++ tailWord_3302340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3302343 : List Nat := [1, 1, 4, 1, 1, 2, 3, 2, 3, 3, 2]
def baseStart_3302343 : Nat := 118140960795 + 3302343 * 2 ^ 59
def prefixEnd_3302343 : Nat := 4983230072969 + 3 ^ 40 * 3302343 * 2
def baseEnd_3302343 : Nat := 1695689245010678301525307

theorem tailTrace_3302343 : CollatzResearch.WordTrace tailWord_3302343 prefixEnd_3302343 1695689245010678301525307 := by
  unfold tailWord_3302343
  simp only [CollatzResearch.WordTrace]
  refine ⟨120446344275182781127551683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80297562850121854085034455 120446344275182781127551683)
  ·
    refine ⟨180669516412774171691327525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120446344275182781127551683 180669516412774171691327525)
    ·
      refine ⟨33875534327395157192123911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 180669516412774171691327525 33875534327395157192123911)
      ·
        refine ⟨50813301491092735788185867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33875534327395157192123911 50813301491092735788185867)
        ·
          refine ⟨76219952236639103682278801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50813301491092735788185867 76219952236639103682278801)
          ·
            refine ⟨57164964177479327761709101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76219952236639103682278801 57164964177479327761709101)
            ·
              refine ⟨21436861566554747910640913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57164964177479327761709101 21436861566554747910640913)
              ·
                refine ⟨16077646174916060932980685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21436861566554747910640913 16077646174916060932980685)
                ·
                  refine ⟨6029117315593522849867757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16077646174916060932980685 6029117315593522849867757)
                  ·
                    refine ⟨2260918993347571068700409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6029117315593522849867757 2260918993347571068700409)
                    ·
                      refine ⟨1695689245010678301525307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2260918993347571068700409 1695689245010678301525307)
                      ·
                        rfl

theorem cell23_3302343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 2, 3, 3, 2].length) (baseStart_3302343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3302343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3302343 prefixEnd_3302343 := by exact prefixLift 3302343
  have htrace : WordTrace (prefixWord ++ tailWord_3302343) baseStart_3302343 baseEnd_3302343 := by
    simpa [prefixWord, tailWord_3302343, baseEnd_3302343] using wordTrace_append hprefix tailTrace_3302343
  have hstable : (prefixWord ++ tailWord_3302343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3302343).length < 2 ^ (prefixWord ++ tailWord_3302343).sum := by decide
  have hdescent : baseEnd_3302343 < baseStart_3302343 := by decide
  rcases family_descends (prefixWord ++ tailWord_3302343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3302350 : List Nat := [4, 1, 1, 1, 2, 3, 2, 3, 2, 1, 3]
def baseStart_3302350 : Nat := 118140960795 + 3302350 * 2 ^ 59
def prefixEnd_3302350 : Nat := 4983230072969 + 3 ^ 40 * 3302350 * 2
def baseEnd_3302350 : Nat := 1695692839375259774137775

theorem tailTrace_3302350 : CollatzResearch.WordTrace tailWord_3302350 prefixEnd_3302350 1695692839375259774137775 := by
  unfold tailWord_3302350
  simp only [CollatzResearch.WordTrace]
  refine ⟨15055824948269677665382063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80297733057438280882037669 15055824948269677665382063)
  ·
    refine ⟨22583737422404516498073095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15055824948269677665382063 22583737422404516498073095)
    ·
      refine ⟨33875606133606774747109643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22583737422404516498073095 33875606133606774747109643)
      ·
        refine ⟨50813409200410162120664465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33875606133606774747109643 50813409200410162120664465)
        ·
          refine ⟨38110056900307621590498349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50813409200410162120664465 38110056900307621590498349)
          ·
            refine ⟨14291271337615358096436881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38110056900307621590498349 14291271337615358096436881)
            ·
              refine ⟨10718453503211518572327661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14291271337615358096436881 10718453503211518572327661)
              ·
                refine ⟨4019420063704319464622873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10718453503211518572327661 4019420063704319464622873)
                ·
                  refine ⟨3014565047778239598467155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4019420063704319464622873 3014565047778239598467155)
                  ·
                    refine ⟨4521847571667359397700733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3014565047778239598467155 4521847571667359397700733)
                    ·
                      refine ⟨1695692839375259774137775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4521847571667359397700733 1695692839375259774137775)
                      ·
                        rfl

theorem cell23_3302350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 3, 2, 1, 3].length) (baseStart_3302350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3302350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3302350 prefixEnd_3302350 := by exact prefixLift 3302350
  have htrace : WordTrace (prefixWord ++ tailWord_3302350) baseStart_3302350 baseEnd_3302350 := by
    simpa [prefixWord, tailWord_3302350, baseEnd_3302350] using wordTrace_append hprefix tailTrace_3302350
  have hstable : (prefixWord ++ tailWord_3302350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3302350).length < 2 ^ (prefixWord ++ tailWord_3302350).sum := by decide
  have hdescent : baseEnd_3302350 < baseStart_3302350 := by decide
  rcases family_descends (prefixWord ++ tailWord_3302350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3302376 : List Nat := [2, 1, 4, 1, 1, 1, 2, 3, 2, 1, 5]
def baseStart_3302376 : Nat := 118140960795 + 3302376 * 2 ^ 59
def prefixEnd_3302376 : Nat := 4983230072969 + 3 ^ 40 * 3302376 * 2
def baseEnd_3302376 : Nat := 1695706189872276672412655

theorem tailTrace_3302376 : CollatzResearch.WordTrace tailWord_3302376 prefixEnd_3302376 1695706189872276672412655 := by
  unfold tailWord_3302376
  simp only [CollatzResearch.WordTrace]
  refine ⟨60223773942031613881751491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80298365256042151842335321 60223773942031613881751491)
  ·
    refine ⟨90335660913047420822627237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60223773942031613881751491 90335660913047420822627237)
    ·
      refine ⟨16937936421196391404242607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90335660913047420822627237 16937936421196391404242607)
      ·
        refine ⟨25406904631794587106363911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16937936421196391404242607 25406904631794587106363911)
        ·
          refine ⟨38110356947691880659545867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25406904631794587106363911 38110356947691880659545867)
          ·
            refine ⟨57165535421537820989318801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38110356947691880659545867 57165535421537820989318801)
            ·
              refine ⟨42874151566153365741989101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57165535421537820989318801 42874151566153365741989101)
              ·
                refine ⟨16077806837307512153245913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42874151566153365741989101 16077806837307512153245913)
                ·
                  refine ⟨12058355127980634114934435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16077806837307512153245913 12058355127980634114934435)
                  ·
                    refine ⟨18087532691970951172401653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12058355127980634114934435 18087532691970951172401653)
                    ·
                      refine ⟨1695706189872276672412655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18087532691970951172401653 1695706189872276672412655)
                      ·
                        rfl

theorem cell23_3302376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 3, 2, 1, 5].length) (baseStart_3302376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3302376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3302376 prefixEnd_3302376 := by exact prefixLift 3302376
  have htrace : WordTrace (prefixWord ++ tailWord_3302376) baseStart_3302376 baseEnd_3302376 := by
    simpa [prefixWord, tailWord_3302376, baseEnd_3302376] using wordTrace_append hprefix tailTrace_3302376
  have hstable : (prefixWord ++ tailWord_3302376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3302376).length < 2 ^ (prefixWord ++ tailWord_3302376).sum := by decide
  have hdescent : baseEnd_3302376 < baseStart_3302376 := by decide
  rcases family_descends (prefixWord ++ tailWord_3302376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3302396 : List Nat := [2, 2, 2, 1, 2, 3, 1, 3, 7]
def baseStart_3302396 : Nat := 118140960795 + 3302396 * 2 ^ 59
def prefixEnd_3302396 : Nat := 4983230072969 + 3 ^ 40 * 3302396 * 2
def baseEnd_3302396 : Nat := 188412939942818510462507

theorem tailTrace_3302396 : CollatzResearch.WordTrace tailWord_3302396 prefixEnd_3302396 188412939942818510462507 := by
  unfold tailWord_3302396
  simp only [CollatzResearch.WordTrace]
  refine ⟨60224138671995385589615521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80298851562660514119487361 60224138671995385589615521)
  ·
    refine ⟨45168104003996539192211641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60224138671995385589615521 45168104003996539192211641)
    ·
      refine ⟨33876078002997404394158731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45168104003996539192211641 33876078002997404394158731)
      ·
        refine ⟨50814117004496106591238097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33876078002997404394158731 50814117004496106591238097)
        ·
          refine ⟨38110587753372079943428573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50814117004496106591238097 38110587753372079943428573)
          ·
            refine ⟨14291470407514529978785715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38110587753372079943428573 14291470407514529978785715)
            ·
              refine ⟨21437205611271794968178573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14291470407514529978785715 21437205611271794968178573)
              ·
                refine ⟨8038952104226923113066965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21437205611271794968178573 8038952104226923113066965)
                ·
                  refine ⟨188412939942818510462507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8038952104226923113066965 188412939942818510462507)
                  ·
                    rfl

theorem cell23_3302396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 3, 7].length) (baseStart_3302396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3302396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3302396 prefixEnd_3302396 := by exact prefixLift 3302396
  have htrace : WordTrace (prefixWord ++ tailWord_3302396) baseStart_3302396 baseEnd_3302396 := by
    simpa [prefixWord, tailWord_3302396, baseEnd_3302396] using wordTrace_append hprefix tailTrace_3302396
  have hstable : (prefixWord ++ tailWord_3302396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3302396).length < 2 ^ (prefixWord ++ tailWord_3302396).sum := by decide
  have hdescent : baseEnd_3302396 < baseStart_3302396 := by decide
  rcases family_descends (prefixWord ++ tailWord_3302396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3302426 : List Nat := [3, 1, 1, 3, 1, 2, 1, 3, 1, 7]
def baseStart_3302426 : Nat := 118140960795 + 3302426 * 2 ^ 59
def prefixEnd_3302426 : Nat := 4983230072969 + 3 ^ 40 * 3302426 * 2
def baseEnd_3302426 : Nat := 565243954635000492262475

theorem tailTrace_3302426 : CollatzResearch.WordTrace tailWord_3302426 prefixEnd_3302426 565243954635000492262475 := by
  unfold tailWord_3302426
  simp only [CollatzResearch.WordTrace]
  refine ⟨30112342883470521575705783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80299581022588057535215421 30112342883470521575705783)
  ·
    refine ⟨45168514325205782363558675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30112342883470521575705783 45168514325205782363558675)
    ·
      refine ⟨67752771487808673545338013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45168514325205782363558675 67752771487808673545338013)
      ·
        refine ⟨25407289307928252579501755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67752771487808673545338013 25407289307928252579501755)
        ·
          refine ⟨38110933961892378869252633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25407289307928252579501755 38110933961892378869252633)
          ·
            refine ⟨28583200471419284151939475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38110933961892378869252633 28583200471419284151939475)
            ·
              refine ⟨42874800707128926227909213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28583200471419284151939475 42874800707128926227909213)
              ·
                refine ⟨16078050265173347335465955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42874800707128926227909213 16078050265173347335465955)
                ·
                  refine ⟨24117075397760021003198933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16078050265173347335465955 24117075397760021003198933)
                  ·
                    refine ⟨565243954635000492262475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24117075397760021003198933 565243954635000492262475)
                    ·
                      rfl

theorem cell23_3302426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 3, 1, 7].length) (baseStart_3302426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3302426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3302426 prefixEnd_3302426 := by exact prefixLift 3302426
  have htrace : WordTrace (prefixWord ++ tailWord_3302426) baseStart_3302426 baseEnd_3302426 := by
    simpa [prefixWord, tailWord_3302426, baseEnd_3302426] using wordTrace_append hprefix tailTrace_3302426
  have hstable : (prefixWord ++ tailWord_3302426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3302426).length < 2 ^ (prefixWord ++ tailWord_3302426).sum := by decide
  have hdescent : baseEnd_3302426 < baseStart_3302426 := by decide
  rcases family_descends (prefixWord ++ tailWord_3302426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3302463 : List Nat := [1, 1, 2, 2, 3, 1, 1, 3, 1, 6, 2]
def baseStart_3302463 : Nat := 118140960795 + 3302463 * 2 ^ 59
def prefixEnd_3302463 : Nat := 4983230072969 + 3 ^ 40 * 3302463 * 2
def baseEnd_3302463 : Nat := 1695750862689217832024755

theorem tailTrace_3302463 : CollatzResearch.WordTrace tailWord_3302463 prefixEnd_3302463 1695750862689217832024755 := by
  unfold tailWord_3302463
  simp only [CollatzResearch.WordTrace]
  refine ⟨120450721034748041621920043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80300480689832027747946695 120450721034748041621920043)
  ·
    refine ⟨180676081552122062432880065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120450721034748041621920043 180676081552122062432880065)
    ·
      refine ⟨135507061164091546824660049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180676081552122062432880065 135507061164091546824660049)
      ·
        refine ⟨101630295873068660118495037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135507061164091546824660049 101630295873068660118495037)
        ·
          refine ⟨38111360952400747544435639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101630295873068660118495037 38111360952400747544435639)
          ·
            refine ⟨57167041428601121316653459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38111360952400747544435639 57167041428601121316653459)
            ·
              refine ⟨85750562142901681974980189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57167041428601121316653459 85750562142901681974980189)
              ·
                refine ⟨32156460803588130740617571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85750562142901681974980189 32156460803588130740617571)
                ·
                  refine ⟨48234691205382196110926357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32156460803588130740617571 48234691205382196110926357)
                  ·
                    refine ⟨2261001150252290442699673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 48234691205382196110926357 2261001150252290442699673)
                    ·
                      refine ⟨1695750862689217832024755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2261001150252290442699673 1695750862689217832024755)
                      ·
                        rfl

theorem cell23_3302463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 3, 1, 6, 2].length) (baseStart_3302463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3302463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3302463 prefixEnd_3302463 := by exact prefixLift 3302463
  have htrace : WordTrace (prefixWord ++ tailWord_3302463) baseStart_3302463 baseEnd_3302463 := by
    simpa [prefixWord, tailWord_3302463, baseEnd_3302463] using wordTrace_append hprefix tailTrace_3302463
  have hstable : (prefixWord ++ tailWord_3302463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3302463).length < 2 ^ (prefixWord ++ tailWord_3302463).sum := by decide
  have hdescent : baseEnd_3302463 < baseStart_3302463 := by decide
  rcases family_descends (prefixWord ++ tailWord_3302463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3302476 : List Nat := [2, 2, 1, 3, 1, 1, 1, 2, 1, 3, 6]
def baseStart_3302476 : Nat := 118140960795 + 3302476 * 2 ^ 59
def prefixEnd_3302476 : Nat := 4983230072969 + 3 ^ 40 * 3302476 * 2
def baseEnd_3302476 : Nat := 1695757537937726281162195

theorem tailTrace_3302476 : CollatzResearch.WordTrace tailWord_3302476 prefixEnd_3302476 1695757537937726281162195 := by
  unfold tailWord_3302476
  simp only [CollatzResearch.WordTrace]
  refine ⟨60225597591850472421071641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80300796789133963228095521 60225597591850472421071641)
  ·
    refine ⟨45169198193887854315803731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60225597591850472421071641 45169198193887854315803731)
    ·
      refine ⟨67753797290831781473705597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45169198193887854315803731 67753797290831781473705597)
      ·
        refine ⟨25407673984061918052639599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67753797290831781473705597 25407673984061918052639599)
        ·
          refine ⟨38111510976092877078959399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25407673984061918052639599 38111510976092877078959399)
          ·
            refine ⟨57167266464139315618439099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38111510976092877078959399 57167266464139315618439099)
            ·
              refine ⟨85750899696208973427658649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57167266464139315618439099 85750899696208973427658649)
              ·
                refine ⟨64313174772156730070743987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85750899696208973427658649 64313174772156730070743987)
                ·
                  refine ⟨96469762158235095106115981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64313174772156730070743987 96469762158235095106115981)
                  ·
                    refine ⟨36176160809338160664793493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 96469762158235095106115981 36176160809338160664793493)
                    ·
                      refine ⟨1695757537937726281162195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36176160809338160664793493 1695757537937726281162195)
                      ·
                        rfl

theorem cell23_3302476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_3302476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3302476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3302476 prefixEnd_3302476 := by exact prefixLift 3302476
  have htrace : WordTrace (prefixWord ++ tailWord_3302476) baseStart_3302476 baseEnd_3302476 := by
    simpa [prefixWord, tailWord_3302476, baseEnd_3302476] using wordTrace_append hprefix tailTrace_3302476
  have hstable : (prefixWord ++ tailWord_3302476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3302476).length < 2 ^ (prefixWord ++ tailWord_3302476).sum := by decide
  have hdescent : baseEnd_3302476 < baseStart_3302476 := by decide
  rcases family_descends (prefixWord ++ tailWord_3302476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3302483 : List Nat := [1, 1, 1, 2, 1, 1, 2, 7, 2, 2, 3]
def baseStart_3302483 : Nat := 118140960795 + 3302483 * 2 ^ 59
def prefixEnd_3302483 : Nat := 4983230072969 + 3 ^ 40 * 3302483 * 2
def baseEnd_3302483 : Nat := 1695761132302307753774663

theorem tailTrace_3302483 : CollatzResearch.WordTrace tailWord_3302483 prefixEnd_3302483 1695761132302307753774663 := by
  unfold tailWord_3302483
  simp only [CollatzResearch.WordTrace]
  refine ⟨120451450494675585037648103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80300966996450390025098735 120451450494675585037648103)
  ·
    refine ⟨180677175742013377556472155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120451450494675585037648103 180677175742013377556472155)
    ·
      refine ⟨271015763613020066334708233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180677175742013377556472155 271015763613020066334708233)
      ·
        refine ⟨203261822709765049751031175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 271015763613020066334708233 203261822709765049751031175)
        ·
          refine ⟨304892734064647574626546763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203261822709765049751031175 304892734064647574626546763)
          ·
            refine ⟨457339101096971361939820145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 304892734064647574626546763 457339101096971361939820145)
            ·
              refine ⟨343004325822728521454865109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 457339101096971361939820145 343004325822728521454865109)
              ·
                refine ⟨8039163886470199721598401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 343004325822728521454865109 8039163886470199721598401)
                ·
                  refine ⟨6029372914852649791198801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8039163886470199721598401 6029372914852649791198801)
                  ·
                    refine ⟨4522029686139487343399101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6029372914852649791198801 4522029686139487343399101)
                    ·
                      refine ⟨1695761132302307753774663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4522029686139487343399101 1695761132302307753774663)
                      ·
                        rfl

theorem cell23_3302483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 7, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 7, 2, 2, 3].length) (baseStart_3302483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3302483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3302483 prefixEnd_3302483 := by exact prefixLift 3302483
  have htrace : WordTrace (prefixWord ++ tailWord_3302483) baseStart_3302483 baseEnd_3302483 := by
    simpa [prefixWord, tailWord_3302483, baseEnd_3302483] using wordTrace_append hprefix tailTrace_3302483
  have hstable : (prefixWord ++ tailWord_3302483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3302483).length < 2 ^ (prefixWord ++ tailWord_3302483).sum := by decide
  have hdescent : baseEnd_3302483 < baseStart_3302483 := by decide
  rcases family_descends (prefixWord ++ tailWord_3302483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3302503 : List Nat := [1, 1, 5, 1, 1, 3, 1, 4, 6]
def baseStart_3302503 : Nat := 118140960795 + 3302503 * 2 ^ 59
def prefixEnd_3302503 : Nat := 4983230072969 + 3 ^ 40 * 3302503 * 2
def baseEnd_3302503 : Nat := 188419044657266408391619

theorem tailTrace_3302503 : CollatzResearch.WordTrace tailWord_3302503 prefixEnd_3302503 188419044657266408391619 := by
  unfold tailWord_3302503
  simp only [CollatzResearch.WordTrace]
  refine ⟨120452179954603128453376163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80301453303068752302250775 120452179954603128453376163)
  ·
    refine ⟨180678269931904692680064245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120452179954603128453376163 180678269931904692680064245)
    ·
      refine ⟨16938587806116064938756023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 180678269931904692680064245 16938587806116064938756023)
      ·
        refine ⟨25407881709174097408134035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16938587806116064938756023 25407881709174097408134035)
        ·
          refine ⟨38111822563761146112201053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25407881709174097408134035 38111822563761146112201053)
          ·
            refine ⟨14291933461410429792075395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38111822563761146112201053 14291933461410429792075395)
            ·
              refine ⟨21437900192115644688113093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14291933461410429792075395 21437900192115644688113093)
              ·
                refine ⟨4019606286021683379021205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21437900192115644688113093 4019606286021683379021205)
                ·
                  refine ⟨188419044657266408391619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4019606286021683379021205 188419044657266408391619)
                  ·
                    rfl

theorem cell23_3302503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 4, 6].length) (baseStart_3302503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3302503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3302503 prefixEnd_3302503 := by exact prefixLift 3302503
  have htrace : WordTrace (prefixWord ++ tailWord_3302503) baseStart_3302503 baseEnd_3302503 := by
    simpa [prefixWord, tailWord_3302503, baseEnd_3302503] using wordTrace_append hprefix tailTrace_3302503
  have hstable : (prefixWord ++ tailWord_3302503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3302503).length < 2 ^ (prefixWord ++ tailWord_3302503).sum := by decide
  have hdescent : baseEnd_3302503 < baseStart_3302503 := by decide
  rcases family_descends (prefixWord ++ tailWord_3302503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3302547 : List Nat := [1, 1, 1, 2, 1, 2, 5, 5, 1, 1, 3]
def baseStart_3302547 : Nat := 118140960795 + 3302547 * 2 ^ 59
def prefixEnd_3302547 : Nat := 4983230072969 + 3 ^ 40 * 3302547 * 2
def baseEnd_3302547 : Nat := 1695793995064195503374369

theorem tailTrace_3302547 : CollatzResearch.WordTrace tailWord_3302547 prefixEnd_3302547 1695793995064195503374369 := by
  unfold tailWord_3302547
  simp only [CollatzResearch.WordTrace]
  refine ⟨120453784766443723967977895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80302523177629149311985263 120453784766443723967977895)
  ·
    refine ⟨180680677149665585951966843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120453784766443723967977895 180680677149665585951966843)
    ·
      refine ⟨271021015724498378927950265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180680677149665585951966843 271021015724498378927950265)
      ·
        refine ⟨203265761793373784195962699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 271021015724498378927950265 203265761793373784195962699)
        ·
          refine ⟨304898642690060676293944049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203265761793373784195962699 304898642690060676293944049)
          ·
            refine ⟨228673982017545507220458037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 304898642690060676293944049 228673982017545507220458037)
            ·
              refine ⟨21438185814144891301917941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 228673982017545507220458037 21438185814144891301917941)
              ·
                refine ⟨2009829920076083559554807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21438185814144891301917941 2009829920076083559554807)
                ·
                  refine ⟨3014744880114125339332211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2009829920076083559554807 3014744880114125339332211)
                  ·
                    refine ⟨4522117320171188008998317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3014744880114125339332211 4522117320171188008998317)
                    ·
                      refine ⟨1695793995064195503374369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4522117320171188008998317 1695793995064195503374369)
                      ·
                        rfl

theorem cell23_3302547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 5, 1, 1, 3].length) (baseStart_3302547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3302547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3302547 prefixEnd_3302547 := by exact prefixLift 3302547
  have htrace : WordTrace (prefixWord ++ tailWord_3302547) baseStart_3302547 baseEnd_3302547 := by
    simpa [prefixWord, tailWord_3302547, baseEnd_3302547] using wordTrace_append hprefix tailTrace_3302547
  have hstable : (prefixWord ++ tailWord_3302547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3302547).length < 2 ^ (prefixWord ++ tailWord_3302547).sum := by decide
  have hdescent : baseEnd_3302547 < baseStart_3302547 := by decide
  rcases family_descends (prefixWord ++ tailWord_3302547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3302564 : List Nat := [2, 3, 1, 2, 3, 1, 2, 4, 1, 1, 3]
def baseStart_3302564 : Nat := 118140960795 + 3302564 * 2 ^ 59
def prefixEnd_3302564 : Nat := 4983230072969 + 3 ^ 40 * 3302564 * 2
def baseEnd_3302564 : Nat := 1695802724235321936861791

theorem tailTrace_3302564 : CollatzResearch.WordTrace tailWord_3302564 prefixEnd_3302564 1695802724235321936861791 := by
  unfold tailWord_3302564
  simp only [CollatzResearch.WordTrace]
  refine ⟨60227202403691067935673373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80302936538254757247564497 60227202403691067935673373)
  ·
    refine ⟨22585200901384150475877515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60227202403691067935673373 22585200901384150475877515)
    ·
      refine ⟨33877801352076225713816273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22585200901384150475877515 33877801352076225713816273)
      ·
        refine ⟨25408351014057169285362205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33877801352076225713816273 25408351014057169285362205)
        ·
          refine ⟨9528131630271438482010827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25408351014057169285362205 9528131630271438482010827)
          ·
            refine ⟨14292197445407157723016241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9528131630271438482010827 14292197445407157723016241)
            ·
              refine ⟨10719148084055368292262181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14292197445407157723016241 10719148084055368292262181)
              ·
                refine ⟨2009840265760381554799159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10719148084055368292262181 2009840265760381554799159)
                ·
                  refine ⟨3014760398640572332198739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2009840265760381554799159 3014760398640572332198739)
                  ·
                    refine ⟨4522140597960858498298109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3014760398640572332198739 4522140597960858498298109)
                    ·
                      refine ⟨1695802724235321936861791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4522140597960858498298109 1695802724235321936861791)
                      ·
                        rfl

theorem cell23_3302564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 4, 1, 1, 3].length) (baseStart_3302564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3302564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3302564 prefixEnd_3302564 := by exact prefixLift 3302564
  have htrace : WordTrace (prefixWord ++ tailWord_3302564) baseStart_3302564 baseEnd_3302564 := by
    simpa [prefixWord, tailWord_3302564, baseEnd_3302564] using wordTrace_append hprefix tailTrace_3302564
  have hstable : (prefixWord ++ tailWord_3302564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3302564).length < 2 ^ (prefixWord ++ tailWord_3302564).sum := by decide
  have hdescent : baseEnd_3302564 < baseStart_3302564 := by decide
  rcases family_descends (prefixWord ++ tailWord_3302564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3302583 : List Nat := [1, 1, 3, 1, 4, 1, 3, 1, 1, 1, 6]
def baseStart_3302583 : Nat := 118140960795 + 3302583 * 2 ^ 59
def prefixEnd_3302583 : Nat := 4983230072969 + 3 ^ 40 * 3302583 * 2
def baseEnd_3302583 : Nat := 1695812480367757362524203

theorem tailTrace_3302583 : CollatzResearch.WordTrace tailWord_3302583 prefixEnd_3302583 1695812480367757362524203 := by
  unfold tailWord_3302583
  simp only [CollatzResearch.WordTrace]
  refine ⟨120455097794313302116288403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80303398529542201410858935 120455097794313302116288403)
  ·
    refine ⟨180682646691469953174432605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120455097794313302116288403 180682646691469953174432605)
    ·
      refine ⟨67755992509301232440412227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180682646691469953174432605 67755992509301232440412227)
      ·
        refine ⟨101633988763951848660618341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67755992509301232440412227 101633988763951848660618341)
        ·
          refine ⟨19056372893240971623865939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101633988763951848660618341 19056372893240971623865939)
          ·
            refine ⟨28584559339861457435798909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19056372893240971623865939 28584559339861457435798909)
            ·
              refine ⟨10719209752448046538424591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28584559339861457435798909 10719209752448046538424591)
              ·
                refine ⟨16078814628672069807636887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10719209752448046538424591 16078814628672069807636887)
                ·
                  refine ⟨24118221943008104711455331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16078814628672069807636887 24118221943008104711455331)
                  ·
                    refine ⟨36177332914512157067182997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24118221943008104711455331 36177332914512157067182997)
                    ·
                      refine ⟨1695812480367757362524203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36177332914512157067182997 1695812480367757362524203)
                      ·
                        rfl

theorem cell23_3302583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 1, 1, 1, 6].length) (baseStart_3302583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3302583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3302583 prefixEnd_3302583 := by exact prefixLift 3302583
  have htrace : WordTrace (prefixWord ++ tailWord_3302583) baseStart_3302583 baseEnd_3302583 := by
    simpa [prefixWord, tailWord_3302583, baseEnd_3302583] using wordTrace_append hprefix tailTrace_3302583
  have hstable : (prefixWord ++ tailWord_3302583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3302583).length < 2 ^ (prefixWord ++ tailWord_3302583).sum := by decide
  have hdescent : baseEnd_3302583 < baseStart_3302583 := by decide
  rcases family_descends (prefixWord ++ tailWord_3302583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3302631 : List Nat := [1, 1, 5, 3, 2, 2, 2, 1, 2, 4]
def baseStart_3302631 : Nat := 118140960795 + 3302631 * 2 ^ 59
def prefixEnd_3302631 : Nat := 4983230072969 + 3 ^ 40 * 3302631 * 2
def baseEnd_3302631 : Nat := 565279042479724391574661

theorem tailTrace_3302631 : CollatzResearch.WordTrace tailWord_3302631 prefixEnd_3302631 565279042479724391574661 := by
  unfold tailWord_3302631
  simp only [CollatzResearch.WordTrace]
  refine ⟨120456848498139406314035747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80304565665426270876023831 120456848498139406314035747)
  ·
    refine ⟨180685272747209109471053621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120456848498139406314035747 180685272747209109471053621)
    ·
      refine ⟨16939244320050854012911277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 180685272747209109471053621 16939244320050854012911277)
      ·
        refine ⟨6352216620019070254841729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16939244320050854012911277 6352216620019070254841729)
        ·
          refine ⟨4764162465014302691131297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6352216620019070254841729 4764162465014302691131297)
          ·
            refine ⟨3573121848760727018348473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4764162465014302691131297 3573121848760727018348473)
            ·
              refine ⟨2679841386570545263761355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3573121848760727018348473 2679841386570545263761355)
              ·
                refine ⟨4019762079855817895642033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2679841386570545263761355 4019762079855817895642033)
                ·
                  refine ⟨3014821559891863421731525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4019762079855817895642033 3014821559891863421731525)
                  ·
                    refine ⟨565279042479724391574661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3014821559891863421731525 565279042479724391574661)
                    ·
                      rfl

theorem cell23_3302631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 2, 1, 2, 4].length) (baseStart_3302631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3302631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3302631 prefixEnd_3302631 := by exact prefixLift 3302631
  have htrace : WordTrace (prefixWord ++ tailWord_3302631) baseStart_3302631 baseEnd_3302631 := by
    simpa [prefixWord, tailWord_3302631, baseEnd_3302631] using wordTrace_append hprefix tailTrace_3302631
  have hstable : (prefixWord ++ tailWord_3302631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3302631).length < 2 ^ (prefixWord ++ tailWord_3302631).sum := by decide
  have hdescent : baseEnd_3302631 < baseStart_3302631 := by decide
  rcases family_descends (prefixWord ++ tailWord_3302631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3302653 : List Nat := [1, 4, 1, 1, 1, 1, 1, 1, 6, 6]
def baseStart_3302653 : Nat := 118140960795 + 3302653 * 2 ^ 59
def prefixEnd_3302653 : Nat := 4983230072969 + 3 ^ 40 * 3302653 * 2
def baseEnd_3302653 : Nat := 565282808004524029549627

theorem tailTrace_3302653 : CollatzResearch.WordTrace tailWord_3302653 prefixEnd_3302653 565282808004524029549627 := by
  unfold tailWord_3302653
  simp only [CollatzResearch.WordTrace]
  refine ⟨120457650904059704071336613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80305100602706469380891075 120457650904059704071336613)
  ·
    refine ⟨22585809544511194513375615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120457650904059704071336613 22585809544511194513375615)
    ·
      refine ⟨33878714316766791770063423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22585809544511194513375615 33878714316766791770063423)
      ·
        refine ⟨50818071475150187655095135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33878714316766791770063423 50818071475150187655095135)
        ·
          refine ⟨76227107212725281482642703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50818071475150187655095135 76227107212725281482642703)
          ·
            refine ⟨114340660819087922223964055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76227107212725281482642703 114340660819087922223964055)
            ·
              refine ⟨171510991228631883335946083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114340660819087922223964055 171510991228631883335946083)
              ·
                refine ⟨257266486842947825003919125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 171510991228631883335946083 257266486842947825003919125)
                ·
                  refine ⟨12059366570763179297058709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 257266486842947825003919125 12059366570763179297058709)
                  ·
                    refine ⟨565282808004524029549627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12059366570763179297058709 565282808004524029549627)
                    ·
                      rfl

theorem cell23_3302653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 6, 6].length) (baseStart_3302653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3302653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3302653 prefixEnd_3302653 := by exact prefixLift 3302653
  have htrace : WordTrace (prefixWord ++ tailWord_3302653) baseStart_3302653 baseEnd_3302653 := by
    simpa [prefixWord, tailWord_3302653, baseEnd_3302653] using wordTrace_append hprefix tailTrace_3302653
  have hstable : (prefixWord ++ tailWord_3302653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3302653).length < 2 ^ (prefixWord ++ tailWord_3302653).sum := by decide
  have hdescent : baseEnd_3302653 < baseStart_3302653 := by decide
  rcases family_descends (prefixWord ++ tailWord_3302653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3302680 : List Nat := [2, 1, 2, 3, 1, 3, 1, 1, 2, 4, 3]
def baseStart_3302680 : Nat := 118140960795 + 3302680 * 2 ^ 59
def prefixEnd_3302680 : Nat := 4983230072969 + 3 ^ 40 * 3302680 * 2
def baseEnd_3302680 : Nat := 1695862287991243483011257

theorem tailTrace_3302680 : CollatzResearch.WordTrace tailWord_3302680 prefixEnd_3302680 1695862287991243483011257 := by
  unfold tailWord_3302680
  simp only [CollatzResearch.WordTrace]
  refine ⟨60229317837480943841284747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80305757116641258455046329 60229317837480943841284747)
  ·
    refine ⟨90343976756221415761927121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60229317837480943841284747 90343976756221415761927121)
    ·
      refine ⟨67757982567166061821445341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90343976756221415761927121 67757982567166061821445341)
      ·
        refine ⟨25409243462687273183042003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67757982567166061821445341 25409243462687273183042003)
        ·
          refine ⟨38113865194030909774563005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25409243462687273183042003 38113865194030909774563005)
          ·
            refine ⟨14292699447761591165461127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38113865194030909774563005 14292699447761591165461127)
            ·
              refine ⟨21439049171642386748191691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14292699447761591165461127 21439049171642386748191691)
              ·
                refine ⟨32158573757463580122287537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21439049171642386748191691 32158573757463580122287537)
                ·
                  refine ⟨24118930318097685091715653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32158573757463580122287537 24118930318097685091715653)
                  ·
                    refine ⟨4522299434643315954696685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24118930318097685091715653 4522299434643315954696685)
                    ·
                      refine ⟨1695862287991243483011257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4522299434643315954696685 1695862287991243483011257)
                      ·
                        rfl

theorem cell23_3302680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 1, 2, 4, 3].length) (baseStart_3302680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3302680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3302680 prefixEnd_3302680 := by exact prefixLift 3302680
  have htrace : WordTrace (prefixWord ++ tailWord_3302680) baseStart_3302680 baseEnd_3302680 := by
    simpa [prefixWord, tailWord_3302680, baseEnd_3302680] using wordTrace_append hprefix tailTrace_3302680
  have hstable : (prefixWord ++ tailWord_3302680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3302680).length < 2 ^ (prefixWord ++ tailWord_3302680).sum := by decide
  have hdescent : baseEnd_3302680 < baseStart_3302680 := by decide
  rcases family_descends (prefixWord ++ tailWord_3302680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3302683 : List Nat := [1, 1, 1, 1, 1, 1, 5, 5, 7]
def baseStart_3302683 : Nat := 118140960795 + 3302683 * 2 ^ 59
def prefixEnd_3302683 : Nat := 4983230072969 + 3 ^ 40 * 3302683 * 2
def baseEnd_3302683 : Nat := 188429314270356330141527

theorem tailTrace_3302683 : CollatzResearch.WordTrace tailWord_3302683 prefixEnd_3302683 188429314270356330141527 := by
  unfold tailWord_3302683
  simp only [CollatzResearch.WordTrace]
  refine ⟨120458745093951019194928703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80305830062634012796619135 120458745093951019194928703)
  ·
    refine ⟨180688117640926528792393055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120458745093951019194928703 180688117640926528792393055)
    ·
      refine ⟨271032176461389793188589583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180688117640926528792393055 271032176461389793188589583)
      ·
        refine ⟨406548264692084689782884375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271032176461389793188589583 406548264692084689782884375)
        ·
          refine ⟨609822397038127034674326563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 406548264692084689782884375 609822397038127034674326563)
          ·
            refine ⟨914733595557190552011489845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 609822397038127034674326563 914733595557190552011489845)
            ·
              refine ⟨85756274583486614251077173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 914733595557190552011489845 85756274583486614251077173)
              ·
                refine ⟨8039650742201870086038485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 85756274583486614251077173 8039650742201870086038485)
                ·
                  refine ⟨188429314270356330141527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8039650742201870086038485 188429314270356330141527)
                  ·
                    rfl

theorem cell23_3302683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 5, 7].length) (baseStart_3302683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3302683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3302683 prefixEnd_3302683 := by exact prefixLift 3302683
  have htrace : WordTrace (prefixWord ++ tailWord_3302683) baseStart_3302683 baseEnd_3302683 := by
    simpa [prefixWord, tailWord_3302683, baseEnd_3302683] using wordTrace_append hprefix tailTrace_3302683
  have hstable : (prefixWord ++ tailWord_3302683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3302683).length < 2 ^ (prefixWord ++ tailWord_3302683).sum := by decide
  have hdescent : baseEnd_3302683 < baseStart_3302683 := by decide
  rcases family_descends (prefixWord ++ tailWord_3302683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3302730 : List Nat := [3, 1, 2, 1, 1, 1, 1, 6, 2, 5]
def baseStart_3302730 : Nat := 118140960795 + 3302730 * 2 ^ 59
def prefixEnd_3302730 : Nat := 4983230072969 + 3 ^ 40 * 3302730 * 2
def baseEnd_3302730 : Nat := 565295987341322762462009

theorem tailTrace_3302730 : CollatzResearch.WordTrace tailWord_3302730 prefixEnd_3302730 565295987341322762462009 := by
  unfold tailWord_3302730
  simp only [CollatzResearch.WordTrace]
  refine ⟨30115114831195186555472411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80306972883187164147926429 30115114831195186555472411)
  ·
    refine ⟨45172672246792779833208617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30115114831195186555472411 45172672246792779833208617)
    ·
      refine ⟨33879504185094584874906463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45172672246792779833208617 33879504185094584874906463)
      ·
        refine ⟨50819256277641877312359695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33879504185094584874906463 50819256277641877312359695)
        ·
          refine ⟨76228884416462815968539543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50819256277641877312359695 76228884416462815968539543)
          ·
            refine ⟨114343326624694223952809315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76228884416462815968539543 114343326624694223952809315)
            ·
              refine ⟨171514989937041335929213973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114343326624694223952809315 171514989937041335929213973)
              ·
                refine ⟨8039765153298812621681905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 171514989937041335929213973 8039765153298812621681905)
                ·
                  refine ⟨6029823864974109466261429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8039765153298812621681905 6029823864974109466261429)
                  ·
                    refine ⟨565295987341322762462009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6029823864974109466261429 565295987341322762462009)
                    ·
                      rfl

theorem cell23_3302730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 6, 2, 5].length) (baseStart_3302730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3302730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3302730 prefixEnd_3302730 := by exact prefixLift 3302730
  have htrace : WordTrace (prefixWord ++ tailWord_3302730) baseStart_3302730 baseEnd_3302730 := by
    simpa [prefixWord, tailWord_3302730, baseEnd_3302730] using wordTrace_append hprefix tailTrace_3302730
  have hstable : (prefixWord ++ tailWord_3302730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3302730).length < 2 ^ (prefixWord ++ tailWord_3302730).sum := by decide
  have hdescent : baseEnd_3302730 < baseStart_3302730 := by decide
  rcases family_descends (prefixWord ++ tailWord_3302730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3302740 : List Nat := [2, 4, 1, 1, 2, 1, 2, 1, 1, 1, 7]
def baseStart_3302740 : Nat := 118140960795 + 3302740 * 2 ^ 59
def prefixEnd_3302740 : Nat := 4983230072969 + 3 ^ 40 * 3302740 * 2
def baseEnd_3302740 : Nat := 1695893096830513248260981

theorem tailTrace_3302740 : CollatzResearch.WordTrace tailWord_3302740 prefixEnd_3302740 1695893096830513248260981 := by
  unfold tailWord_3302740
  simp only [CollatzResearch.WordTrace]
  refine ⟨60230412027372258964876837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80307216036496345286502449 60230412027372258964876837)
  ·
    refine ⟨11293202255132298555914407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60230412027372258964876837 11293202255132298555914407)
    ·
      refine ⟨16939803382698447833871611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11293202255132298555914407 16939803382698447833871611)
      ·
        refine ⟨25409705074047671750807417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16939803382698447833871611 25409705074047671750807417)
        ·
          refine ⟨19057278805535753813105563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25409705074047671750807417 19057278805535753813105563)
          ·
            refine ⟨28585918208303630719658345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19057278805535753813105563 28585918208303630719658345)
            ·
              refine ⟨21439438656227723039743759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28585918208303630719658345 21439438656227723039743759)
              ·
                refine ⟨32159157984341584559615639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21439438656227723039743759 32159157984341584559615639)
                ·
                  refine ⟨48238736976512376839423459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32159157984341584559615639 48238736976512376839423459)
                  ·
                    refine ⟨72358105464768565259135189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48238736976512376839423459 72358105464768565259135189)
                    ·
                      refine ⟨1695893096830513248260981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 72358105464768565259135189 1695893096830513248260981)
                      ·
                        rfl

theorem cell23_3302740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_3302740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3302740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3302740 prefixEnd_3302740 := by exact prefixLift 3302740
  have htrace : WordTrace (prefixWord ++ tailWord_3302740) baseStart_3302740 baseEnd_3302740 := by
    simpa [prefixWord, tailWord_3302740, baseEnd_3302740] using wordTrace_append hprefix tailTrace_3302740
  have hstable : (prefixWord ++ tailWord_3302740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3302740).length < 2 ^ (prefixWord ++ tailWord_3302740).sum := by decide
  have hdescent : baseEnd_3302740 < baseStart_3302740 := by decide
  rcases family_descends (prefixWord ++ tailWord_3302740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3302787 : List Nat := [1, 1, 1, 3, 5, 1, 1, 1, 4, 2, 3]
def baseStart_3302787 : Nat := 118140960795 + 3302787 * 2 ^ 59
def prefixEnd_3302787 : Nat := 4983230072969 + 3 ^ 40 * 3302787 * 2
def baseEnd_3302787 : Nat := 1695917230421274564373265

theorem tailTrace_3302787 : CollatzResearch.WordTrace tailWord_3302787 prefixEnd_3302787 1695917230421274564373265 := by
  unfold tailWord_3302787
  simp only [CollatzResearch.WordTrace]
  refine ⟨120462538285574244956714615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80308358857049496637809743 120462538285574244956714615)
  ·
    refine ⟨180693807428361367435071923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120462538285574244956714615 180693807428361367435071923)
    ·
      refine ⟨271040711142542051152607885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180693807428361367435071923 271040711142542051152607885)
      ·
        refine ⟨101640266678453269182227957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 271040711142542051152607885 101640266678453269182227957)
        ·
          refine ⟨9528775001104993985833871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 101640266678453269182227957 9528775001104993985833871)
          ·
            refine ⟨14293162501657490978750807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9528775001104993985833871 14293162501657490978750807)
            ·
              refine ⟨21439743752486236468126211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14293162501657490978750807 21439743752486236468126211)
              ·
                refine ⟨32159615628729354702189317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21439743752486236468126211 32159615628729354702189317)
                ·
                  refine ⟨6029927930386754006660497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32159615628729354702189317 6029927930386754006660497)
                  ·
                    refine ⟨4522445947790065504995373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6029927930386754006660497 4522445947790065504995373)
                    ·
                      refine ⟨1695917230421274564373265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4522445947790065504995373 1695917230421274564373265)
                      ·
                        rfl

theorem cell23_3302787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 1, 4, 2, 3].length) (baseStart_3302787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3302787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3302787 prefixEnd_3302787 := by exact prefixLift 3302787
  have htrace : WordTrace (prefixWord ++ tailWord_3302787) baseStart_3302787 baseEnd_3302787 := by
    simpa [prefixWord, tailWord_3302787, baseEnd_3302787] using wordTrace_append hprefix tailTrace_3302787
  have hstable : (prefixWord ++ tailWord_3302787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3302787).length < 2 ^ (prefixWord ++ tailWord_3302787).sum := by decide
  have hdescent : baseEnd_3302787 < baseStart_3302787 := by decide
  rcases family_descends (prefixWord ++ tailWord_3302787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3302857 : List Nat := [1, 2, 1, 1, 2, 1, 3, 2, 2, 6, 2]
def baseStart_3302857 : Nat := 118140960795 + 3302857 * 2 ^ 59
def prefixEnd_3302857 : Nat := 4983230072969 + 3 ^ 40 * 3302857 * 2
def baseEnd_3302857 : Nat := 1695953174067089290497943

theorem tailTrace_3302857 : CollatzResearch.WordTrace tailWord_3302857 prefixEnd_3302857 1695953174067089290497943 := by
  unfold tailWord_3302857
  simp only [CollatzResearch.WordTrace]
  refine ⟨120465091395320646911762825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80310060930213764607841883 120465091395320646911762825)
  ·
    refine ⟨90348818546490485183822119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120465091395320646911762825 90348818546490485183822119)
    ·
      refine ⟨135523227819735727775733179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90348818546490485183822119 135523227819735727775733179)
      ·
        refine ⟨203284841729603591663599769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135523227819735727775733179 203284841729603591663599769)
        ·
          refine ⟨152463631297202693747699827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203284841729603591663599769 152463631297202693747699827)
          ·
            refine ⟨228695446945804040621549741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152463631297202693747699827 228695446945804040621549741)
            ·
              refine ⟨85760792604676515233081153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 228695446945804040621549741 85760792604676515233081153)
              ·
                refine ⟨64320594453507386424810865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85760792604676515233081153 64320594453507386424810865)
                ·
                  refine ⟨48240445840130539818608149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64320594453507386424810865 48240445840130539818608149)
                  ·
                    refine ⟨2261270898756119053997257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 48240445840130539818608149 2261270898756119053997257)
                    ·
                      refine ⟨1695953174067089290497943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2261270898756119053997257 1695953174067089290497943)
                      ·
                        rfl

theorem cell23_3302857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 2, 6, 2].length) (baseStart_3302857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3302857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3302857 prefixEnd_3302857 := by exact prefixLift 3302857
  have htrace : WordTrace (prefixWord ++ tailWord_3302857) baseStart_3302857 baseEnd_3302857 := by
    simpa [prefixWord, tailWord_3302857, baseEnd_3302857] using wordTrace_append hprefix tailTrace_3302857
  have hstable : (prefixWord ++ tailWord_3302857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3302857).length < 2 ^ (prefixWord ++ tailWord_3302857).sum := by decide
  have hdescent : baseEnd_3302857 < baseStart_3302857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3302857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3302901 : List Nat := [1, 3, 5, 1, 1, 2, 1, 1, 4, 4]
def baseStart_3302901 : Nat := 118140960795 + 3302901 * 2 ^ 59
def prefixEnd_3302901 : Nat := 4983230072969 + 3 ^ 40 * 3302901 * 2
def baseEnd_3302901 : Nat := 565325255738629039449247

theorem tailTrace_3302901 : CollatzResearch.WordTrace tailWord_3302901 prefixEnd_3302901 565325255738629039449247 := by
  unfold tailWord_3302901
  simp only [CollatzResearch.WordTrace]
  refine ⟨120466696207161242426364557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80311130804774161617576371 120466696207161242426364557)
  ·
    refine ⟨45175011077685465909886709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120466696207161242426364557 45175011077685465909886709)
    ·
      refine ⟨4235157288533012429051879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 45175011077685465909886709 4235157288533012429051879)
      ·
        refine ⟨6352735932799518643577819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4235157288533012429051879 6352735932799518643577819)
        ·
          refine ⟨9529103899199277965366729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6352735932799518643577819 9529103899199277965366729)
          ·
            refine ⟨7146827924399458474025047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9529103899199277965366729 7146827924399458474025047)
            ·
              refine ⟨10720241886599187711037571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7146827924399458474025047 10720241886599187711037571)
              ·
                refine ⟨16080362829898781566556357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10720241886599187711037571 16080362829898781566556357)
                ·
                  refine ⟨3015068030606021543729317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16080362829898781566556357 3015068030606021543729317)
                  ·
                    refine ⟨565325255738629039449247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3015068030606021543729317 565325255738629039449247)
                    ·
                      rfl

theorem cell23_3302901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_3302901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3302901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3302901 prefixEnd_3302901 := by exact prefixLift 3302901
  have htrace : WordTrace (prefixWord ++ tailWord_3302901) baseStart_3302901 baseEnd_3302901 := by
    simpa [prefixWord, tailWord_3302901, baseEnd_3302901] using wordTrace_append hprefix tailTrace_3302901
  have hstable : (prefixWord ++ tailWord_3302901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3302901).length < 2 ^ (prefixWord ++ tailWord_3302901).sum := by decide
  have hdescent : baseEnd_3302901 < baseStart_3302901 := by decide
  rcases family_descends (prefixWord ++ tailWord_3302901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3302908 : List Nat := [2, 2, 2, 1, 2, 1, 4, 4, 1, 2, 2]
def baseStart_3302908 : Nat := 118140960795 + 3302908 * 2 ^ 59
def prefixEnd_3302908 : Nat := 4983230072969 + 3 ^ 40 * 3302908 * 2
def baseEnd_3302908 : Nat := 1695979361580468590960209

theorem tailTrace_3302908 : CollatzResearch.WordTrace tailWord_3302908 prefixEnd_3302908 1695979361580468590960209 := by
  unfold tailWord_3302908
  simp only [CollatzResearch.WordTrace]
  refine ⟨60233475759067941310934689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80311301012090588414579585 60233475759067941310934689)
  ·
    refine ⟨45175106819300955983201017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60233475759067941310934689 45175106819300955983201017)
    ·
      refine ⟨33881330114475716987400763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45175106819300955983201017 33881330114475716987400763)
      ·
        refine ⟨50821995171713575481101145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33881330114475716987400763 50821995171713575481101145)
        ·
          refine ⟨38116496378785181610825859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50821995171713575481101145 38116496378785181610825859)
          ·
            refine ⟨57174744568177772416238789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38116496378785181610825859 57174744568177772416238789)
            ·
              refine ⟨10720264606533332328044773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57174744568177772416238789 10720264606533332328044773)
              ·
                refine ⟨2010049613724999811508395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10720264606533332328044773 2010049613724999811508395)
                ·
                  refine ⟨3015074420587499717262593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2010049613724999811508395 3015074420587499717262593)
                  ·
                    refine ⟨2261305815440624787946945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3015074420587499717262593 2261305815440624787946945)
                    ·
                      refine ⟨1695979361580468590960209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2261305815440624787946945 1695979361580468590960209)
                      ·
                        rfl

theorem cell23_3302908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 4, 1, 2, 2].length) (baseStart_3302908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3302908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3302908 prefixEnd_3302908 := by exact prefixLift 3302908
  have htrace : WordTrace (prefixWord ++ tailWord_3302908) baseStart_3302908 baseEnd_3302908 := by
    simpa [prefixWord, tailWord_3302908, baseEnd_3302908] using wordTrace_append hprefix tailTrace_3302908
  have hstable : (prefixWord ++ tailWord_3302908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3302908).length < 2 ^ (prefixWord ++ tailWord_3302908).sum := by decide
  have hdescent : baseEnd_3302908 < baseStart_3302908 := by decide
  rcases family_descends (prefixWord ++ tailWord_3302908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3302925 : List Nat := [1, 7, 1, 1, 2, 1, 2, 2, 1, 1, 4]
def baseStart_3302925 : Nat := 118140960795 + 3302925 * 2 ^ 59
def prefixEnd_3302925 : Nat := 4983230072969 + 3 ^ 40 * 3302925 * 2
def baseEnd_3302925 : Nat := 1695988090751595024447631

theorem tailTrace_3302925 : CollatzResearch.WordTrace tailWord_3302925 prefixEnd_3302925 1695988090751595024447631 := by
  unfold tailWord_3302925
  simp only [CollatzResearch.WordTrace]
  refine ⟨120467571559074294525238229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80311714372716196350158819 120467571559074294525238229)
  ·
    refine ⟨2823458708415803777935271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 120467571559074294525238229 2823458708415803777935271)
    ·
      refine ⟨4235188062623705666902907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2823458708415803777935271 4235188062623705666902907)
      ·
        refine ⟨6352782093935558500354361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4235188062623705666902907 6352782093935558500354361)
        ·
          refine ⟨4764586570451668875265771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6352782093935558500354361 4764586570451668875265771)
          ·
            refine ⟨7146879855677503312898657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4764586570451668875265771 7146879855677503312898657)
            ·
              refine ⟨5360159891758127484673993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7146879855677503312898657 5360159891758127484673993)
              ·
                refine ⟨4020119918818595613505495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5360159891758127484673993 4020119918818595613505495)
                ·
                  refine ⟨6030179878227893420258243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4020119918818595613505495 6030179878227893420258243)
                  ·
                    refine ⟨9045269817341840130387365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6030179878227893420258243 9045269817341840130387365)
                    ·
                      refine ⟨1695988090751595024447631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9045269817341840130387365 1695988090751595024447631)
                      ·
                        rfl

theorem cell23_3302925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_3302925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3302925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3302925 prefixEnd_3302925 := by exact prefixLift 3302925
  have htrace : WordTrace (prefixWord ++ tailWord_3302925) baseStart_3302925 baseEnd_3302925 := by
    simpa [prefixWord, tailWord_3302925, baseEnd_3302925] using wordTrace_append hprefix tailTrace_3302925
  have hstable : (prefixWord ++ tailWord_3302925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3302925).length < 2 ^ (prefixWord ++ tailWord_3302925).sum := by decide
  have hdescent : baseEnd_3302925 < baseStart_3302925 := by decide
  rcases family_descends (prefixWord ++ tailWord_3302925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3303057 : List Nat := [1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 5]
def baseStart_3303057 : Nat := 118140960795 + 3303057 * 2 ^ 59
def prefixEnd_3303057 : Nat := 4983230072969 + 3 ^ 40 * 3303057 * 2
def baseEnd_3303057 : Nat := 1696055870197988507997023

theorem tailTrace_3303057 : CollatzResearch.WordTrace tailWord_3303057 prefixEnd_3303057 1696055870197988507997023 := by
  unfold tailWord_3303057
  simp only [CollatzResearch.WordTrace]
  refine ⟨120472385994596081069043425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80314923996397387379362283 120472385994596081069043425)
  ·
    refine ⟨90354289495947060801782569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120472385994596081069043425 90354289495947060801782569)
    ·
      refine ⟨67765717121960295601336927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90354289495947060801782569 67765717121960295601336927)
      ·
        refine ⟨101648575682940443402005391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67765717121960295601336927 101648575682940443402005391)
        ·
          refine ⟨152472863524410665103008087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101648575682940443402005391 152472863524410665103008087)
          ·
            refine ⟨228709295286615997654512131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152472863524410665103008087 228709295286615997654512131)
            ·
              refine ⟨343063942929923996481768197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 228709295286615997654512131 343063942929923996481768197)
              ·
                refine ⟨64324489299360749340331537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 343063942929923996481768197 64324489299360749340331537)
                ·
                  refine ⟨48243366974520562005248653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64324489299360749340331537 48243366974520562005248653)
                  ·
                    refine ⟨18091262615445210751968245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48243366974520562005248653 18091262615445210751968245)
                    ·
                      refine ⟨1696055870197988507997023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18091262615445210751968245 1696055870197988507997023)
                      ·
                        rfl

theorem cell23_3303057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 5].length) (baseStart_3303057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3303057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3303057 prefixEnd_3303057 := by exact prefixLift 3303057
  have htrace : WordTrace (prefixWord ++ tailWord_3303057) baseStart_3303057 baseEnd_3303057 := by
    simpa [prefixWord, tailWord_3303057, baseEnd_3303057] using wordTrace_append hprefix tailTrace_3303057
  have hstable : (prefixWord ++ tailWord_3303057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3303057).length < 2 ^ (prefixWord ++ tailWord_3303057).sum := by decide
  have hdescent : baseEnd_3303057 < baseStart_3303057 := by decide
  rcases family_descends (prefixWord ++ tailWord_3303057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3303104 : List Nat := [2, 1, 1, 2, 4, 1, 1, 1, 2, 5, 3]
def baseStart_3303104 : Nat := 118140960795 + 3303104 * 2 ^ 59
def prefixEnd_3303104 : Nat := 4983230072969 + 3 ^ 40 * 3303104 * 2
def baseEnd_3303104 : Nat := 1696080003788749824109307

theorem tailTrace_3303104 : CollatzResearch.WordTrace tailWord_3303104 prefixEnd_3303104 1696080003788749824109307 := by
  unfold tailWord_3303104
  simp only [CollatzResearch.WordTrace]
  refine ⟨60237050112712904048002183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80316066816950538730669577 60237050112712904048002183)
  ·
    refine ⟨90355575169069356072003275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60237050112712904048002183 90355575169069356072003275)
    ·
      refine ⟨135533362753604034108004913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90355575169069356072003275 135533362753604034108004913)
      ·
        refine ⟨101650022065203025581003685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135533362753604034108004913 101650022065203025581003685)
        ·
          refine ⟨19059379137225567296438191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101650022065203025581003685 19059379137225567296438191)
          ·
            refine ⟨28589068705838350944657287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19059379137225567296438191 28589068705838350944657287)
            ·
              refine ⟨42883603058757526416985931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28589068705838350944657287 42883603058757526416985931)
              ·
                refine ⟨64325404588136289625478897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42883603058757526416985931 64325404588136289625478897)
                ·
                  refine ⟨48244053441102217219109173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64325404588136289625478897 48244053441102217219109173)
                  ·
                    refine ⟨4522880010103332864291485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48244053441102217219109173 4522880010103332864291485)
                    ·
                      refine ⟨1696080003788749824109307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4522880010103332864291485 1696080003788749824109307)
                      ·
                        rfl

theorem cell23_3303104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 2, 5, 3].length) (baseStart_3303104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3303104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3303104 prefixEnd_3303104 := by exact prefixLift 3303104
  have htrace : WordTrace (prefixWord ++ tailWord_3303104) baseStart_3303104 baseEnd_3303104 := by
    simpa [prefixWord, tailWord_3303104, baseEnd_3303104] using wordTrace_append hprefix tailTrace_3303104
  have hstable : (prefixWord ++ tailWord_3303104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3303104).length < 2 ^ (prefixWord ++ tailWord_3303104).sum := by decide
  have hdescent : baseEnd_3303104 < baseStart_3303104 := by decide
  rcases family_descends (prefixWord ++ tailWord_3303104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3303107 : List Nat := [1, 1, 1, 3, 1, 1, 1, 1, 4, 9]
def baseStart_3303107 : Nat := 118140960795 + 3303107 * 2 ^ 59
def prefixEnd_3303107 : Nat := 4983230072969 + 3 ^ 40 * 3303107 * 2
def baseEnd_3303107 : Nat := 565360514743571104123931

theorem tailTrace_3303107 : CollatzResearch.WordTrace tailWord_3303107 prefixEnd_3303107 565360514743571104123931 := by
  unfold tailWord_3303107
  simp only [CollatzResearch.WordTrace]
  refine ⟨120474209644414939608363575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80316139762943293072242383 120474209644414939608363575)
  ·
    refine ⟨180711314466622409412545363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120474209644414939608363575 180711314466622409412545363)
    ·
      refine ⟨271066971699933614118818045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180711314466622409412545363 271066971699933614118818045)
      ·
        refine ⟨101650114387475105294556767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 271066971699933614118818045 101650114387475105294556767)
        ·
          refine ⟨152475171581212657941835151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101650114387475105294556767 152475171581212657941835151)
          ·
            refine ⟨228712757371818986912752727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152475171581212657941835151 228712757371818986912752727)
            ·
              refine ⟨343069136057728480369129091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 228712757371818986912752727 343069136057728480369129091)
              ·
                refine ⟨514603704086592720553693637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 343069136057728480369129091 514603704086592720553693637)
                ·
                  refine ⟨96488194516236135103817557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 514603704086592720553693637 96488194516236135103817557)
                  ·
                    refine ⟨565360514743571104123931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 96488194516236135103817557 565360514743571104123931)
                    ·
                      rfl

theorem cell23_3303107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 9].length) (baseStart_3303107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3303107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3303107 prefixEnd_3303107 := by exact prefixLift 3303107
  have htrace : WordTrace (prefixWord ++ tailWord_3303107) baseStart_3303107 baseEnd_3303107 := by
    simpa [prefixWord, tailWord_3303107, baseEnd_3303107] using wordTrace_append hprefix tailTrace_3303107
  have hstable : (prefixWord ++ tailWord_3303107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3303107).length < 2 ^ (prefixWord ++ tailWord_3303107).sum := by decide
  have hdescent : baseEnd_3303107 < baseStart_3303107 := by decide
  rcases family_descends (prefixWord ++ tailWord_3303107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3303132 : List Nat := [2, 2, 5, 1, 3, 1, 1, 1, 3, 4]
def baseStart_3303132 : Nat := 118140960795 + 3303132 * 2 ^ 59
def prefixEnd_3303132 : Nat := 4983230072969 + 3 ^ 40 * 3303132 * 2
def baseEnd_3303132 : Nat := 565364793749025238186393

theorem tailTrace_3303132 : CollatzResearch.WordTrace tailWord_3303132 prefixEnd_3303132 565364793749025238186393 := by
  unfold tailWord_3303132
  simp only [CollatzResearch.WordTrace]
  refine ⟨60237560734662184439011825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80316747646216245918682433 60237560734662184439011825)
  ·
    refine ⟨45178170550996638329258869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60237560734662184439011825 45178170550996638329258869)
    ·
      refine ⟨4235453489155934843368019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 45178170550996638329258869 4235453489155934843368019)
      ·
        refine ⟨6353180233733902265052029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4235453489155934843368019 6353180233733902265052029)
        ·
          refine ⟨2382442587650213349394511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6353180233733902265052029 2382442587650213349394511)
          ·
            refine ⟨3573663881475320024091767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2382442587650213349394511 3573663881475320024091767)
            ·
              refine ⟨5360495822212980036137651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3573663881475320024091767 5360495822212980036137651)
              ·
                refine ⟨8040743733319470054206477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5360495822212980036137651 8040743733319470054206477)
                ·
                  refine ⟨3015278899994801270327429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8040743733319470054206477 3015278899994801270327429)
                  ·
                    refine ⟨565364793749025238186393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3015278899994801270327429 565364793749025238186393)
                    ·
                      rfl

theorem cell23_3303132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_3303132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3303132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3303132 prefixEnd_3303132 := by exact prefixLift 3303132
  have htrace : WordTrace (prefixWord ++ tailWord_3303132) baseStart_3303132 baseEnd_3303132 := by
    simpa [prefixWord, tailWord_3303132, baseEnd_3303132] using wordTrace_append hprefix tailTrace_3303132
  have hstable : (prefixWord ++ tailWord_3303132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3303132).length < 2 ^ (prefixWord ++ tailWord_3303132).sum := by decide
  have hdescent : baseEnd_3303132 < baseStart_3303132 := by decide
  rcases family_descends (prefixWord ++ tailWord_3303132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3303158 : List Nat := [5, 1, 1, 1, 1, 3, 3, 2, 1, 5]
def baseStart_3303158 : Nat := 118140960795 + 3303158 * 2 ^ 59
def prefixEnd_3303158 : Nat := 4983230072969 + 3 ^ 40 * 3303158 * 2
def baseEnd_3303158 : Nat := 565369243914697537611353

theorem tailTrace_3303158 : CollatzResearch.WordTrace tailWord_3303158 prefixEnd_3303158 565369243914697537611353 := by
  unfold tailWord_3303158
  simp only [CollatzResearch.WordTrace]
  refine ⟨7529754360451885957404383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 80317379844820116878980085 7529754360451885957404383)
  ·
    refine ⟨11294631540677828936106575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7529754360451885957404383 11294631540677828936106575)
    ·
      refine ⟨16941947311016743404159863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11294631540677828936106575 16941947311016743404159863)
      ·
        refine ⟨25412920966525115106239795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16941947311016743404159863 25412920966525115106239795)
        ·
          refine ⟨38119381449787672659359693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25412920966525115106239795 38119381449787672659359693)
          ·
            refine ⟨14294768043670377247259885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38119381449787672659359693 14294768043670377247259885)
            ·
              refine ⟨5360538016376391467722457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14294768043670377247259885 5360538016376391467722457)
              ·
                refine ⟨4020403512282293600791843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5360538016376391467722457 4020403512282293600791843)
                ·
                  refine ⟨6030605268423440401187765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4020403512282293600791843 6030605268423440401187765)
                  ·
                    refine ⟨565369243914697537611353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6030605268423440401187765 565369243914697537611353)
                    ·
                      rfl

theorem cell23_3303158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3, 2, 1, 5].length) (baseStart_3303158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3303158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3303158 prefixEnd_3303158 := by exact prefixLift 3303158
  have htrace : WordTrace (prefixWord ++ tailWord_3303158) baseStart_3303158 baseEnd_3303158 := by
    simpa [prefixWord, tailWord_3303158, baseEnd_3303158] using wordTrace_append hprefix tailTrace_3303158
  have hstable : (prefixWord ++ tailWord_3303158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3303158).length < 2 ^ (prefixWord ++ tailWord_3303158).sum := by decide
  have hdescent : baseEnd_3303158 < baseStart_3303158 := by decide
  rcases family_descends (prefixWord ++ tailWord_3303158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3303175 : List Nat := [1, 1, 4, 4, 2, 1, 3, 1, 1, 5]
def baseStart_3303175 : Nat := 118140960795 + 3303175 * 2 ^ 59
def prefixEnd_3303175 : Nat := 4983230072969 + 3 ^ 40 * 3303175 * 2
def baseEnd_3303175 : Nat := 565372153638406348773827

theorem tailTrace_3303175 : CollatzResearch.WordTrace tailWord_3303175 prefixEnd_3303175 565372153638406348773827 := by
  unfold tailWord_3303175
  simp only [CollatzResearch.WordTrace]
  refine ⟨120476689808168587221838979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80317793205445724814559319 120476689808168587221838979)
  ·
    refine ⟨180715034712252880832758469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120476689808168587221838979 180715034712252880832758469)
    ·
      refine ⟨33884069008547415156142213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 180715034712252880832758469 33884069008547415156142213)
      ·
        refine ⟨6353262939102640341776665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33884069008547415156142213 6353262939102640341776665)
        ·
          refine ⟨4764947204326980256332499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6353262939102640341776665 4764947204326980256332499)
          ·
            refine ⟨7147420806490470384498749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4764947204326980256332499 7147420806490470384498749)
            ·
              refine ⟨2680282802433926394187031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7147420806490470384498749 2680282802433926394187031)
              ·
                refine ⟨4020424203650889591280547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2680282802433926394187031 4020424203650889591280547)
                ·
                  refine ⟨6030636305476334386920821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4020424203650889591280547 6030636305476334386920821)
                  ·
                    refine ⟨565372153638406348773827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6030636305476334386920821 565372153638406348773827)
                    ·
                      rfl

theorem cell23_3303175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 3, 1, 1, 5].length) (baseStart_3303175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3303175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3303175 prefixEnd_3303175 := by exact prefixLift 3303175
  have htrace : WordTrace (prefixWord ++ tailWord_3303175) baseStart_3303175 baseEnd_3303175 := by
    simpa [prefixWord, tailWord_3303175, baseEnd_3303175] using wordTrace_append hprefix tailTrace_3303175
  have hstable : (prefixWord ++ tailWord_3303175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3303175).length < 2 ^ (prefixWord ++ tailWord_3303175).sum := by decide
  have hdescent : baseEnd_3303175 < baseStart_3303175 := by decide
  rcases family_descends (prefixWord ++ tailWord_3303175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3303195 : List Nat := [1, 1, 1, 1, 1, 1, 4, 8, 1, 2, 2]
def baseStart_3303195 : Nat := 118140960795 + 3303195 * 2 ^ 59
def prefixEnd_3303195 : Nat := 4983230072969 + 3 ^ 40 * 3303195 * 2
def baseEnd_3303195 : Nat := 1696126730528308968071389

theorem tailTrace_3303195 : CollatzResearch.WordTrace tailWord_3303195 prefixEnd_3303195 1696126730528308968071389 := by
  unfold tailWord_3303195
  simp only [CollatzResearch.WordTrace]
  refine ⟨120477419268096130637567039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80318279512064087091711359 120477419268096130637567039)
  ·
    refine ⟨180716128902144195956350559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120477419268096130637567039 180716128902144195956350559)
    ·
      refine ⟨271074193353216293934525839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180716128902144195956350559 271074193353216293934525839)
      ·
        refine ⟨406611290029824440901788759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271074193353216293934525839 406611290029824440901788759)
        ·
          refine ⟨609916935044736661352683139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 406611290029824440901788759 609916935044736661352683139)
          ·
            refine ⟨914875402567104992029024709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 609916935044736661352683139 914875402567104992029024709)
            ·
              refine ⟨171539137981332186005442133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 914875402567104992029024709 171539137981332186005442133)
              ·
                refine ⟨2010224273218736554751275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 171539137981332186005442133 2010224273218736554751275)
                ·
                  refine ⟨3015336409828104832126913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2010224273218736554751275 3015336409828104832126913)
                  ·
                    refine ⟨2261502307371078624095185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3015336409828104832126913 2261502307371078624095185)
                    ·
                      refine ⟨1696126730528308968071389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2261502307371078624095185 1696126730528308968071389)
                      ·
                        rfl

theorem cell23_3303195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 8, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 8, 1, 2, 2].length) (baseStart_3303195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3303195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3303195 prefixEnd_3303195 := by exact prefixLift 3303195
  have htrace : WordTrace (prefixWord ++ tailWord_3303195) baseStart_3303195 baseEnd_3303195 := by
    simpa [prefixWord, tailWord_3303195, baseEnd_3303195] using wordTrace_append hprefix tailTrace_3303195
  have hstable : (prefixWord ++ tailWord_3303195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3303195).length < 2 ^ (prefixWord ++ tailWord_3303195).sum := by decide
  have hdescent : baseEnd_3303195 < baseStart_3303195 := by decide
  rcases family_descends (prefixWord ++ tailWord_3303195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3303201 : List Nat := [1, 2, 3, 2, 1, 5, 1, 8]
def baseStart_3303201 : Nat := 118140960795 + 3303201 * 2 ^ 59
def prefixEnd_3303201 : Nat := 4983230072969 + 3 ^ 40 * 3303201 * 2
def baseEnd_3303201 : Nat := 62819622644897627577643

theorem tailTrace_3303201 : CollatzResearch.WordTrace tailWord_3303201 prefixEnd_3303201 62819622644897627577643 := by
  unfold tailWord_3303201
  simp only [CollatzResearch.WordTrace]
  refine ⟨120477638106074393662285457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80318425404049595774856971 120477638106074393662285457)
  ·
    refine ⟨90358228579555795246714093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120477638106074393662285457 90358228579555795246714093)
    ·
      refine ⟨33884335717333423217517785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90358228579555795246714093 33884335717333423217517785)
      ·
        refine ⟨25413251788000067413138339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33884335717333423217517785 25413251788000067413138339)
        ·
          refine ⟨38119877682000101119707509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25413251788000067413138339 38119877682000101119707509)
          ·
            refine ⟨3573738532687509479972579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38119877682000101119707509 3573738532687509479972579)
            ·
              refine ⟨5360607799031264219958869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3573738532687509479972579 5360607799031264219958869)
              ·
                refine ⟨62819622644897627577643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5360607799031264219958869 62819622644897627577643)
                ·
                  rfl

theorem cell23_3303201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 1, 8].length) (baseStart_3303201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3303201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3303201 prefixEnd_3303201 := by exact prefixLift 3303201
  have htrace : WordTrace (prefixWord ++ tailWord_3303201) baseStart_3303201 baseEnd_3303201 := by
    simpa [prefixWord, tailWord_3303201, baseEnd_3303201] using wordTrace_append hprefix tailTrace_3303201
  have hstable : (prefixWord ++ tailWord_3303201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3303201).length < 2 ^ (prefixWord ++ tailWord_3303201).sum := by decide
  have hdescent : baseEnd_3303201 < baseStart_3303201 := by decide
  rcases family_descends (prefixWord ++ tailWord_3303201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3303208 : List Nat := [2, 1, 5, 1, 1, 3, 2, 1, 1, 2, 4]
def baseStart_3303208 : Nat := 118140960795 + 3303208 * 2 ^ 59
def prefixEnd_3303208 : Nat := 4983230072969 + 3 ^ 40 * 3303208 * 2
def baseEnd_3303208 : Nat := 1696133405776817417208829

theorem tailTrace_3303208 : CollatzResearch.WordTrace tailWord_3303208 prefixEnd_3303208 1696133405776817417208829 := by
  unfold tailWord_3303208
  simp only [CollatzResearch.WordTrace]
  refine ⟨60238946708524516928895139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80318595611366022571860185 60238946708524516928895139)
  ·
    refine ⟨90358420062786775393342709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60238946708524516928895139 90358420062786775393342709)
    ·
      refine ⟨8471101880886260193125879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 90358420062786775393342709 8471101880886260193125879)
      ·
        refine ⟨12706652821329390289688819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8471101880886260193125879 12706652821329390289688819)
        ·
          refine ⟨19059979231994085434533229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12706652821329390289688819 19059979231994085434533229)
          ·
            refine ⟨7147492211997782037949961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19059979231994085434533229 7147492211997782037949961)
            ·
              refine ⟨5360619158998336528462471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7147492211997782037949961 5360619158998336528462471)
              ·
                refine ⟨8040928738497504792693707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5360619158998336528462471 8040928738497504792693707)
                ·
                  refine ⟨12061393107746257189040561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8040928738497504792693707 12061393107746257189040561)
                  ·
                    refine ⟨9046044830809692891780421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12061393107746257189040561 9046044830809692891780421)
                    ·
                      refine ⟨1696133405776817417208829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9046044830809692891780421 1696133405776817417208829)
                      ·
                        rfl

theorem cell23_3303208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2, 1, 1, 2, 4].length) (baseStart_3303208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3303208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3303208 prefixEnd_3303208 := by exact prefixLift 3303208
  have htrace : WordTrace (prefixWord ++ tailWord_3303208) baseStart_3303208 baseEnd_3303208 := by
    simpa [prefixWord, tailWord_3303208, baseEnd_3303208] using wordTrace_append hprefix tailTrace_3303208
  have hstable : (prefixWord ++ tailWord_3303208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3303208).length < 2 ^ (prefixWord ++ tailWord_3303208).sum := by decide
  have hdescent : baseEnd_3303208 < baseStart_3303208 := by decide
  rcases family_descends (prefixWord ++ tailWord_3303208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3303229 : List Nat := [1, 4, 1, 4, 1, 2, 2, 3, 1, 2, 2]
def baseStart_3303229 : Nat := 118140960795 + 3303229 * 2 ^ 59
def prefixEnd_3303229 : Nat := 4983230072969 + 3 ^ 40 * 3303229 * 2
def baseEnd_3303229 : Nat := 1696144188870561835046233

theorem tailTrace_3303229 : CollatzResearch.WordTrace tailWord_3303229 prefixEnd_3303229 1696144188870561835046233 := by
  unfold tailWord_3303229
  simp only [CollatzResearch.WordTrace]
  refine ⟨120478659349972954444304741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80319106233315302962869827 120478659349972954444304741)
  ·
    refine ⟨22589748628119928958307139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120478659349972954444304741 22589748628119928958307139)
    ·
      refine ⟨33884622942179893437460709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22589748628119928958307139 33884622942179893437460709)
      ·
        refine ⟨6353366801658730019523883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33884622942179893437460709 6353366801658730019523883)
        ·
          refine ⟨9530050202488095029285825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6353366801658730019523883 9530050202488095029285825)
          ·
            refine ⟨7147537651866071271964369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9530050202488095029285825 7147537651866071271964369)
            ·
              refine ⟨5360653238899553453973277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7147537651866071271964369 5360653238899553453973277)
              ·
                refine ⟨2010244964587332545239979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5360653238899553453973277 2010244964587332545239979)
                ·
                  refine ⟨3015367446880998817859969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2010244964587332545239979 3015367446880998817859969)
                  ·
                    refine ⟨2261525585160749113394977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3015367446880998817859969 2261525585160749113394977)
                    ·
                      refine ⟨1696144188870561835046233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2261525585160749113394977 1696144188870561835046233)
                      ·
                        rfl

theorem cell23_3303229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2, 3, 1, 2, 2].length) (baseStart_3303229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3303229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3303229 prefixEnd_3303229 := by exact prefixLift 3303229
  have htrace : WordTrace (prefixWord ++ tailWord_3303229) baseStart_3303229 baseEnd_3303229 := by
    simpa [prefixWord, tailWord_3303229, baseEnd_3303229] using wordTrace_append hprefix tailTrace_3303229
  have hstable : (prefixWord ++ tailWord_3303229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3303229).length < 2 ^ (prefixWord ++ tailWord_3303229).sum := by decide
  have hdescent : baseEnd_3303229 < baseStart_3303229 := by decide
  rcases family_descends (prefixWord ++ tailWord_3303229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3303251 : List Nat := [1, 1, 1, 2, 1, 1, 3, 1, 2, 8, 2]
def baseStart_3303251 : Nat := 118140960795 + 3303251 * 2 ^ 59
def prefixEnd_3303251 : Nat := 4983230072969 + 3 ^ 40 * 3303251 * 2
def baseEnd_3303251 : Nat := 1696155485444960748971131

theorem tailTrace_3303251 : CollatzResearch.WordTrace tailWord_3303251 prefixEnd_3303251 1696155485444960748971131 := by
  unfold tailWord_3303251
  simp only [CollatzResearch.WordTrace]
  refine ⟨120479461755893252201605607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80319641170595501467737071 120479461755893252201605607)
  ·
    refine ⟨180719192633839878302408411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120479461755893252201605607 180719192633839878302408411)
    ·
      refine ⟨271078788950759817453612617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180719192633839878302408411 271078788950759817453612617)
      ·
        refine ⟨203309091713069863090209463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 271078788950759817453612617 203309091713069863090209463)
        ·
          refine ⟨304963637569604794635314195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203309091713069863090209463 304963637569604794635314195)
          ·
            refine ⟨457445456354407191952971293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 304963637569604794635314195 457445456354407191952971293)
            ·
              refine ⟨171542046132902696982364235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 457445456354407191952971293 171542046132902696982364235)
              ·
                refine ⟨257313069199354045473546353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 171542046132902696982364235 257313069199354045473546353)
                ·
                  refine ⟨192984801899515534105159765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 257313069199354045473546353 192984801899515534105159765)
                  ·
                    refine ⟨2261540647259947665294841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 192984801899515534105159765 2261540647259947665294841)
                    ·
                      refine ⟨1696155485444960748971131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2261540647259947665294841 1696155485444960748971131)
                      ·
                        rfl

theorem cell23_3303251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 8, 2].length) (baseStart_3303251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3303251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3303251 prefixEnd_3303251 := by exact prefixLift 3303251
  have htrace : WordTrace (prefixWord ++ tailWord_3303251) baseStart_3303251 baseEnd_3303251 := by
    simpa [prefixWord, tailWord_3303251, baseEnd_3303251] using wordTrace_append hprefix tailTrace_3303251
  have hstable : (prefixWord ++ tailWord_3303251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3303251).length < 2 ^ (prefixWord ++ tailWord_3303251).sum := by decide
  have hdescent : baseEnd_3303251 < baseStart_3303251 := by decide
  rcases family_descends (prefixWord ++ tailWord_3303251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3303271 : List Nat := [1, 1, 5, 1, 2, 1, 2, 2, 2, 1, 5]
def baseStart_3303271 : Nat := 118140960795 + 3303271 * 2 ^ 59
def prefixEnd_3303271 : Nat := 4983230072969 + 3 ^ 40 * 3303271 * 2
def baseEnd_3303271 : Nat := 1696165755058050670721039

theorem tailTrace_3303271 : CollatzResearch.WordTrace tailWord_3303271 prefixEnd_3303271 1696165755058050670721039 := by
  unfold tailWord_3303271
  simp only [CollatzResearch.WordTrace]
  refine ⟨120480191215820795617333667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80320127477213863744889111 120480191215820795617333667)
  ·
    refine ⟨180720286823731193426000501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120480191215820795617333667 180720286823731193426000501)
    ·
      refine ⟨16942526889724799383687547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 180720286823731193426000501 16942526889724799383687547)
      ·
        refine ⟨25413790334587199075531321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16942526889724799383687547 25413790334587199075531321)
        ·
          refine ⟨19060342750940399306648491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25413790334587199075531321 19060342750940399306648491)
          ·
            refine ⟨28590514126410598959972737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19060342750940399306648491 28590514126410598959972737)
            ·
              refine ⟨21442885594807949219979553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28590514126410598959972737 21442885594807949219979553)
              ·
                refine ⟨16082164196105961914984665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21442885594807949219979553 16082164196105961914984665)
                ·
                  refine ⟨12061623147079471436238499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16082164196105961914984665 12061623147079471436238499)
                  ·
                    refine ⟨18092434720619207154357749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12061623147079471436238499 18092434720619207154357749)
                    ·
                      refine ⟨1696165755058050670721039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18092434720619207154357749 1696165755058050670721039)
                      ·
                        rfl

theorem cell23_3303271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 2, 2, 1, 5].length) (baseStart_3303271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3303271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3303271 prefixEnd_3303271 := by exact prefixLift 3303271
  have htrace : WordTrace (prefixWord ++ tailWord_3303271) baseStart_3303271 baseEnd_3303271 := by
    simpa [prefixWord, tailWord_3303271, baseEnd_3303271] using wordTrace_append hprefix tailTrace_3303271
  have hstable : (prefixWord ++ tailWord_3303271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3303271).length < 2 ^ (prefixWord ++ tailWord_3303271).sum := by decide
  have hdescent : baseEnd_3303271 < baseStart_3303271 := by decide
  rcases family_descends (prefixWord ++ tailWord_3303271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3303285 : List Nat := [1, 3, 4, 1, 1, 1, 1, 1, 6, 2, 2]
def baseStart_3303285 : Nat := 118140960795 + 3303285 * 2 ^ 59
def prefixEnd_3303285 : Nat := 4983230072969 + 3 ^ 40 * 3303285 * 2
def baseEnd_3303285 : Nat := 1696172943787213615945975

theorem tailTrace_3303285 : CollatzResearch.WordTrace tailWord_3303285 prefixEnd_3303285 1696172943787213615945975 := by
  unfold tailWord_3303285
  simp only [CollatzResearch.WordTrace]
  refine ⟨120480701837770076008343309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80320467891846717338895539 120480701837770076008343309)
  ·
    refine ⟨45180263189163778503128741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120480701837770076008343309 45180263189163778503128741)
    ·
      refine ⟨8471299347968208469336639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45180263189163778503128741 8471299347968208469336639)
      ·
        refine ⟨12706949021952312704004959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8471299347968208469336639 12706949021952312704004959)
        ·
          refine ⟨19060423532928469056007439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12706949021952312704004959 19060423532928469056007439)
          ·
            refine ⟨28590635299392703584011159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19060423532928469056007439 28590635299392703584011159)
            ·
              refine ⟨42885952949089055376016739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28590635299392703584011159 42885952949089055376016739)
              ·
                refine ⟨64328929423633583064025109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42885952949089055376016739 64328929423633583064025109)
                ·
                  refine ⟨3015418566732824206126177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 64328929423633583064025109 3015418566732824206126177)
                  ·
                    refine ⟨2261563925049618154594633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3015418566732824206126177 2261563925049618154594633)
                    ·
                      refine ⟨1696172943787213615945975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2261563925049618154594633 1696172943787213615945975)
                      ·
                        rfl

theorem cell23_3303285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 6, 2, 2].length) (baseStart_3303285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3303285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3303285 prefixEnd_3303285 := by exact prefixLift 3303285
  have htrace : WordTrace (prefixWord ++ tailWord_3303285) baseStart_3303285 baseEnd_3303285 := by
    simpa [prefixWord, tailWord_3303285, baseEnd_3303285] using wordTrace_append hprefix tailTrace_3303285
  have hstable : (prefixWord ++ tailWord_3303285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3303285).length < 2 ^ (prefixWord ++ tailWord_3303285).sum := by decide
  have hdescent : baseEnd_3303285 < baseStart_3303285 := by decide
  rcases family_descends (prefixWord ++ tailWord_3303285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3303319 : List Nat := [1, 1, 3, 3, 1, 5, 2, 1, 2, 2, 2]
def baseStart_3303319 : Nat := 118140960795 + 3303319 * 2 ^ 59
def prefixEnd_3303319 : Nat := 4983230072969 + 3 ^ 40 * 3303319 * 2
def baseEnd_3303319 : Nat := 1696190402129466482920819

theorem tailTrace_3303319 : CollatzResearch.WordTrace tailWord_3303319 prefixEnd_3303319 1696190402129466482920819 := by
  unfold tailWord_3303319
  simp only [CollatzResearch.WordTrace]
  refine ⟨120481941919646899815081011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80321294613097933210054007 120481941919646899815081011)
  ·
    refine ⟨180722912879470349722621517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120481941919646899815081011 180722912879470349722621517)
    ·
      refine ⟨67771092329801381145983069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180722912879470349722621517 67771092329801381145983069)
      ·
        refine ⟨25414159623675517929743651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67771092329801381145983069 25414159623675517929743651)
        ·
          refine ⟨38121239435513276894615477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25414159623675517929743651 38121239435513276894615477)
          ·
            refine ⟨3573866197079369708870201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38121239435513276894615477 3573866197079369708870201)
            ·
              refine ⟨2680399647809527281652651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3573866197079369708870201 2680399647809527281652651)
              ·
                refine ⟨4020599471714290922478977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2680399647809527281652651 4020599471714290922478977)
                ·
                  refine ⟨3015449603785718191859233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4020599471714290922478977 3015449603785718191859233)
                  ·
                    refine ⟨2261587202839288643894425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3015449603785718191859233 2261587202839288643894425)
                    ·
                      refine ⟨1696190402129466482920819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2261587202839288643894425 1696190402129466482920819)
                      ·
                        rfl

theorem cell23_3303319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 2, 1, 2, 2, 2].length) (baseStart_3303319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3303319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3303319 prefixEnd_3303319 := by exact prefixLift 3303319
  have htrace : WordTrace (prefixWord ++ tailWord_3303319) baseStart_3303319 baseEnd_3303319 := by
    simpa [prefixWord, tailWord_3303319, baseEnd_3303319] using wordTrace_append hprefix tailTrace_3303319
  have hstable : (prefixWord ++ tailWord_3303319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3303319).length < 2 ^ (prefixWord ++ tailWord_3303319).sum := by decide
  have hdescent : baseEnd_3303319 < baseStart_3303319 := by decide
  rcases family_descends (prefixWord ++ tailWord_3303319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3303385 : List Nat := [1, 2, 1, 2, 6, 1, 1, 2, 3, 4]
def baseStart_3303385 : Nat := 118140960795 + 3303385 * 2 ^ 59
def prefixEnd_3303385 : Nat := 4983230072969 + 3 ^ 40 * 3303385 * 2
def baseEnd_3303385 : Nat := 565408097284221074898505

theorem tailTrace_3303385 : CollatzResearch.WordTrace tailWord_3303385 prefixEnd_3303385 565408097284221074898505 := by
  unfold tailWord_3303385
  simp only [CollatzResearch.WordTrace]
  refine ⟨120484349137407793086983609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80322899424938528724655739 120484349137407793086983609)
  ·
    refine ⟨90363261853055844815237707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120484349137407793086983609 90363261853055844815237707)
    ·
      refine ⟨135544892779583767222856561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90363261853055844815237707 135544892779583767222856561)
      ·
        refine ⟨101658669584687825417142421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135544892779583767222856561 101658669584687825417142421)
        ·
          refine ⟨4765250136782241816428551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 101658669584687825417142421 4765250136782241816428551)
          ·
            refine ⟨7147875205173362724642827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4765250136782241816428551 7147875205173362724642827)
            ·
              refine ⟨10721812807760044086964241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7147875205173362724642827 10721812807760044086964241)
              ·
                refine ⟨8041359605820033065223181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10721812807760044086964241 8041359605820033065223181)
                ·
                  refine ⟨3015509852182512399458693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8041359605820033065223181 3015509852182512399458693)
                  ·
                    refine ⟨565408097284221074898505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3015509852182512399458693 565408097284221074898505)
                    ·
                      rfl

theorem cell23_3303385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 2, 3, 4].length) (baseStart_3303385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3303385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3303385 prefixEnd_3303385 := by exact prefixLift 3303385
  have htrace : WordTrace (prefixWord ++ tailWord_3303385) baseStart_3303385 baseEnd_3303385 := by
    simpa [prefixWord, tailWord_3303385, baseEnd_3303385] using wordTrace_append hprefix tailTrace_3303385
  have hstable : (prefixWord ++ tailWord_3303385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3303385).length < 2 ^ (prefixWord ++ tailWord_3303385).sum := by decide
  have hdescent : baseEnd_3303385 < baseStart_3303385 := by decide
  rcases family_descends (prefixWord ++ tailWord_3303385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3303395 : List Nat := [1, 1, 1, 6, 1, 2, 3, 1, 2, 2, 3]
def baseStart_3303395 : Nat := 118140960795 + 3303395 * 2 ^ 59
def prefixEnd_3303395 : Nat := 4983230072969 + 3 ^ 40 * 3303395 * 2
def baseEnd_3303395 : Nat := 1696229426659208185570469

theorem tailTrace_3303395 : CollatzResearch.WordTrace tailWord_3303395 prefixEnd_3303395 1696229426659208185570469 := by
  unfold tailWord_3303395
  simp only [CollatzResearch.WordTrace]
  refine ⟨120484713867371564794847639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80323142578247709863231759 120484713867371564794847639)
  ·
    refine ⟨180727070801057347192271459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120484713867371564794847639 180727070801057347192271459)
    ·
      refine ⟨271090606201586020788407189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180727070801057347192271459 271090606201586020788407189)
      ·
        refine ⟨12707372165699344724456587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 271090606201586020788407189 12707372165699344724456587)
        ·
          refine ⟨19061058248549017086684881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12707372165699344724456587 19061058248549017086684881)
          ·
            refine ⟨14295793686411762815013661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19061058248549017086684881 14295793686411762815013661)
            ·
              refine ⟨5360922632404411055630123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14295793686411762815013661 5360922632404411055630123)
              ·
                refine ⟨8041383948606616583445185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5360922632404411055630123 8041383948606616583445185)
                ·
                  refine ⟨6031037961454962437583889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8041383948606616583445185 6031037961454962437583889)
                  ·
                    refine ⟨4523278471091221828187917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6031037961454962437583889 4523278471091221828187917)
                    ·
                      refine ⟨1696229426659208185570469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4523278471091221828187917 1696229426659208185570469)
                      ·
                        rfl

theorem cell23_3303395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3, 1, 2, 2, 3].length) (baseStart_3303395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3303395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3303395 prefixEnd_3303395 := by exact prefixLift 3303395
  have htrace : WordTrace (prefixWord ++ tailWord_3303395) baseStart_3303395 baseEnd_3303395 := by
    simpa [prefixWord, tailWord_3303395, baseEnd_3303395] using wordTrace_append hprefix tailTrace_3303395
  have hstable : (prefixWord ++ tailWord_3303395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3303395).length < 2 ^ (prefixWord ++ tailWord_3303395).sum := by decide
  have hdescent : baseEnd_3303395 < baseStart_3303395 := by decide
  rcases family_descends (prefixWord ++ tailWord_3303395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3303402 : List Nat := [3, 1, 3, 1, 2, 1, 4, 3, 1, 4]
def baseStart_3303402 : Nat := 118140960795 + 3303402 * 2 ^ 59
def prefixEnd_3303402 : Nat := 4983230072969 + 3 ^ 40 * 3303402 * 2
def baseEnd_3303402 : Nat := 565411007007929886060979

theorem tailTrace_3303402 : CollatzResearch.WordTrace tailWord_3303402 prefixEnd_3303402 565411007007929886060979 := by
  unfold tailWord_3303402
  simp only [CollatzResearch.WordTrace]
  refine ⟨30121242294586551247588115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80323312785564136660234973 30121242294586551247588115)
  ·
    refine ⟨45181863441879826871382173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30121242294586551247588115 45181863441879826871382173)
    ·
      refine ⟨16943198790704935076768315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45181863441879826871382173 16943198790704935076768315)
      ·
        refine ⟨25414798186057402615152473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16943198790704935076768315 25414798186057402615152473)
        ·
          refine ⟨19061098639543051961364355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25414798186057402615152473 19061098639543051961364355)
          ·
            refine ⟨28591647959314577942046533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19061098639543051961364355 28591647959314577942046533)
            ·
              refine ⟨5360933992371483364133725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28591647959314577942046533 5360933992371483364133725)
              ·
                refine ⟨2010350247139306261550147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5360933992371483364133725 2010350247139306261550147)
                ·
                  refine ⟨3015525370708959392325221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2010350247139306261550147 3015525370708959392325221)
                  ·
                    refine ⟨565411007007929886060979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3015525370708959392325221 565411007007929886060979)
                    ·
                      rfl

theorem cell23_3303402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4, 3, 1, 4].length) (baseStart_3303402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3303402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3303402 prefixEnd_3303402 := by exact prefixLift 3303402
  have htrace : WordTrace (prefixWord ++ tailWord_3303402) baseStart_3303402 baseEnd_3303402 := by
    simpa [prefixWord, tailWord_3303402, baseEnd_3303402] using wordTrace_append hprefix tailTrace_3303402
  have hstable : (prefixWord ++ tailWord_3303402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3303402).length < 2 ^ (prefixWord ++ tailWord_3303402).sum := by decide
  have hdescent : baseEnd_3303402 < baseStart_3303402 := by decide
  rcases family_descends (prefixWord ++ tailWord_3303402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3303458 : List Nat := [3, 3, 1, 1, 1, 2, 2, 1, 3, 6]
def baseStart_3303458 : Nat := 118140960795 + 3303458 * 2 ^ 59
def prefixEnd_3303458 : Nat := 4983230072969 + 3 ^ 40 * 3303458 * 2
def baseEnd_3303458 : Nat := 565420591980147146360893

theorem tailTrace_3303458 : CollatzResearch.WordTrace tailWord_3303458 prefixEnd_3303458 565420591980147146360893 := by
  unfold tailWord_3303458
  simp only [CollatzResearch.WordTrace]
  refine ⟨30121752916535831638597757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80324674444095551036260685 30121752916535831638597757)
  ·
    refine ⟨11295657343700936864474159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30121752916535831638597757 11295657343700936864474159)
    ·
      refine ⟨16943486015551405296711239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11295657343700936864474159 16943486015551405296711239)
      ·
        refine ⟨25415229023327107945066859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16943486015551405296711239 25415229023327107945066859)
        ·
          refine ⟨38122843534990661917600289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25415229023327107945066859 38122843534990661917600289)
          ·
            refine ⟨28592132651242996438200217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38122843534990661917600289 28592132651242996438200217)
            ·
              refine ⟨21444099488432247328650163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28592132651242996438200217 21444099488432247328650163)
              ·
                refine ⟨32166149232648370992975245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21444099488432247328650163 32166149232648370992975245)
                ·
                  refine ⟨12062305962243139122365717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32166149232648370992975245 12062305962243139122365717)
                  ·
                    refine ⟨565420591980147146360893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12062305962243139122365717 565420591980147146360893)
                    ·
                      rfl

theorem cell23_3303458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 3, 6].length) (baseStart_3303458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3303458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3303458 prefixEnd_3303458 := by exact prefixLift 3303458
  have htrace : WordTrace (prefixWord ++ tailWord_3303458) baseStart_3303458 baseEnd_3303458 := by
    simpa [prefixWord, tailWord_3303458, baseEnd_3303458] using wordTrace_append hprefix tailTrace_3303458
  have hstable : (prefixWord ++ tailWord_3303458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3303458).length < 2 ^ (prefixWord ++ tailWord_3303458).sum := by decide
  have hdescent : baseEnd_3303458 < baseStart_3303458 := by decide
  rcases family_descends (prefixWord ++ tailWord_3303458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3303476 : List Nat := [2, 5, 1, 2, 2, 2, 1, 1, 3, 1, 3]
def baseStart_3303476 : Nat := 118140960795 + 3303476 * 2 ^ 59
def prefixEnd_3303476 : Nat := 4983230072969 + 3 ^ 40 * 3303476 * 2
def baseEnd_3303476 : Nat := 1696271018592222368657597

theorem tailTrace_3303476 : CollatzResearch.WordTrace tailWord_3303476 prefixEnd_3303476 1696271018592222368657597 := by
  unfold tailWord_3303476
  simp only [CollatzResearch.WordTrace]
  refine ⟨60243834090039057814273141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80325112120052077085697521 60243834090039057814273141)
  ·
    refine ⟨5647859445941161670088107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 60243834090039057814273141 5647859445941161670088107)
    ·
      refine ⟨8471789168911742505132161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5647859445941161670088107 8471789168911742505132161)
      ·
        refine ⟨6353841876683806878849121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8471789168911742505132161 6353841876683806878849121)
        ·
          refine ⟨4765381407512855159136841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6353841876683806878849121 4765381407512855159136841)
          ·
            refine ⟨3574036055634641369352631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4765381407512855159136841 3574036055634641369352631)
            ·
              refine ⟨5361054083451962054028947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3574036055634641369352631 5361054083451962054028947)
              ·
                refine ⟨8041581125177943081043421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5361054083451962054028947 8041581125177943081043421)
                ·
                  refine ⟨3015592921941728655391283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8041581125177943081043421 3015592921941728655391283)
                  ·
                    refine ⟨4523389382912592983086925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3015592921941728655391283 4523389382912592983086925)
                    ·
                      refine ⟨1696271018592222368657597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4523389382912592983086925 1696271018592222368657597)
                      ·
                        rfl

theorem cell23_3303476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_3303476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3303476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3303476 prefixEnd_3303476 := by exact prefixLift 3303476
  have htrace : WordTrace (prefixWord ++ tailWord_3303476) baseStart_3303476 baseEnd_3303476 := by
    simpa [prefixWord, tailWord_3303476, baseEnd_3303476] using wordTrace_append hprefix tailTrace_3303476
  have hstable : (prefixWord ++ tailWord_3303476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3303476).length < 2 ^ (prefixWord ++ tailWord_3303476).sum := by decide
  have hdescent : baseEnd_3303476 < baseStart_3303476 := by decide
  rcases family_descends (prefixWord ++ tailWord_3303476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3303485 : List Nat := [1, 4, 1, 3, 1, 1, 2, 2, 3, 2, 3]
def baseStart_3303485 : Nat := 118140960795 + 3303485 * 2 ^ 59
def prefixEnd_3303485 : Nat := 4983230072969 + 3 ^ 40 * 3303485 * 2
def baseEnd_3303485 : Nat := 1696275639918112833445055

theorem tailTrace_3303485 : CollatzResearch.WordTrace tailWord_3303485 prefixEnd_3303485 1696275639918112833445055 := by
  unfold tailWord_3303485
  simp only [CollatzResearch.WordTrace]
  refine ⟨120487996437045510165623909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80325330958030340110415939 120487996437045510165623909)
  ·
    refine ⟨22591499331946033156054483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120487996437045510165623909 22591499331946033156054483)
    ·
      refine ⟨33887248997919049734081725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22591499331946033156054483 33887248997919049734081725)
      ·
        refine ⟨12707718374219643650280647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33887248997919049734081725 12707718374219643650280647)
        ·
          refine ⟨19061577561329465475420971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12707718374219643650280647 19061577561329465475420971)
          ·
            refine ⟨28592366341994198213131457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19061577561329465475420971 28592366341994198213131457)
            ·
              refine ⟨21444274756495648659848593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28592366341994198213131457 21444274756495648659848593)
              ·
                refine ⟨16083206067371736494886445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21444274756495648659848593 16083206067371736494886445)
                ·
                  refine ⟨6031202275264401185582417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16083206067371736494886445 6031202275264401185582417)
                  ·
                    refine ⟨4523401706448300889186813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6031202275264401185582417 4523401706448300889186813)
                    ·
                      refine ⟨1696275639918112833445055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4523401706448300889186813 1696275639918112833445055)
                      ·
                        rfl

theorem cell23_3303485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 2, 3, 2, 3].length) (baseStart_3303485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3303485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3303485 prefixEnd_3303485 := by exact prefixLift 3303485
  have htrace : WordTrace (prefixWord ++ tailWord_3303485) baseStart_3303485 baseEnd_3303485 := by
    simpa [prefixWord, tailWord_3303485, baseEnd_3303485] using wordTrace_append hprefix tailTrace_3303485
  have hstable : (prefixWord ++ tailWord_3303485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3303485).length < 2 ^ (prefixWord ++ tailWord_3303485).sum := by decide
  have hdescent : baseEnd_3303485 < baseStart_3303485 := by decide
  rcases family_descends (prefixWord ++ tailWord_3303485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3303488 : List Nat := [2, 1, 1, 2, 2, 5, 2, 8]
def baseStart_3303488 : Nat := 118140960795 + 3303488 * 2 ^ 59
def prefixEnd_3303488 : Nat := 4983230072969 + 3 ^ 40 * 3303488 * 2
def baseEnd_3303488 : Nat := 62825080754076900803983

theorem tailTrace_3303488 : CollatzResearch.WordTrace tailWord_3303488 prefixEnd_3303488 62825080754076900803983 := by
  unfold tailWord_3303488
  simp only [CollatzResearch.WordTrace]
  refine ⟨60244052928017320838991559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80325403904023094451988745 60244052928017320838991559)
  ·
    refine ⟨90366079392025981258487339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60244052928017320838991559 90366079392025981258487339)
    ·
      refine ⟨135549119088038971887731009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90366079392025981258487339 135549119088038971887731009)
      ·
        refine ⟨101661839316029228915798257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135549119088038971887731009 101661839316029228915798257)
        ·
          refine ⟨76246379487021921686848693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101661839316029228915798257 76246379487021921686848693)
          ·
            refine ⟨7148098076908305158142065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 76246379487021921686848693 7148098076908305158142065)
            ·
              refine ⟨5361073557681228868606549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7148098076908305158142065 5361073557681228868606549)
              ·
                refine ⟨62825080754076900803983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5361073557681228868606549 62825080754076900803983)
                ·
                  rfl

theorem cell23_3303488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2, 8].length) (baseStart_3303488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3303488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3303488 prefixEnd_3303488 := by exact prefixLift 3303488
  have htrace : WordTrace (prefixWord ++ tailWord_3303488) baseStart_3303488 baseEnd_3303488 := by
    simpa [prefixWord, tailWord_3303488, baseEnd_3303488] using wordTrace_append hprefix tailTrace_3303488
  have hstable : (prefixWord ++ tailWord_3303488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3303488).length < 2 ^ (prefixWord ++ tailWord_3303488).sum := by decide
  have hdescent : baseEnd_3303488 < baseStart_3303488 := by decide
  rcases family_descends (prefixWord ++ tailWord_3303488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3303502 : List Nat := [4, 1, 1, 1, 1, 4, 3, 2, 1, 2, 3]
def baseStart_3303502 : Nat := 118140960795 + 3303502 * 2 ^ 59
def prefixEnd_3303502 : Nat := 4983230072969 + 3 ^ 40 * 3303502 * 2
def baseEnd_3303502 : Nat := 1696284369089239266932477

theorem tailTrace_3303502 : CollatzResearch.WordTrace tailWord_3303502 prefixEnd_3303502 1696284369089239266932477 := by
  unfold tailWord_3303502
  simp only [CollatzResearch.WordTrace]
  refine ⟨15061077059747990258624095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80325744318655948045995173 15061077059747990258624095)
  ·
    refine ⟨22591615589621985387936143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15061077059747990258624095 22591615589621985387936143)
    ·
      refine ⟨33887423384432978081904215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22591615589621985387936143 33887423384432978081904215)
      ·
        refine ⟨50831135076649467122856323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33887423384432978081904215 50831135076649467122856323)
        ·
          refine ⟨76246702614974200684284485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50831135076649467122856323 76246702614974200684284485)
          ·
            refine ⟨14296256740307662628303341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76246702614974200684284485 14296256740307662628303341)
            ·
              refine ⟨5361096277615373485613753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14296256740307662628303341 5361096277615373485613753)
              ·
                refine ⟨4020822208211530114210315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5361096277615373485613753 4020822208211530114210315)
                ·
                  refine ⟨6031233312317295171315473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4020822208211530114210315 6031233312317295171315473)
                  ·
                    refine ⟨4523424984237971378486605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6031233312317295171315473 4523424984237971378486605)
                    ·
                      refine ⟨1696284369089239266932477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4523424984237971378486605 1696284369089239266932477)
                      ·
                        rfl

theorem cell23_3303502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3, 2, 1, 2, 3].length) (baseStart_3303502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3303502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3303502 prefixEnd_3303502 := by exact prefixLift 3303502
  have htrace : WordTrace (prefixWord ++ tailWord_3303502) baseStart_3303502 baseEnd_3303502 := by
    simpa [prefixWord, tailWord_3303502, baseEnd_3303502] using wordTrace_append hprefix tailTrace_3303502
  have hstable : (prefixWord ++ tailWord_3303502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3303502).length < 2 ^ (prefixWord ++ tailWord_3303502).sum := by decide
  have hdescent : baseEnd_3303502 < baseStart_3303502 := by decide
  rcases family_descends (prefixWord ++ tailWord_3303502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3303532 : List Nat := [2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 3]
def baseStart_3303532 : Nat := 118140960795 + 3303532 * 2 ^ 59
def prefixEnd_3303532 : Nat := 4983230072969 + 3 ^ 40 * 3303532 * 2
def baseEnd_3303532 : Nat := 1696299773508874149557339

theorem tailTrace_3303532 : CollatzResearch.WordTrace tailWord_3303532 prefixEnd_3303532 1696299773508874149557339 := by
  unfold tailWord_3303532
  simp only [CollatzResearch.WordTrace]
  refine ⟨60244855333937618596292425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80326473778583491461723233 60244855333937618596292425)
  ·
    refine ⟨45183641500453213947219319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60244855333937618596292425 45183641500453213947219319)
    ·
      refine ⟨67775462250679820920828979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45183641500453213947219319 67775462250679820920828979)
      ·
        refine ⟨101663193376019731381243469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67775462250679820920828979 101663193376019731381243469)
        ·
          refine ⟨38123697516007399267966301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101663193376019731381243469 38123697516007399267966301)
          ·
            refine ⟨14296386568502774725487363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38123697516007399267966301 14296386568502774725487363)
            ·
              refine ⟨21444579852754162088231045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14296386568502774725487363 21444579852754162088231045)
              ·
                refine ⟨4020858722391405391543321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21444579852754162088231045 4020858722391405391543321)
                ·
                  refine ⟨3015644041793554043657491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4020858722391405391543321 3015644041793554043657491)
                  ·
                    refine ⟨4523466062690331065486237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3015644041793554043657491 4523466062690331065486237)
                    ·
                      refine ⟨1696299773508874149557339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4523466062690331065486237 1696299773508874149557339)
                      ·
                        rfl

theorem cell23_3303532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 3].length) (baseStart_3303532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3303532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3303532 prefixEnd_3303532 := by exact prefixLift 3303532
  have htrace : WordTrace (prefixWord ++ tailWord_3303532) baseStart_3303532 baseEnd_3303532 := by
    simpa [prefixWord, tailWord_3303532, baseEnd_3303532] using wordTrace_append hprefix tailTrace_3303532
  have hstable : (prefixWord ++ tailWord_3303532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3303532).length < 2 ^ (prefixWord ++ tailWord_3303532).sum := by decide
  have hdescent : baseEnd_3303532 < baseStart_3303532 := by decide
  rcases family_descends (prefixWord ++ tailWord_3303532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3303548 : List Nat := [2, 2, 2, 1, 1, 4, 1, 1, 1, 8]
def baseStart_3303548 : Nat := 118140960795 + 3303548 * 2 ^ 59
def prefixEnd_3303548 : Nat := 4983230072969 + 3 ^ 40 * 3303548 * 2
def baseEnd_3303548 : Nat := 565435996399782028985755

theorem tailTrace_3303548 : CollatzResearch.WordTrace tailWord_3303548 prefixEnd_3303548 565435996399782028985755 := by
  unfold tailWord_3303548
  simp only [CollatzResearch.WordTrace]
  refine ⟨60245147117908635962583649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80326862823878181283444865 60245147117908635962583649)
  ·
    refine ⟨45183860338431476971937737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60245147117908635962583649 45183860338431476971937737)
    ·
      refine ⟨33887895253823607728953303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45183860338431476971937737 33887895253823607728953303)
      ·
        refine ⟨50831842880735411593429955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33887895253823607728953303 50831842880735411593429955)
        ·
          refine ⟨76247764321103117390144933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50831842880735411593429955 76247764321103117390144933)
          ·
            refine ⟨14296455810206834510652175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76247764321103117390144933 14296455810206834510652175)
            ·
              refine ⟨21444683715310251765978263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14296455810206834510652175 21444683715310251765978263)
              ·
                refine ⟨32167025572965377648967395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21444683715310251765978263 32167025572965377648967395)
                ·
                  refine ⟨48250538359448066473451093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32167025572965377648967395 48250538359448066473451093)
                  ·
                    refine ⟨565435996399782028985755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 48250538359448066473451093 565435996399782028985755)
                    ·
                      rfl

theorem cell23_3303548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 1, 1, 8].length) (baseStart_3303548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3303548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3303548 prefixEnd_3303548 := by exact prefixLift 3303548
  have htrace : WordTrace (prefixWord ++ tailWord_3303548) baseStart_3303548 baseEnd_3303548 := by
    simpa [prefixWord, tailWord_3303548, baseEnd_3303548] using wordTrace_append hprefix tailTrace_3303548
  have hstable : (prefixWord ++ tailWord_3303548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3303548).length < 2 ^ (prefixWord ++ tailWord_3303548).sum := by decide
  have hdescent : baseEnd_3303548 < baseStart_3303548 := by decide
  rcases family_descends (prefixWord ++ tailWord_3303548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3303568 : List Nat := [2, 1, 1, 1, 1, 1, 5, 2, 1, 4, 4]
def baseStart_3303568 : Nat := 118140960795 + 3303568 * 2 ^ 59
def prefixEnd_3303568 : Nat := 4983230072969 + 3 ^ 40 * 3303568 * 2
def baseEnd_3303568 : Nat := 1696318258812436008707173

theorem tailTrace_3303568 : CollatzResearch.WordTrace tailWord_3303568 prefixEnd_3303568 1696318258812436008707173 := by
  unfold tailWord_3303568
  simp only [CollatzResearch.WordTrace]
  refine ⟨60245511847872407670447679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80327349130496543560596905 60245511847872407670447679)
  ·
    refine ⟨90368267771808611505671519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60245511847872407670447679 90368267771808611505671519)
    ·
      refine ⟨135552401657712917258507279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90368267771808611505671519 135552401657712917258507279)
      ·
        refine ⟨203328602486569375887760919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135552401657712917258507279 203328602486569375887760919)
        ·
          refine ⟨304992903729854063831641379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203328602486569375887760919 304992903729854063831641379)
          ·
            refine ⟨457489355594781095747462069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 304992903729854063831641379 457489355594781095747462069)
            ·
              refine ⟨42889627087010727726324569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 457489355594781095747462069 42889627087010727726324569)
              ·
                refine ⟨32167220315258045794743427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42889627087010727726324569 32167220315258045794743427)
                ·
                  refine ⟨48250830472887068692115141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32167220315258045794743427 48250830472887068692115141)
                  ·
                    refine ⟨9047030713666325379771589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48250830472887068692115141 9047030713666325379771589)
                    ·
                      refine ⟨1696318258812436008707173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9047030713666325379771589 1696318258812436008707173)
                      ·
                        rfl

theorem cell23_3303568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4, 4].length) (baseStart_3303568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3303568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3303568 prefixEnd_3303568 := by exact prefixLift 3303568
  have htrace : WordTrace (prefixWord ++ tailWord_3303568) baseStart_3303568 baseEnd_3303568 := by
    simpa [prefixWord, tailWord_3303568, baseEnd_3303568] using wordTrace_append hprefix tailTrace_3303568
  have hstable : (prefixWord ++ tailWord_3303568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3303568).length < 2 ^ (prefixWord ++ tailWord_3303568).sum := by decide
  have hdescent : baseEnd_3303568 < baseStart_3303568 := by decide
  rcases family_descends (prefixWord ++ tailWord_3303568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3303585 : List Nat := [1, 2, 3, 3, 1, 2, 1, 2, 2, 2, 4]
def baseStart_3303585 : Nat := 118140960795 + 3303585 * 2 ^ 59
def prefixEnd_3303585 : Nat := 4983230072969 + 3 ^ 40 * 3303585 * 2
def baseEnd_3303585 : Nat := 1696326987983562442194595

theorem tailTrace_3303585 : CollatzResearch.WordTrace tailWord_3303585 prefixEnd_3303585 1696326987983562442194595 := by
  unfold tailWord_3303585
  simp only [CollatzResearch.WordTrace]
  refine ⟨120491643736683227244264209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80327762491122151496176139 120491643736683227244264209)
  ·
    refine ⟨90368732802512420433198157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120491643736683227244264209 90368732802512420433198157)
    ·
      refine ⟨33888274800942157662449309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90368732802512420433198157 33888274800942157662449309)
      ·
        refine ⟨12708103050353309123418491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33888274800942157662449309 12708103050353309123418491)
        ·
          refine ⟨19062154575529963685127737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12708103050353309123418491 19062154575529963685127737)
          ·
            refine ⟨14296615931647472763845803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19062154575529963685127737 14296615931647472763845803)
            ·
              refine ⟨21444923897471209145768705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14296615931647472763845803 21444923897471209145768705)
              ·
                refine ⟨16083692923103406859326529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21444923897471209145768705 16083692923103406859326529)
                ·
                  refine ⟨12062769692327555144494897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16083692923103406859326529 12062769692327555144494897)
                  ·
                    refine ⟨9047077269245666358371173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12062769692327555144494897 9047077269245666358371173)
                    ·
                      refine ⟨1696326987983562442194595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9047077269245666358371173 1696326987983562442194595)
                      ·
                        rfl

theorem cell23_3303585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_3303585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3303585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3303585 prefixEnd_3303585 := by exact prefixLift 3303585
  have htrace : WordTrace (prefixWord ++ tailWord_3303585) baseStart_3303585 baseEnd_3303585 := by
    simpa [prefixWord, tailWord_3303585, baseEnd_3303585] using wordTrace_append hprefix tailTrace_3303585
  have hstable : (prefixWord ++ tailWord_3303585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3303585).length < 2 ^ (prefixWord ++ tailWord_3303585).sum := by decide
  have hdescent : baseEnd_3303585 < baseStart_3303585 := by decide
  rcases family_descends (prefixWord ++ tailWord_3303585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3303608 : List Nat := [2, 1, 2, 1, 2, 1, 3, 1, 3, 7]
def baseStart_3303608 : Nat := 118140960795 + 3303608 * 2 ^ 59
def prefixEnd_3303608 : Nat := 4983230072969 + 3 ^ 40 * 3303608 * 2
def baseEnd_3303608 : Nat := 565446266012871950735663

theorem tailTrace_3303608 : CollatzResearch.WordTrace tailWord_3303608 prefixEnd_3303608 565446266012871950735663 := by
  unfold tailWord_3303608
  simp only [CollatzResearch.WordTrace]
  refine ⟨60246241307799951086175739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80328321743733268114900985 60246241307799951086175739)
  ·
    refine ⟨90369361961699926629263609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60246241307799951086175739 90369361961699926629263609)
    ·
      refine ⟨67777021471274944971947707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90369361961699926629263609 67777021471274944971947707)
      ·
        refine ⟨101665532206912417457921561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67777021471274944971947707 101665532206912417457921561)
        ·
          refine ⟨76249149155184313093441171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101665532206912417457921561 76249149155184313093441171)
          ·
            refine ⟨114373723732776469640161757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76249149155184313093441171 114373723732776469640161757)
            ·
              refine ⟨42890146399791176115060659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 114373723732776469640161757 42890146399791176115060659)
              ·
                refine ⟨64335219599686764172590989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42890146399791176115060659 64335219599686764172590989)
                ·
                  refine ⟨24125707349882536564721621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64335219599686764172590989 24125707349882536564721621)
                  ·
                    refine ⟨565446266012871950735663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24125707349882536564721621 565446266012871950735663)
                    ·
                      rfl

theorem cell23_3303608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 3, 7].length) (baseStart_3303608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3303608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3303608 prefixEnd_3303608 := by exact prefixLift 3303608
  have htrace : WordTrace (prefixWord ++ tailWord_3303608) baseStart_3303608 baseEnd_3303608 := by
    simpa [prefixWord, tailWord_3303608, baseEnd_3303608] using wordTrace_append hprefix tailTrace_3303608
  have hstable : (prefixWord ++ tailWord_3303608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3303608).length < 2 ^ (prefixWord ++ tailWord_3303608).sum := by decide
  have hdescent : baseEnd_3303608 < baseStart_3303608 := by decide
  rcases family_descends (prefixWord ++ tailWord_3303608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3303662 : List Nat := [4, 1, 2, 1, 1, 1, 1, 3, 1, 6, 2]
def baseStart_3303662 : Nat := 118140960795 + 3303662 * 2 ^ 59
def prefixEnd_3303662 : Nat := 4983230072969 + 3 ^ 40 * 3303662 * 2
def baseEnd_3303662 : Nat := 1696366525993958640931741

theorem tailTrace_3303662 : CollatzResearch.WordTrace tailWord_3303662 prefixEnd_3303662 1696366525993958640931741 := by
  unfold tailWord_3303662
  simp only [CollatzResearch.WordTrace]
  refine ⟨15061806519675533674352155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80329634771602846263211493 15061806519675533674352155)
  ·
    refine ⟨22592709779513300511528233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15061806519675533674352155 22592709779513300511528233)
    ·
      refine ⟨16944532334634975383646175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22592709779513300511528233 16944532334634975383646175)
      ·
        refine ⟨25416798501952463075469263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16944532334634975383646175 25416798501952463075469263)
        ·
          refine ⟨38125197752928694613203895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25416798501952463075469263 38125197752928694613203895)
          ·
            refine ⟨57187796629393041919805843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38125197752928694613203895 57187796629393041919805843)
            ·
              refine ⟨85781694944089562879708765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57187796629393041919805843 85781694944089562879708765)
              ·
                refine ⟨32168135604033586079890787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85781694944089562879708765 32168135604033586079890787)
                ·
                  refine ⟨48252203406050379119836181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32168135604033586079890787 48252203406050379119836181)
                  ·
                    refine ⟨2261822034658611521242321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 48252203406050379119836181 2261822034658611521242321)
                    ·
                      refine ⟨1696366525993958640931741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2261822034658611521242321 1696366525993958640931741)
                      ·
                        rfl

theorem cell23_3303662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 3, 1, 6, 2].length) (baseStart_3303662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3303662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3303662 prefixEnd_3303662 := by exact prefixLift 3303662
  have htrace : WordTrace (prefixWord ++ tailWord_3303662) baseStart_3303662 baseEnd_3303662 := by
    simpa [prefixWord, tailWord_3303662, baseEnd_3303662] using wordTrace_append hprefix tailTrace_3303662
  have hstable : (prefixWord ++ tailWord_3303662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3303662).length < 2 ^ (prefixWord ++ tailWord_3303662).sum := by decide
  have hdescent : baseEnd_3303662 < baseStart_3303662 := by decide
  rcases family_descends (prefixWord ++ tailWord_3303662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3303665 : List Nat := [1, 2, 2, 2, 2, 1, 2, 1, 3, 4, 3]
def baseStart_3303665 : Nat := 118140960795 + 3303665 * 2 ^ 59
def prefixEnd_3303665 : Nat := 4983230072969 + 3 ^ 40 * 3303665 * 2
def baseEnd_3303665 : Nat := 1696368066435922129194227

theorem tailTrace_3303665 : CollatzResearch.WordTrace tailWord_3303665 prefixEnd_3303665 1696368066435922129194227 := by
  unfold tailWord_3303665
  simp only [CollatzResearch.WordTrace]
  refine ⟨120494561576393400907176449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80329707717595600604784299 120494561576393400907176449)
  ·
    refine ⟨90370921182295050680382337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120494561576393400907176449 90370921182295050680382337)
    ·
      refine ⟨67778190886721288010286753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90370921182295050680382337 67778190886721288010286753)
      ·
        refine ⟨50833643165040966007715065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67778190886721288010286753 50833643165040966007715065)
        ·
          refine ⟨38125232373780724505786299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50833643165040966007715065 38125232373780724505786299)
          ·
            refine ⟨57187848560671086758679449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38125232373780724505786299 57187848560671086758679449)
            ·
              refine ⟨42890886420503315069009587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57187848560671086758679449 42890886420503315069009587)
              ·
                refine ⟨64336329630754972603514381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42890886420503315069009587 64336329630754972603514381)
                ·
                  refine ⟨24126123611533114726317893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64336329630754972603514381 24126123611533114726317893)
                  ·
                    refine ⟨4523648177162459011184605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24126123611533114726317893 4523648177162459011184605)
                    ·
                      refine ⟨1696368066435922129194227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4523648177162459011184605 1696368066435922129194227)
                      ·
                        rfl

theorem cell23_3303665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 3, 4, 3].length) (baseStart_3303665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3303665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3303665 prefixEnd_3303665 := by exact prefixLift 3303665
  have htrace : WordTrace (prefixWord ++ tailWord_3303665) baseStart_3303665 baseEnd_3303665 := by
    simpa [prefixWord, tailWord_3303665, baseEnd_3303665] using wordTrace_append hprefix tailTrace_3303665
  have hstable : (prefixWord ++ tailWord_3303665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3303665).length < 2 ^ (prefixWord ++ tailWord_3303665).sum := by decide
  have hdescent : baseEnd_3303665 < baseStart_3303665 := by decide
  rcases family_descends (prefixWord ++ tailWord_3303665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3303706 : List Nat := [3, 1, 1, 3, 4, 1, 1, 4, 1, 4]
def baseStart_3303706 : Nat := 118140960795 + 3303706 * 2 ^ 59
def prefixEnd_3303706 : Nat := 4983230072969 + 3 ^ 40 * 3303706 * 2
def baseEnd_3303706 : Nat := 565463039714252156260513

theorem tailTrace_3303706 : CollatzResearch.WordTrace tailWord_3303706 prefixEnd_3303706 565463039714252156260513 := by
  unfold tailWord_3303706
  simp only [CollatzResearch.WordTrace]
  refine ⟨30124014242311216227354743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80330704646163243272945981 30124014242311216227354743)
  ·
    refine ⟨45186021363466824341032115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30124014242311216227354743 45186021363466824341032115)
    ·
      refine ⟨67779032045200236511548173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45186021363466824341032115 67779032045200236511548173)
      ·
        refine ⟨25417137016950088691830565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67779032045200236511548173 25417137016950088691830565)
        ·
          refine ⟨4765713190678141629718231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25417137016950088691830565 4765713190678141629718231)
          ·
            refine ⟨7148569786017212444577347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4765713190678141629718231 7148569786017212444577347)
            ·
              refine ⟨10722854679025818666866021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7148569786017212444577347 10722854679025818666866021)
              ·
                refine ⟨2010535252317341000037379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10722854679025818666866021 2010535252317341000037379)
                ·
                  refine ⟨3015802878476011500056069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2010535252317341000037379 3015802878476011500056069)
                  ·
                    refine ⟨565463039714252156260513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3015802878476011500056069 565463039714252156260513)
                    ·
                      rfl

theorem cell23_3303706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 4, 1, 4].length) (baseStart_3303706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3303706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3303706 prefixEnd_3303706 := by exact prefixLift 3303706
  have htrace : WordTrace (prefixWord ++ tailWord_3303706) baseStart_3303706 baseEnd_3303706 := by
    simpa [prefixWord, tailWord_3303706, baseEnd_3303706] using wordTrace_append hprefix tailTrace_3303706
  have hstable : (prefixWord ++ tailWord_3303706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3303706).length < 2 ^ (prefixWord ++ tailWord_3303706).sum := by decide
  have hdescent : baseEnd_3303706 < baseStart_3303706 := by decide
  rcases family_descends (prefixWord ++ tailWord_3303706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3303715 : List Nat := [1, 1, 1, 4, 2, 2, 1, 1, 5, 5]
def baseStart_3303715 : Nat := 118140960795 + 3303715 * 2 ^ 59
def prefixEnd_3303715 : Nat := 4983230072969 + 3 ^ 40 * 3303715 * 2
def baseEnd_3303715 : Nat := 565464580156215644522999

theorem tailTrace_3303715 : CollatzResearch.WordTrace tailWord_3303715 prefixEnd_3303715 565464580156215644522999 := by
  unfold tailWord_3303715
  simp only [CollatzResearch.WordTrace]
  refine ⟨120496385226212259446496599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80330923484141506297664399 120496385226212259446496599)
  ·
    refine ⟨180744577839318389169744899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120496385226212259446496599 180744577839318389169744899)
    ·
      refine ⟨271116866758977583754617349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180744577839318389169744899 271116866758977583754617349)
      ·
        refine ⟨50834412517308296953990753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 271116866758977583754617349 50834412517308296953990753)
        ·
          refine ⟨38125809387981222715493065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50834412517308296953990753 38125809387981222715493065)
          ·
            refine ⟨28594357040985917036619799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38125809387981222715493065 28594357040985917036619799)
            ·
              refine ⟨42891535561478875554929699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28594357040985917036619799 42891535561478875554929699)
              ·
                refine ⟨64337303342218313332394549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42891535561478875554929699 64337303342218313332394549)
                ·
                  refine ⟨6031622188332966874911989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 64337303342218313332394549 6031622188332966874911989)
                  ·
                    refine ⟨565464580156215644522999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6031622188332966874911989 565464580156215644522999)
                    ·
                      rfl

theorem cell23_3303715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 5, 5].length) (baseStart_3303715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3303715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3303715 prefixEnd_3303715 := by exact prefixLift 3303715
  have htrace : WordTrace (prefixWord ++ tailWord_3303715) baseStart_3303715 baseEnd_3303715 := by
    simpa [prefixWord, tailWord_3303715, baseEnd_3303715] using wordTrace_append hprefix tailTrace_3303715
  have hstable : (prefixWord ++ tailWord_3303715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3303715).length < 2 ^ (prefixWord ++ tailWord_3303715).sum := by decide
  have hdescent : baseEnd_3303715 < baseStart_3303715 := by decide
  rcases family_descends (prefixWord ++ tailWord_3303715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3303786 : List Nat := [3, 1, 3, 3, 1, 2, 2, 2, 1, 1, 4]
def baseStart_3303786 : Nat := 118140960795 + 3303786 * 2 ^ 59
def prefixEnd_3303786 : Nat := 4983230072969 + 3 ^ 40 * 3303786 * 2
def baseEnd_3303786 : Nat := 1696430197595116155781171

theorem tailTrace_3303786 : CollatzResearch.WordTrace tailWord_3303786 prefixEnd_3303786 1696430197595116155781171 := by
  unfold tailWord_3303786
  simp only [CollatzResearch.WordTrace]
  refine ⟨30124743702238759643082803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80332649872636692381554141 30124743702238759643082803)
  ·
    refine ⟨45187115553358139464624205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30124743702238759643082803 45187115553358139464624205)
    ·
      refine ⟨16945168332509302299234077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45187115553358139464624205 16945168332509302299234077)
      ·
        refine ⟨6354438124690988362212779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16945168332509302299234077 6354438124690988362212779)
        ·
          refine ⟨9531657187036482543319169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6354438124690988362212779 9531657187036482543319169)
          ·
            refine ⟨7148742890277361907489377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9531657187036482543319169 7148742890277361907489377)
            ·
              refine ⟨5361557167708021430617033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7148742890277361907489377 5361557167708021430617033)
              ·
                refine ⟨4021167875781016072962775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5361557167708021430617033 4021167875781016072962775)
                ·
                  refine ⟨6031751813671524109444163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4021167875781016072962775 6031751813671524109444163)
                  ·
                    refine ⟨9047627720507286164166245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6031751813671524109444163 9047627720507286164166245)
                    ·
                      refine ⟨1696430197595116155781171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9047627720507286164166245 1696430197595116155781171)
                      ·
                        rfl

theorem cell23_3303786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_3303786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3303786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3303786 prefixEnd_3303786 := by exact prefixLift 3303786
  have htrace : WordTrace (prefixWord ++ tailWord_3303786) baseStart_3303786 baseEnd_3303786 := by
    simpa [prefixWord, tailWord_3303786, baseEnd_3303786] using wordTrace_append hprefix tailTrace_3303786
  have hstable : (prefixWord ++ tailWord_3303786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3303786).length < 2 ^ (prefixWord ++ tailWord_3303786).sum := by decide
  have hdescent : baseEnd_3303786 < baseStart_3303786 := by decide
  rcases family_descends (prefixWord ++ tailWord_3303786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3303792 : List Nat := [2, 1, 1, 1, 4, 3, 4, 7]
def baseStart_3303792 : Nat := 118140960795 + 3303792 * 2 ^ 59
def prefixEnd_3303792 : Nat := 4983230072969 + 3 ^ 40 * 3303792 * 2
def baseEnd_3303792 : Nat := 62830862165890486381709

theorem tailTrace_3303792 : CollatzResearch.WordTrace tailWord_3303792 prefixEnd_3303792 62830862165890486381709 := by
  unfold tailWord_3303792
  simp only [CollatzResearch.WordTrace]
  refine ⟨60249596823466650798524815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80332795764622201064699753 60249596823466650798524815)
  ·
    refine ⟨90374395235199976197787223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60249596823466650798524815 90374395235199976197787223)
    ·
      refine ⟨135561592852799964296680835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90374395235199976197787223 135561592852799964296680835)
      ·
        refine ⟨203342389279199946445021253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135561592852799964296680835 203342389279199946445021253)
        ·
          refine ⟨38126697989849989958441485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 203342389279199946445021253 38126697989849989958441485)
          ·
            refine ⟨14297511746193746234415557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38126697989849989958441485 14297511746193746234415557)
            ·
              refine ⟨2680783452411327418952917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14297511746193746234415557 2680783452411327418952917)
              ·
                refine ⟨62830862165890486381709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2680783452411327418952917 62830862165890486381709)
                ·
                  rfl

theorem cell23_3303792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 4, 7].length) (baseStart_3303792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3303792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3303792 prefixEnd_3303792 := by exact prefixLift 3303792
  have htrace : WordTrace (prefixWord ++ tailWord_3303792) baseStart_3303792 baseEnd_3303792 := by
    simpa [prefixWord, tailWord_3303792, baseEnd_3303792] using wordTrace_append hprefix tailTrace_3303792
  have hstable : (prefixWord ++ tailWord_3303792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3303792).length < 2 ^ (prefixWord ++ tailWord_3303792).sum := by decide
  have hdescent : baseEnd_3303792 < baseStart_3303792 := by decide
  rcases family_descends (prefixWord ++ tailWord_3303792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3303803 : List Nat := [1, 1, 1, 1, 1, 7, 3, 3, 1, 2, 2]
def baseStart_3303803 : Nat := 118140960795 + 3303803 * 2 ^ 59
def prefixEnd_3303803 : Nat := 4983230072969 + 3 ^ 40 * 3303803 * 2
def baseEnd_3303803 : Nat := 1696438926766242589268593

theorem tailTrace_3303803 : CollatzResearch.WordTrace tailWord_3303803 prefixEnd_3303803 1696438926766242589268593 := by
  unfold tailWord_3303803
  simp only [CollatzResearch.WordTrace]
  refine ⟨120499594849893450475700063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80333063233262300317133375 120499594849893450475700063)
  ·
    refine ⟨180749392274840175713550095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120499594849893450475700063 180749392274840175713550095)
    ·
      refine ⟨271124088412260263570325143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180749392274840175713550095 271124088412260263570325143)
      ·
        refine ⟨406686132618390395355487715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271124088412260263570325143 406686132618390395355487715)
        ·
          refine ⟨610029198927585593033231573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 406686132618390395355487715 610029198927585593033231573)
          ·
            refine ⟨14297559349865287336716365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 610029198927585593033231573 14297559349865287336716365)
            ·
              refine ⟨5361584756199482751268637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14297559349865287336716365 5361584756199482751268637)
              ·
                refine ⟨2010594283574806031725739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5361584756199482751268637 2010594283574806031725739)
                ·
                  refine ⟨3015891425362209047588609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2010594283574806031725739 3015891425362209047588609)
                  ·
                    refine ⟨2261918569021656785691457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3015891425362209047588609 2261918569021656785691457)
                    ·
                      refine ⟨1696438926766242589268593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2261918569021656785691457 1696438926766242589268593)
                      ·
                        rfl

theorem cell23_3303803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3, 3, 1, 2, 2].length) (baseStart_3303803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3303803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3303803 prefixEnd_3303803 := by exact prefixLift 3303803
  have htrace : WordTrace (prefixWord ++ tailWord_3303803) baseStart_3303803 baseEnd_3303803 := by
    simpa [prefixWord, tailWord_3303803, baseEnd_3303803] using wordTrace_append hprefix tailTrace_3303803
  have hstable : (prefixWord ++ tailWord_3303803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3303803).length < 2 ^ (prefixWord ++ tailWord_3303803).sum := by decide
  have hdescent : baseEnd_3303803 < baseStart_3303803 := by decide
  rcases family_descends (prefixWord ++ tailWord_3303803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3303819 : List Nat := [1, 1, 1, 1, 4, 4, 2, 1, 4, 1, 3]
def baseStart_3303819 : Nat := 118140960795 + 3303819 * 2 ^ 59
def prefixEnd_3303819 : Nat := 4983230072969 + 3 ^ 40 * 3303819 * 2
def baseEnd_3303819 : Nat := 1696447142456714526668519

theorem tailTrace_3303819 : CollatzResearch.WordTrace tailWord_3303819 prefixEnd_3303819 1696447142456714526668519 := by
  unfold tailWord_3303819
  simp only [CollatzResearch.WordTrace]
  refine ⟨120500178417835485208282511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80333452278556990138855007 120500178417835485208282511)
  ·
    refine ⟨180750267626753227812423767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120500178417835485208282511 180750267626753227812423767)
    ·
      refine ⟨271125401440129841718635651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180750267626753227812423767 271125401440129841718635651)
      ·
        refine ⟨406688102160194762577953477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271125401440129841718635651 406688102160194762577953477)
        ·
          refine ⟨76254019155036517983366277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 406688102160194762577953477 76254019155036517983366277)
          ·
            refine ⟨14297628591569347121881177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76254019155036517983366277 14297628591569347121881177)
            ·
              refine ⟨10723221443677010341410883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14297628591569347121881177 10723221443677010341410883)
              ·
                refine ⟨16084832165515515512116325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10723221443677010341410883 16084832165515515512116325)
                ·
                  refine ⟨3015906031034159158521811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16084832165515515512116325 3015906031034159158521811)
                  ·
                    refine ⟨4523859046551238737782717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3015906031034159158521811 4523859046551238737782717)
                    ·
                      refine ⟨1696447142456714526668519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4523859046551238737782717 1696447142456714526668519)
                      ·
                        rfl

theorem cell23_3303819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 1, 4, 1, 3].length) (baseStart_3303819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3303819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3303819 prefixEnd_3303819 := by exact prefixLift 3303819
  have htrace : WordTrace (prefixWord ++ tailWord_3303819) baseStart_3303819 baseEnd_3303819 := by
    simpa [prefixWord, tailWord_3303819, baseEnd_3303819] using wordTrace_append hprefix tailTrace_3303819
  have hstable : (prefixWord ++ tailWord_3303819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3303819).length < 2 ^ (prefixWord ++ tailWord_3303819).sum := by decide
  have hdescent : baseEnd_3303819 < baseStart_3303819 := by decide
  rcases family_descends (prefixWord ++ tailWord_3303819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3303820 : List Nat := [2, 2, 1, 2, 1, 5, 3, 2, 1, 2, 2]
def baseStart_3303820 : Nat := 118140960795 + 3303820 * 2 ^ 59
def prefixEnd_3303820 : Nat := 4983230072969 + 3 ^ 40 * 3303820 * 2
def baseEnd_3303820 : Nat := 1696447655937369022756015

theorem tailTrace_3303820 : CollatzResearch.WordTrace tailWord_3303820 prefixEnd_3303820 1696447655937369022756015 := by
  unfold tailWord_3303820
  simp only [CollatzResearch.WordTrace]
  refine ⟨60250107445415931189534457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80333476593887908252712609 60250107445415931189534457)
  ·
    refine ⟨45187580584061948392150843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60250107445415931189534457 45187580584061948392150843)
    ·
      refine ⟨67781370876092922588226265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45187580584061948392150843 67781370876092922588226265)
      ·
        refine ⟨50836028157069691941169699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67781370876092922588226265 50836028157069691941169699)
        ·
          refine ⟨76254042235604537911754549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50836028157069691941169699 76254042235604537911754549)
          ·
            refine ⟨7148816459587925429226989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 76254042235604537911754549 7148816459587925429226989)
            ·
              refine ⟨2680806172345472035960121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7148816459587925429226989 2680806172345472035960121)
              ·
                refine ⟨2010604629259104026970091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2680806172345472035960121 2010604629259104026970091)
                ·
                  refine ⟨3015906943888656040455137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2010604629259104026970091 3015906943888656040455137)
                  ·
                    refine ⟨2261930207916492030341353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3015906943888656040455137 2261930207916492030341353)
                    ·
                      refine ⟨1696447655937369022756015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2261930207916492030341353 1696447655937369022756015)
                      ·
                        rfl

theorem cell23_3303820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 3, 2, 1, 2, 2].length) (baseStart_3303820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3303820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3303820 prefixEnd_3303820 := by exact prefixLift 3303820
  have htrace : WordTrace (prefixWord ++ tailWord_3303820) baseStart_3303820 baseEnd_3303820 := by
    simpa [prefixWord, tailWord_3303820, baseEnd_3303820] using wordTrace_append hprefix tailTrace_3303820
  have hstable : (prefixWord ++ tailWord_3303820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3303820).length < 2 ^ (prefixWord ++ tailWord_3303820).sum := by decide
  have hdescent : baseEnd_3303820 < baseStart_3303820 := by decide
  rcases family_descends (prefixWord ++ tailWord_3303820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3303829 : List Nat := [1, 3, 2, 1, 1, 2, 1, 4, 3, 3, 2]
def baseStart_3303829 : Nat := 118140960795 + 3303829 * 2 ^ 59
def prefixEnd_3303829 : Nat := 4983230072969 + 3 ^ 40 * 3303829 * 2
def baseEnd_3303829 : Nat := 1696452277263259487543473

theorem tailTrace_3303829 : CollatzResearch.WordTrace tailWord_3303829 prefixEnd_3303829 1696452277263259487543473 := by
  unfold tailWord_3303829
  simp only [CollatzResearch.WordTrace]
  refine ⟨120500543147799256916146541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80333695431866171277431027 120500543147799256916146541)
  ·
    refine ⟨45187703680424721343554953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120500543147799256916146541 45187703680424721343554953)
    ·
      refine ⟨33890777760318541007666215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45187703680424721343554953 33890777760318541007666215)
      ·
        refine ⟨50836166640477811511499323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33890777760318541007666215 50836166640477811511499323)
        ·
          refine ⟨76254249960716717267248985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50836166640477811511499323 76254249960716717267248985)
          ·
            refine ⟨57190687470537537950436739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76254249960716717267248985 57190687470537537950436739)
            ·
              refine ⟨85786031205806306925655109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57190687470537537950436739 85786031205806306925655109)
              ·
                refine ⟨16084880851088682548560333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85786031205806306925655109 16084880851088682548560333)
                ·
                  refine ⟨6031830319158255955710125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16084880851088682548560333 6031830319158255955710125)
                  ·
                    refine ⟨2261936369684345983391297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6031830319158255955710125 2261936369684345983391297)
                    ·
                      refine ⟨1696452277263259487543473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2261936369684345983391297 1696452277263259487543473)
                      ·
                        rfl

theorem cell23_3303829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 4, 3, 3, 2].length) (baseStart_3303829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3303829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3303829 prefixEnd_3303829 := by exact prefixLift 3303829
  have htrace : WordTrace (prefixWord ++ tailWord_3303829) baseStart_3303829 baseEnd_3303829 := by
    simpa [prefixWord, tailWord_3303829, baseEnd_3303829] using wordTrace_append hprefix tailTrace_3303829
  have hstable : (prefixWord ++ tailWord_3303829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3303829).length < 2 ^ (prefixWord ++ tailWord_3303829).sum := by decide
  have hdescent : baseEnd_3303829 < baseStart_3303829 := by decide
  rcases family_descends (prefixWord ++ tailWord_3303829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3303863 : List Nat := [1, 1, 3, 1, 3, 4, 3, 1, 1, 3, 2]
def baseStart_3303863 : Nat := 118140960795 + 3303863 * 2 ^ 59
def prefixEnd_3303863 : Nat := 4983230072969 + 3 ^ 40 * 3303863 * 2
def baseEnd_3303863 : Nat := 1696469735605512354518317

theorem tailTrace_3303863 : CollatzResearch.WordTrace tailWord_3303863 prefixEnd_3303863 1696469735605512354518317 := by
  unfold tailWord_3303863
  simp only [CollatzResearch.WordTrace]
  refine ⟨120501783229676080722884243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80334522153117387148589495 120501783229676080722884243)
  ·
    refine ⟨180752674844514121084326365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120501783229676080722884243 180752674844514121084326365)
    ·
      refine ⟨67782253066692795406622387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180752674844514121084326365 67782253066692795406622387)
      ·
        refine ⟨101673379600039193109933581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67782253066692795406622387 101673379600039193109933581)
        ·
          refine ⟨38127517350014697416225093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101673379600039193109933581 38127517350014697416225093)
          ·
            refine ⟨7148909503127755765542205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38127517350014697416225093 7148909503127755765542205)
            ·
              refine ⟨2680841063672908412078327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7148909503127755765542205 2680841063672908412078327)
              ·
                refine ⟨4021261595509362618117491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2680841063672908412078327 4021261595509362618117491)
                ·
                  refine ⟨6031892393264043927176237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4021261595509362618117491 6031892393264043927176237)
                  ·
                    refine ⟨2261959647474016472691089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6031892393264043927176237 2261959647474016472691089)
                    ·
                      refine ⟨1696469735605512354518317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2261959647474016472691089 1696469735605512354518317)
                      ·
                        rfl

theorem cell23_3303863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 3, 1, 1, 3, 2].length) (baseStart_3303863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3303863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3303863 prefixEnd_3303863 := by exact prefixLift 3303863
  have htrace : WordTrace (prefixWord ++ tailWord_3303863) baseStart_3303863 baseEnd_3303863 := by
    simpa [prefixWord, tailWord_3303863, baseEnd_3303863] using wordTrace_append hprefix tailTrace_3303863
  have hstable : (prefixWord ++ tailWord_3303863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3303863).length < 2 ^ (prefixWord ++ tailWord_3303863).sum := by decide
  have hdescent : baseEnd_3303863 < baseStart_3303863 := by decide
  rcases family_descends (prefixWord ++ tailWord_3303863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3303872 : List Nat := [2, 1, 1, 2, 3, 1, 1, 4, 2, 2, 4]
def baseStart_3303872 : Nat := 118140960795 + 3303872 * 2 ^ 59
def prefixEnd_3303872 : Nat := 4983230072969 + 3 ^ 40 * 3303872 * 2
def baseEnd_3303872 : Nat := 1696474356931402819305775

theorem tailTrace_3303872 : CollatzResearch.WordTrace tailWord_3303872 prefixEnd_3303872 1696474356931402819305775 := by
  unfold tailWord_3303872
  simp only [CollatzResearch.WordTrace]
  refine ⟨60251055743321737629980935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80334740991095650173307913 60251055743321737629980935)
  ·
    refine ⟨90376583614982606444971403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60251055743321737629980935 90376583614982606444971403)
    ·
      refine ⟨135564875422473909667457105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90376583614982606444971403 135564875422473909667457105)
      ·
        refine ⟨101673656566855432250592829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135564875422473909667457105 101673656566855432250592829)
        ·
          refine ⟨38127621212570787093972311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101673656566855432250592829 38127621212570787093972311)
          ·
            refine ⟨57191431818856180640958467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38127621212570787093972311 57191431818856180640958467)
            ·
              refine ⟨85787147728284270961437701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57191431818856180640958467 85787147728284270961437701)
              ·
                refine ⟨16085090199053300805269569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85787147728284270961437701 16085090199053300805269569)
                ·
                  refine ⟨12063817649289975603952177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16085090199053300805269569 12063817649289975603952177)
                  ·
                    refine ⟨9047863236967481702964133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12063817649289975603952177 9047863236967481702964133)
                    ·
                      refine ⟨1696474356931402819305775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9047863236967481702964133 1696474356931402819305775)
                      ·
                        rfl

theorem cell23_3303872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2, 4].length) (baseStart_3303872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3303872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3303872 prefixEnd_3303872 := by exact prefixLift 3303872
  have htrace : WordTrace (prefixWord ++ tailWord_3303872) baseStart_3303872 baseEnd_3303872 := by
    simpa [prefixWord, tailWord_3303872, baseEnd_3303872] using wordTrace_append hprefix tailTrace_3303872
  have hstable : (prefixWord ++ tailWord_3303872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3303872).length < 2 ^ (prefixWord ++ tailWord_3303872).sum := by decide
  have hdescent : baseEnd_3303872 < baseStart_3303872 := by decide
  rcases family_descends (prefixWord ++ tailWord_3303872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3303882 : List Nat := [3, 1, 2, 1, 2, 2, 2, 3, 7]
def baseStart_3303882 : Nat := 118140960795 + 3303882 * 2 ^ 59
def prefixEnd_3303882 : Nat := 4983230072969 + 3 ^ 40 * 3303882 * 2
def baseEnd_3303882 : Nat := 188497721304216420020081

theorem tailTrace_3303882 : CollatzResearch.WordTrace tailWord_3303882 prefixEnd_3303882 188497721304216420020081 := by
  unfold tailWord_3303882
  simp only [CollatzResearch.WordTrace]
  refine ⟨30125619054151811741956475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80334984144404831311883933 30125619054151811741956475)
  ·
    refine ⟨45188428581227717612934713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30125619054151811741956475 45188428581227717612934713)
    ·
      refine ⟨33891321435920788209701035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45188428581227717612934713 33891321435920788209701035)
      ·
        refine ⟨50836982153881182314551553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33891321435920788209701035 50836982153881182314551553)
        ·
          refine ⟨38127736615410886735913665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50836982153881182314551553 38127736615410886735913665)
          ·
            refine ⟨28595802461558165051935249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38127736615410886735913665 28595802461558165051935249)
            ·
              refine ⟨21446851846168623788951437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28595802461558165051935249 21446851846168623788951437)
              ·
                refine ⟨8042569442313233920856789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21446851846168623788951437 8042569442313233920856789)
                ·
                  refine ⟨188497721304216420020081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8042569442313233920856789 188497721304216420020081)
                  ·
                    rfl

theorem cell23_3303882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 3, 7].length) (baseStart_3303882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3303882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3303882 prefixEnd_3303882 := by exact prefixLift 3303882
  have htrace : WordTrace (prefixWord ++ tailWord_3303882) baseStart_3303882 baseEnd_3303882 := by
    simpa [prefixWord, tailWord_3303882, baseEnd_3303882] using wordTrace_append hprefix tailTrace_3303882
  have hstable : (prefixWord ++ tailWord_3303882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3303882).length < 2 ^ (prefixWord ++ tailWord_3303882).sum := by decide
  have hdescent : baseEnd_3303882 < baseStart_3303882 := by decide
  rcases family_descends (prefixWord ++ tailWord_3303882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3303893 : List Nat := [1, 3, 2, 3, 1, 2, 2, 3, 2, 2, 2]
def baseStart_3303893 : Nat := 118140960795 + 3303893 * 2 ^ 59
def prefixEnd_3303893 : Nat := 4983230072969 + 3 ^ 40 * 3303893 * 2
def baseEnd_3303893 : Nat := 1696485140025147237143179

theorem tailTrace_3303893 : CollatzResearch.WordTrace tailWord_3303893 prefixEnd_3303893 1696485140025147237143179 := by
  unfold tailWord_3303893
  simp only [CollatzResearch.WordTrace]
  refine ⟨120502877419567395846476333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80335251613044930564317555 120502877419567395846476333)
  ·
    refine ⟨45188579032337773442428625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120502877419567395846476333 45188579032337773442428625)
    ·
      refine ⟨33891434274253330081821469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45188579032337773442428625 33891434274253330081821469)
      ·
        refine ⟨12709287852844998780683051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33891434274253330081821469 12709287852844998780683051)
        ·
          refine ⟨19063931779267498171024577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12709287852844998780683051 19063931779267498171024577)
          ·
            refine ⟨14297948834450623628268433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19063931779267498171024577 14297948834450623628268433)
            ·
              refine ⟨10723461625837967721201325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14297948834450623628268433 10723461625837967721201325)
              ·
                refine ⟨4021298109689237895450497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10723461625837967721201325 4021298109689237895450497)
                ·
                  refine ⟨3015973582266928421587873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4021298109689237895450497 3015973582266928421587873)
                  ·
                    refine ⟨2261980186700196316190905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3015973582266928421587873 2261980186700196316190905)
                    ·
                      refine ⟨1696485140025147237143179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2261980186700196316190905 1696485140025147237143179)
                      ·
                        rfl

theorem cell23_3303893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 3, 2, 2, 2].length) (baseStart_3303893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3303893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3303893 prefixEnd_3303893 := by exact prefixLift 3303893
  have htrace : WordTrace (prefixWord ++ tailWord_3303893) baseStart_3303893 baseEnd_3303893 := by
    simpa [prefixWord, tailWord_3303893, baseEnd_3303893] using wordTrace_append hprefix tailTrace_3303893
  have hstable : (prefixWord ++ tailWord_3303893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3303893).length < 2 ^ (prefixWord ++ tailWord_3303893).sum := by decide
  have hdescent : baseEnd_3303893 < baseStart_3303893 := by decide
  rcases family_descends (prefixWord ++ tailWord_3303893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3303969 : List Nat := [1, 2, 3, 2, 2, 1, 1, 3, 1, 4, 3]
def baseStart_3303969 : Nat := 118140960795 + 3303969 * 2 ^ 59
def prefixEnd_3303969 : Nat := 4983230072969 + 3 ^ 40 * 3303969 * 2
def baseEnd_3303969 : Nat := 1696524164554888939792829

theorem tailTrace_3303969 : CollatzResearch.WordTrace tailWord_3303969 prefixEnd_3303969 1696524164554888939792829 := by
  unfold tailWord_3303969
  simp only [CollatzResearch.WordTrace]
  refine ⟨120505649367292060826242961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80337099578194707217495307 120505649367292060826242961)
  ·
    refine ⟨90379237025469045619682221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120505649367292060826242961 90379237025469045619682221)
    ·
      refine ⟨33892213884550892107380833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90379237025469045619682221 33892213884550892107380833)
      ·
        refine ⟨25419160413413169080535625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33892213884550892107380833 25419160413413169080535625)
        ·
          refine ⟨19064370310059876810401719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25419160413413169080535625 19064370310059876810401719)
          ·
            refine ⟨28596555465089815215602579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19064370310059876810401719 28596555465089815215602579)
            ·
              refine ⟨42894833197634722823403869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28596555465089815215602579 42894833197634722823403869)
              ·
                refine ⟨16085562449113021058776451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42894833197634722823403869 16085562449113021058776451)
                ·
                  refine ⟨24128343673669531588164677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16085562449113021058776451 24128343673669531588164677)
                  ·
                    refine ⟨4524064438813037172780877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24128343673669531588164677 4524064438813037172780877)
                    ·
                      refine ⟨1696524164554888939792829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4524064438813037172780877 1696524164554888939792829)
                      ·
                        rfl

theorem cell23_3303969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 3, 1, 4, 3].length) (baseStart_3303969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3303969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3303969 prefixEnd_3303969 := by exact prefixLift 3303969
  have htrace : WordTrace (prefixWord ++ tailWord_3303969) baseStart_3303969 baseEnd_3303969 := by
    simpa [prefixWord, tailWord_3303969, baseEnd_3303969] using wordTrace_append hprefix tailTrace_3303969
  have hstable : (prefixWord ++ tailWord_3303969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3303969).length < 2 ^ (prefixWord ++ tailWord_3303969).sum := by decide
  have hdescent : baseEnd_3303969 < baseStart_3303969 := by decide
  rcases family_descends (prefixWord ++ tailWord_3303969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3303989 : List Nat := [1, 3, 3, 1, 1, 2, 2, 4, 6]
def baseStart_3303989 : Nat := 118140960795 + 3303989 * 2 ^ 59
def prefixEnd_3303989 : Nat := 4983230072969 + 3 ^ 40 * 3303989 * 2
def baseEnd_3303989 : Nat := 188503826018664317949193

theorem tailTrace_3303989 : CollatzResearch.WordTrace tailWord_3303989 prefixEnd_3303989 188503826018664317949193 := by
  unfold tailWord_3303989
  simp only [CollatzResearch.WordTrace]
  refine ⟨120506378827219604241971021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80337585884813069494647347 120506378827219604241971021)
  ·
    refine ⟨45189892060207351590739133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120506378827219604241971021 45189892060207351590739133)
    ·
      refine ⟨16946209522577756846527175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45189892060207351590739133 16946209522577756846527175)
      ·
        refine ⟨25419314283866635269790763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16946209522577756846527175 25419314283866635269790763)
        ·
          refine ⟨38128971425799952904686145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25419314283866635269790763 38128971425799952904686145)
          ·
            refine ⟨28596728569349964678514609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38128971425799952904686145 28596728569349964678514609)
            ·
              refine ⟨21447546427012473508885957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28596728569349964678514609 21447546427012473508885957)
              ·
                refine ⟨4021414955064838782916117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21447546427012473508885957 4021414955064838782916117)
                ·
                  refine ⟨188503826018664317949193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4021414955064838782916117 188503826018664317949193)
                  ·
                    rfl

theorem cell23_3303989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 4, 6].length) (baseStart_3303989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3303989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3303989 prefixEnd_3303989 := by exact prefixLift 3303989
  have htrace : WordTrace (prefixWord ++ tailWord_3303989) baseStart_3303989 baseEnd_3303989 := by
    simpa [prefixWord, tailWord_3303989, baseEnd_3303989] using wordTrace_append hprefix tailTrace_3303989
  have hstable : (prefixWord ++ tailWord_3303989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3303989).length < 2 ^ (prefixWord ++ tailWord_3303989).sum := by decide
  have hdescent : baseEnd_3303989 < baseStart_3303989 := by decide
  rcases family_descends (prefixWord ++ tailWord_3303989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3304090 : List Nat := [3, 1, 1, 6, 1, 1, 1, 3, 1, 1, 4]
def baseStart_3304090 : Nat := 118140960795 + 3304090 * 2 ^ 59
def prefixEnd_3304090 : Nat := 4983230072969 + 3 ^ 40 * 3304090 * 2
def baseEnd_3304090 : Nat := 1696586295714082966379773

theorem tailTrace_3304090 : CollatzResearch.WordTrace tailWord_3304090 prefixEnd_3304090 1696586295714082966379773 := by
  unfold tailWord_3304090
  simp only [CollatzResearch.WordTrace]
  refine ⟨30127515649963424622849431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80340041733235798994265149 30127515649963424622849431)
  ·
    refine ⟨45191273474945136934274147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30127515649963424622849431 45191273474945136934274147)
    ·
      refine ⟨67786910212417705401411221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45191273474945136934274147 67786910212417705401411221)
      ·
        refine ⟨3177511416207079940691151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 67786910212417705401411221 3177511416207079940691151)
        ·
          refine ⟨4766267124310619911036727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3177511416207079940691151 4766267124310619911036727)
          ·
            refine ⟨7149400686465929866555091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4766267124310619911036727 7149400686465929866555091)
            ·
              refine ⟨10724101029698894799832637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7149400686465929866555091 10724101029698894799832637)
              ·
                refine ⟨4021537886137085549937239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10724101029698894799832637 4021537886137085549937239)
                ·
                  refine ⟨6032306829205628324905859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4021537886137085549937239 6032306829205628324905859)
                  ·
                    refine ⟨9048460243808442487358789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6032306829205628324905859 9048460243808442487358789)
                    ·
                      refine ⟨1696586295714082966379773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9048460243808442487358789 1696586295714082966379773)
                      ·
                        rfl

theorem cell23_3304090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_3304090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3304090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3304090 prefixEnd_3304090 := by exact prefixLift 3304090
  have htrace : WordTrace (prefixWord ++ tailWord_3304090) baseStart_3304090 baseEnd_3304090 := by
    simpa [prefixWord, tailWord_3304090, baseEnd_3304090] using wordTrace_append hprefix tailTrace_3304090
  have hstable : (prefixWord ++ tailWord_3304090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3304090).length < 2 ^ (prefixWord ++ tailWord_3304090).sum := by decide
  have hdescent : baseEnd_3304090 < baseStart_3304090 := by decide
  rcases family_descends (prefixWord ++ tailWord_3304090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3304219 : List Nat := [1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 8]
def baseStart_3304219 : Nat := 118140960795 + 3304219 * 2 ^ 59
def prefixEnd_3304219 : Nat := 4983230072969 + 3 ^ 40 * 3304219 * 2
def baseEnd_3304219 : Nat := 1696652534718512961666679

theorem tailTrace_3304219 : CollatzResearch.WordTrace tailWord_3304219 prefixEnd_3304219 1696652534718512961666679 := by
  unfold tailWord_3304219
  simp only [CollatzResearch.WordTrace]
  refine ⟨120514767616386353522843711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80343178410924235681895807 120514767616386353522843711)
  ·
    refine ⟨180772151424579530284265567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120514767616386353522843711 180772151424579530284265567)
    ·
      refine ⟨271158227136869295426398351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180772151424579530284265567 271158227136869295426398351)
      ·
        refine ⟨406737340705303943139597527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271158227136869295426398351 406737340705303943139597527)
        ·
          refine ⟨610106011057955914709396291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 406737340705303943139597527 610106011057955914709396291)
          ·
            refine ⟨915159016586933872064094437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 610106011057955914709396291 915159016586933872064094437)
            ·
              refine ⟨171592315610050101012017707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 915159016586933872064094437 171592315610050101012017707)
              ·
                refine ⟨257388473415075151518026561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 171592315610050101012017707 257388473415075151518026561)
                ·
                  refine ⟨193041355061306363638519921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 257388473415075151518026561 193041355061306363638519921)
                  ·
                    refine ⟨144781016295979772728889941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 193041355061306363638519921 144781016295979772728889941)
                    ·
                      refine ⟨1696652534718512961666679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 144781016295979772728889941 1696652534718512961666679)
                      ·
                        rfl

theorem cell23_3304219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 8].length) (baseStart_3304219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3304219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3304219 prefixEnd_3304219 := by exact prefixLift 3304219
  have htrace : WordTrace (prefixWord ++ tailWord_3304219) baseStart_3304219 baseEnd_3304219 := by
    simpa [prefixWord, tailWord_3304219, baseEnd_3304219] using wordTrace_append hprefix tailTrace_3304219
  have hstable : (prefixWord ++ tailWord_3304219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3304219).length < 2 ^ (prefixWord ++ tailWord_3304219).sum := by decide
  have hdescent : baseEnd_3304219 < baseStart_3304219 := by decide
  rcases family_descends (prefixWord ++ tailWord_3304219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3304220 : List Nat := [2, 2, 3, 1, 1, 3, 4, 2, 5]
def baseStart_3304220 : Nat := 118140960795 + 3304220 * 2 ^ 59
def prefixEnd_3304220 : Nat := 4983230072969 + 3 ^ 40 * 3304220 * 2
def baseEnd_3304220 : Nat := 188517005355463050861575

theorem tailTrace_3304220 : CollatzResearch.WordTrace tailWord_3304220 prefixEnd_3304220 188517005355463050861575 := by
  unfold tailWord_3304220
  simp only [CollatzResearch.WordTrace]
  refine ⟨60257402044691365346815057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80343202726255153795753409 60257402044691365346815057)
  ·
    refine ⟨45193051533518524010111293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60257402044691365346815057 45193051533518524010111293)
    ·
      refine ⟨16947394325069446503791735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45193051533518524010111293 16947394325069446503791735)
      ·
        refine ⟨25421091487604169755687603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16947394325069446503791735 25421091487604169755687603)
        ·
          refine ⟨38131637231406254633531405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25421091487604169755687603 38131637231406254633531405)
          ·
            refine ⟨14299363961777345487574277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38131637231406254633531405 14299363961777345487574277)
            ·
              refine ⟨2681130742833252278920177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14299363961777345487574277 2681130742833252278920177)
              ·
                refine ⟨2010848057124939209190133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2681130742833252278920177 2010848057124939209190133)
                ·
                  refine ⟨188517005355463050861575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2010848057124939209190133 188517005355463050861575)
                  ·
                    rfl

theorem cell23_3304220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 4, 2, 5].length) (baseStart_3304220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3304220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3304220 prefixEnd_3304220 := by exact prefixLift 3304220
  have htrace : WordTrace (prefixWord ++ tailWord_3304220) baseStart_3304220 baseEnd_3304220 := by
    simpa [prefixWord, tailWord_3304220, baseEnd_3304220] using wordTrace_append hprefix tailTrace_3304220
  have hstable : (prefixWord ++ tailWord_3304220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3304220).length < 2 ^ (prefixWord ++ tailWord_3304220).sum := by decide
  have hdescent : baseEnd_3304220 < baseStart_3304220 := by decide
  rcases family_descends (prefixWord ++ tailWord_3304220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3304223 : List Nat := [1, 1, 2, 4, 2, 2, 1, 1, 2, 5, 2]
def baseStart_3304223 : Nat := 118140960795 + 3304223 * 2 ^ 59
def prefixEnd_3304223 : Nat := 4983230072969 + 3 ^ 40 * 3304223 * 2
def baseEnd_3304223 : Nat := 1696654588641130946016661

theorem tailTrace_3304223 : CollatzResearch.WordTrace tailWord_3304223 prefixEnd_3304223 1696654588641130946016661 := by
  unfold tailWord_3304223
  simp only [CollatzResearch.WordTrace]
  refine ⟨120514913508371862205989323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80343275672247908137326215 120514913508371862205989323)
  ·
    refine ⟨180772370262557793308983985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120514913508371862205989323 180772370262557793308983985)
    ·
      refine ⟨135579277696918344981737989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180772370262557793308983985 135579277696918344981737989)
      ·
        refine ⟨25421114568172189684075873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 135579277696918344981737989 25421114568172189684075873)
        ·
          refine ⟨19065835926129142263056905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25421114568172189684075873 19065835926129142263056905)
          ·
            refine ⟨14299376944596856697292679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19065835926129142263056905 14299376944596856697292679)
            ·
              refine ⟨21449065416895285045939019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14299376944596856697292679 21449065416895285045939019)
              ·
                refine ⟨32173598125342927568908529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21449065416895285045939019 32173598125342927568908529)
                ·
                  refine ⟨24130198594007195676681397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32173598125342927568908529 24130198594007195676681397)
                  ·
                    refine ⟨2262206118188174594688881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24130198594007195676681397 2262206118188174594688881)
                    ·
                      refine ⟨1696654588641130946016661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2262206118188174594688881 1696654588641130946016661)
                      ·
                        rfl

theorem cell23_3304223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 1, 2, 5, 2].length) (baseStart_3304223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3304223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3304223 prefixEnd_3304223 := by exact prefixLift 3304223
  have htrace : WordTrace (prefixWord ++ tailWord_3304223) baseStart_3304223 baseEnd_3304223 := by
    simpa [prefixWord, tailWord_3304223, baseEnd_3304223] using wordTrace_append hprefix tailTrace_3304223
  have hstable : (prefixWord ++ tailWord_3304223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3304223).length < 2 ^ (prefixWord ++ tailWord_3304223).sum := by decide
  have hdescent : baseEnd_3304223 < baseStart_3304223 := by decide
  rcases family_descends (prefixWord ++ tailWord_3304223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3304236 : List Nat := [2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 4]
def baseStart_3304236 : Nat := 118140960795 + 3304236 * 2 ^ 59
def prefixEnd_3304236 : Nat := 4983230072969 + 3 ^ 40 * 3304236 * 2
def baseEnd_3304236 : Nat := 1696661263889639395154101

theorem tailTrace_3304236 : CollatzResearch.WordTrace tailWord_3304236 prefixEnd_3304236 1696661263889639395154101 := by
  unfold tailWord_3304236
  simp only [CollatzResearch.WordTrace]
  refine ⟨60257693828662382713106281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80343591771549843617475041 60257693828662382713106281)
  ·
    refine ⟨45193270371496787034829711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60257693828662382713106281 45193270371496787034829711)
    ·
      refine ⟨67789905557245180552244567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45193270371496787034829711 67789905557245180552244567)
      ·
        refine ⟨101684858335867770828366851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67789905557245180552244567 101684858335867770828366851)
        ·
          refine ⟨152527287503801656242550277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101684858335867770828366851 152527287503801656242550277)
          ·
            refine ⟨28598866406962810545478177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 152527287503801656242550277 28598866406962810545478177)
            ·
              refine ⟨21449149805222107909108633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28598866406962810545478177 21449149805222107909108633)
              ·
                refine ⟨16086862353916580931831475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21449149805222107909108633 16086862353916580931831475)
                ·
                  refine ⟨24130293530874871397747213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16086862353916580931831475 24130293530874871397747213)
                  ·
                    refine ⟨9048860074078076774155205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24130293530874871397747213 9048860074078076774155205)
                    ·
                      refine ⟨1696661263889639395154101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9048860074078076774155205 1696661263889639395154101)
                      ·
                        rfl

theorem cell23_3304236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 4].length) (baseStart_3304236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3304236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3304236 prefixEnd_3304236 := by exact prefixLift 3304236
  have htrace : WordTrace (prefixWord ++ tailWord_3304236) baseStart_3304236 baseEnd_3304236 := by
    simpa [prefixWord, tailWord_3304236, baseEnd_3304236] using wordTrace_append hprefix tailTrace_3304236
  have hstable : (prefixWord ++ tailWord_3304236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3304236).length < 2 ^ (prefixWord ++ tailWord_3304236).sum := by decide
  have hdescent : baseEnd_3304236 < baseStart_3304236 := by decide
  rcases family_descends (prefixWord ++ tailWord_3304236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3304250 : List Nat := [3, 1, 1, 1, 6, 2, 1, 1, 2, 5]
def baseStart_3304250 : Nat := 118140960795 + 3304250 * 2 ^ 59
def prefixEnd_3304250 : Nat := 4983230072969 + 3 ^ 40 * 3304250 * 2
def baseEnd_3304250 : Nat := 565556150872934113459679

theorem tailTrace_3304250 : CollatzResearch.WordTrace tailWord_3304250 prefixEnd_3304250 565556150872934113459679 := by
  unfold tailWord_3304250
  simp only [CollatzResearch.WordTrace]
  refine ⟨30128974569818511454305551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80343932186182697211481469 30128974569818511454305551)
  ·
    refine ⟨45193461854727767181458327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30128974569818511454305551 45193461854727767181458327)
    ·
      refine ⟨67790192782091650772187491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45193461854727767181458327 67790192782091650772187491)
      ·
        refine ⟨101685289173137476158281237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67790192782091650772187491 101685289173137476158281237)
        ·
          refine ⟨4766497929990819194919433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 101685289173137476158281237 4766497929990819194919433)
          ·
            refine ⟨3574873447493114396189575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4766497929990819194919433 3574873447493114396189575)
            ·
              refine ⟨5362310171239671594284363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3574873447493114396189575 5362310171239671594284363)
              ·
                refine ⟨8043465256859507391426545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5362310171239671594284363 8043465256859507391426545)
                ·
                  refine ⟨6032598942644630543569909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8043465256859507391426545 6032598942644630543569909)
                  ·
                    refine ⟨565556150872934113459679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6032598942644630543569909 565556150872934113459679)
                    ·
                      rfl

theorem cell23_3304250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 1, 1, 2, 5].length) (baseStart_3304250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3304250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3304250 prefixEnd_3304250 := by exact prefixLift 3304250
  have htrace : WordTrace (prefixWord ++ tailWord_3304250) baseStart_3304250 baseEnd_3304250 := by
    simpa [prefixWord, tailWord_3304250, baseEnd_3304250] using wordTrace_append hprefix tailTrace_3304250
  have hstable : (prefixWord ++ tailWord_3304250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3304250).length < 2 ^ (prefixWord ++ tailWord_3304250).sum := by decide
  have hdescent : baseEnd_3304250 < baseStart_3304250 := by decide
  rcases family_descends (prefixWord ++ tailWord_3304250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3304323 : List Nat := [1, 1, 1, 3, 4, 1, 1, 5, 1, 5]
def baseStart_3304323 : Nat := 118140960795 + 3304323 * 2 ^ 59
def prefixEnd_3304323 : Nat := 4983230072969 + 3 ^ 40 * 3304323 * 2
def baseEnd_3304323 : Nat := 565568645568860184922067

theorem tailTrace_3304323 : CollatzResearch.WordTrace tailWord_3304323 prefixEnd_3304323 565568645568860184922067 := by
  unfold tailWord_3304323
  simp only [CollatzResearch.WordTrace]
  refine ⟨120518560808009579284629623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80345707205339719523086415 120518560808009579284629623)
  ·
    refine ⟨180777841212014368926944435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120518560808009579284629623 180777841212014368926944435)
    ·
      refine ⟨271166761818021553390416653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180777841212014368926944435 271166761818021553390416653)
      ·
        refine ⟨101687535681758082521406245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 271166761818021553390416653 101687535681758082521406245)
        ·
          refine ⟨19066412940329640472763671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101687535681758082521406245 19066412940329640472763671)
          ·
            refine ⟨28599619410494460709145507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19066412940329640472763671 28599619410494460709145507)
            ·
              refine ⟨42899429115741691063718261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28599619410494460709145507 42899429115741691063718261)
              ·
                refine ⟨4021821479600783537223587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42899429115741691063718261 4021821479600783537223587)
                ·
                  refine ⟨6032732219401175305835381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4021821479600783537223587 6032732219401175305835381)
                  ·
                    refine ⟨565568645568860184922067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6032732219401175305835381 565568645568860184922067)
                    ·
                      rfl

theorem cell23_3304323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 5, 1, 5].length) (baseStart_3304323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3304323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3304323 prefixEnd_3304323 := by exact prefixLift 3304323
  have htrace : WordTrace (prefixWord ++ tailWord_3304323) baseStart_3304323 baseEnd_3304323 := by
    simpa [prefixWord, tailWord_3304323, baseEnd_3304323] using wordTrace_append hprefix tailTrace_3304323
  have hstable : (prefixWord ++ tailWord_3304323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3304323).length < 2 ^ (prefixWord ++ tailWord_3304323).sum := by decide
  have hdescent : baseEnd_3304323 < baseStart_3304323 := by decide
  rcases family_descends (prefixWord ++ tailWord_3304323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3304343 : List Nat := [1, 1, 3, 3, 1, 2, 2, 2, 3, 1, 4]
def baseStart_3304343 : Nat := 118140960795 + 3304343 * 2 ^ 59
def prefixEnd_3304343 : Nat := 4983230072969 + 3 ^ 40 * 3304343 * 2
def baseEnd_3304343 : Nat := 1696716206319670476516109

theorem tailTrace_3304343 : CollatzResearch.WordTrace tailWord_3304343 prefixEnd_3304343 1696716206319670476516109 := by
  unfold tailWord_3304343
  simp only [CollatzResearch.WordTrace]
  refine ⟨120519290267937122700357683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80346193511958081800238455 120519290267937122700357683)
  ·
    refine ⟨180778935401905684050536525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120519290267937122700357683 180778935401905684050536525)
    ·
      refine ⟨67792100775714631518951197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180778935401905684050536525 67792100775714631518951197)
      ·
        refine ⟨25422037790892986819606699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67792100775714631518951197 25422037790892986819606699)
        ·
          refine ⟨38133056686339480229410049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25422037790892986819606699 38133056686339480229410049)
          ·
            refine ⟨28599792514754610172057537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38133056686339480229410049 28599792514754610172057537)
            ·
              refine ⟨21449844386065957629043153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28599792514754610172057537 21449844386065957629043153)
              ·
                refine ⟨16087383289549468221782365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21449844386065957629043153 16087383289549468221782365)
                ·
                  refine ⟨6032768733581050583168387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16087383289549468221782365 6032768733581050583168387)
                  ·
                    refine ⟨9049153100371575874752581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6032768733581050583168387 9049153100371575874752581)
                    ·
                      refine ⟨1696716206319670476516109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9049153100371575874752581 1696716206319670476516109)
                      ·
                        rfl

theorem cell23_3304343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 2, 3, 1, 4].length) (baseStart_3304343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3304343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3304343 prefixEnd_3304343 := by exact prefixLift 3304343
  have htrace : WordTrace (prefixWord ++ tailWord_3304343) baseStart_3304343 baseEnd_3304343 := by
    simpa [prefixWord, tailWord_3304343, baseEnd_3304343] using wordTrace_append hprefix tailTrace_3304343
  have hstable : (prefixWord ++ tailWord_3304343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3304343).length < 2 ^ (prefixWord ++ tailWord_3304343).sum := by decide
  have hdescent : baseEnd_3304343 < baseStart_3304343 := by decide
  rcases family_descends (prefixWord ++ tailWord_3304343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3304363 : List Nat := [1, 1, 1, 1, 2, 1, 1, 7, 3, 2, 3]
def baseStart_3304363 : Nat := 118140960795 + 3304363 * 2 ^ 59
def prefixEnd_3304363 : Nat := 4983230072969 + 3 ^ 40 * 3304363 * 2
def baseEnd_3304363 : Nat := 1696726475932760398266017

theorem tailTrace_3304363 : CollatzResearch.WordTrace tailWord_3304363 prefixEnd_3304363 1696726475932760398266017 := by
  unfold tailWord_3304363
  simp only [CollatzResearch.WordTrace]
  refine ⟨120520019727864666116085743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80346679818576444077390495 120520019727864666116085743)
  ·
    refine ⟨180780029591796999174128615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120520019727864666116085743 180780029591796999174128615)
    ·
      refine ⟨271170044387695498761192923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180780029591796999174128615 271170044387695498761192923)
      ·
        refine ⟨406755066581543248141789385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271170044387695498761192923 406755066581543248141789385)
        ·
          refine ⟨305066299936157436106342039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 406755066581543248141789385 305066299936157436106342039)
          ·
            refine ⟨457599449904236154159513059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 305066299936157436106342039 457599449904236154159513059)
            ·
              refine ⟨686399174856354231239269589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 457599449904236154159513059 686399174856354231239269589)
              ·
                refine ⟨16087480660695802294670381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 686399174856354231239269589 16087480660695802294670381)
                ·
                  refine ⟨6032805247760925860501393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16087480660695802294670381 6032805247760925860501393)
                  ·
                    refine ⟨4524603935820694395376045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6032805247760925860501393 4524603935820694395376045)
                    ·
                      refine ⟨1696726475932760398266017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4524603935820694395376045 1696726475932760398266017)
                      ·
                        rfl

theorem cell23_3304363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 7, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 7, 3, 2, 3].length) (baseStart_3304363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3304363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3304363 prefixEnd_3304363 := by exact prefixLift 3304363
  have htrace : WordTrace (prefixWord ++ tailWord_3304363) baseStart_3304363 baseEnd_3304363 := by
    simpa [prefixWord, tailWord_3304363, baseEnd_3304363] using wordTrace_append hprefix tailTrace_3304363
  have hstable : (prefixWord ++ tailWord_3304363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3304363).length < 2 ^ (prefixWord ++ tailWord_3304363).sum := by decide
  have hdescent : baseEnd_3304363 < baseStart_3304363 := by decide
  rcases family_descends (prefixWord ++ tailWord_3304363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3304377 : List Nat := [1, 2, 1, 4, 2, 3, 3, 1, 1, 1, 4]
def baseStart_3304377 : Nat := 118140960795 + 3304377 * 2 ^ 59
def prefixEnd_3304377 : Nat := 4983230072969 + 3 ^ 40 * 3304377 * 2
def baseEnd_3304377 : Nat := 1696733664661923343490953

theorem tailTrace_3304377 : CollatzResearch.WordTrace tailWord_3304377 prefixEnd_3304377 1696733664661923343490953 := by
  unfold tailWord_3304377
  simp only [CollatzResearch.WordTrace]
  refine ⟨120520530349813946507095385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80347020233209297671396923 120520530349813946507095385)
  ·
    refine ⟨90390397762360459880321539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120520530349813946507095385 90390397762360459880321539)
    ·
      refine ⟨135585596643540689820482309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90390397762360459880321539 135585596643540689820482309)
      ·
        refine ⟨25422299370663879341340433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 135585596643540689820482309 25422299370663879341340433)
        ·
          refine ⟨19066724527997909506005325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25422299370663879341340433 19066724527997909506005325)
          ·
            refine ⟨7150021697999216064751997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19066724527997909506005325 7150021697999216064751997)
            ·
              refine ⟨2681258136749706024281999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7150021697999216064751997 2681258136749706024281999)
              ·
                refine ⟨4021887205124559036422999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2681258136749706024281999 4021887205124559036422999)
                ·
                  refine ⟨6032830807686838554634499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4021887205124559036422999 6032830807686838554634499)
                  ·
                    refine ⟨9049246211530257831951749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6032830807686838554634499 9049246211530257831951749)
                    ·
                      refine ⟨1696733664661923343490953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9049246211530257831951749 1696733664661923343490953)
                      ·
                        rfl

theorem cell23_3304377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 3, 1, 1, 1, 4].length) (baseStart_3304377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3304377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3304377 prefixEnd_3304377 := by exact prefixLift 3304377
  have htrace : WordTrace (prefixWord ++ tailWord_3304377) baseStart_3304377 baseEnd_3304377 := by
    simpa [prefixWord, tailWord_3304377, baseEnd_3304377] using wordTrace_append hprefix tailTrace_3304377
  have hstable : (prefixWord ++ tailWord_3304377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3304377).length < 2 ^ (prefixWord ++ tailWord_3304377).sum := by decide
  have hdescent : baseEnd_3304377 < baseStart_3304377 := by decide
  rcases family_descends (prefixWord ++ tailWord_3304377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3304410 : List Nat := [3, 1, 1, 2, 4, 1, 1, 3, 1, 3, 3]
def baseStart_3304410 : Nat := 118140960795 + 3304410 * 2 ^ 59
def prefixEnd_3304410 : Nat := 4983230072969 + 3 ^ 40 * 3304410 * 2
def baseEnd_3304410 : Nat := 1696750609523521714378301

theorem tailTrace_3304410 : CollatzResearch.WordTrace tailWord_3304410 prefixEnd_3304410 1696750609523521714378301 := by
  unfold tailWord_3304410
  simp only [CollatzResearch.WordTrace]
  refine ⟨30130433489673598285761671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80347822639129595428697789 30130433489673598285761671)
  ·
    refine ⟨45195650234510397428642507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30130433489673598285761671 45195650234510397428642507)
    ·
      refine ⟨67793475351765596142963761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45195650234510397428642507 67793475351765596142963761)
      ·
        refine ⟨50845106513824197107222821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67793475351765596142963761 50845106513824197107222821)
        ·
          refine ⟨9533457471342036957604279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50845106513824197107222821 9533457471342036957604279)
          ·
            refine ⟨14300186207013055436406419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9533457471342036957604279 14300186207013055436406419)
            ·
              refine ⟨21450279310519583154609629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14300186207013055436406419 21450279310519583154609629)
              ·
                refine ⟨8043854741444843682978611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21450279310519583154609629 8043854741444843682978611)
                ·
                  refine ⟨12065782112167265524467917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8043854741444843682978611 12065782112167265524467917)
                  ·
                    refine ⟨4524668292062724571675469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12065782112167265524467917 4524668292062724571675469)
                    ·
                      refine ⟨1696750609523521714378301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4524668292062724571675469 1696750609523521714378301)
                      ·
                        rfl

theorem cell23_3304410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 3, 1, 3, 3].length) (baseStart_3304410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3304410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3304410 prefixEnd_3304410 := by exact prefixLift 3304410
  have htrace : WordTrace (prefixWord ++ tailWord_3304410) baseStart_3304410 baseEnd_3304410 := by
    simpa [prefixWord, tailWord_3304410, baseEnd_3304410] using wordTrace_append hprefix tailTrace_3304410
  have hstable : (prefixWord ++ tailWord_3304410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3304410).length < 2 ^ (prefixWord ++ tailWord_3304410).sum := by decide
  have hdescent : baseEnd_3304410 < baseStart_3304410 := by decide
  rcases family_descends (prefixWord ++ tailWord_3304410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3304444 : List Nat := [2, 2, 2, 1, 2, 5, 1, 2, 2, 1, 3]
def baseStart_3304444 : Nat := 118140960795 + 3304444 * 2 ^ 59
def prefixEnd_3304444 : Nat := 4983230072969 + 3 ^ 40 * 3304444 * 2
def baseEnd_3304444 : Nat := 1696768067865774581353145

theorem tailTrace_3304444 : CollatzResearch.WordTrace tailWord_3304444 prefixEnd_3304444 1696768067865774581353145 := by
  unfold tailWord_3304444
  simp only [CollatzResearch.WordTrace]
  refine ⟨60261487020285608474892193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80348649360380811299856257 60261487020285608474892193)
  ·
    refine ⟨45196115265214206356169145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60261487020285608474892193 45196115265214206356169145)
    ·
      refine ⟨33897086448910654767126859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45196115265214206356169145 33897086448910654767126859)
      ·
        refine ⟨50845629673365982150690289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33897086448910654767126859 50845629673365982150690289)
        ·
          refine ⟨38134222255024486613017717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50845629673365982150690289 38134222255024486613017717)
          ·
            refine ⟨3575083336408545619970411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38134222255024486613017717 3575083336408545619970411)
            ·
              refine ⟨5362625004612818429955617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3575083336408545619970411 5362625004612818429955617)
              ·
                refine ⟨4021968753459613822466713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5362625004612818429955617 4021968753459613822466713)
                ·
                  refine ⟨3016476565094710366850035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4021968753459613822466713 3016476565094710366850035)
                  ·
                    refine ⟨4524714847642065550275053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3016476565094710366850035 4524714847642065550275053)
                    ·
                      refine ⟨1696768067865774581353145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4524714847642065550275053 1696768067865774581353145)
                      ·
                        rfl

theorem cell23_3304444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 1, 2, 2, 1, 3].length) (baseStart_3304444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3304444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3304444 prefixEnd_3304444 := by exact prefixLift 3304444
  have htrace : WordTrace (prefixWord ++ tailWord_3304444) baseStart_3304444 baseEnd_3304444 := by
    simpa [prefixWord, tailWord_3304444, baseEnd_3304444] using wordTrace_append hprefix tailTrace_3304444
  have hstable : (prefixWord ++ tailWord_3304444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3304444).length < 2 ^ (prefixWord ++ tailWord_3304444).sum := by decide
  have hdescent : baseEnd_3304444 < baseStart_3304444 := by decide
  rcases family_descends (prefixWord ++ tailWord_3304444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3304473 : List Nat := [1, 2, 1, 2, 1, 1, 6, 2, 7]
def baseStart_3304473 : Nat := 118140960795 + 3304473 * 2 ^ 59
def prefixEnd_3304473 : Nat := 4983230072969 + 3 ^ 40 * 3304473 * 2
def baseEnd_3304473 : Nat := 188531439867194996432279

theorem tailTrace_3304473 : CollatzResearch.WordTrace tailWord_3304473 prefixEnd_3304473 188531439867194996432279 := by
  unfold tailWord_3304473
  simp only [CollatzResearch.WordTrace]
  refine ⟨120524031757466154902590073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80349354504977436601726715 120524031757466154902590073)
  ·
    refine ⟨90393023818099616176942555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120524031757466154902590073 90393023818099616176942555)
    ·
      refine ⟨135589535727149424265413833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90393023818099616176942555 135589535727149424265413833)
      ·
        refine ⟨101692151795362068199060375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135589535727149424265413833 101692151795362068199060375)
        ·
          refine ⟨152538227693043102298590563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101692151795362068199060375 152538227693043102298590563)
          ·
            refine ⟨228807341539564653447885845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152538227693043102298590563 228807341539564653447885845)
            ·
              refine ⟨10725344134667093130369649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 228807341539564653447885845 10725344134667093130369649)
              ·
                refine ⟨8044008101000319847777237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10725344134667093130369649 8044008101000319847777237)
                ·
                  refine ⟨188531439867194996432279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8044008101000319847777237 188531439867194996432279)
                  ·
                    rfl

theorem cell23_3304473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 2, 7].length) (baseStart_3304473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3304473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3304473 prefixEnd_3304473 := by exact prefixLift 3304473
  have htrace : WordTrace (prefixWord ++ tailWord_3304473) baseStart_3304473 baseEnd_3304473 := by
    simpa [prefixWord, tailWord_3304473, baseEnd_3304473] using wordTrace_append hprefix tailTrace_3304473
  have hstable : (prefixWord ++ tailWord_3304473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3304473).length < 2 ^ (prefixWord ++ tailWord_3304473).sum := by decide
  have hdescent : baseEnd_3304473 < baseStart_3304473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3304473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3304484 : List Nat := [2, 3, 1, 4, 1, 1, 1, 2, 4, 2, 2]
def baseStart_3304484 : Nat := 118140960795 + 3304484 * 2 ^ 59
def prefixEnd_3304484 : Nat := 4983230072969 + 3 ^ 40 * 3304484 * 2
def baseEnd_3304484 : Nat := 1696788607091954424852961

theorem tailTrace_3304484 : CollatzResearch.WordTrace tailWord_3304484 prefixEnd_3304484 1696788607091954424852961 := by
  unfold tailWord_3304484
  simp only [CollatzResearch.WordTrace]
  refine ⟨60262216480213151890620253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80349621973617535854160337 60262216480213151890620253)
  ·
    refine ⟨22598331180079931958982595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60262216480213151890620253 22598331180079931958982595)
    ·
      refine ⟨33897496770119897938473893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22598331180079931958982595 33897496770119897938473893)
      ·
        refine ⟨6355780644397480863463855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33897496770119897938473893 6355780644397480863463855)
        ·
          refine ⟨9533670966596221295195783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6355780644397480863463855 9533670966596221295195783)
          ·
            refine ⟨14300506449894331942793675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9533670966596221295195783 14300506449894331942793675)
            ·
              refine ⟨21450759674841497914190513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14300506449894331942793675 21450759674841497914190513)
              ·
                refine ⟨16088069756131123435642885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21450759674841497914190513 16088069756131123435642885)
                ·
                  refine ⟨3016513079274585644183041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16088069756131123435642885 3016513079274585644183041)
                  ·
                    refine ⟨2262384809455939233137281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3016513079274585644183041 2262384809455939233137281)
                    ·
                      refine ⟨1696788607091954424852961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2262384809455939233137281 1696788607091954424852961)
                      ·
                        rfl

theorem cell23_3304484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 2, 4, 2, 2].length) (baseStart_3304484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3304484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3304484 prefixEnd_3304484 := by exact prefixLift 3304484
  have htrace : WordTrace (prefixWord ++ tailWord_3304484) baseStart_3304484 baseEnd_3304484 := by
    simpa [prefixWord, tailWord_3304484, baseEnd_3304484] using wordTrace_append hprefix tailTrace_3304484
  have hstable : (prefixWord ++ tailWord_3304484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3304484).length < 2 ^ (prefixWord ++ tailWord_3304484).sum := by decide
  have hdescent : baseEnd_3304484 < baseStart_3304484 := by decide
  rcases family_descends (prefixWord ++ tailWord_3304484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3304487 : List Nat := [1, 1, 7, 1, 1, 2, 1, 1, 2, 1, 5]
def baseStart_3304487 : Nat := 118140960795 + 3304487 * 2 ^ 59
def prefixEnd_3304487 : Nat := 4983230072969 + 3 ^ 40 * 3304487 * 2
def baseEnd_3304487 : Nat := 1696790147533917913115447

theorem tailTrace_3304487 : CollatzResearch.WordTrace tailWord_3304487 prefixEnd_3304487 1696790147533917913115447 := by
  unfold tailWord_3304487
  simp only [CollatzResearch.WordTrace]
  refine ⟨120524542379415435293599715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80349694919610290195733143 120524542379415435293599715)
  ·
    refine ⟨180786813569123152940399573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120524542379415435293599715 180786813569123152940399573)
    ·
      refine ⟨4237190943026323897040615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 180786813569123152940399573 4237190943026323897040615)
      ·
        refine ⟨6355786414539485845560923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4237190943026323897040615 6355786414539485845560923)
        ·
          refine ⟨9533679621809228768341385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6355786414539485845560923 9533679621809228768341385)
          ·
            refine ⟨7150259716356921576256039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9533679621809228768341385 7150259716356921576256039)
            ·
              refine ⟨10725389574535382364384059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7150259716356921576256039 10725389574535382364384059)
              ·
                refine ⟨16088084361803073546576089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10725389574535382364384059 16088084361803073546576089)
                ·
                  refine ⟨12066063271352305159932067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16088084361803073546576089 12066063271352305159932067)
                  ·
                    refine ⟨18099094907028457739898101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12066063271352305159932067 18099094907028457739898101)
                    ·
                      refine ⟨1696790147533917913115447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18099094907028457739898101 1696790147533917913115447)
                      ·
                        rfl

theorem cell23_3304487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_3304487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3304487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3304487 prefixEnd_3304487 := by exact prefixLift 3304487
  have htrace : WordTrace (prefixWord ++ tailWord_3304487) baseStart_3304487 baseEnd_3304487 := by
    simpa [prefixWord, tailWord_3304487, baseEnd_3304487] using wordTrace_append hprefix tailTrace_3304487
  have hstable : (prefixWord ++ tailWord_3304487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3304487).length < 2 ^ (prefixWord ++ tailWord_3304487).sum := by decide
  have hdescent : baseEnd_3304487 < baseStart_3304487 := by decide
  rcases family_descends (prefixWord ++ tailWord_3304487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3304518 : List Nat := [6, 1, 1, 1, 1, 3, 1, 3, 2, 2, 2]
def baseStart_3304518 : Nat := 118140960795 + 3304518 * 2 ^ 59
def prefixEnd_3304518 : Nat := 4983230072969 + 3 ^ 40 * 3304518 * 2
def baseEnd_3304518 : Nat := 1696806065434207291827805

theorem tailTrace_3304518 : CollatzResearch.WordTrace tailWord_3304518 prefixEnd_3304518 1696806065434207291827805 := by
  unfold tailWord_3304518
  simp only [CollatzResearch.WordTrace]
  refine ⟨3766427282571972737124319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 80350448694868751725318805 3766427282571972737124319)
  ·
    refine ⟨5649640923857959105686479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3766427282571972737124319 5649640923857959105686479)
    ·
      refine ⟨8474461385786938658529719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5649640923857959105686479 8474461385786938658529719)
      ·
        refine ⟨12711692078680407987794579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8474461385786938658529719 12711692078680407987794579)
        ·
          refine ⟨19067538118020611981691869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12711692078680407987794579 19067538118020611981691869)
          ·
            refine ⟨7150326794257729493134451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19067538118020611981691869 7150326794257729493134451)
            ·
              refine ⟨10725490191386594239701677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7150326794257729493134451 10725490191386594239701677)
              ·
                refine ⟨4022058821769972839888129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10725490191386594239701677 4022058821769972839888129)
                ·
                  refine ⟨3016544116327479629916097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4022058821769972839888129 3016544116327479629916097)
                  ·
                    refine ⟨2262408087245609722437073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3016544116327479629916097 2262408087245609722437073)
                    ·
                      refine ⟨1696806065434207291827805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2262408087245609722437073 1696806065434207291827805)
                      ·
                        rfl

theorem cell23_3304518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 3, 2, 2, 2].length) (baseStart_3304518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3304518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3304518 prefixEnd_3304518 := by exact prefixLift 3304518
  have htrace : WordTrace (prefixWord ++ tailWord_3304518) baseStart_3304518 baseEnd_3304518 := by
    simpa [prefixWord, tailWord_3304518, baseEnd_3304518] using wordTrace_append hprefix tailTrace_3304518
  have hstable : (prefixWord ++ tailWord_3304518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3304518).length < 2 ^ (prefixWord ++ tailWord_3304518).sum := by decide
  have hdescent : baseEnd_3304518 < baseStart_3304518 := by decide
  rcases family_descends (prefixWord ++ tailWord_3304518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3304557 : List Nat := [1, 5, 1, 1, 2, 2, 2, 2, 2, 1, 4]
def baseStart_3304557 : Nat := 118140960795 + 3304557 * 2 ^ 59
def prefixEnd_3304557 : Nat := 4983230072969 + 3 ^ 40 * 3304557 * 2
def baseEnd_3304557 : Nat := 1696826091179732639240125

theorem tailTrace_3304557 : CollatzResearch.WordTrace tailWord_3304557 prefixEnd_3304557 1696826091179732639240125 := by
  unfold tailWord_3304557
  simp only [CollatzResearch.WordTrace]
  refine ⟨120527095489161837248647925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80351396992774558165765283 120527095489161837248647925)
  ·
    refine ⟨11299415202108922242060743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 120527095489161837248647925 11299415202108922242060743)
    ·
      refine ⟨16949122803163383363091115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11299415202108922242060743 16949122803163383363091115)
      ·
        refine ⟨25423684204745075044636673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16949122803163383363091115 25423684204745075044636673)
        ·
          refine ⟨19067763153558806283477505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25423684204745075044636673 19067763153558806283477505)
          ·
            refine ⟨14300822365169104712608129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19067763153558806283477505 14300822365169104712608129)
            ·
              refine ⟨10725616773876828534456097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14300822365169104712608129 10725616773876828534456097)
              ·
                refine ⟨8044212580407621400842073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10725616773876828534456097 8044212580407621400842073)
                ·
                  refine ⟨6033159435305716050631555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8044212580407621400842073 6033159435305716050631555)
                  ·
                    refine ⟨9049739152958574075947333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6033159435305716050631555 9049739152958574075947333)
                    ·
                      refine ⟨1696826091179732639240125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9049739152958574075947333 1696826091179732639240125)
                      ·
                        rfl

theorem cell23_3304557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 2, 2, 1, 4].length) (baseStart_3304557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3304557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3304557 prefixEnd_3304557 := by exact prefixLift 3304557
  have htrace : WordTrace (prefixWord ++ tailWord_3304557) baseStart_3304557 baseEnd_3304557 := by
    simpa [prefixWord, tailWord_3304557, baseEnd_3304557] using wordTrace_append hprefix tailTrace_3304557
  have hstable : (prefixWord ++ tailWord_3304557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3304557).length < 2 ^ (prefixWord ++ tailWord_3304557).sum := by decide
  have hdescent : baseEnd_3304557 < baseStart_3304557 := by decide
  rcases family_descends (prefixWord ++ tailWord_3304557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3304584 : List Nat := [2, 1, 3, 4, 2, 1, 1, 2, 3, 4]
def baseStart_3304584 : Nat := 118140960795 + 3304584 * 2 ^ 59
def prefixEnd_3304584 : Nat := 4983230072969 + 3 ^ 40 * 3304584 * 2
def baseEnd_3304584 : Nat := 565613318385801344534167

theorem tailTrace_3304584 : CollatzResearch.WordTrace tailWord_3304584 prefixEnd_3304584 565613318385801344534167 := by
  unfold tailWord_3304584
  simp only [CollatzResearch.WordTrace]
  refine ⟨60264040130032010429940403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80352053506709347239920537 60264040130032010429940403)
  ·
    refine ⟨90396060195048015644910605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60264040130032010429940403 90396060195048015644910605)
    ·
      refine ⟨33898522573143005866841477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90396060195048015644910605 33898522573143005866841477)
      ·
        refine ⟨6355972982464313600032777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33898522573143005866841477 6355972982464313600032777)
        ·
          refine ⟨4766979736848235200024583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6355972982464313600032777 4766979736848235200024583)
          ·
            refine ⟨7150469605272352800036875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4766979736848235200024583 7150469605272352800036875)
            ·
              refine ⟨10725704407908529200055313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7150469605272352800036875 10725704407908529200055313)
              ·
                refine ⟨8044278305931396900041485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10725704407908529200055313 8044278305931396900041485)
                ·
                  refine ⟨3016604364724273837515557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8044278305931396900041485 3016604364724273837515557)
                  ·
                    refine ⟨565613318385801344534167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3016604364724273837515557 565613318385801344534167)
                    ·
                      rfl

theorem cell23_3304584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 2, 3, 4].length) (baseStart_3304584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3304584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3304584 prefixEnd_3304584 := by exact prefixLift 3304584
  have htrace : WordTrace (prefixWord ++ tailWord_3304584) baseStart_3304584 baseEnd_3304584 := by
    simpa [prefixWord, tailWord_3304584, baseEnd_3304584] using wordTrace_append hprefix tailTrace_3304584
  have hstable : (prefixWord ++ tailWord_3304584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3304584).length < 2 ^ (prefixWord ++ tailWord_3304584).sum := by decide
  have hdescent : baseEnd_3304584 < baseStart_3304584 := by decide
  rcases family_descends (prefixWord ++ tailWord_3304584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3304594 : List Nat := [3, 2, 3, 1, 1, 2, 3, 1, 2, 2, 3]
def baseStart_3304594 : Nat := 118140960795 + 3304594 * 2 ^ 59
def prefixEnd_3304594 : Nat := 4983230072969 + 3 ^ 40 * 3304594 * 2
def baseEnd_3304594 : Nat := 1696845089963948994477455

theorem tailTrace_3304594 : CollatzResearch.WordTrace tailWord_3304594 prefixEnd_3304594 1696845089963948994477455 := by
  unfold tailWord_3304594
  simp only [CollatzResearch.WordTrace]
  refine ⟨30132111247506948141936209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80352296660018528378496557 30132111247506948141936209)
  ·
    refine ⟨22599083435630211106452157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30132111247506948141936209 22599083435630211106452157)
    ·
      refine ⟨8474656288361329164919559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22599083435630211106452157 8474656288361329164919559)
      ·
        refine ⟨12711984432541993747379339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8474656288361329164919559 12711984432541993747379339)
        ·
          refine ⟨19067976648812990621069009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12711984432541993747379339 19067976648812990621069009)
          ·
            refine ⟨14300982486609742965801757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19067976648812990621069009 14300982486609742965801757)
            ·
              refine ⟨5362868432478653612175659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14300982486609742965801757 5362868432478653612175659)
              ·
                refine ⟨8044302648717980418263489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5362868432478653612175659 8044302648717980418263489)
                ·
                  refine ⟨6033226986538485313697617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8044302648717980418263489 6033226986538485313697617)
                  ·
                    refine ⟨4524920239903863985273213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6033226986538485313697617 4524920239903863985273213)
                    ·
                      refine ⟨1696845089963948994477455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4524920239903863985273213 1696845089963948994477455)
                      ·
                        rfl

theorem cell23_3304594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3, 1, 2, 2, 3].length) (baseStart_3304594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3304594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3304594 prefixEnd_3304594 := by exact prefixLift 3304594
  have htrace : WordTrace (prefixWord ++ tailWord_3304594) baseStart_3304594 baseEnd_3304594 := by
    simpa [prefixWord, tailWord_3304594, baseEnd_3304594] using wordTrace_append hprefix tailTrace_3304594
  have hstable : (prefixWord ++ tailWord_3304594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3304594).length < 2 ^ (prefixWord ++ tailWord_3304594).sum := by decide
  have hdescent : baseEnd_3304594 < baseStart_3304594 := by decide
  rcases family_descends (prefixWord ++ tailWord_3304594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3304641 : List Nat := [1, 2, 6, 1, 1, 1, 2, 2, 3, 1, 3]
def baseStart_3304641 : Nat := 118140960795 + 3304641 * 2 ^ 59
def prefixEnd_3304641 : Nat := 4983230072969 + 3 ^ 40 * 3304641 * 2
def baseEnd_3304641 : Nat := 1696869223554710310589739

theorem tailTrace_3304641 : CollatzResearch.WordTrace tailWord_3304641 prefixEnd_3304641 1696869223554710310589739 := by
  unfold tailWord_3304641
  simp only [CollatzResearch.WordTrace]
  refine ⟨120530159220857519594705777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80353439480571679729803851 120530159220857519594705777)
  ·
    refine ⟨90397619415643139696029333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120530159220857519594705777 90397619415643139696029333)
    ·
      refine ⟨4237388410108272173251375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 90397619415643139696029333 4237388410108272173251375)
      ·
        refine ⟨6356082615162408259877063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4237388410108272173251375 6356082615162408259877063)
        ·
          refine ⟨9534123922743612389815595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6356082615162408259877063 9534123922743612389815595)
          ·
            refine ⟨14301185884115418584723393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9534123922743612389815595 14301185884115418584723393)
            ·
              refine ⟨10725889413086563938542545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14301185884115418584723393 10725889413086563938542545)
              ·
                refine ⟨8044417059814922953906909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10725889413086563938542545 8044417059814922953906909)
                ·
                  refine ⟨3016656397430596107715091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8044417059814922953906909 3016656397430596107715091)
                  ·
                    refine ⟨4524984596145894161572637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3016656397430596107715091 4524984596145894161572637)
                    ·
                      refine ⟨1696869223554710310589739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4524984596145894161572637 1696869223554710310589739)
                      ·
                        rfl

theorem cell23_3304641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_3304641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3304641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3304641 prefixEnd_3304641 := by exact prefixLift 3304641
  have htrace : WordTrace (prefixWord ++ tailWord_3304641) baseStart_3304641 baseEnd_3304641 := by
    simpa [prefixWord, tailWord_3304641, baseEnd_3304641] using wordTrace_append hprefix tailTrace_3304641
  have hstable : (prefixWord ++ tailWord_3304641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3304641).length < 2 ^ (prefixWord ++ tailWord_3304641).sum := by decide
  have hdescent : baseEnd_3304641 < baseStart_3304641 := by decide
  rcases family_descends (prefixWord ++ tailWord_3304641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3304687 : List Nat := [1, 1, 2, 1, 7, 1, 2, 8]
def baseStart_3304687 : Nat := 118140960795 + 3304687 * 2 ^ 59
def prefixEnd_3304687 : Nat := 4983230072969 + 3 ^ 40 * 3304687 * 2
def baseEnd_3304687 : Nat := 62847883098696930763501

theorem tailTrace_3304687 : CollatzResearch.WordTrace tailWord_3304687 prefixEnd_3304687 62847883098696930763501 := by
  unfold tailWord_3304687
  simp only [CollatzResearch.WordTrace]
  refine ⟨120531836978690869450880315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80354557985793912967253543 120531836978690869450880315)
  ·
    refine ⟨180797755468036304176320473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120531836978690869450880315 180797755468036304176320473)
    ·
      refine ⟨135598316601027228132240355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180797755468036304176320473 135598316601027228132240355)
      ·
        refine ⟨203397474901540842198360533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135598316601027228132240355 203397474901540842198360533)
        ·
          refine ⟨4767128318004863489024075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 203397474901540842198360533 4767128318004863489024075)
          ·
            refine ⟨7150692477007295233536113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4767128318004863489024075 7150692477007295233536113)
            ·
              refine ⟨5363019357755471425152085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7150692477007295233536113 5363019357755471425152085)
              ·
                refine ⟨62847883098696930763501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5363019357755471425152085 62847883098696930763501)
                ·
                  rfl

theorem cell23_3304687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 2, 8].length) (baseStart_3304687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3304687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3304687 prefixEnd_3304687 := by exact prefixLift 3304687
  have htrace : WordTrace (prefixWord ++ tailWord_3304687) baseStart_3304687 baseEnd_3304687 := by
    simpa [prefixWord, tailWord_3304687, baseEnd_3304687] using wordTrace_append hprefix tailTrace_3304687
  have hstable : (prefixWord ++ tailWord_3304687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3304687).length < 2 ^ (prefixWord ++ tailWord_3304687).sum := by decide
  have hdescent : baseEnd_3304687 < baseStart_3304687 := by decide
  rcases family_descends (prefixWord ++ tailWord_3304687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3304691 : List Nat := [1, 1, 1, 2, 2, 7, 2, 1, 2, 4]
def baseStart_3304691 : Nat := 118140960795 + 3304691 * 2 ^ 59
def prefixEnd_3304691 : Nat := 4983230072969 + 3 ^ 40 * 3304691 * 2
def baseEnd_3304691 : Nat := 565631632529145038321503

theorem tailTrace_3304691 : CollatzResearch.WordTrace tailWord_3304691 prefixEnd_3304691 565631632529145038321503 := by
  unfold tailWord_3304691
  simp only [CollatzResearch.WordTrace]
  refine ⟨120531982870676378134025927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80354655247117585422683951 120531982870676378134025927)
  ·
    refine ⟨180797974306014567201038891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120531982870676378134025927 180797974306014567201038891)
    ·
      refine ⟨271196961459021850801558337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180797974306014567201038891 271196961459021850801558337)
      ·
        refine ⟨203397721094266388101168753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 271196961459021850801558337 203397721094266388101168753)
        ·
          refine ⟨152548290820699791075876565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203397721094266388101168753 152548290820699791075876565)
          ·
            refine ⟨3575350566110151353340857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 152548290820699791075876565 3575350566110151353340857)
            ·
              refine ⟨2681512924582613515005643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3575350566110151353340857 2681512924582613515005643)
              ·
                refine ⟨4022269386873920272508465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2681512924582613515005643 4022269386873920272508465)
                ·
                  refine ⟨3016702040155440204381349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4022269386873920272508465 3016702040155440204381349)
                  ·
                    refine ⟨565631632529145038321503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3016702040155440204381349 565631632529145038321503)
                    ·
                      rfl

theorem cell23_3304691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 2, 1, 2, 4].length) (baseStart_3304691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3304691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3304691 prefixEnd_3304691 := by exact prefixLift 3304691
  have htrace : WordTrace (prefixWord ++ tailWord_3304691) baseStart_3304691 baseEnd_3304691 := by
    simpa [prefixWord, tailWord_3304691, baseEnd_3304691] using wordTrace_append hprefix tailTrace_3304691
  have hstable : (prefixWord ++ tailWord_3304691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3304691).length < 2 ^ (prefixWord ++ tailWord_3304691).sum := by decide
  have hdescent : baseEnd_3304691 < baseStart_3304691 := by decide
  rcases family_descends (prefixWord ++ tailWord_3304691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3304697 : List Nat := [1, 2, 1, 3, 1, 1, 4, 3, 1, 3, 3]
def baseStart_3304697 : Nat := 118140960795 + 3304697 * 2 ^ 59
def prefixEnd_3304697 : Nat := 4983230072969 + 3 ^ 40 * 3304697 * 2
def baseEnd_3304697 : Nat := 1696897978471362091489481

theorem tailTrace_3304697 : CollatzResearch.WordTrace tailWord_3304697 prefixEnd_3304697 1696897978471362091489481 := by
  unfold tailWord_3304697
  simp only [CollatzResearch.WordTrace]
  refine ⟨120532201708654641158744345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80354801139103094105829563 120532201708654641158744345)
  ·
    refine ⟨90399151281490980869058259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120532201708654641158744345 90399151281490980869058259)
    ·
      refine ⟨135598726922236471303587389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90399151281490980869058259 135598726922236471303587389)
      ·
        refine ⟨50849522595838676738845271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135598726922236471303587389 50849522595838676738845271)
        ·
          refine ⟨76274283893758015108267907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50849522595838676738845271 76274283893758015108267907)
          ·
            refine ⟨114411425840637022662401861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76274283893758015108267907 114411425840637022662401861)
            ·
              refine ⟨21452142345119441749200349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 114411425840637022662401861 21452142345119441749200349)
              ·
                refine ⟨8044553379419790655950131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21452142345119441749200349 8044553379419790655950131)
                ·
                  refine ⟨12066830069129685983925197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8044553379419790655950131 12066830069129685983925197)
                  ·
                    refine ⟨4525061275923632243971949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12066830069129685983925197 4525061275923632243971949)
                    ·
                      refine ⟨1696897978471362091489481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4525061275923632243971949 1696897978471362091489481)
                      ·
                        rfl

theorem cell23_3304697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 3, 1, 3, 3].length) (baseStart_3304697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3304697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3304697 prefixEnd_3304697 := by exact prefixLift 3304697
  have htrace : WordTrace (prefixWord ++ tailWord_3304697) baseStart_3304697 baseEnd_3304697 := by
    simpa [prefixWord, tailWord_3304697, baseEnd_3304697] using wordTrace_append hprefix tailTrace_3304697
  have hstable : (prefixWord ++ tailWord_3304697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3304697).length < 2 ^ (prefixWord ++ tailWord_3304697).sum := by decide
  have hdescent : baseEnd_3304697 < baseStart_3304697 := by decide
  rcases family_descends (prefixWord ++ tailWord_3304697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3304787 : List Nat := [1, 1, 1, 2, 1, 1, 5, 1, 4, 3, 3]
def baseStart_3304787 : Nat := 118140960795 + 3304787 * 2 ^ 59
def prefixEnd_3304787 : Nat := 4983230072969 + 3 ^ 40 * 3304787 * 2
def baseEnd_3304787 : Nat := 1696944191730266739364067

theorem tailTrace_3304787 : CollatzResearch.WordTrace tailWord_3304787 prefixEnd_3304787 1696944191730266739364067 := by
  unfold tailWord_3304787
  simp only [CollatzResearch.WordTrace]
  refine ⟨120535484278328586529520615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80356989518885724353013743 120535484278328586529520615)
  ·
    refine ⟨180803226417492879794280923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120535484278328586529520615 180803226417492879794280923)
    ·
      refine ⟨271204839626239319691421385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180803226417492879794280923 271204839626239319691421385)
      ·
        refine ⟨203403629719679489768566039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 271204839626239319691421385 203403629719679489768566039)
        ·
          refine ⟨305105444579519234652849059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203403629719679489768566039 305105444579519234652849059)
          ·
            refine ⟨457658166869278851979273589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 305105444579519234652849059 457658166869278851979273589)
            ·
              refine ⟨42905453143994892373056899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 457658166869278851979273589 42905453143994892373056899)
              ·
                refine ⟨64358179715992338559585349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42905453143994892373056899 64358179715992338559585349)
                ·
                  refine ⟨12067158696748563479922253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64358179715992338559585349 12067158696748563479922253)
                  ·
                    refine ⟨4525184511280711304970845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12067158696748563479922253 4525184511280711304970845)
                    ·
                      refine ⟨1696944191730266739364067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4525184511280711304970845 1696944191730266739364067)
                      ·
                        rfl

theorem cell23_3304787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 4, 3, 3].length) (baseStart_3304787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3304787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3304787 prefixEnd_3304787 := by exact prefixLift 3304787
  have htrace : WordTrace (prefixWord ++ tailWord_3304787) baseStart_3304787 baseEnd_3304787 := by
    simpa [prefixWord, tailWord_3304787, baseEnd_3304787] using wordTrace_append hprefix tailTrace_3304787
  have hstable : (prefixWord ++ tailWord_3304787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3304787).length < 2 ^ (prefixWord ++ tailWord_3304787).sum := by decide
  have hdescent : baseEnd_3304787 < baseStart_3304787 := by decide
  rcases family_descends (prefixWord ++ tailWord_3304787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3304794 : List Nat := [3, 1, 1, 2, 1, 2, 4, 4, 5]
def baseStart_3304794 : Nat := 118140960795 + 3304794 * 2 ^ 59
def prefixEnd_3304794 : Nat := 4983230072969 + 3 ^ 40 * 3304794 * 2
def baseEnd_3304794 : Nat := 188549754010538690219615

theorem tailTrace_3304794 : CollatzResearch.WordTrace tailWord_3304794 prefixEnd_3304794 188549754010538690219615 := by
  unfold tailWord_3304794
  simp only [CollatzResearch.WordTrace]
  refine ⟨30133934897325806681256359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80357159726202151150016957 30133934897325806681256359)
  ·
    refine ⟨45200902345988710021884539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30133934897325806681256359 45200902345988710021884539)
    ·
      refine ⟨67801353518983065032826809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45200902345988710021884539 67801353518983065032826809)
      ·
        refine ⟨50851015139237298774620107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67801353518983065032826809 50851015139237298774620107)
        ·
          refine ⟨76276522708855948161930161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50851015139237298774620107 76276522708855948161930161)
          ·
            refine ⟨57207392031641961121447621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76276522708855948161930161 57207392031641961121447621)
            ·
              refine ⟨10726386005932867710271429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57207392031641961121447621 10726386005932867710271429)
              ·
                refine ⟨2011197376112412695675893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10726386005932867710271429 2011197376112412695675893)
                ·
                  refine ⟨188549754010538690219615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2011197376112412695675893 188549754010538690219615)
                  ·
                    rfl

theorem cell23_3304794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 4, 5].length) (baseStart_3304794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3304794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3304794 prefixEnd_3304794 := by exact prefixLift 3304794
  have htrace : WordTrace (prefixWord ++ tailWord_3304794) baseStart_3304794 baseEnd_3304794 := by
    simpa [prefixWord, tailWord_3304794, baseEnd_3304794] using wordTrace_append hprefix tailTrace_3304794
  have hstable : (prefixWord ++ tailWord_3304794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3304794).length < 2 ^ (prefixWord ++ tailWord_3304794).sum := by decide
  have hdescent : baseEnd_3304794 < baseStart_3304794 := by decide
  rcases family_descends (prefixWord ++ tailWord_3304794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3304804 : List Nat := [2, 3, 1, 1, 3, 2, 2, 1, 2, 3, 3]
def baseStart_3304804 : Nat := 118140960795 + 3304804 * 2 ^ 59
def prefixEnd_3304804 : Nat := 4983230072969 + 3 ^ 40 * 3304804 * 2
def baseEnd_3304804 : Nat := 1696952920901393172851489

theorem tailTrace_3304804 : CollatzResearch.WordTrace tailWord_3304804 prefixEnd_3304804 1696952920901393172851489 := by
  unfold tailWord_3304804
  simp only [CollatzResearch.WordTrace]
  refine ⟨60268052159633499216444733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80357402879511332288592977 60268052159633499216444733)
  ·
    refine ⟨22600519559862562206166775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60268052159633499216444733 22600519559862562206166775)
    ·
      refine ⟨33900779339793843309250163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22600519559862562206166775 33900779339793843309250163)
      ·
        refine ⟨50851169009690764963875245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33900779339793843309250163 50851169009690764963875245)
        ·
          refine ⟨19069188378634036861453217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50851169009690764963875245 19069188378634036861453217)
          ·
            refine ⟨14301891283975527646089913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19069188378634036861453217 14301891283975527646089913)
            ·
              refine ⟨10726418462981645734567435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14301891283975527646089913 10726418462981645734567435)
              ·
                refine ⟨16089627694472468601851153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10726418462981645734567435 16089627694472468601851153)
                ·
                  refine ⟨12067220770854351451388365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16089627694472468601851153 12067220770854351451388365)
                  ·
                    refine ⟨4525207789070381794270637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12067220770854351451388365 4525207789070381794270637)
                    ·
                      refine ⟨1696952920901393172851489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4525207789070381794270637 1696952920901393172851489)
                      ·
                        rfl

theorem cell23_3304804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 1, 2, 3, 3].length) (baseStart_3304804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3304804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3304804 prefixEnd_3304804 := by exact prefixLift 3304804
  have htrace : WordTrace (prefixWord ++ tailWord_3304804) baseStart_3304804 baseEnd_3304804 := by
    simpa [prefixWord, tailWord_3304804, baseEnd_3304804] using wordTrace_append hprefix tailTrace_3304804
  have hstable : (prefixWord ++ tailWord_3304804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3304804).length < 2 ^ (prefixWord ++ tailWord_3304804).sum := by decide
  have hdescent : baseEnd_3304804 < baseStart_3304804 := by decide
  rcases family_descends (prefixWord ++ tailWord_3304804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
