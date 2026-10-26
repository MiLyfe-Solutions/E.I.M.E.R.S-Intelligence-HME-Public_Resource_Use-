import V185TrunkScan20Chunk095

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_582670 : List Nat := [4, 1, 1, 2, 2, 2, 2, 3, 3]
def baseStart_582670 : Nat := 118140960795 + 582670 * 2 ^ 59
def prefixEnd_582670 : Nat := 4983230072969 + 3 ^ 40 * 582670 * 2
def baseEnd_582670 : Nat := 265946464849191586351427

theorem tailTrace_582670 : CollatzResearch.WordTrace tailWord_582670 prefixEnd_582670 265946464849191586351427 := by
  unfold tailWord_582670
  simp only [CollatzResearch.WordTrace]
  refine ⟨2656465099886697119818183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14167813866062384639030309 2656465099886697119818183)
  ·
    refine ⟨3984697649830045679727275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2656465099886697119818183 3984697649830045679727275)
    ·
      refine ⟨5977046474745068519590913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3984697649830045679727275 5977046474745068519590913)
      ·
        refine ⟨4482784856058801389693185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5977046474745068519590913 4482784856058801389693185)
        ·
          refine ⟨3362088642044101042269889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4482784856058801389693185 3362088642044101042269889)
          ·
            refine ⟨2521566481533075781702417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3362088642044101042269889 2521566481533075781702417)
            ·
              refine ⟨1891174861149806836276813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2521566481533075781702417 1891174861149806836276813)
              ·
                refine ⟨709190572931177563603805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1891174861149806836276813 709190572931177563603805)
                ·
                  refine ⟨265946464849191586351427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 709190572931177563603805 265946464849191586351427)
                  ·
                    rfl

theorem cell20_582670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 3, 3].length) (baseStart_582670 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_582670 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_582670 prefixEnd_582670 := by exact prefixLift 582670
  have htrace : WordTrace (prefixWord ++ tailWord_582670) baseStart_582670 baseEnd_582670 := by
    simpa [prefixWord, tailWord_582670, baseEnd_582670] using wordTrace_append hprefix tailTrace_582670
  have hstable : (prefixWord ++ tailWord_582670).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582670).length < 2 ^ (prefixWord ++ tailWord_582670).sum := by decide
  have hdescent : baseEnd_582670 < baseStart_582670 := by decide
  rcases family_descends (prefixWord ++ tailWord_582670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582677 : List Nat := [1, 3, 2, 1, 4, 2, 1, 2, 4]
def baseStart_582677 : Nat := 118140960795 + 582677 * 2 ^ 59
def prefixEnd_582677 : Nat := 4983230072969 + 3 ^ 40 * 582677 * 2
def baseEnd_582677 : Nat := 265949659839930673118065

theorem tailTrace_582677 : CollatzResearch.WordTrace tailWord_582677 prefixEnd_582677 265949659839930673118065 := by
  unfold tailWord_582677
  simp only [CollatzResearch.WordTrace]
  refine ⟨21251976110068217154050285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14167984073378811436033523 21251976110068217154050285)
  ·
    refine ⟨7969491041275581432768857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21251976110068217154050285 7969491041275581432768857)
    ·
      refine ⟨5977118280956686074576643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7969491041275581432768857 5977118280956686074576643)
      ·
        refine ⟨8965677421435029111864965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5977118280956686074576643 8965677421435029111864965)
        ·
          refine ⟨1681064516519067958474681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8965677421435029111864965 1681064516519067958474681)
          ·
            refine ⟨1260798387389300968856011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1681064516519067958474681 1260798387389300968856011)
            ·
              refine ⟨1891197581083951453284017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1260798387389300968856011 1891197581083951453284017)
              ·
                refine ⟨1418398185812963589963013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1891197581083951453284017 1418398185812963589963013)
                ·
                  refine ⟨265949659839930673118065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1418398185812963589963013 265949659839930673118065)
                  ·
                    rfl

theorem cell20_582677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 2, 4].length) (baseStart_582677 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_582677 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_582677 prefixEnd_582677 := by exact prefixLift 582677
  have htrace : WordTrace (prefixWord ++ tailWord_582677) baseStart_582677 baseEnd_582677 := by
    simpa [prefixWord, tailWord_582677, baseEnd_582677] using wordTrace_append hprefix tailTrace_582677
  have hstable : (prefixWord ++ tailWord_582677).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582677).length < 2 ^ (prefixWord ++ tailWord_582677).sum := by decide
  have hdescent : baseEnd_582677 < baseStart_582677 := by decide
  rcases family_descends (prefixWord ++ tailWord_582677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582705 : List Nat := [1, 2, 2, 3, 1, 2, 9]
def baseStart_582705 : Nat := 118140960795 + 582705 * 2 ^ 59
def prefixEnd_582705 : Nat := 4983230072969 + 3 ^ 40 * 582705 * 2
def baseEnd_582705 : Nat := 29551382200320780020513

theorem tailTrace_582705 : CollatzResearch.WordTrace tailWord_582705 prefixEnd_582705 29551382200320780020513 := by
  unfold tailWord_582705
  simp only [CollatzResearch.WordTrace]
  refine ⟨21252997353966777936069569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14168664902644518624046379 21252997353966777936069569)
  ·
    refine ⟨15939748015475083452052177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21252997353966777936069569 15939748015475083452052177)
    ·
      refine ⟨11954811011606312589039133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15939748015475083452052177 11954811011606312589039133)
      ·
        refine ⟨4483054129352367220889675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11954811011606312589039133 4483054129352367220889675)
        ·
          refine ⟨6724581194028550831334513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4483054129352367220889675 6724581194028550831334513)
          ·
            refine ⟨5043435895521413123500885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6724581194028550831334513 5043435895521413123500885)
            ·
              refine ⟨29551382200320780020513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5043435895521413123500885 29551382200320780020513)
              ·
                rfl

theorem cell20_582705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 9].length) (baseStart_582705 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_582705 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_582705 prefixEnd_582705 := by exact prefixLift 582705
  have htrace : WordTrace (prefixWord ++ tailWord_582705) baseStart_582705 baseEnd_582705 := by
    simpa [prefixWord, tailWord_582705, baseEnd_582705] using wordTrace_append hprefix tailTrace_582705
  have hstable : (prefixWord ++ tailWord_582705).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582705).length < 2 ^ (prefixWord ++ tailWord_582705).sum := by decide
  have hdescent : baseEnd_582705 < baseStart_582705 := by decide
  rcases family_descends (prefixWord ++ tailWord_582705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582767 : List Nat := [1, 1, 2, 1, 3, 3, 2, 4, 3]
def baseStart_582767 : Nat := 118140960795 + 582767 * 2 ^ 59
def prefixEnd_582767 : Nat := 4983230072969 + 3 ^ 40 * 582767 * 2
def baseEnd_582767 : Nat := 265990738292290360117697

theorem tailTrace_582767 : CollatzResearch.WordTrace tailWord_582767 prefixEnd_582767 265990738292290360117697 := by
  unfold tailWord_582767
  simp only [CollatzResearch.WordTrace]
  refine ⟨21255258679742162524826555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14170172453161441683217703 21255258679742162524826555)
  ·
    refine ⟨31882888019613243787239833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21255258679742162524826555 31882888019613243787239833)
    ·
      refine ⟨23912166014709932840429875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31882888019613243787239833 23912166014709932840429875)
      ·
        refine ⟨35868249022064899260644813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23912166014709932840429875 35868249022064899260644813)
        ·
          refine ⟨13450593383274337222741805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35868249022064899260644813 13450593383274337222741805)
          ·
            refine ⟨5043972518727876458528177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13450593383274337222741805 5043972518727876458528177)
            ·
              refine ⟨3782979389045907343896133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5043972518727876458528177 3782979389045907343896133)
              ·
                refine ⟨709308635446107626980525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3782979389045907343896133 709308635446107626980525)
                ·
                  refine ⟨265990738292290360117697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 709308635446107626980525 265990738292290360117697)
                  ·
                    rfl

theorem cell20_582767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 4, 3].length) (baseStart_582767 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_582767 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_582767 prefixEnd_582767 := by exact prefixLift 582767
  have htrace : WordTrace (prefixWord ++ tailWord_582767) baseStart_582767 baseEnd_582767 := by
    simpa [prefixWord, tailWord_582767, baseEnd_582767] using wordTrace_append hprefix tailTrace_582767
  have hstable : (prefixWord ++ tailWord_582767).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582767).length < 2 ^ (prefixWord ++ tailWord_582767).sum := by decide
  have hdescent : baseEnd_582767 < baseStart_582767 := by decide
  rcases family_descends (prefixWord ++ tailWord_582767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582784 : List Nat := [2, 1, 1, 2, 1, 3, 6, 1, 3]
def baseStart_582784 : Nat := 118140960795 + 582784 * 2 ^ 59
def prefixEnd_582784 : Nat := 4983230072969 + 3 ^ 40 * 582784 * 2
def baseEnd_582784 : Nat := 265998497555513856550961

theorem tailTrace_582784 : CollatzResearch.WordTrace tailWord_582784 prefixEnd_582784 265998497555513856550961 := by
  unfold tailWord_582784
  simp only [CollatzResearch.WordTrace]
  refine ⟨10627939360340287214097703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14170585813787049618796937 10627939360340287214097703)
  ·
    refine ⟨15941909040510430821146555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10627939360340287214097703 15941909040510430821146555)
    ·
      refine ⟨23912863560765646231719833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15941909040510430821146555 23912863560765646231719833)
      ·
        refine ⟨17934647670574234673789875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23912863560765646231719833 17934647670574234673789875)
        ·
          refine ⟨26901971505861352010684813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17934647670574234673789875 26901971505861352010684813)
          ·
            refine ⟨10088239314698007004006805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26901971505861352010684813 10088239314698007004006805)
            ·
              refine ⟨472886217876469078312819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 10088239314698007004006805 472886217876469078312819)
              ·
                refine ⟨709329326814703617469229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 472886217876469078312819 709329326814703617469229)
                ·
                  refine ⟨265998497555513856550961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 709329326814703617469229 265998497555513856550961)
                  ·
                    rfl

theorem cell20_582784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 6, 1, 3].length) (baseStart_582784 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_582784 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_582784 prefixEnd_582784 := by exact prefixLift 582784
  have htrace : WordTrace (prefixWord ++ tailWord_582784) baseStart_582784 baseEnd_582784 := by
    simpa [prefixWord, tailWord_582784, baseEnd_582784] using wordTrace_append hprefix tailTrace_582784
  have hstable : (prefixWord ++ tailWord_582784).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582784).length < 2 ^ (prefixWord ++ tailWord_582784).sum := by decide
  have hdescent : baseEnd_582784 < baseStart_582784 := by decide
  rcases family_descends (prefixWord ++ tailWord_582784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582798 : List Nat := [4, 1, 1, 3, 2, 1, 2, 6]
def baseStart_582798 : Nat := 118140960795 + 582798 * 2 ^ 59
def prefixEnd_582798 : Nat := 4983230072969 + 3 ^ 40 * 582798 * 2
def baseEnd_582798 : Nat := 88668295845664010028079

theorem tailTrace_582798 : CollatzResearch.WordTrace tailWord_582798 prefixEnd_582798 88668295845664010028079 := by
  unfold tailWord_582798
  simp only [CollatzResearch.WordTrace]
  refine ⟨2657048667828731852400631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14170926228419903212803365 2657048667828731852400631)
  ·
    refine ⟨3985573001743097778600947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2657048667828731852400631 3985573001743097778600947)
    ·
      refine ⟨5978359502614646667901421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3985573001743097778600947 5978359502614646667901421)
      ·
        refine ⟨2241884813480492500463033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5978359502614646667901421 2241884813480492500463033)
        ·
          refine ⟨1681413610110369375347275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2241884813480492500463033 1681413610110369375347275)
          ·
            refine ⟨2522120415165554063020913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1681413610110369375347275 2522120415165554063020913)
            ·
              refine ⟨1891590311374165547265685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2522120415165554063020913 1891590311374165547265685)
              ·
                refine ⟨88668295845664010028079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1891590311374165547265685 88668295845664010028079)
                ·
                  rfl

theorem cell20_582798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 6].length) (baseStart_582798 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_582798 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_582798 prefixEnd_582798 := by exact prefixLift 582798
  have htrace : WordTrace (prefixWord ++ tailWord_582798) baseStart_582798 baseEnd_582798 := by
    simpa [prefixWord, tailWord_582798, baseEnd_582798] using wordTrace_append hprefix tailTrace_582798
  have hstable : (prefixWord ++ tailWord_582798).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582798).length < 2 ^ (prefixWord ++ tailWord_582798).sum := by decide
  have hdescent : baseEnd_582798 < baseStart_582798 := by decide
  rcases family_descends (prefixWord ++ tailWord_582798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582881 : List Nat := [1, 2, 3, 1, 3, 3, 1, 1, 5]
def baseStart_582881 : Nat := 118140960795 + 582881 * 2 ^ 59
def prefixEnd_582881 : Nat := 4983230072969 + 3 ^ 40 * 582881 * 2
def baseEnd_582881 : Nat := 266042770998612630317231

theorem tailTrace_582881 : CollatzResearch.WordTrace tailWord_582881 prefixEnd_582881 266042770998612630317231 := by
  unfold tailWord_582881
  simp only [CollatzResearch.WordTrace]
  refine ⟨21259416601329159994476497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14172944400886106662984331 21259416601329159994476497)
  ·
    refine ⟨15944562450996869995857373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21259416601329159994476497 15944562450996869995857373)
    ·
      refine ⟨5979210919123826248446515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15944562450996869995857373 5979210919123826248446515)
      ·
        refine ⟨8968816378685739372669773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5979210919123826248446515 8968816378685739372669773)
        ·
          refine ⟨3363306142007152264751165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8968816378685739372669773 3363306142007152264751165)
          ·
            refine ⟨1261239803252682099281687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3363306142007152264751165 1261239803252682099281687)
            ·
              refine ⟨1891859704879023148922531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1261239803252682099281687 1891859704879023148922531)
              ·
                refine ⟨2837789557318534723383797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1891859704879023148922531 2837789557318534723383797)
                ·
                  refine ⟨266042770998612630317231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2837789557318534723383797 266042770998612630317231)
                  ·
                    rfl

theorem cell20_582881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 1, 5].length) (baseStart_582881 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_582881 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_582881 prefixEnd_582881 := by exact prefixLift 582881
  have htrace : WordTrace (prefixWord ++ tailWord_582881) baseStart_582881 baseEnd_582881 := by
    simpa [prefixWord, tailWord_582881, baseEnd_582881] using wordTrace_append hprefix tailTrace_582881
  have hstable : (prefixWord ++ tailWord_582881).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582881).length < 2 ^ (prefixWord ++ tailWord_582881).sum := by decide
  have hdescent : baseEnd_582881 < baseStart_582881 := by decide
  rcases family_descends (prefixWord ++ tailWord_582881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582908 : List Nat := [2, 2, 2, 1, 6, 1, 2, 4]
def baseStart_582908 : Nat := 118140960795 + 582908 * 2 ^ 59
def prefixEnd_582908 : Nat := 4983230072969 + 3 ^ 40 * 582908 * 2
def baseEnd_582908 : Nat := 88685031511440178805707

theorem tailTrace_582908 : CollatzResearch.WordTrace tailWord_582908 prefixEnd_582908 88685031511440178805707 := by
  unfold tailWord_582908
  simp only [CollatzResearch.WordTrace]
  refine ⟨10630200686115671802854689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14173600914820895737139585 10630200686115671802854689)
  ·
    refine ⟨7972650514586753852141017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10630200686115671802854689 7972650514586753852141017)
    ·
      refine ⟨5979487885940065389105763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7972650514586753852141017 5979487885940065389105763)
      ·
        refine ⟨8969231828910098083658645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5979487885940065389105763 8969231828910098083658645)
        ·
          refine ⟨420432741980160847671499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 8969231828910098083658645 420432741980160847671499)
          ·
            refine ⟨630649112970241271507249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 420432741980160847671499 630649112970241271507249)
            ·
              refine ⟨472986834727680953630437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 630649112970241271507249 472986834727680953630437)
              ·
                refine ⟨88685031511440178805707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 472986834727680953630437 88685031511440178805707)
                ·
                  rfl

theorem cell20_582908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 2, 4].length) (baseStart_582908 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_582908 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_582908 prefixEnd_582908 := by exact prefixLift 582908
  have htrace : WordTrace (prefixWord ++ tailWord_582908) baseStart_582908 baseEnd_582908 := by
    simpa [prefixWord, tailWord_582908, baseEnd_582908] using wordTrace_append hprefix tailTrace_582908
  have hstable : (prefixWord ++ tailWord_582908).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582908).length < 2 ^ (prefixWord ++ tailWord_582908).sum := by decide
  have hdescent : baseEnd_582908 < baseStart_582908 := by decide
  rcases family_descends (prefixWord ++ tailWord_582908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_582995 : List Nat := [1, 1, 1, 2, 1, 1, 8, 2, 3]
def baseStart_582995 : Nat := 118140960795 + 582995 * 2 ^ 59
def prefixEnd_582995 : Nat := 4983230072969 + 3 ^ 40 * 582995 * 2
def baseEnd_582995 : Nat := 266094803704934900516765

theorem tailTrace_582995 : CollatzResearch.WordTrace tailWord_582995 prefixEnd_582995 266094803704934900516765 := by
  unfold tailWord_582995
  simp only [CollatzResearch.WordTrace]
  refine ⟨21263574522916157464126439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14175716348610771642750959 21263574522916157464126439)
  ·
    refine ⟨31895361784374236196189659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21263574522916157464126439 31895361784374236196189659)
    ·
      refine ⟨47843042676561354294284489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31895361784374236196189659 47843042676561354294284489)
      ·
        refine ⟨35882282007421015720713367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47843042676561354294284489 35882282007421015720713367)
        ·
          refine ⟨53823423011131523581070051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35882282007421015720713367 53823423011131523581070051)
          ·
            refine ⟨80735134516697285371605077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53823423011131523581070051 80735134516697285371605077)
            ·
              refine ⟨946114857617546312948497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 80735134516697285371605077 946114857617546312948497)
              ·
                refine ⟨709586143213159734711373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 946114857617546312948497 709586143213159734711373)
                ·
                  refine ⟨266094803704934900516765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 709586143213159734711373 266094803704934900516765)
                  ·
                    rfl

theorem cell20_582995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8, 2, 3].length) (baseStart_582995 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_582995 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_582995 prefixEnd_582995 := by exact prefixLift 582995
  have htrace : WordTrace (prefixWord ++ tailWord_582995) baseStart_582995 baseEnd_582995 := by
    simpa [prefixWord, tailWord_582995, baseEnd_582995] using wordTrace_append hprefix tailTrace_582995
  have hstable : (prefixWord ++ tailWord_582995).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_582995).length < 2 ^ (prefixWord ++ tailWord_582995).sum := by decide
  have hdescent : baseEnd_582995 < baseStart_582995 := by decide
  rcases family_descends (prefixWord ++ tailWord_582995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583022 : List Nat := [4, 1, 2, 4, 1, 1, 3, 4]
def baseStart_583022 : Nat := 118140960795 + 583022 * 2 ^ 59
def prefixEnd_583022 : Nat := 4983230072969 + 3 ^ 40 * 583022 * 2
def baseEnd_583022 : Nat := 88702375746880935538885

theorem tailTrace_583022 : CollatzResearch.WordTrace tailWord_583022 prefixEnd_583022 88702375746880935538885 := by
  unfold tailWord_583022
  simp only [CollatzResearch.WordTrace]
  refine ⟨2658069911727292634419915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14176372862545560716906213 2658069911727292634419915)
  ·
    refine ⟨3987104867590938951629873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2658069911727292634419915 3987104867590938951629873)
    ·
      refine ⟨2990328650693204213722405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3987104867590938951629873 2990328650693204213722405)
      ·
        refine ⟨560686622004975790072951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2990328650693204213722405 560686622004975790072951)
        ·
          refine ⟨841029933007463685109427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 560686622004975790072951 841029933007463685109427)
          ·
            refine ⟨1261544899511195527664141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 841029933007463685109427 1261544899511195527664141)
            ·
              refine ⟨473079337316698322874053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1261544899511195527664141 473079337316698322874053)
              ·
                refine ⟨88702375746880935538885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 473079337316698322874053 88702375746880935538885)
                ·
                  rfl

theorem cell20_583022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 3, 4].length) (baseStart_583022 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_583022 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_583022 prefixEnd_583022 := by exact prefixLift 583022
  have htrace : WordTrace (prefixWord ++ tailWord_583022) baseStart_583022 baseEnd_583022 := by
    simpa [prefixWord, tailWord_583022, baseEnd_583022] using wordTrace_append hprefix tailTrace_583022
  have hstable : (prefixWord ++ tailWord_583022).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583022).length < 2 ^ (prefixWord ++ tailWord_583022).sum := by decide
  have hdescent : baseEnd_583022 < baseStart_583022 := by decide
  rcases family_descends (prefixWord ++ tailWord_583022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583026 : List Nat := [3, 2, 1, 2, 1, 2, 5, 4]
def baseStart_583026 : Nat := 118140960795 + 583026 * 2 ^ 59
def prefixEnd_583026 : Nat := 4983230072969 + 3 ^ 40 * 583026 * 2
def baseEnd_583026 : Nat := 88702984316545523494435

theorem tailTrace_583026 : CollatzResearch.WordTrace tailWord_583026 prefixEnd_583026 88702984316545523494435 := by
  unfold tailWord_583026
  simp only [CollatzResearch.WordTrace]
  refine ⟨5316176296450962439626233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14176470123869233172336621 5316176296450962439626233)
  ·
    refine ⟨3987132222338221829719675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5316176296450962439626233 3987132222338221829719675)
    ·
      refine ⟨5980698333507332744579513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3987132222338221829719675 5980698333507332744579513)
      ·
        refine ⟨4485523750130499558434635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5980698333507332744579513 4485523750130499558434635)
        ·
          refine ⟨6728285625195749337651953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4485523750130499558434635 6728285625195749337651953)
          ·
            refine ⟨5046214218896812003238965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6728285625195749337651953 5046214218896812003238965)
            ·
              refine ⟨473082583021576125303653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5046214218896812003238965 473082583021576125303653)
              ·
                refine ⟨88702984316545523494435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 473082583021576125303653 88702984316545523494435)
                ·
                  rfl

theorem cell20_583026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 5, 4].length) (baseStart_583026 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_583026 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_583026 prefixEnd_583026 := by exact prefixLift 583026
  have htrace : WordTrace (prefixWord ++ tailWord_583026) baseStart_583026 baseEnd_583026 := by
    simpa [prefixWord, tailWord_583026, baseEnd_583026] using wordTrace_append hprefix tailTrace_583026
  have hstable : (prefixWord ++ tailWord_583026).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583026).length < 2 ^ (prefixWord ++ tailWord_583026).sum := by decide
  have hdescent : baseEnd_583026 < baseStart_583026 := by decide
  rcases family_descends (prefixWord ++ tailWord_583026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583047 : List Nat := [1, 1, 4, 2, 2, 3, 7]
def baseStart_583047 : Nat := 118140960795 + 583047 * 2 ^ 59
def prefixEnd_583047 : Nat := 4983230072969 + 3 ^ 40 * 583047 * 2
def baseEnd_583047 : Nat := 29568726435761536753691

theorem tailTrace_583047 : CollatzResearch.WordTrace tailWord_583047 prefixEnd_583047 29568726435761536753691 := by
  unfold tailWord_583047
  simp only [CollatzResearch.WordTrace]
  refine ⟨21265471118727770345019395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14176980745818513563346263 21265471118727770345019395)
  ·
    refine ⟨31898206678091655517529093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21265471118727770345019395 31898206678091655517529093)
    ·
      refine ⟨5980913752142185409536705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31898206678091655517529093 5980913752142185409536705)
      ·
        refine ⟨4485685314106639057152529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5980913752142185409536705 4485685314106639057152529)
        ·
          refine ⟨3364263985579979292864397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4485685314106639057152529 3364263985579979292864397)
          ·
            refine ⟨1261598994592492234824149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3364263985579979292864397 1261598994592492234824149)
            ·
              refine ⟨29568726435761536753691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1261598994592492234824149 29568726435761536753691)
              ·
                rfl

theorem cell20_583047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 7].length) (baseStart_583047 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_583047 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_583047 prefixEnd_583047 := by exact prefixLift 583047
  have htrace : WordTrace (prefixWord ++ tailWord_583047) baseStart_583047 baseEnd_583047 := by
    simpa [prefixWord, tailWord_583047, baseEnd_583047] using wordTrace_append hprefix tailTrace_583047
  have hstable : (prefixWord ++ tailWord_583047).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583047).length < 2 ^ (prefixWord ++ tailWord_583047).sum := by decide
  have hdescent : baseEnd_583047 < baseStart_583047 := by decide
  rcases family_descends (prefixWord ++ tailWord_583047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583112 : List Nat := [2, 1, 3, 1, 3, 1, 5, 2, 2]
def baseStart_583112 : Nat := 118140960795 + 583112 * 2 ^ 59
def prefixEnd_583112 : Nat := 4983230072969 + 3 ^ 40 * 583112 * 2
def baseEnd_583112 : Nat := 266148205693002493616287

theorem tailTrace_583112 : CollatzResearch.WordTrace tailWord_583112 prefixEnd_583112 266148205693002493616287 := by
  unfold tailWord_583112
  simp only [CollatzResearch.WordTrace]
  refine ⟨10633920931746143223067795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14178561242328190964090393 10633920931746143223067795)
  ·
    refine ⟨15950881397619214834601693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10633920931746143223067795 15950881397619214834601693)
    ·
      refine ⟨5981580524107205562975635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15950881397619214834601693 5981580524107205562975635)
      ·
        refine ⟨8972370786160808344463453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5981580524107205562975635 8972370786160808344463453)
        ·
          refine ⟨3364639044810303129173795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8972370786160808344463453 3364639044810303129173795)
          ·
            refine ⟨5046958567215454693760693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3364639044810303129173795 5046958567215454693760693)
            ·
              refine ⟨473152365676448877540065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5046958567215454693760693 473152365676448877540065)
              ·
                refine ⟨354864274257336658155049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 473152365676448877540065 354864274257336658155049)
                ·
                  refine ⟨266148205693002493616287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 354864274257336658155049 266148205693002493616287)
                  ·
                    rfl

theorem cell20_583112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 5, 2, 2].length) (baseStart_583112 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_583112 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_583112 prefixEnd_583112 := by exact prefixLift 583112
  have htrace : WordTrace (prefixWord ++ tailWord_583112) baseStart_583112 baseEnd_583112 := by
    simpa [prefixWord, tailWord_583112, baseEnd_583112] using wordTrace_append hprefix tailTrace_583112
  have hstable : (prefixWord ++ tailWord_583112).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583112).length < 2 ^ (prefixWord ++ tailWord_583112).sum := by decide
  have hdescent : baseEnd_583112 < baseStart_583112 := by decide
  rcases family_descends (prefixWord ++ tailWord_583112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583178 : List Nat := [3, 1, 2, 2, 2, 4, 1, 5]
def baseStart_583178 : Nat := 118140960795 + 583178 * 2 ^ 59
def prefixEnd_583178 : Nat := 4983230072969 + 3 ^ 40 * 583178 * 2
def baseEnd_583178 : Nat := 88726109963799865805339

theorem tailTrace_583178 : CollatzResearch.WordTrace tailWord_583178 prefixEnd_583178 88726109963799865805339 := by
  unfold tailWord_583178
  simp only [CollatzResearch.WordTrace]
  refine ⟨5317562270313294929509547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14180166054168786478692125 5317562270313294929509547)
  ·
    refine ⟨7976343405469942394264321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5317562270313294929509547 7976343405469942394264321)
    ·
      refine ⟨5982257554102456795698241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7976343405469942394264321 5982257554102456795698241)
      ·
        refine ⟨4486693165576842596773681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5982257554102456795698241 4486693165576842596773681)
        ·
          refine ⟨3365019874182631947580261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4486693165576842596773681 3365019874182631947580261)
          ·
            refine ⟨630941226409243490171299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3365019874182631947580261 630941226409243490171299)
            ·
              refine ⟨946411839613865235256949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 630941226409243490171299 946411839613865235256949)
              ·
                refine ⟨88726109963799865805339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 946411839613865235256949 88726109963799865805339)
                ·
                  rfl

theorem cell20_583178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 1, 5].length) (baseStart_583178 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_583178 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_583178 prefixEnd_583178 := by exact prefixLift 583178
  have htrace : WordTrace (prefixWord ++ tailWord_583178) baseStart_583178 baseEnd_583178 := by
    simpa [prefixWord, tailWord_583178, baseEnd_583178] using wordTrace_append hprefix tailTrace_583178
  have hstable : (prefixWord ++ tailWord_583178).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583178).length < 2 ^ (prefixWord ++ tailWord_583178).sum := by decide
  have hdescent : baseEnd_583178 < baseStart_583178 := by decide
  rcases family_descends (prefixWord ++ tailWord_583178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583188 : List Nat := [2, 4, 3, 1, 2, 1, 1, 2, 4]
def baseStart_583188 : Nat := 118140960795 + 583188 * 2 ^ 59
def prefixEnd_583188 : Nat := 4983230072969 + 3 ^ 40 * 583188 * 2
def baseEnd_583188 : Nat := 266182894163884007082643

theorem tailTrace_583188 : CollatzResearch.WordTrace tailWord_583188 prefixEnd_583188 266182894163884007082643 := by
  unfold tailWord_583188
  simp only [CollatzResearch.WordTrace]
  refine ⟨10635306905608475712951109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14180409207477967617268145 10635306905608475712951109)
  ·
    refine ⟨1994120044801589196178333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10635306905608475712951109 1994120044801589196178333)
    ·
      refine ⟨747795016800595948566875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1994120044801589196178333 747795016800595948566875)
      ·
        refine ⟨1121692525200893922850313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 747795016800595948566875 1121692525200893922850313)
        ·
          refine ⟨841269393900670442137735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1121692525200893922850313 841269393900670442137735)
          ·
            refine ⟨1261904090851005663206603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 841269393900670442137735 1261904090851005663206603)
            ·
              refine ⟨1892856136276508494809905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1261904090851005663206603 1892856136276508494809905)
              ·
                refine ⟨1419642102207381371107429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1892856136276508494809905 1419642102207381371107429)
                ·
                  refine ⟨266182894163884007082643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1419642102207381371107429 266182894163884007082643)
                  ·
                    rfl

theorem cell20_583188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 2, 4].length) (baseStart_583188 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_583188 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_583188 prefixEnd_583188 := by exact prefixLift 583188
  have htrace : WordTrace (prefixWord ++ tailWord_583188) baseStart_583188 baseEnd_583188 := by
    simpa [prefixWord, tailWord_583188, baseEnd_583188] using wordTrace_append hprefix tailTrace_583188
  have hstable : (prefixWord ++ tailWord_583188).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583188).length < 2 ^ (prefixWord ++ tailWord_583188).sum := by decide
  have hdescent : baseEnd_583188 < baseStart_583188 := by decide
  rcases family_descends (prefixWord ++ tailWord_583188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583223 : List Nat := [1, 1, 3, 1, 2, 4, 3, 2, 3]
def baseStart_583223 : Nat := 118140960795 + 583223 * 2 ^ 59
def prefixEnd_583223 : Nat := 4983230072969 + 3 ^ 40 * 583223 * 2
def baseEnd_583223 : Nat := 266198869117579440915833

theorem tailTrace_583223 : CollatzResearch.WordTrace tailWord_583223 prefixEnd_583223 266198869117579440915833 := by
  unfold tailWord_583223
  simp only [CollatzResearch.WordTrace]
  refine ⟨21271890366090152403426323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14181260244060101602284215 21271890366090152403426323)
  ·
    refine ⟨31907835549135228605139485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21271890366090152403426323 31907835549135228605139485)
    ·
      refine ⟨11965438330925710726927307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31907835549135228605139485 11965438330925710726927307)
      ·
        refine ⟨17948157496388566090390961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11965438330925710726927307 17948157496388566090390961)
        ·
          refine ⟨13461118122291424567793221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17948157496388566090390961 13461118122291424567793221)
          ·
            refine ⟨2523959647929642106461229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13461118122291424567793221 2523959647929642106461229)
            ·
              refine ⟨946484867973615789922961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2523959647929642106461229 946484867973615789922961)
              ·
                refine ⟨709863650980211842442221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 946484867973615789922961 709863650980211842442221)
                ·
                  refine ⟨266198869117579440915833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 709863650980211842442221 266198869117579440915833)
                  ·
                    rfl

theorem cell20_583223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3, 2, 3].length) (baseStart_583223 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_583223 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_583223 prefixEnd_583223 := by exact prefixLift 583223
  have htrace : WordTrace (prefixWord ++ tailWord_583223) baseStart_583223 baseEnd_583223 := by
    simpa [prefixWord, tailWord_583223, baseEnd_583223] using wordTrace_append hprefix tailTrace_583223
  have hstable : (prefixWord ++ tailWord_583223).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583223).length < 2 ^ (prefixWord ++ tailWord_583223).sum := by decide
  have hdescent : baseEnd_583223 < baseStart_583223 := by decide
  rcases family_descends (prefixWord ++ tailWord_583223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583285 : List Nat := [1, 3, 4, 2, 1, 1, 3, 1, 4]
def baseStart_583285 : Nat := 118140960795 + 583285 * 2 ^ 59
def prefixEnd_583285 : Nat := 4983230072969 + 3 ^ 40 * 583285 * 2
def baseEnd_583285 : Nat := 266227167606982780848913

theorem tailTrace_583285 : CollatzResearch.WordTrace tailWord_583285 prefixEnd_583285 266227167606982780848913 := by
  unfold tailWord_583285
  simp only [CollatzResearch.WordTrace]
  refine ⟨21274151691865536992183309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14182767794577024661455539 21274151691865536992183309)
  ·
    refine ⟨7977806884449576372068741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21274151691865536992183309 7977806884449576372068741)
    ·
      refine ⟨1495838790834295569762889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7977806884449576372068741 1495838790834295569762889)
      ·
        refine ⟨1121879093125721677322167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1495838790834295569762889 1121879093125721677322167)
        ·
          refine ⟨1682818639688582515983251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1121879093125721677322167 1682818639688582515983251)
          ·
            refine ⟨2524227959532873773974877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1682818639688582515983251 2524227959532873773974877)
            ·
              refine ⟨946585484824827665240579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2524227959532873773974877 946585484824827665240579)
              ·
                refine ⟨1419878227237241497860869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 946585484824827665240579 1419878227237241497860869)
                ·
                  refine ⟨266227167606982780848913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1419878227237241497860869 266227167606982780848913)
                  ·
                    rfl

theorem cell20_583285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3, 1, 4].length) (baseStart_583285 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_583285 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_583285 prefixEnd_583285 := by exact prefixLift 583285
  have htrace : WordTrace (prefixWord ++ tailWord_583285) baseStart_583285 baseEnd_583285 := by
    simpa [prefixWord, tailWord_583285, baseEnd_583285] using wordTrace_append hprefix tailTrace_583285
  have hstable : (prefixWord ++ tailWord_583285).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583285).length < 2 ^ (prefixWord ++ tailWord_583285).sum := by decide
  have hdescent : baseEnd_583285 < baseStart_583285 := by decide
  rcases family_descends (prefixWord ++ tailWord_583285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583330 : List Nat := [3, 3, 1, 4, 1, 8]
def baseStart_583330 : Nat := 118140960795 + 583330 * 2 ^ 59
def prefixEnd_583330 : Nat := 4983230072969 + 3 ^ 40 * 583330 * 2
def baseEnd_583330 : Nat := 9861026179006023124027

theorem tailTrace_583330 : CollatzResearch.WordTrace tailWord_583330 prefixEnd_583330 9861026179006023124027 := by
  unfold tailWord_583330
  simp only [CollatzResearch.WordTrace]
  refine ⟨5318948244175627419392861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14183861984468339785047629 5318948244175627419392861)
  ·
    refine ⟨1994605591565860282272323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5318948244175627419392861 1994605591565860282272323)
    ·
      refine ⟨2991908387348790423408485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1994605591565860282272323 2991908387348790423408485)
      ·
        refine ⟨560982822627898204389091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2991908387348790423408485 560982822627898204389091)
        ·
          refine ⟨841474233941847306583637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 560982822627898204389091 841474233941847306583637)
          ·
            refine ⟨9861026179006023124027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 841474233941847306583637 9861026179006023124027)
            ·
              rfl

theorem cell20_583330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 8].length) (baseStart_583330 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_583330 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_583330 prefixEnd_583330 := by exact prefixLift 583330
  have htrace : WordTrace (prefixWord ++ tailWord_583330) baseStart_583330 baseEnd_583330 := by
    simpa [prefixWord, tailWord_583330, baseEnd_583330] using wordTrace_append hprefix tailTrace_583330
  have hstable : (prefixWord ++ tailWord_583330).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583330).length < 2 ^ (prefixWord ++ tailWord_583330).sum := by decide
  have hdescent : baseEnd_583330 < baseStart_583330 := by decide
  rcases family_descends (prefixWord ++ tailWord_583330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583336 : List Nat := [2, 1, 7, 1, 1, 1, 1, 4, 2]
def baseStart_583336 : Nat := 118140960795 + 583336 * 2 ^ 59
def prefixEnd_583336 : Nat := 4983230072969 + 3 ^ 40 * 583336 * 2
def baseEnd_583336 : Nat := 266250445396653270148705

theorem tailTrace_583336 : CollatzResearch.WordTrace tailWord_583336 prefixEnd_583336 266250445396653270148705 := by
  unfold tailWord_583336
  simp only [CollatzResearch.WordTrace]
  refine ⟨10638005907340386351144931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14184007876453848468193241 10638005907340386351144931)
  ·
    refine ⟨15957008861010579526717397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10638005907340386351144931 15957008861010579526717397)
    ·
      refine ⟨373992395179935457657439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 15957008861010579526717397 373992395179935457657439)
      ·
        refine ⟨560988592769903186486159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 373992395179935457657439 560988592769903186486159)
        ·
          refine ⟨841482889154854779729239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 560988592769903186486159 841482889154854779729239)
          ·
            refine ⟨1262224333732282169593859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 841482889154854779729239 1262224333732282169593859)
            ·
              refine ⟨1893336500598423254390789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1262224333732282169593859 1893336500598423254390789)
              ·
                refine ⟨355000593862204360198273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1893336500598423254390789 355000593862204360198273)
                ·
                  refine ⟨266250445396653270148705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 355000593862204360198273 266250445396653270148705)
                  ·
                    rfl

theorem cell20_583336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 4, 2].length) (baseStart_583336 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_583336 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_583336 prefixEnd_583336 := by exact prefixLift 583336
  have htrace : WordTrace (prefixWord ++ tailWord_583336) baseStart_583336 baseEnd_583336 := by
    simpa [prefixWord, tailWord_583336, baseEnd_583336] using wordTrace_append hprefix tailTrace_583336
  have hstable : (prefixWord ++ tailWord_583336).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583336).length < 2 ^ (prefixWord ++ tailWord_583336).sum := by decide
  have hdescent : baseEnd_583336 < baseStart_583336 := by decide
  rcases family_descends (prefixWord ++ tailWord_583336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583351 : List Nat := [1, 1, 3, 1, 5, 1, 3, 5]
def baseStart_583351 : Nat := 118140960795 + 583351 * 2 ^ 59
def prefixEnd_583351 : Nat := 4983230072969 + 3 ^ 40 * 583351 * 2
def baseEnd_583351 : Nat := 88752430601793294882881

theorem tailTrace_583351 : CollatzResearch.WordTrace tailWord_583351 prefixEnd_583351 88752430601793294882881 := by
  unfold tailWord_583351
  simp only [CollatzResearch.WordTrace]
  refine ⟨21276558909626430264085907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14184372606417620176057271 21276558909626430264085907)
  ·
    refine ⟨31914838364439645396128861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21276558909626430264085907 31914838364439645396128861)
    ·
      refine ⟨11968064386664867023548323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31914838364439645396128861 11968064386664867023548323)
      ·
        refine ⟨17952096579997300535322485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11968064386664867023548323 17952096579997300535322485)
        ·
          refine ⟨1683009054374746925186483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17952096579997300535322485 1683009054374746925186483)
          ·
            refine ⟨2524513581562120387779725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1683009054374746925186483 2524513581562120387779725)
            ·
              refine ⟨946692593085795145417397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2524513581562120387779725 946692593085795145417397)
              ·
                refine ⟨88752430601793294882881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 946692593085795145417397 88752430601793294882881)
                ·
                  rfl

theorem cell20_583351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3, 5].length) (baseStart_583351 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_583351 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_583351 prefixEnd_583351 := by exact prefixLift 583351
  have htrace : WordTrace (prefixWord ++ tailWord_583351) baseStart_583351 baseEnd_583351 := by
    simpa [prefixWord, tailWord_583351, baseEnd_583351] using wordTrace_append hprefix tailTrace_583351
  have hstable : (prefixWord ++ tailWord_583351).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583351).length < 2 ^ (prefixWord ++ tailWord_583351).sum := by decide
  have hdescent : baseEnd_583351 < baseStart_583351 := by decide
  rcases family_descends (prefixWord ++ tailWord_583351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583365 : List Nat := [1, 3, 1, 1, 1, 1, 2, 6, 4]
def baseStart_583365 : Nat := 118140960795 + 583365 * 2 ^ 59
def prefixEnd_583365 : Nat := 4983230072969 + 3 ^ 40 * 583365 * 2
def baseEnd_583365 : Nat := 266263681786858058181919

theorem tailTrace_583365 : CollatzResearch.WordTrace tailWord_583365 prefixEnd_583365 266263681786858058181919 := by
  unfold tailWord_583365
  simp only [CollatzResearch.WordTrace]
  refine ⟨21277069531575710655095549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14184713021050473770063699 21277069531575710655095549)
  ·
    refine ⟨7978901074340891495660831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21277069531575710655095549 7978901074340891495660831)
    ·
      refine ⟨11968351611511337243491247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7978901074340891495660831 11968351611511337243491247)
      ·
        refine ⟨17952527417267005865236871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11968351611511337243491247 17952527417267005865236871)
        ·
          refine ⟨26928791125900508797855307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17952527417267005865236871 26928791125900508797855307)
          ·
            refine ⟨40393186688850763196782961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26928791125900508797855307 40393186688850763196782961)
            ·
              refine ⟨30294890016638072397587221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40393186688850763196782961 30294890016638072397587221)
              ·
                refine ⟨1420072969529909643636901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 30294890016638072397587221 1420072969529909643636901)
                ·
                  refine ⟨266263681786858058181919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1420072969529909643636901 266263681786858058181919)
                  ·
                    rfl

theorem cell20_583365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 6, 4].length) (baseStart_583365 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_583365 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_583365 prefixEnd_583365 := by exact prefixLift 583365
  have htrace : WordTrace (prefixWord ++ tailWord_583365) baseStart_583365 baseEnd_583365 := by
    simpa [prefixWord, tailWord_583365, baseEnd_583365] using wordTrace_append hprefix tailTrace_583365
  have hstable : (prefixWord ++ tailWord_583365).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583365).length < 2 ^ (prefixWord ++ tailWord_583365).sum := by decide
  have hdescent : baseEnd_583365 < baseStart_583365 := by decide
  rcases family_descends (prefixWord ++ tailWord_583365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583378 : List Nat := [3, 2, 2, 2, 2, 2, 2, 3, 2]
def baseStart_583378 : Nat := 118140960795 + 583378 * 2 ^ 59
def prefixEnd_583378 : Nat := 4983230072969 + 3 ^ 40 * 583378 * 2
def baseEnd_583378 : Nat := 266269615341087790748533

theorem tailTrace_583378 : CollatzResearch.WordTrace tailWord_583378 prefixEnd_583378 266269615341087790748533 := by
  unfold tailWord_583378
  simp only [CollatzResearch.WordTrace]
  refine ⟨5319385920132153468829697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14185029120352409250212525 5319385920132153468829697)
  ·
    refine ⟨3989539440099115101622273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5319385920132153468829697 3989539440099115101622273)
    ·
      refine ⟨2992154580074336326216705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3989539440099115101622273 2992154580074336326216705)
      ·
        refine ⟨2244115935055752244662529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2992154580074336326216705 2244115935055752244662529)
        ·
          refine ⟨1683086951291814183496897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2244115935055752244662529 1683086951291814183496897)
          ·
            refine ⟨1262315213468860637622673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1683086951291814183496897 1262315213468860637622673)
            ·
              refine ⟨946736410101645478217005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1262315213468860637622673 946736410101645478217005)
              ·
                refine ⟨355026153788117054331377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 946736410101645478217005 355026153788117054331377)
                ·
                  refine ⟨266269615341087790748533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 355026153788117054331377 266269615341087790748533)
                  ·
                    rfl

theorem cell20_583378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2, 3, 2].length) (baseStart_583378 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_583378 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_583378 prefixEnd_583378 := by exact prefixLift 583378
  have htrace : WordTrace (prefixWord ++ tailWord_583378) baseStart_583378 baseEnd_583378 := by
    simpa [prefixWord, tailWord_583378, baseEnd_583378] using wordTrace_append hprefix tailTrace_583378
  have hstable : (prefixWord ++ tailWord_583378).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583378).length < 2 ^ (prefixWord ++ tailWord_583378).sum := by decide
  have hdescent : baseEnd_583378 < baseStart_583378 := by decide
  rcases family_descends (prefixWord ++ tailWord_583378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583388 : List Nat := [2, 2, 5, 1, 3, 1, 1, 2, 3]
def baseStart_583388 : Nat := 118140960795 + 583388 * 2 ^ 59
def prefixEnd_583388 : Nat := 4983230072969 + 3 ^ 40 * 583388 * 2
def baseEnd_583388 : Nat := 266274179613572200415159

theorem tailTrace_583388 : CollatzResearch.WordTrace tailWord_583388 prefixEnd_583388 266274179613572200415159 := by
  unfold tailWord_583388
  simp only [CollatzResearch.WordTrace]
  refine ⟨10638954205246192791591409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14185272273661590388788545 10638954205246192791591409)
  ·
    refine ⟨7979215653934644593693557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10638954205246192791591409 7979215653934644593693557)
    ·
      refine ⟨748051467556372930658771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7979215653934644593693557 748051467556372930658771)
      ·
        refine ⟨1122077201334559395988157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 748051467556372930658771 1122077201334559395988157)
        ·
          refine ⟨420778950500459773495559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1122077201334559395988157 420778950500459773495559)
          ·
            refine ⟨631168425750689660243339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 420778950500459773495559 631168425750689660243339)
            ·
              refine ⟨946752638626034490365009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 631168425750689660243339 946752638626034490365009)
              ·
                refine ⟨710064478969525867773757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 946752638626034490365009 710064478969525867773757)
                ·
                  refine ⟨266274179613572200415159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 710064478969525867773757 266274179613572200415159)
                  ·
                    rfl

theorem cell20_583388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 1, 2, 3].length) (baseStart_583388 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_583388 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_583388 prefixEnd_583388 := by exact prefixLift 583388
  have htrace : WordTrace (prefixWord ++ tailWord_583388) baseStart_583388 baseEnd_583388 := by
    simpa [prefixWord, tailWord_583388, baseEnd_583388] using wordTrace_append hprefix tailTrace_583388
  have hstable : (prefixWord ++ tailWord_583388).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583388).length < 2 ^ (prefixWord ++ tailWord_583388).sum := by decide
  have hdescent : baseEnd_583388 < baseStart_583388 := by decide
  rcases family_descends (prefixWord ++ tailWord_583388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583396 : List Nat := [2, 3, 1, 1, 1, 3, 3, 1, 5]
def baseStart_583396 : Nat := 118140960795 + 583396 * 2 ^ 59
def prefixEnd_583396 : Nat := 4983230072969 + 3 ^ 40 * 583396 * 2
def baseEnd_583396 : Nat := 266277831031559728148459

theorem tailTrace_583396 : CollatzResearch.WordTrace tailWord_583396 prefixEnd_583396 266277831031559728148459 := by
  unfold tailWord_583396
  simp only [CollatzResearch.WordTrace]
  refine ⟨10639100097231701474737021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14185466796308935299649361 10639100097231701474737021)
  ·
    refine ⟨3989662536461888053026383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10639100097231701474737021 3989662536461888053026383)
    ·
      refine ⟨5984493804692832079539575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3989662536461888053026383 5984493804692832079539575)
      ·
        refine ⟨8976740707039248119309363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5984493804692832079539575 8976740707039248119309363)
        ·
          refine ⟨13465111060558872178964045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8976740707039248119309363 13465111060558872178964045)
          ·
            refine ⟨5049416647709577067111517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13465111060558872178964045 5049416647709577067111517)
            ·
              refine ⟨1893531242891091400166819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5049416647709577067111517 1893531242891091400166819)
              ·
                refine ⟨2840296864336637100250229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1893531242891091400166819 2840296864336637100250229)
                ·
                  refine ⟨266277831031559728148459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2840296864336637100250229 266277831031559728148459)
                  ·
                    rfl

theorem cell20_583396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 1, 5].length) (baseStart_583396 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_583396 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_583396 prefixEnd_583396 := by exact prefixLift 583396
  have htrace : WordTrace (prefixWord ++ tailWord_583396) baseStart_583396 baseEnd_583396 := by
    simpa [prefixWord, tailWord_583396, baseEnd_583396] using wordTrace_append hprefix tailTrace_583396
  have hstable : (prefixWord ++ tailWord_583396).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583396).length < 2 ^ (prefixWord ++ tailWord_583396).sum := by decide
  have hdescent : baseEnd_583396 < baseStart_583396 := by decide
  rcases family_descends (prefixWord ++ tailWord_583396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583403 : List Nat := [1, 1, 1, 1, 2, 4, 3, 3, 4]
def baseStart_583403 : Nat := 118140960795 + 583403 * 2 ^ 59
def prefixEnd_583403 : Nat := 4983230072969 + 3 ^ 40 * 583403 * 2
def baseEnd_583403 : Nat := 266281026022298814915097

theorem tailTrace_583403 : CollatzResearch.WordTrace tailWord_583403 prefixEnd_583403 266281026022298814915097 := by
  unfold tailWord_583403
  simp only [CollatzResearch.WordTrace]
  refine ⟨21278455505438043144978863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14185637003625362096652575 21278455505438043144978863)
  ·
    refine ⟨31917683258157064717468295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21278455505438043144978863 31917683258157064717468295)
    ·
      refine ⟨47876524887235597076202443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31917683258157064717468295 47876524887235597076202443)
      ·
        refine ⟨71814787330853395614303665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47876524887235597076202443 71814787330853395614303665)
        ·
          refine ⟨53861090498140046710727749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71814787330853395614303665 53861090498140046710727749)
          ·
            refine ⟨10098954468401258758261453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53861090498140046710727749 10098954468401258758261453)
            ·
              refine ⟨3787107925650472034348045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10098954468401258758261453 3787107925650472034348045)
              ·
                refine ⟨1420165472118927012880517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3787107925650472034348045 1420165472118927012880517)
                ·
                  refine ⟨266281026022298814915097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1420165472118927012880517 266281026022298814915097)
                  ·
                    rfl

theorem cell20_583403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 3, 4].length) (baseStart_583403 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_583403 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_583403 prefixEnd_583403 := by exact prefixLift 583403
  have htrace : WordTrace (prefixWord ++ tailWord_583403) baseStart_583403 baseEnd_583403 := by
    simpa [prefixWord, tailWord_583403, baseEnd_583403] using wordTrace_append hprefix tailTrace_583403
  have hstable : (prefixWord ++ tailWord_583403).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583403).length < 2 ^ (prefixWord ++ tailWord_583403).sum := by decide
  have hdescent : baseEnd_583403 < baseStart_583403 := by decide
  rcases family_descends (prefixWord ++ tailWord_583403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583427 : List Nat := [1, 1, 1, 3, 2, 2, 6, 4]
def baseStart_583427 : Nat := 118140960795 + 583427 * 2 ^ 59
def prefixEnd_583427 : Nat := 4983230072969 + 3 ^ 40 * 583427 * 2
def baseEnd_583427 : Nat := 88763993425420466038333

theorem tailTrace_583427 : CollatzResearch.WordTrace tailWord_583427 prefixEnd_583427 88763993425420466038333 := by
  unfold tailWord_583427
  simp only [CollatzResearch.WordTrace]
  refine ⟨21279330857351095243852535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14186220571567396829235023 21279330857351095243852535)
  ·
    refine ⟨31918996286026642865778803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21279330857351095243852535 31918996286026642865778803)
    ·
      refine ⟨47878494429039964298668205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31918996286026642865778803 47878494429039964298668205)
      ·
        refine ⟨17954435410889986612000577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47878494429039964298668205 17954435410889986612000577)
        ·
          refine ⟨13465826558167489959000433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17954435410889986612000577 13465826558167489959000433)
          ·
            refine ⟨10099369918625617469250325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13465826558167489959000433 10099369918625617469250325)
            ·
              refine ⟨473407964935575818871109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 10099369918625617469250325 473407964935575818871109)
              ·
                refine ⟨88763993425420466038333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 473407964935575818871109 88763993425420466038333)
                ·
                  rfl

theorem cell20_583427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 6, 4].length) (baseStart_583427 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_583427 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_583427 prefixEnd_583427 := by exact prefixLift 583427
  have htrace : WordTrace (prefixWord ++ tailWord_583427) baseStart_583427 baseEnd_583427 := by
    simpa [prefixWord, tailWord_583427, baseEnd_583427] using wordTrace_append hprefix tailTrace_583427
  have hstable : (prefixWord ++ tailWord_583427).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583427).length < 2 ^ (prefixWord ++ tailWord_583427).sum := by decide
  have hdescent : baseEnd_583427 < baseStart_583427 := by decide
  rcases family_descends (prefixWord ++ tailWord_583427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583434 : List Nat := [3, 1, 2, 2, 1, 3, 1, 2, 5]
def baseStart_583434 : Nat := 118140960795 + 583434 * 2 ^ 59
def prefixEnd_583434 : Nat := 4983230072969 + 3 ^ 40 * 583434 * 2
def baseEnd_583434 : Nat := 266295175267000484881637

theorem tailTrace_583434 : CollatzResearch.WordTrace tailWord_583434 prefixEnd_583434 266295175267000484881637 := by
  unfold tailWord_583434
  simp only [CollatzResearch.WordTrace]
  refine ⟨5319896542081433859839339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14186390778883823626238237 5319896542081433859839339)
  ·
    refine ⟨7979844813122150789759009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5319896542081433859839339 7979844813122150789759009)
    ·
      refine ⟨5984883609841613092319257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7979844813122150789759009 5984883609841613092319257)
      ·
        refine ⟨4488662707381209819239443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5984883609841613092319257 4488662707381209819239443)
        ·
          refine ⟨6732994061071814728859165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4488662707381209819239443 6732994061071814728859165)
          ·
            refine ⟨2524872772901930523322187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6732994061071814728859165 2524872772901930523322187)
            ·
              refine ⟨3787309159352895784983281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2524872772901930523322187 3787309159352895784983281)
              ·
                refine ⟨2840481869514671838737461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3787309159352895784983281 2840481869514671838737461)
                ·
                  refine ⟨266295175267000484881637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2840481869514671838737461 266295175267000484881637)
                  ·
                    rfl

theorem cell20_583434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 2, 5].length) (baseStart_583434 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_583434 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_583434 prefixEnd_583434 := by exact prefixLift 583434
  have htrace : WordTrace (prefixWord ++ tailWord_583434) baseStart_583434 baseEnd_583434 := by
    simpa [prefixWord, tailWord_583434, baseEnd_583434] using wordTrace_append hprefix tailTrace_583434
  have hstable : (prefixWord ++ tailWord_583434).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583434).length < 2 ^ (prefixWord ++ tailWord_583434).sum := by decide
  have hdescent : baseEnd_583434 < baseStart_583434 := by decide
  rcases family_descends (prefixWord ++ tailWord_583434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583448 : List Nat := [2, 1, 2, 3, 1, 1, 10]
def baseStart_583448 : Nat := 118140960795 + 583448 * 2 ^ 59
def prefixEnd_583448 : Nat := 4983230072969 + 3 ^ 40 * 583448 * 2
def baseEnd_583448 : Nat := 29589062805386517601657

theorem tailTrace_583448 : CollatzResearch.WordTrace tailWord_583448 prefixEnd_583448 29589062805386517601657 := by
  unfold tailWord_583448
  simp only [CollatzResearch.WordTrace]
  refine ⟨10640048395137507915183499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14186731193516677220244665 10640048395137507915183499)
  ·
    refine ⟨15960072592706261872775249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10640048395137507915183499 15960072592706261872775249)
    ·
      refine ⟨11970054444529696404581437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15960072592706261872775249 11970054444529696404581437)
      ·
        refine ⟨4488770416698636151718039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11970054444529696404581437 4488770416698636151718039)
        ·
          refine ⟨6733155625047954227577059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4488770416698636151718039 6733155625047954227577059)
          ·
            refine ⟨10099733437571931341365589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6733155625047954227577059 10099733437571931341365589)
            ·
              refine ⟨29589062805386517601657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 10099733437571931341365589 29589062805386517601657)
              ·
                rfl

theorem cell20_583448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 10].length) (baseStart_583448 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_583448 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_583448 prefixEnd_583448 := by exact prefixLift 583448
  have htrace : WordTrace (prefixWord ++ tailWord_583448) baseStart_583448 baseEnd_583448 := by
    simpa [prefixWord, tailWord_583448, baseEnd_583448] using wordTrace_append hprefix tailTrace_583448
  have hstable : (prefixWord ++ tailWord_583448).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583448).length < 2 ^ (prefixWord ++ tailWord_583448).sum := by decide
  have hdescent : baseEnd_583448 < baseStart_583448 := by decide
  rcases family_descends (prefixWord ++ tailWord_583448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583468 : List Nat := [2, 2, 1, 1, 1, 7, 2, 1, 3]
def baseStart_583468 : Nat := 118140960795 + 583468 * 2 ^ 59
def prefixEnd_583468 : Nat := 4983230072969 + 3 ^ 40 * 583468 * 2
def baseEnd_583468 : Nat := 266310693793447477748165

theorem tailTrace_583468 : CollatzResearch.WordTrace tailWord_583468 prefixEnd_583468 266310693793447477748165 := by
  unfold tailWord_583468
  simp only [CollatzResearch.WordTrace]
  refine ⟨10640413125101279623047529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14187217500135039497396705 10640413125101279623047529)
  ·
    refine ⟨7980309843825959717285647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10640413125101279623047529 7980309843825959717285647)
    ·
      refine ⟨11970464765738939575928471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7980309843825959717285647 11970464765738939575928471)
      ·
        refine ⟨17955697148608409363892707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11970464765738939575928471 17955697148608409363892707)
        ·
          refine ⟨26933545722912614045839061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17955697148608409363892707 26933545722912614045839061)
          ·
            refine ⟨631254977880764391699353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 26933545722912614045839061 631254977880764391699353)
            ·
              refine ⟨473441233410573293774515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 631254977880764391699353 473441233410573293774515)
              ·
                refine ⟨710161850115859940661773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 473441233410573293774515 710161850115859940661773)
                ·
                  refine ⟨266310693793447477748165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 710161850115859940661773 266310693793447477748165)
                  ·
                    rfl

theorem cell20_583468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 3].length) (baseStart_583468 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_583468 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_583468 prefixEnd_583468 := by exact prefixLift 583468
  have htrace : WordTrace (prefixWord ++ tailWord_583468) baseStart_583468 baseEnd_583468 := by
    simpa [prefixWord, tailWord_583468, baseEnd_583468] using wordTrace_append hprefix tailTrace_583468
  have hstable : (prefixWord ++ tailWord_583468).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583468).length < 2 ^ (prefixWord ++ tailWord_583468).sum := by decide
  have hdescent : baseEnd_583468 < baseStart_583468 := by decide
  rcases family_descends (prefixWord ++ tailWord_583468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583531 : List Nat := [1, 1, 1, 1, 2, 2, 3, 2, 7]
def baseStart_583531 : Nat := 118140960795 + 583531 * 2 ^ 59
def prefixEnd_583531 : Nat := 4983230072969 + 3 ^ 40 * 583531 * 2
def baseEnd_583531 : Nat := 266339448710099258647907

theorem tailTrace_583531 : CollatzResearch.WordTrace tailWord_583531 prefixEnd_583531 266339448710099258647907 := by
  unfold tailWord_583531
  simp only [CollatzResearch.WordTrace]
  refine ⟨21283124048974321005638447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14188749365982880670425631 21283124048974321005638447)
  ·
    refine ⟨31924686073461481508457671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21283124048974321005638447 31924686073461481508457671)
    ·
      refine ⟨47887029110192222262686507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31924686073461481508457671 47887029110192222262686507)
      ·
        refine ⟨71830543665288333394029761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47887029110192222262686507 71830543665288333394029761)
        ·
          refine ⟨53872907748966250045522321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71830543665288333394029761 53872907748966250045522321)
          ·
            refine ⟨40404680811724687534141741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53872907748966250045522321 40404680811724687534141741)
            ·
              refine ⟨15151755304396757825303153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40404680811724687534141741 15151755304396757825303153)
              ·
                refine ⟨11363816478297568368977365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15151755304396757825303153 11363816478297568368977365)
                ·
                  refine ⟨266339448710099258647907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11363816478297568368977365 266339448710099258647907)
                  ·
                    rfl

theorem cell20_583531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 7].length) (baseStart_583531 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_583531 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_583531 prefixEnd_583531 := by exact prefixLift 583531
  have htrace : WordTrace (prefixWord ++ tailWord_583531) baseStart_583531 baseEnd_583531 := by
    simpa [prefixWord, tailWord_583531, baseEnd_583531] using wordTrace_append hprefix tailTrace_583531
  have hstable : (prefixWord ++ tailWord_583531).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583531).length < 2 ^ (prefixWord ++ tailWord_583531).sum := by decide
  have hdescent : baseEnd_583531 < baseStart_583531 := by decide
  rcases family_descends (prefixWord ++ tailWord_583531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583534 : List Nat := [4, 1, 2, 3, 1, 1, 1, 1, 6]
def baseStart_583534 : Nat := 118140960795 + 583534 * 2 ^ 59
def prefixEnd_583534 : Nat := 4983230072969 + 3 ^ 40 * 583534 * 2
def baseEnd_583534 : Nat := 266340817991844581547895

theorem tailTrace_583534 : CollatzResearch.WordTrace tailWord_583534 prefixEnd_583534 266340817991844581547895 := by
  unfold tailWord_583534
  simp only [CollatzResearch.WordTrace]
  refine ⟨2660404183495431564749707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14188822311975635011998437 2660404183495431564749707)
  ·
    refine ⟨3990606275243147347124561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2660404183495431564749707 3990606275243147347124561)
    ·
      refine ⟨2992954706432360510343421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3990606275243147347124561 2992954706432360510343421)
      ·
        refine ⟨1122358014912135191378783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2992954706432360510343421 1122358014912135191378783)
        ·
          refine ⟨1683537022368202787068175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1122358014912135191378783 1683537022368202787068175)
          ·
            refine ⟨2525305533552304180602263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1683537022368202787068175 2525305533552304180602263)
            ·
              refine ⟨3787958300328456270903395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2525305533552304180602263 3787958300328456270903395)
              ·
                refine ⟨5681937450492684406355093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3787958300328456270903395 5681937450492684406355093)
                ·
                  refine ⟨266340817991844581547895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5681937450492684406355093 266340817991844581547895)
                  ·
                    rfl

theorem cell20_583534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 1, 6].length) (baseStart_583534 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_583534 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_583534 prefixEnd_583534 := by exact prefixLift 583534
  have htrace : WordTrace (prefixWord ++ tailWord_583534) baseStart_583534 baseEnd_583534 := by
    simpa [prefixWord, tailWord_583534, baseEnd_583534] using wordTrace_append hprefix tailTrace_583534
  have hstable : (prefixWord ++ tailWord_583534).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583534).length < 2 ^ (prefixWord ++ tailWord_583534).sum := by decide
  have hdescent : baseEnd_583534 < baseStart_583534 := by decide
  rcases family_descends (prefixWord ++ tailWord_583534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583572 : List Nat := [2, 4, 2, 1, 1, 2, 1, 3, 4]
def baseStart_583572 : Nat := 118140960795 + 583572 * 2 ^ 59
def prefixEnd_583572 : Nat := 4983230072969 + 3 ^ 40 * 583572 * 2
def baseEnd_583572 : Nat := 266358162227285338281073

theorem tailTrace_583572 : CollatzResearch.WordTrace tailWord_583572 prefixEnd_583572 266358162227285338281073 := by
  unfold tailWord_583572
  simp only [CollatzResearch.WordTrace]
  refine ⟨10642309720912892503940485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14189746294550523338587313 10642309720912892503940485)
  ·
    refine ⟨1995433072671167344488841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10642309720912892503940485 1995433072671167344488841)
    ·
      refine ⟨1496574804503375508366631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1995433072671167344488841 1496574804503375508366631)
      ·
        refine ⟨2244862206755063262549947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1496574804503375508366631 2244862206755063262549947)
        ·
          refine ⟨3367293310132594893824921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2244862206755063262549947 3367293310132594893824921)
          ·
            refine ⟨2525469982599446170368691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3367293310132594893824921 2525469982599446170368691)
            ·
              refine ⟨3788204973899169255553037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2525469982599446170368691 3788204973899169255553037)
              ·
                refine ⟨1420576865212188470832389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3788204973899169255553037 1420576865212188470832389)
                ·
                  refine ⟨266358162227285338281073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1420576865212188470832389 266358162227285338281073)
                  ·
                    rfl

theorem cell20_583572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_583572 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_583572 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_583572 prefixEnd_583572 := by exact prefixLift 583572
  have htrace : WordTrace (prefixWord ++ tailWord_583572) baseStart_583572 baseEnd_583572 := by
    simpa [prefixWord, tailWord_583572, baseEnd_583572] using wordTrace_append hprefix tailTrace_583572
  have hstable : (prefixWord ++ tailWord_583572).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583572).length < 2 ^ (prefixWord ++ tailWord_583572).sum := by decide
  have hdescent : baseEnd_583572 < baseStart_583572 := by decide
  rcases family_descends (prefixWord ++ tailWord_583572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583592 : List Nat := [2, 1, 6, 2, 1, 2, 2, 4]
def baseStart_583592 : Nat := 118140960795 + 583592 * 2 ^ 59
def prefixEnd_583592 : Nat := 4983230072969 + 3 ^ 40 * 583592 * 2
def baseEnd_583592 : Nat := 88789096924084719204775

theorem tailTrace_583592 : CollatzResearch.WordTrace tailWord_583592 prefixEnd_583592 88789096924084719204775 := by
  unfold tailWord_583592
  simp only [CollatzResearch.WordTrace]
  refine ⟨10642674450876664211804515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14190232601168885615739353 10642674450876664211804515)
  ·
    refine ⟨15964011676314996317706773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10642674450876664211804515 15964011676314996317706773)
    ·
      refine ⟨748313047327265452392505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 15964011676314996317706773 748313047327265452392505)
      ·
        refine ⟨561234785495449089294379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 748313047327265452392505 561234785495449089294379)
        ·
          refine ⟨841852178243173633941569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 561234785495449089294379 841852178243173633941569)
          ·
            refine ⟨631389133682380225456177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 841852178243173633941569 631389133682380225456177)
            ·
              refine ⟨473541850261785169092133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 631389133682380225456177 473541850261785169092133)
              ·
                refine ⟨88789096924084719204775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 473541850261785169092133 88789096924084719204775)
                ·
                  rfl

theorem cell20_583592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 2, 4].length) (baseStart_583592 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_583592 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_583592 prefixEnd_583592 := by exact prefixLift 583592
  have htrace : WordTrace (prefixWord ++ tailWord_583592) baseStart_583592 baseEnd_583592 := by
    simpa [prefixWord, tailWord_583592, baseEnd_583592] using wordTrace_append hprefix tailTrace_583592
  have hstable : (prefixWord ++ tailWord_583592).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583592).length < 2 ^ (prefixWord ++ tailWord_583592).sum := by decide
  have hdescent : baseEnd_583592 < baseStart_583592 := by decide
  rcases family_descends (prefixWord ++ tailWord_583592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583610 : List Nat := [3, 1, 1, 1, 2, 1, 2, 7, 2]
def baseStart_583610 : Nat := 118140960795 + 583610 * 2 ^ 59
def prefixEnd_583610 : Nat := 4983230072969 + 3 ^ 40 * 583610 * 2
def baseEnd_583610 : Nat := 266375506462726095014251

theorem tailTrace_583610 : CollatzResearch.WordTrace tailWord_583610 prefixEnd_583610 266375506462726095014251 := by
  unfold tailWord_583610
  simp only [CollatzResearch.WordTrace]
  refine ⟨5321501353922029374441071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14190670277125411665176189 5321501353922029374441071)
  ·
    refine ⟨7982252030883044061661607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5321501353922029374441071 7982252030883044061661607)
    ·
      refine ⟨11973378046324566092492411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7982252030883044061661607 11973378046324566092492411)
      ·
        refine ⟨17960067069486849138738617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11973378046324566092492411 17960067069486849138738617)
        ·
          refine ⟨13470050302115136854053963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17960067069486849138738617 13470050302115136854053963)
          ·
            refine ⟨20205075453172705281080945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13470050302115136854053963 20205075453172705281080945)
            ·
              refine ⟨15153806589879528960810709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20205075453172705281080945 15153806589879528960810709)
              ·
                refine ⟨355167341950301460019001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 15153806589879528960810709 355167341950301460019001)
                ·
                  refine ⟨266375506462726095014251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 355167341950301460019001 266375506462726095014251)
                  ·
                    rfl

theorem cell20_583610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 7, 2].length) (baseStart_583610 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_583610 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_583610 prefixEnd_583610 := by exact prefixLift 583610
  have htrace : WordTrace (prefixWord ++ tailWord_583610) baseStart_583610 baseEnd_583610 := by
    simpa [prefixWord, tailWord_583610, baseEnd_583610] using wordTrace_append hprefix tailTrace_583610
  have hstable : (prefixWord ++ tailWord_583610).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583610).length < 2 ^ (prefixWord ++ tailWord_583610).sum := by decide
  have hdescent : baseEnd_583610 < baseStart_583610 := by decide
  rcases family_descends (prefixWord ++ tailWord_583610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583624 : List Nat := [2, 1, 3, 1, 4, 1, 2, 1, 5]
def baseStart_583624 : Nat := 118140960795 + 583624 * 2 ^ 59
def prefixEnd_583624 : Nat := 4983230072969 + 3 ^ 40 * 583624 * 2
def baseEnd_583624 : Nat := 266381896444204268547527

theorem tailTrace_583624 : CollatzResearch.WordTrace tailWord_583624 prefixEnd_583624 266381896444204268547527 := by
  unfold tailWord_583624
  simp only [CollatzResearch.WordTrace]
  refine ⟨10643258018818698944386963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14191010691758265259182617 10643258018818698944386963)
  ·
    refine ⟨15964887028228048416580445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10643258018818698944386963 15964887028228048416580445)
    ·
      refine ⟨5986832635585518156217667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15964887028228048416580445 5986832635585518156217667)
      ·
        refine ⟨8980248953378277234326501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5986832635585518156217667 8980248953378277234326501)
        ·
          refine ⟨1683796678758426981436219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8980248953378277234326501 1683796678758426981436219)
          ·
            refine ⟨2525695018137640472154329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1683796678758426981436219 2525695018137640472154329)
            ·
              refine ⟨1894271263603230354115747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2525695018137640472154329 1894271263603230354115747)
              ·
                refine ⟨2841406895404845531173621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1894271263603230354115747 2841406895404845531173621)
                ·
                  refine ⟨266381896444204268547527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2841406895404845531173621 266381896444204268547527)
                  ·
                    rfl

theorem cell20_583624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 1, 5].length) (baseStart_583624 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_583624 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_583624 prefixEnd_583624 := by exact prefixLift 583624
  have htrace : WordTrace (prefixWord ++ tailWord_583624) baseStart_583624 baseEnd_583624 := by
    simpa [prefixWord, tailWord_583624, baseEnd_583624] using wordTrace_append hprefix tailTrace_583624
  have hstable : (prefixWord ++ tailWord_583624).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583624).length < 2 ^ (prefixWord ++ tailWord_583624).sum := by decide
  have hdescent : baseEnd_583624 < baseStart_583624 := by decide
  rcases family_descends (prefixWord ++ tailWord_583624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583627 : List Nat := [1, 1, 1, 1, 3, 4, 5, 2, 2]
def baseStart_583627 : Nat := 118140960795 + 583627 * 2 ^ 59
def prefixEnd_583627 : Nat := 4983230072969 + 3 ^ 40 * 583627 * 2
def baseEnd_583627 : Nat := 266383265725949591447515

theorem tailTrace_583627 : CollatzResearch.WordTrace tailWord_583627 prefixEnd_583627 266383265725949591447515 := by
  unfold tailWord_583627
  simp only [CollatzResearch.WordTrace]
  refine ⟨21286625456626529401133135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14191083637751019600755423 21286625456626529401133135)
  ·
    refine ⟨31929938184939794101699703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21286625456626529401133135 31929938184939794101699703)
    ·
      refine ⟨47894907277409691152549555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31929938184939794101699703 47894907277409691152549555)
      ·
        refine ⟨71842360916114536728824333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47894907277409691152549555 71842360916114536728824333)
        ·
          refine ⟨26940885343542951273309125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71842360916114536728824333 26940885343542951273309125)
          ·
            refine ⟨5051416001914303363745461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26940885343542951273309125 5051416001914303363745461)
            ·
              refine ⟨473570250179465940351137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5051416001914303363745461 473570250179465940351137)
              ·
                refine ⟨355177687634599455263353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 473570250179465940351137 355177687634599455263353)
                ·
                  refine ⟨266383265725949591447515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 355177687634599455263353 266383265725949591447515)
                  ·
                    rfl

theorem cell20_583627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 5, 2, 2].length) (baseStart_583627 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_583627 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_583627 prefixEnd_583627 := by exact prefixLift 583627
  have htrace : WordTrace (prefixWord ++ tailWord_583627) baseStart_583627 baseEnd_583627 := by
    simpa [prefixWord, tailWord_583627, baseEnd_583627] using wordTrace_append hprefix tailTrace_583627
  have hstable : (prefixWord ++ tailWord_583627).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583627).length < 2 ^ (prefixWord ++ tailWord_583627).sum := by decide
  have hdescent : baseEnd_583627 < baseStart_583627 := by decide
  rcases family_descends (prefixWord ++ tailWord_583627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583634 : List Nat := [3, 2, 2, 3, 2, 1, 2, 5]
def baseStart_583634 : Nat := 118140960795 + 583634 * 2 ^ 59
def prefixEnd_583634 : Nat := 4983230072969 + 3 ^ 40 * 583634 * 2
def baseEnd_583634 : Nat := 88795486905562892738051

theorem tailTrace_583634 : CollatzResearch.WordTrace tailWord_583634 prefixEnd_583634 88795486905562892738051 := by
  unfold tailWord_583634
  simp only [CollatzResearch.WordTrace]
  refine ⟨5321720191900292399159489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14191253845067446397758637 5321720191900292399159489)
  ·
    refine ⟨3991290143925219299369617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5321720191900292399159489 3991290143925219299369617)
    ·
      refine ⟨2993467607943914474527213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3991290143925219299369617 2993467607943914474527213)
      ·
        refine ⟨1122550352978967927947705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2993467607943914474527213 1122550352978967927947705)
        ·
          refine ⟨841912764734225945960779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1122550352978967927947705 841912764734225945960779)
          ·
            refine ⟨1262869147101338918941169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 841912764734225945960779 1262869147101338918941169)
            ·
              refine ⟨947151860326004189205877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1262869147101338918941169 947151860326004189205877)
              ·
                refine ⟨88795486905562892738051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 947151860326004189205877 88795486905562892738051)
                ·
                  rfl

theorem cell20_583634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 2, 5].length) (baseStart_583634 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_583634 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_583634 prefixEnd_583634 := by exact prefixLift 583634
  have htrace : WordTrace (prefixWord ++ tailWord_583634) baseStart_583634 baseEnd_583634 := by
    simpa [prefixWord, tailWord_583634, baseEnd_583634] using wordTrace_append hprefix tailTrace_583634
  have hstable : (prefixWord ++ tailWord_583634).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583634).length < 2 ^ (prefixWord ++ tailWord_583634).sum := by decide
  have hdescent : baseEnd_583634 < baseStart_583634 := by decide
  rcases family_descends (prefixWord ++ tailWord_583634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583641 : List Nat := [1, 2, 1, 2, 6, 1, 1, 3, 3]
def baseStart_583641 : Nat := 118140960795 + 583641 * 2 ^ 59
def prefixEnd_583641 : Nat := 4983230072969 + 3 ^ 40 * 583641 * 2
def baseEnd_583641 : Nat := 266389655707427764980791

theorem tailTrace_583641 : CollatzResearch.WordTrace tailWord_583641 prefixEnd_583641 266389655707427764980791 := by
  unfold tailWord_583641
  simp only [CollatzResearch.WordTrace]
  refine ⟨21287136078575809792142777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14191424052383873194761851 21287136078575809792142777)
  ·
    refine ⟨15965352058931857344107083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21287136078575809792142777 15965352058931857344107083)
    ·
      refine ⟨23948028088397786016160625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15965352058931857344107083 23948028088397786016160625)
      ·
        refine ⟨17961021066298339512120469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23948028088397786016160625 17961021066298339512120469)
        ·
          refine ⟨841922862482734664630647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 17961021066298339512120469 841922862482734664630647)
          ·
            refine ⟨1262884293724101996945971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 841922862482734664630647 1262884293724101996945971)
            ·
              refine ⟨1894326440586152995418957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1262884293724101996945971 1894326440586152995418957)
              ·
                refine ⟨710372415219807373282109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1894326440586152995418957 710372415219807373282109)
                ·
                  refine ⟨266389655707427764980791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 710372415219807373282109 266389655707427764980791)
                  ·
                    rfl

theorem cell20_583641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 3, 3].length) (baseStart_583641 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_583641 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_583641 prefixEnd_583641 := by exact prefixLift 583641
  have htrace : WordTrace (prefixWord ++ tailWord_583641) baseStart_583641 baseEnd_583641 := by
    simpa [prefixWord, tailWord_583641, baseEnd_583641] using wordTrace_append hprefix tailTrace_583641
  have hstable : (prefixWord ++ tailWord_583641).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583641).length < 2 ^ (prefixWord ++ tailWord_583641).sum := by decide
  have hdescent : baseEnd_583641 < baseStart_583641 := by decide
  rcases family_descends (prefixWord ++ tailWord_583641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583683 : List Nat := [1, 1, 1, 3, 2, 1, 1, 5, 5]
def baseStart_583683 : Nat := 118140960795 + 583683 * 2 ^ 59
def prefixEnd_583683 : Nat := 4983230072969 + 3 ^ 40 * 583683 * 2
def baseEnd_583683 : Nat := 266408825651862285580619

theorem tailTrace_583683 : CollatzResearch.WordTrace tailWord_583683 prefixEnd_583683 266408825651862285580619 := by
  unfold tailWord_583683
  simp only [CollatzResearch.WordTrace]
  refine ⟨21288667944423650965171703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14192445296282433976781135 21288667944423650965171703)
  ·
    refine ⟨31933001916635476447757555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21288667944423650965171703 31933001916635476447757555)
    ·
      refine ⟨47899502874953214671636333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31933001916635476447757555 47899502874953214671636333)
      ·
        refine ⟨17962313578107455501863625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47899502874953214671636333 17962313578107455501863625)
        ·
          refine ⟨13471735183580591626397719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17962313578107455501863625 13471735183580591626397719)
          ·
            refine ⟨20207602775370887439596579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13471735183580591626397719 20207602775370887439596579)
            ·
              refine ⟨30311404163056331159394869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20207602775370887439596579 30311404163056331159394869)
              ·
                refine ⟨2841694140286531046193269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30311404163056331159394869 2841694140286531046193269)
                ·
                  refine ⟨266408825651862285580619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2841694140286531046193269 266408825651862285580619)
                  ·
                    rfl

theorem cell20_583683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 5, 5].length) (baseStart_583683 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_583683 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_583683 prefixEnd_583683 := by exact prefixLift 583683
  have htrace : WordTrace (prefixWord ++ tailWord_583683) baseStart_583683 baseEnd_583683 := by
    simpa [prefixWord, tailWord_583683, baseEnd_583683] using wordTrace_append hprefix tailTrace_583683
  have hstable : (prefixWord ++ tailWord_583683).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583683).length < 2 ^ (prefixWord ++ tailWord_583683).sum := by decide
  have hdescent : baseEnd_583683 < baseStart_583683 := by decide
  rcases family_descends (prefixWord ++ tailWord_583683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583786 : List Nat := [3, 1, 3, 2, 4, 1, 6]
def baseStart_583786 : Nat := 118140960795 + 583786 * 2 ^ 59
def prefixEnd_583786 : Nat := 4983230072969 + 3 ^ 40 * 583786 * 2
def baseEnd_583786 : Nat := 29606204184272411682985

theorem tailTrace_583786 : CollatzResearch.WordTrace tailWord_583786 prefixEnd_583786 29606204184272411682985 := by
  unfold tailWord_583786
  simp only [CollatzResearch.WordTrace]
  refine ⟨5323106165762624889042803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14194949775366999704114141 5323106165762624889042803)
  ·
    refine ⟨7984659248643937333564205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5323106165762624889042803 7984659248643937333564205)
    ·
      refine ⟨2994247218241476500086577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7984659248643937333564205 2994247218241476500086577)
      ·
        refine ⟨2245685413681107375064933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2994247218241476500086577 2245685413681107375064933)
        ·
          refine ⟨421066015065207632824675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2245685413681107375064933 421066015065207632824675)
          ·
            refine ⟨631599022597811449237013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 421066015065207632824675 631599022597811449237013)
            ·
              refine ⟨29606204184272411682985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 631599022597811449237013 29606204184272411682985)
              ·
                rfl

theorem cell20_583786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 6].length) (baseStart_583786 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_583786 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_583786 prefixEnd_583786 := by exact prefixLift 583786
  have htrace : WordTrace (prefixWord ++ tailWord_583786) baseStart_583786 baseEnd_583786 := by
    simpa [prefixWord, tailWord_583786, baseEnd_583786] using wordTrace_append hprefix tailTrace_583786
  have hstable : (prefixWord ++ tailWord_583786).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583786).length < 2 ^ (prefixWord ++ tailWord_583786).sum := by decide
  have hdescent : baseEnd_583786 < baseStart_583786 := by decide
  rcases family_descends (prefixWord ++ tailWord_583786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583866 : List Nat := [3, 1, 1, 1, 2, 2, 5, 5]
def baseStart_583866 : Nat := 118140960795 + 583866 * 2 ^ 59
def prefixEnd_583866 : Nat := 4983230072969 + 3 ^ 40 * 583866 * 2
def baseEnd_583866 : Nat := 88830783946108994159957

theorem tailTrace_583866 : CollatzResearch.WordTrace tailWord_583866 prefixEnd_583866 88830783946108994159957 := by
  unfold tailWord_583866
  simp only [CollatzResearch.WordTrace]
  refine ⟨5323835625690168304770863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14196895001840448812722301 5323835625690168304770863)
  ·
    refine ⟨7985753438535252457156295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5323835625690168304770863 7985753438535252457156295)
    ·
      refine ⟨11978630157802878685734443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7985753438535252457156295 11978630157802878685734443)
      ·
        refine ⟨17967945236704318028601665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11978630157802878685734443 17967945236704318028601665)
        ·
          refine ⟨13475958927528238521451249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17967945236704318028601665 13475958927528238521451249)
          ·
            refine ⟨10106969195646178891088437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13475958927528238521451249 10106969195646178891088437)
            ·
              refine ⟨947528362091829271039541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10106969195646178891088437 947528362091829271039541)
              ·
                refine ⟨88830783946108994159957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 947528362091829271039541 88830783946108994159957)
                ·
                  rfl

theorem cell20_583866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5, 5].length) (baseStart_583866 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_583866 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_583866 prefixEnd_583866 := by exact prefixLift 583866
  have htrace : WordTrace (prefixWord ++ tailWord_583866) baseStart_583866 baseEnd_583866 := by
    simpa [prefixWord, tailWord_583866, baseEnd_583866] using wordTrace_append hprefix tailTrace_583866
  have hstable : (prefixWord ++ tailWord_583866).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583866).length < 2 ^ (prefixWord ++ tailWord_583866).sum := by decide
  have hdescent : baseEnd_583866 < baseStart_583866 := by decide
  rcases family_descends (prefixWord ++ tailWord_583866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583876 : List Nat := [2, 3, 3, 1, 2, 2, 1, 2, 4]
def baseStart_583876 : Nat := 118140960795 + 583876 * 2 ^ 59
def prefixEnd_583876 : Nat := 4983230072969 + 3 ^ 40 * 583876 * 2
def baseEnd_583876 : Nat := 266496916110811392146497

theorem tailTrace_583876 : CollatzResearch.WordTrace tailWord_583876 prefixEnd_583876 266496916110811392146497 := by
  unfold tailWord_583876
  simp only [CollatzResearch.WordTrace]
  refine ⟨10647853616362222463473741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14197138155149629951298321 10647853616362222463473741)
  ·
    refine ⟨3992945106135833423802653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10647853616362222463473741 3992945106135833423802653)
    ·
      refine ⟨1497354414800937533925995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3992945106135833423802653 1497354414800937533925995)
      ·
        refine ⟨2246031622201406300888993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1497354414800937533925995 2246031622201406300888993)
        ·
          refine ⟨1684523716651054725666745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2246031622201406300888993 1684523716651054725666745)
          ·
            refine ⟨1263392787488291044250059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1684523716651054725666745 1263392787488291044250059)
            ·
              refine ⟨1895089181232436566375089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1263392787488291044250059 1895089181232436566375089)
              ·
                refine ⟨1421316885924327424781317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1895089181232436566375089 1421316885924327424781317)
                ·
                  refine ⟨266496916110811392146497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1421316885924327424781317 266496916110811392146497)
                  ·
                    rfl

theorem cell20_583876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 2, 4].length) (baseStart_583876 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_583876 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_583876 prefixEnd_583876 := by exact prefixLift 583876
  have htrace : WordTrace (prefixWord ++ tailWord_583876) baseStart_583876 baseEnd_583876 := by
    simpa [prefixWord, tailWord_583876, baseEnd_583876] using wordTrace_append hprefix tailTrace_583876
  have hstable : (prefixWord ++ tailWord_583876).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583876).length < 2 ^ (prefixWord ++ tailWord_583876).sum := by decide
  have hdescent : baseEnd_583876 < baseStart_583876 := by decide
  rcases family_descends (prefixWord ++ tailWord_583876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583900 : List Nat := [2, 2, 5, 2, 1, 1, 7]
def baseStart_583900 : Nat := 118140960795 + 583900 * 2 ^ 59
def prefixEnd_583900 : Nat := 4983230072969 + 3 ^ 40 * 583900 * 2
def baseEnd_583900 : Nat := 29611985596085997260711

theorem tailTrace_583900 : CollatzResearch.WordTrace tailWord_583900 prefixEnd_583900 29611985596085997260711 := by
  unfold tailWord_583900
  simp only [CollatzResearch.WordTrace]
  refine ⟨10648291292318748512910577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14197721723091664683880769 10648291292318748512910577)
  ·
    refine ⟨7986218469239061384682933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10648291292318748512910577 7986218469239061384682933)
    ·
      refine ⟨748707981491162004814025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7986218469239061384682933 748707981491162004814025)
      ·
        refine ⟨561530986118371503610519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 748707981491162004814025 561530986118371503610519)
        ·
          refine ⟨842296479177557255415779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 561530986118371503610519 842296479177557255415779)
          ·
            refine ⟨1263444718766335883123669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 842296479177557255415779 1263444718766335883123669)
            ·
              refine ⟨29611985596085997260711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1263444718766335883123669 29611985596085997260711)
              ·
                rfl

theorem cell20_583900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 7].length) (baseStart_583900 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_583900 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_583900 prefixEnd_583900 := by exact prefixLift 583900
  have htrace : WordTrace (prefixWord ++ tailWord_583900) baseStart_583900 baseEnd_583900 := by
    simpa [prefixWord, tailWord_583900, baseEnd_583900] using wordTrace_append hprefix tailTrace_583900
  have hstable : (prefixWord ++ tailWord_583900).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583900).length < 2 ^ (prefixWord ++ tailWord_583900).sum := by decide
  have hdescent : baseEnd_583900 < baseStart_583900 := by decide
  rcases family_descends (prefixWord ++ tailWord_583900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583907 : List Nat := [1, 1, 1, 8, 1, 1, 1, 1, 5]
def baseStart_583907 : Nat := 118140960795 + 583907 * 2 ^ 59
def prefixEnd_583907 : Nat := 4983230072969 + 3 ^ 40 * 583907 * 2
def baseEnd_583907 : Nat := 266511065355513062113037

theorem tailTrace_583907 : CollatzResearch.WordTrace tailWord_583907 prefixEnd_583907 266511065355513062113037 := by
  unfold tailWord_583907
  simp only [CollatzResearch.WordTrace]
  refine ⟨21296837895612137221325975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14197891930408091480883983 21296837895612137221325975)
  ·
    refine ⟨31945256843418205831988963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21296837895612137221325975 31945256843418205831988963)
    ·
      refine ⟨47917885265127308747983445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31945256843418205831988963 47917885265127308747983445)
      ·
        refine ⟨561537717950710649390431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 47917885265127308747983445 561537717950710649390431)
        ·
          refine ⟨842306576926065974085647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 561537717950710649390431 842306576926065974085647)
          ·
            refine ⟨1263459865389098961128471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 842306576926065974085647 1263459865389098961128471)
            ·
              refine ⟨1895189798083648441692707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1263459865389098961128471 1895189798083648441692707)
              ·
                refine ⟨2842784697125472662539061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1895189798083648441692707 2842784697125472662539061)
                ·
                  refine ⟨266511065355513062113037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2842784697125472662539061 266511065355513062113037)
                  ·
                    rfl

theorem cell20_583907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 1, 5].length) (baseStart_583907 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_583907 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_583907 prefixEnd_583907 := by exact prefixLift 583907
  have htrace : WordTrace (prefixWord ++ tailWord_583907) baseStart_583907 baseEnd_583907 := by
    simpa [prefixWord, tailWord_583907, baseEnd_583907] using wordTrace_append hprefix tailTrace_583907
  have hstable : (prefixWord ++ tailWord_583907).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583907).length < 2 ^ (prefixWord ++ tailWord_583907).sum := by decide
  have hdescent : baseEnd_583907 < baseStart_583907 := by decide
  rcases family_descends (prefixWord ++ tailWord_583907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583914 : List Nat := [3, 1, 3, 1, 1, 2, 1, 6, 2]
def baseStart_583914 : Nat := 118140960795 + 583914 * 2 ^ 59
def prefixEnd_583914 : Nat := 4983230072969 + 3 ^ 40 * 583914 * 2
def baseEnd_583914 : Nat := 266514260346252148879675

theorem tailTrace_583914 : CollatzResearch.WordTrace tailWord_583914 prefixEnd_583914 266514260346252148879675 := by
  unfold tailWord_583914
  simp only [CollatzResearch.WordTrace]
  refine ⟨5324273301646694354207699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14198062137724518277887197 5324273301646694354207699)
  ·
    refine ⟨7986409952470041531311549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5324273301646694354207699 7986409952470041531311549)
    ·
      refine ⟨2994903732176265574241831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7986409952470041531311549 2994903732176265574241831)
      ·
        refine ⟨4492355598264398361362747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2994903732176265574241831 4492355598264398361362747)
        ·
          refine ⟨6738533397396597542044121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4492355598264398361362747 6738533397396597542044121)
          ·
            refine ⟨5053900048047448156533091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6738533397396597542044121 5053900048047448156533091)
            ·
              refine ⟨7580850072071172234799637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5053900048047448156533091 7580850072071172234799637)
              ·
                refine ⟨355352347128336198506233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7580850072071172234799637 355352347128336198506233)
                ·
                  refine ⟨266514260346252148879675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 355352347128336198506233 266514260346252148879675)
                  ·
                    rfl

theorem cell20_583914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 6, 2].length) (baseStart_583914 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_583914 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_583914 prefixEnd_583914 := by exact prefixLift 583914
  have htrace : WordTrace (prefixWord ++ tailWord_583914) baseStart_583914 baseEnd_583914 := by
    simpa [prefixWord, tailWord_583914, baseEnd_583914] using wordTrace_append hprefix tailTrace_583914
  have hstable : (prefixWord ++ tailWord_583914).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583914).length < 2 ^ (prefixWord ++ tailWord_583914).sum := by decide
  have hdescent : baseEnd_583914 < baseStart_583914 := by decide
  rcases family_descends (prefixWord ++ tailWord_583914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583938 : List Nat := [3, 4, 1, 1, 2, 1, 4, 4]
def baseStart_583938 : Nat := 118140960795 + 583938 * 2 ^ 59
def prefixEnd_583938 : Nat := 4983230072969 + 3 ^ 40 * 583938 * 2
def baseEnd_583938 : Nat := 88841738200071577359859

theorem tailTrace_583938 : CollatzResearch.WordTrace tailWord_583938 prefixEnd_583938 88841738200071577359859 := by
  unfold tailWord_583938
  simp only [CollatzResearch.WordTrace]
  refine ⟨5324492139624957378926117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14198645705666553010469645 5324492139624957378926117)
  ·
    refine ⟨998342276179679508548647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5324492139624957378926117 998342276179679508548647)
    ·
      refine ⟨1497513414269519262822971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 998342276179679508548647 1497513414269519262822971)
      ·
        refine ⟨2246270121404278894234457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1497513414269519262822971 2246270121404278894234457)
        ·
          refine ⟨1684702591053209170675843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2246270121404278894234457 1684702591053209170675843)
          ·
            refine ⟨2527053886579813756013765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1684702591053209170675843 2527053886579813756013765)
            ·
              refine ⟨473822603733715079252581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2527053886579813756013765 473822603733715079252581)
              ·
                refine ⟨88841738200071577359859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 473822603733715079252581 88841738200071577359859)
                ·
                  rfl

theorem cell20_583938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 4, 4].length) (baseStart_583938 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_583938 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_583938 prefixEnd_583938 := by exact prefixLift 583938
  have htrace : WordTrace (prefixWord ++ tailWord_583938) baseStart_583938 baseEnd_583938 := by
    simpa [prefixWord, tailWord_583938, baseEnd_583938] using wordTrace_append hprefix tailTrace_583938
  have hstable : (prefixWord ++ tailWord_583938).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583938).length < 2 ^ (prefixWord ++ tailWord_583938).sum := by decide
  have hdescent : baseEnd_583938 < baseStart_583938 := by decide
  rcases family_descends (prefixWord ++ tailWord_583938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583963 : List Nat := [1, 1, 1, 1, 1, 1, 14]
def baseStart_583963 : Nat := 118140960795 + 583963 * 2 ^ 59
def prefixEnd_583963 : Nat := 4983230072969 + 3 ^ 40 * 583963 * 2
def baseEnd_583963 : Nat := 29615180586825084027349

theorem tailTrace_583963 : CollatzResearch.WordTrace tailWord_583963 prefixEnd_583963 29615180586825084027349 := by
  unfold tailWord_583963
  simp only [CollatzResearch.WordTrace]
  refine ⟨21298880383409258785364543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14199253588939505856909695 21298880383409258785364543)
  ·
    refine ⟨31948320575113888178046815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21298880383409258785364543 31948320575113888178046815)
    ·
      refine ⟨47922480862670832267070223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31948320575113888178046815 47922480862670832267070223)
      ·
        refine ⟨71883721294006248400605335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47922480862670832267070223 71883721294006248400605335)
        ·
          refine ⟨107825581941009372600908003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71883721294006248400605335 107825581941009372600908003)
          ·
            refine ⟨161738372911514058901362005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107825581941009372600908003 161738372911514058901362005)
            ·
              refine ⟨29615180586825084027349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 14 161738372911514058901362005 29615180586825084027349)
              ·
                rfl

theorem cell20_583963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 14].length) (baseStart_583963 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_583963 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_583963 prefixEnd_583963 := by exact prefixLift 583963
  have htrace : WordTrace (prefixWord ++ tailWord_583963) baseStart_583963 baseEnd_583963 := by
    simpa [prefixWord, tailWord_583963, baseEnd_583963] using wordTrace_append hprefix tailTrace_583963
  have hstable : (prefixWord ++ tailWord_583963).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583963).length < 2 ^ (prefixWord ++ tailWord_583963).sum := by decide
  have hdescent : baseEnd_583963 < baseStart_583963 := by decide
  rcases family_descends (prefixWord ++ tailWord_583963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_583975 : List Nat := [1, 1, 8, 1, 2, 1, 2, 1, 3]
def baseStart_583975 : Nat := 118140960795 + 583975 * 2 ^ 59
def prefixEnd_583975 : Nat := 4983230072969 + 3 ^ 40 * 583975 * 2
def baseEnd_583975 : Nat := 266542102408407047846093

theorem tailTrace_583975 : CollatzResearch.WordTrace tailWord_583975 prefixEnd_583975 266542102408407047846093 := by
  unfold tailWord_583975
  simp only [CollatzResearch.WordTrace]
  refine ⟨21299318059365784834801379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14199545372910523223200919 21299318059365784834801379)
  ·
    refine ⟨31948977089048677252202069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21299318059365784834801379 31948977089048677252202069)
    ·
      refine ⟨374402075262289186549243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 31948977089048677252202069 374402075262289186549243)
      ·
        refine ⟨561603112893433779823865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 374402075262289186549243 561603112893433779823865)
        ·
          refine ⟨421202334670075334867899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 561603112893433779823865 421202334670075334867899)
          ·
            refine ⟨631803502005113002301849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 421202334670075334867899 631803502005113002301849)
            ·
              refine ⟨473852626503834751726387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 631803502005113002301849 473852626503834751726387)
              ·
                refine ⟨710778939755752127589581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 473852626503834751726387 710778939755752127589581)
                ·
                  refine ⟨266542102408407047846093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 710778939755752127589581 266542102408407047846093)
                  ·
                    rfl

theorem cell20_583975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 2, 1, 3].length) (baseStart_583975 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_583975 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_583975 prefixEnd_583975 := by exact prefixLift 583975
  have htrace : WordTrace (prefixWord ++ tailWord_583975) baseStart_583975 baseEnd_583975 := by
    simpa [prefixWord, tailWord_583975, baseEnd_583975] using wordTrace_append hprefix tailTrace_583975
  have hstable : (prefixWord ++ tailWord_583975).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_583975).length < 2 ^ (prefixWord ++ tailWord_583975).sum := by decide
  have hdescent : baseEnd_583975 < baseStart_583975 := by decide
  rcases family_descends (prefixWord ++ tailWord_583975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584021 : List Nat := [1, 3, 2, 2, 4, 1, 2, 2, 3]
def baseStart_584021 : Nat := 118140960795 + 584021 * 2 ^ 59
def prefixEnd_584021 : Nat := 4983230072969 + 3 ^ 40 * 584021 * 2
def baseEnd_584021 : Nat := 266563098061835332312571

theorem tailTrace_584021 : CollatzResearch.WordTrace tailWord_584021 prefixEnd_584021 266563098061835332312571 := by
  unfold tailWord_584021
  simp only [CollatzResearch.WordTrace]
  refine ⟨21300995817199134690975917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14200663878132756460650611 21300995817199134690975917)
  ·
    refine ⟨7987873431449675509115969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21300995817199134690975917 7987873431449675509115969)
    ·
      refine ⟨5990905073587256631836977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7987873431449675509115969 5990905073587256631836977)
      ·
        refine ⟨4493178805190442473877733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5990905073587256631836977 4493178805190442473877733)
        ·
          refine ⟨842471025973207963852075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4493178805190442473877733 842471025973207963852075)
          ·
            refine ⟨1263706538959811945778113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 842471025973207963852075 1263706538959811945778113)
            ·
              refine ⟨947779904219858959333585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1263706538959811945778113 947779904219858959333585)
              ·
                refine ⟨710834928164894219500189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 947779904219858959333585 710834928164894219500189)
                ·
                  refine ⟨266563098061835332312571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 710834928164894219500189 266563098061835332312571)
                  ·
                    rfl

theorem cell20_584021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 2, 2, 3].length) (baseStart_584021 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_584021 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_584021 prefixEnd_584021 := by exact prefixLift 584021
  have htrace : WordTrace (prefixWord ++ tailWord_584021) baseStart_584021 baseEnd_584021 := by
    simpa [prefixWord, tailWord_584021, baseEnd_584021] using wordTrace_append hprefix tailTrace_584021
  have hstable : (prefixWord ++ tailWord_584021).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584021).length < 2 ^ (prefixWord ++ tailWord_584021).sum := by decide
  have hdescent : baseEnd_584021 < baseStart_584021 := by decide
  rcases family_descends (prefixWord ++ tailWord_584021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584104 : List Nat := [2, 1, 6, 1, 1, 1, 2, 2, 4]
def baseStart_584104 : Nat := 118140960795 + 584104 * 2 ^ 59
def prefixEnd_584104 : Nat := 4983230072969 + 3 ^ 40 * 584104 * 2
def baseEnd_584104 : Nat := 266600981523455932545565

theorem tailTrace_584104 : CollatzResearch.WordTrace tailWord_584104 prefixEnd_584104 266600981523455932545565 := by
  unfold tailWord_584104
  simp only [CollatzResearch.WordTrace]
  refine ⟨10652011537949219933123683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14202682050598959910831577 10652011537949219933123683)
  ·
    refine ⟨15978017306923829899685525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10652011537949219933123683 15978017306923829899685525)
    ·
      refine ⟨748969561262054526547759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 15978017306923829899685525 748969561262054526547759)
      ·
        refine ⟨1123454341893081789821639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 748969561262054526547759 1123454341893081789821639)
        ·
          refine ⟨1685181512839622684732459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1123454341893081789821639 1685181512839622684732459)
          ·
            refine ⟨2527772269259434027098689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1685181512839622684732459 2527772269259434027098689)
            ·
              refine ⟨1895829201944575520324017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2527772269259434027098689 1895829201944575520324017)
              ·
                refine ⟨1421871901458431640243013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1895829201944575520324017 1421871901458431640243013)
                ·
                  refine ⟨266600981523455932545565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1421871901458431640243013 266600981523455932545565)
                  ·
                    rfl

theorem cell20_584104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 2, 4].length) (baseStart_584104 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_584104 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_584104 prefixEnd_584104 := by exact prefixLift 584104
  have htrace : WordTrace (prefixWord ++ tailWord_584104) baseStart_584104 baseEnd_584104 := by
    simpa [prefixWord, tailWord_584104, baseEnd_584104] using wordTrace_append hprefix tailTrace_584104
  have hstable : (prefixWord ++ tailWord_584104).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584104).length < 2 ^ (prefixWord ++ tailWord_584104).sum := by decide
  have hdescent : baseEnd_584104 < baseStart_584104 := by decide
  rcases family_descends (prefixWord ++ tailWord_584104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584121 : List Nat := [1, 2, 1, 4, 3, 3, 1, 3, 2]
def baseStart_584121 : Nat := 118140960795 + 584121 * 2 ^ 59
def prefixEnd_584121 : Nat := 4983230072969 + 3 ^ 40 * 584121 * 2
def baseEnd_584121 : Nat := 266608740786679428978829

theorem tailTrace_584121 : CollatzResearch.WordTrace tailWord_584121 prefixEnd_584121 266608740786679428978829 := by
  unfold tailWord_584121
  simp only [CollatzResearch.WordTrace]
  refine ⟨21304643116836851769616217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14203095411224567846410811 21304643116836851769616217)
  ·
    refine ⟨15978482337627638827212163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21304643116836851769616217 15978482337627638827212163)
    ·
      refine ⟨23967723506441458240818245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15978482337627638827212163 23967723506441458240818245)
      ·
        refine ⟨4493948157457773420153421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23967723506441458240818245 4493948157457773420153421)
        ·
          refine ⟨1685230559046665032557533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4493948157457773420153421 1685230559046665032557533)
          ·
            refine ⟨631961459642499387209075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1685230559046665032557533 631961459642499387209075)
            ·
              refine ⟨947942189463749080813613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 631961459642499387209075 947942189463749080813613)
              ·
                refine ⟨355478321048905905305105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 947942189463749080813613 355478321048905905305105)
                ·
                  refine ⟨266608740786679428978829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 355478321048905905305105 266608740786679428978829)
                  ·
                    rfl

theorem cell20_584121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 1, 3, 2].length) (baseStart_584121 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_584121 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_584121 prefixEnd_584121 := by exact prefixLift 584121
  have htrace : WordTrace (prefixWord ++ tailWord_584121) baseStart_584121 baseEnd_584121 := by
    simpa [prefixWord, tailWord_584121, baseEnd_584121] using wordTrace_append hprefix tailTrace_584121
  have hstable : (prefixWord ++ tailWord_584121).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584121).length < 2 ^ (prefixWord ++ tailWord_584121).sum := by decide
  have hdescent : baseEnd_584121 < baseStart_584121 := by decide
  rcases family_descends (prefixWord ++ tailWord_584121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584139 : List Nat := [1, 1, 1, 1, 3, 3, 1, 6, 3]
def baseStart_584139 : Nat := 118140960795 + 584139 * 2 ^ 59
def prefixEnd_584139 : Nat := 4983230072969 + 3 ^ 40 * 584139 * 2
def baseEnd_584139 : Nat := 266616956477151366378755

theorem tailTrace_584139 : CollatzResearch.WordTrace tailWord_584139 prefixEnd_584139 266616956477151366378755 := by
  unfold tailWord_584139
  simp only [CollatzResearch.WordTrace]
  refine ⟨21305299630771640843771471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14203533087181093895847647 21305299630771640843771471)
  ·
    refine ⟨31957949446157461265657207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21305299630771640843771471 31957949446157461265657207)
    ·
      refine ⟨47936924169236191898485811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31957949446157461265657207 47936924169236191898485811)
      ·
        refine ⟨71905386253854287847728717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47936924169236191898485811 71905386253854287847728717)
        ·
          refine ⟨26964519845195357942898269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71905386253854287847728717 26964519845195357942898269)
          ·
            refine ⟨10111694941948259228586851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26964519845195357942898269 10111694941948259228586851)
            ·
              refine ⟨15167542412922388842880277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10111694941948259228586851 15167542412922388842880277)
              ·
                refine ⟨710978550605736977010013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 15167542412922388842880277 710978550605736977010013)
                ·
                  refine ⟨266616956477151366378755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 710978550605736977010013 266616956477151366378755)
                  ·
                    rfl

theorem cell20_584139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 6, 3].length) (baseStart_584139 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_584139 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_584139 prefixEnd_584139 := by exact prefixLift 584139
  have htrace : WordTrace (prefixWord ++ tailWord_584139) baseStart_584139 baseEnd_584139 := by
    simpa [prefixWord, tailWord_584139, baseEnd_584139] using wordTrace_append hprefix tailTrace_584139
  have hstable : (prefixWord ++ tailWord_584139).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584139).length < 2 ^ (prefixWord ++ tailWord_584139).sum := by decide
  have hdescent : baseEnd_584139 < baseStart_584139 := by decide
  rcases family_descends (prefixWord ++ tailWord_584139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584170 : List Nat := [3, 1, 3, 1, 3, 1, 2, 6]
def baseStart_584170 : Nat := 118140960795 + 584170 * 2 ^ 59
def prefixEnd_584170 : Nat := 4983230072969 + 3 ^ 40 * 584170 * 2
def baseEnd_584170 : Nat := 88877035240617678781765

theorem tailTrace_584170 : CollatzResearch.WordTrace tailWord_584170 prefixEnd_584170 88877035240617678781765 := by
  unfold tailWord_584170
  simp only [CollatzResearch.WordTrace]
  refine ⟨5326607573414833284537491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14204286862439555425433309 5326607573414833284537491)
  ·
    refine ⟨7989911360122249926806237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5326607573414833284537491 7989911360122249926806237)
    ·
      refine ⟨2996216760045843722552339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7989911360122249926806237 2996216760045843722552339)
      ·
        refine ⟨4494325140068765583828509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2996216760045843722552339 4494325140068765583828509)
        ·
          refine ⟨1685371927525787093935691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4494325140068765583828509 1685371927525787093935691)
          ·
            refine ⟨2528057891288680640903537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1685371927525787093935691 2528057891288680640903537)
            ·
              refine ⟨1896043418466510480677653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2528057891288680640903537 1896043418466510480677653)
              ·
                refine ⟨88877035240617678781765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1896043418466510480677653 88877035240617678781765)
                ·
                  rfl

theorem cell20_584170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 6].length) (baseStart_584170 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_584170 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_584170 prefixEnd_584170 := by exact prefixLift 584170
  have htrace : WordTrace (prefixWord ++ tailWord_584170) baseStart_584170 baseEnd_584170 := by
    simpa [prefixWord, tailWord_584170, baseEnd_584170] using wordTrace_append hprefix tailTrace_584170
  have hstable : (prefixWord ++ tailWord_584170).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584170).length < 2 ^ (prefixWord ++ tailWord_584170).sum := by decide
  have hdescent : baseEnd_584170 < baseStart_584170 := by decide
  rcases family_descends (prefixWord ++ tailWord_584170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584229 : List Nat := [1, 3, 1, 2, 2, 1, 2, 8]
def baseStart_584229 : Nat := 118140960795 + 584229 * 2 ^ 59
def prefixEnd_584229 : Nat := 4983230072969 + 3 ^ 40 * 584229 * 2
def baseEnd_584229 : Nat := 88886011643170351126129

theorem tailTrace_584229 : CollatzResearch.WordTrace tailWord_584229 prefixEnd_584229 88886011643170351126129 := by
  unfold tailWord_584229
  simp only [CollatzResearch.WordTrace]
  refine ⟨21308582200445586214547741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14205721466963724143031827 21308582200445586214547741)
  ·
    refine ⟨7990718325167094830455403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21308582200445586214547741 7990718325167094830455403)
    ·
      refine ⟨11986077487750642245683105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7990718325167094830455403 11986077487750642245683105)
      ·
        refine ⟨8989558115812981684262329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11986077487750642245683105 8989558115812981684262329)
        ·
          refine ⟨6742168586859736263196747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8989558115812981684262329 6742168586859736263196747)
          ·
            refine ⟨10113252880289604394795121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6742168586859736263196747 10113252880289604394795121)
            ·
              refine ⟨7584939660217203296096341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10113252880289604394795121 7584939660217203296096341)
              ·
                refine ⟨88886011643170351126129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7584939660217203296096341 88886011643170351126129)
                ·
                  rfl

theorem cell20_584229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 8].length) (baseStart_584229 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_584229 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_584229 prefixEnd_584229 := by exact prefixLift 584229
  have htrace : WordTrace (prefixWord ++ tailWord_584229) baseStart_584229 baseEnd_584229 := by
    simpa [prefixWord, tailWord_584229, baseEnd_584229] using wordTrace_append hprefix tailTrace_584229
  have hstable : (prefixWord ++ tailWord_584229).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584229).length < 2 ^ (prefixWord ++ tailWord_584229).sum := by decide
  have hdescent : baseEnd_584229 < baseStart_584229 := by decide
  rcases family_descends (prefixWord ++ tailWord_584229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584286 : List Nat := [4, 4, 1, 2, 1, 2, 1, 3, 2]
def baseStart_584286 : Nat := 118140960795 + 584286 * 2 ^ 59
def prefixEnd_584286 : Nat := 4983230072969 + 3 ^ 40 * 584286 * 2
def baseEnd_584286 : Nat := 266684051282672188478155

theorem tailTrace_584286 : CollatzResearch.WordTrace tailWord_584286 prefixEnd_584286 266684051282672188478155 := by
  unfold tailWord_584286
  simp only [CollatzResearch.WordTrace]
  refine ⟨2663832645154885618671589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14207107440826056632915141 2663832645154885618671589)
  ·
    refine ⟨499468620966541053500923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2663832645154885618671589 499468620966541053500923)
    ·
      refine ⟨749202931449811580251385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 499468620966541053500923 749202931449811580251385)
      ·
        refine ⟨561902198587358685188539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 749202931449811580251385 561902198587358685188539)
        ·
          refine ⟨842853297881038027782809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 561902198587358685188539 842853297881038027782809)
          ·
            refine ⟨632139973410778520837107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 842853297881038027782809 632139973410778520837107)
            ·
              refine ⟨948209960116167781255661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 632139973410778520837107 948209960116167781255661)
              ·
                refine ⟨355578735043562917970873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 948209960116167781255661 355578735043562917970873)
                ·
                  refine ⟨266684051282672188478155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 355578735043562917970873 266684051282672188478155)
                  ·
                    rfl

theorem cell20_584286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_584286 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_584286 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_584286 prefixEnd_584286 := by exact prefixLift 584286
  have htrace : WordTrace (prefixWord ++ tailWord_584286) baseStart_584286 baseEnd_584286 := by
    simpa [prefixWord, tailWord_584286, baseEnd_584286] using wordTrace_append hprefix tailTrace_584286
  have hstable : (prefixWord ++ tailWord_584286).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584286).length < 2 ^ (prefixWord ++ tailWord_584286).sum := by decide
  have hdescent : baseEnd_584286 < baseStart_584286 := by decide
  rcases family_descends (prefixWord ++ tailWord_584286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584325 : List Nat := [1, 3, 1, 1, 4, 4, 2, 1, 3]
def baseStart_584325 : Nat := 118140960795 + 584325 * 2 ^ 59
def prefixEnd_584325 : Nat := 4983230072969 + 3 ^ 40 * 584325 * 2
def baseEnd_584325 : Nat := 266701851945361386177995

theorem tailTrace_584325 : CollatzResearch.WordTrace tailWord_584325 prefixEnd_584325 266701851945361386177995 := by
  unfold tailWord_584325
  simp only [CollatzResearch.WordTrace]
  refine ⟨21312083608097794610042429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14208055738731863073361619 21312083608097794610042429)
  ·
    refine ⟨7992031353036672978765911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21312083608097794610042429 7992031353036672978765911)
    ·
      refine ⟨11988047029555009468148867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7992031353036672978765911 11988047029555009468148867)
      ·
        refine ⟨17982070544332514202223301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11988047029555009468148867 17982070544332514202223301)
        ·
          refine ⟨3371638227062346412916869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17982070544332514202223301 3371638227062346412916869)
          ·
            refine ⟨632182167574189952421913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3371638227062346412916869 632182167574189952421913)
            ·
              refine ⟨474136625680642464316435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 632182167574189952421913 474136625680642464316435)
              ·
                refine ⟨711204938520963696474653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 474136625680642464316435 711204938520963696474653)
                ·
                  refine ⟨266701851945361386177995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 711204938520963696474653 266701851945361386177995)
                  ·
                    rfl

theorem cell20_584325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 2, 1, 3].length) (baseStart_584325 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_584325 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_584325 prefixEnd_584325 := by exact prefixLift 584325
  have htrace : WordTrace (prefixWord ++ tailWord_584325) baseStart_584325 baseEnd_584325 := by
    simpa [prefixWord, tailWord_584325, baseEnd_584325] using wordTrace_append hprefix tailTrace_584325
  have hstable : (prefixWord ++ tailWord_584325).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584325).length < 2 ^ (prefixWord ++ tailWord_584325).sum := by decide
  have hdescent : baseEnd_584325 < baseStart_584325 := by decide
  rcases family_descends (prefixWord ++ tailWord_584325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584343 : List Nat := [1, 1, 3, 3, 2, 1, 1, 8]
def baseStart_584343 : Nat := 118140960795 + 584343 * 2 ^ 59
def prefixEnd_584343 : Nat := 4983230072969 + 3 ^ 40 * 584343 * 2
def baseEnd_584343 : Nat := 88903355878611107859307

theorem tailTrace_584343 : CollatzResearch.WordTrace tailWord_584343 prefixEnd_584343 88903355878611107859307 := by
  unfold tailWord_584343
  simp only [CollatzResearch.WordTrace]
  refine ⟨21312740122032583684197683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14208493414688389122798455 21312740122032583684197683)
  ·
    refine ⟨31969110183048875526296525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21312740122032583684197683 31969110183048875526296525)
    ·
      refine ⟨11988416318643328322361197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31969110183048875526296525 11988416318643328322361197)
      ·
        refine ⟨4495656119491248120885449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11988416318643328322361197 4495656119491248120885449)
        ·
          refine ⟨3371742089618436090664087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4495656119491248120885449 3371742089618436090664087)
          ·
            refine ⟨5057613134427654135996131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3371742089618436090664087 5057613134427654135996131)
            ·
              refine ⟨7586419701641481203994197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5057613134427654135996131 7586419701641481203994197)
              ·
                refine ⟨88903355878611107859307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7586419701641481203994197 88903355878611107859307)
                ·
                  rfl

theorem cell20_584343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 8].length) (baseStart_584343 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_584343 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_584343 prefixEnd_584343 := by exact prefixLift 584343
  have htrace : WordTrace (prefixWord ++ tailWord_584343) baseStart_584343 baseEnd_584343 := by
    simpa [prefixWord, tailWord_584343, baseEnd_584343] using wordTrace_append hprefix tailTrace_584343
  have hstable : (prefixWord ++ tailWord_584343).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584343).length < 2 ^ (prefixWord ++ tailWord_584343).sum := by decide
  have hdescent : baseEnd_584343 < baseStart_584343 := by decide
  rcases family_descends (prefixWord ++ tailWord_584343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584360 : List Nat := [2, 1, 7, 10]
def baseStart_584360 : Nat := 118140960795 + 584360 * 2 ^ 59
def prefixEnd_584360 : Nat := 4983230072969 + 3 ^ 40 * 584360 * 2
def baseEnd_584360 : Nat := 1097604225922044526795

theorem tailTrace_584360 : CollatzResearch.WordTrace tailWord_584360 prefixEnd_584360 1097604225922044526795 := by
  unfold tailWord_584360
  simp only [CollatzResearch.WordTrace]
  refine ⟨10656680081485497793783267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14208906775313997058377689 10656680081485497793783267)
  ·
    refine ⟨15985020122228246690674901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10656680081485497793783267 15985020122228246690674901)
    ·
      refine ⟨374648909114724531812693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 15985020122228246690674901 374648909114724531812693)
      ·
        refine ⟨1097604225922044526795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 10 374648909114724531812693 1097604225922044526795)
        ·
          rfl

theorem cell20_584360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 10].length) (baseStart_584360 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_584360 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_584360 prefixEnd_584360 := by exact prefixLift 584360
  have htrace : WordTrace (prefixWord ++ tailWord_584360) baseStart_584360 baseEnd_584360 := by
    simpa [prefixWord, tailWord_584360, baseEnd_584360] using wordTrace_append hprefix tailTrace_584360
  have hstable : (prefixWord ++ tailWord_584360).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584360).length < 2 ^ (prefixWord ++ tailWord_584360).sum := by decide
  have hdescent : baseEnd_584360 < baseStart_584360 := by decide
  rcases family_descends (prefixWord ++ tailWord_584360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584362 : List Nat := [3, 1, 5, 2, 2, 1, 2, 2, 2]
def baseStart_584362 : Nat := 118140960795 + 584362 * 2 ^ 59
def prefixEnd_584362 : Nat := 4983230072969 + 3 ^ 40 * 584362 * 2
def baseEnd_584362 : Nat := 266718739753553701944511

theorem tailTrace_584362 : CollatzResearch.WordTrace tailWord_584362 prefixEnd_584362 266718739753553701944511 := by
  unfold tailWord_584362
  simp only [CollatzResearch.WordTrace]
  refine ⟨5328358277240937482284835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14208955405975833286092893 5328358277240937482284835)
  ·
    refine ⟨7992537415861406223427253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5328358277240937482284835 7992537415861406223427253)
    ·
      refine ⟨749300382737006833446305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7992537415861406223427253 749300382737006833446305)
      ·
        refine ⟨561975287052755125084729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 749300382737006833446305 561975287052755125084729)
        ·
          refine ⟨421481465289566343813547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 561975287052755125084729 421481465289566343813547)
          ·
            refine ⟨632222197934349515720321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 421481465289566343813547 632222197934349515720321)
            ·
              refine ⟨474166648450762136790241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 632222197934349515720321 474166648450762136790241)
              ·
                refine ⟨355624986338071602592681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 474166648450762136790241 355624986338071602592681)
                ·
                  refine ⟨266718739753553701944511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 355624986338071602592681 266718739753553701944511)
                  ·
                    rfl

theorem cell20_584362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 2, 2, 2].length) (baseStart_584362 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_584362 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_584362 prefixEnd_584362 := by exact prefixLift 584362
  have htrace : WordTrace (prefixWord ++ tailWord_584362) baseStart_584362 baseEnd_584362 := by
    simpa [prefixWord, tailWord_584362, baseEnd_584362] using wordTrace_append hprefix tailTrace_584362
  have hstable : (prefixWord ++ tailWord_584362).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584362).length < 2 ^ (prefixWord ++ tailWord_584362).sum := by decide
  have hdescent : baseEnd_584362 < baseStart_584362 := by decide
  rcases family_descends (prefixWord ++ tailWord_584362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584366 : List Nat := [4, 1, 4, 1, 1, 1, 4, 2, 2]
def baseStart_584366 : Nat := 118140960795 + 584366 * 2 ^ 59
def prefixEnd_584366 : Nat := 4983230072969 + 3 ^ 40 * 584366 * 2
def baseEnd_584366 : Nat := 266720565462547465811161

theorem tailTrace_584366 : CollatzResearch.WordTrace tailWord_584366 prefixEnd_584366 266720565462547465811161 := by
  unfold tailWord_584366
  simp only [CollatzResearch.WordTrace]
  refine ⟨2664197375118657326535619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14209052667299505741523301 2664197375118657326535619)
  ·
    refine ⟨3996296062677985989803429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2664197375118657326535619 3996296062677985989803429)
    ·
      refine ⟨749305511752122373088143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3996296062677985989803429 749305511752122373088143)
      ·
        refine ⟨1123958267628183559632215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 749305511752122373088143 1123958267628183559632215)
        ·
          refine ⟨1685937401442275339448323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1123958267628183559632215 1685937401442275339448323)
          ·
            refine ⟨2528906102163413009172485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1685937401442275339448323 2528906102163413009172485)
            ·
              refine ⟨474169894155639939219841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2528906102163413009172485 474169894155639939219841)
              ·
                refine ⟨355627420616729954414881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 474169894155639939219841 355627420616729954414881)
                ·
                  refine ⟨266720565462547465811161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 355627420616729954414881 266720565462547465811161)
                  ·
                    rfl

theorem cell20_584366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 4, 2, 2].length) (baseStart_584366 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_584366 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_584366 prefixEnd_584366 := by exact prefixLift 584366
  have htrace : WordTrace (prefixWord ++ tailWord_584366) baseStart_584366 baseEnd_584366 := by
    simpa [prefixWord, tailWord_584366, baseEnd_584366] using wordTrace_append hprefix tailTrace_584366
  have hstable : (prefixWord ++ tailWord_584366).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584366).length < 2 ^ (prefixWord ++ tailWord_584366).sum := by decide
  have hdescent : baseEnd_584366 < baseStart_584366 := by decide
  rcases family_descends (prefixWord ++ tailWord_584366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584367 : List Nat := [1, 1, 2, 1, 2, 5, 1, 4, 3]
def baseStart_584367 : Nat := 118140960795 + 584367 * 2 ^ 59
def prefixEnd_584367 : Nat := 4983230072969 + 3 ^ 40 * 584367 * 2
def baseEnd_584367 : Nat := 266721021889795906777823

theorem tailTrace_584367 : CollatzResearch.WordTrace tailWord_584367 prefixEnd_584367 266721021889795906777823 := by
  unfold tailWord_584367
  simp only [CollatzResearch.WordTrace]
  refine ⟨21313615473945635783071355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14209076982630423855380903 21313615473945635783071355)
  ·
    refine ⟨31970423210918453674607033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21313615473945635783071355 31970423210918453674607033)
    ·
      refine ⟨23977817408188840255955275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31970423210918453674607033 23977817408188840255955275)
      ·
        refine ⟨35966726112283260383932913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23977817408188840255955275 35966726112283260383932913)
        ·
          refine ⟨26975044584212445287949685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35966726112283260383932913 26975044584212445287949685)
          ·
            refine ⟨2528910429769916745745283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26975044584212445287949685 2528910429769916745745283)
            ·
              refine ⟨3793365644654875118617925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2528910429769916745745283 3793365644654875118617925)
              ·
                refine ⟨711256058372789084740861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3793365644654875118617925 711256058372789084740861)
                ·
                  refine ⟨266721021889795906777823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 711256058372789084740861 266721021889795906777823)
                  ·
                    rfl

theorem cell20_584367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 4, 3].length) (baseStart_584367 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_584367 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_584367 prefixEnd_584367 := by exact prefixLift 584367
  have htrace : WordTrace (prefixWord ++ tailWord_584367) baseStart_584367 baseEnd_584367 := by
    simpa [prefixWord, tailWord_584367, baseEnd_584367] using wordTrace_append hprefix tailTrace_584367
  have hstable : (prefixWord ++ tailWord_584367).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584367).length < 2 ^ (prefixWord ++ tailWord_584367).sum := by decide
  have hdescent : baseEnd_584367 < baseStart_584367 := by decide
  rcases family_descends (prefixWord ++ tailWord_584367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584408 : List Nat := [2, 1, 2, 2, 3, 3, 2, 3, 2]
def baseStart_584408 : Nat := 118140960795 + 584408 * 2 ^ 59
def prefixEnd_584408 : Nat := 4983230072969 + 3 ^ 40 * 584408 * 2
def baseEnd_584408 : Nat := 266739735406981986410989

theorem tailTrace_584408 : CollatzResearch.WordTrace tailWord_584408 prefixEnd_584408 266739735406981986410989 := by
  unfold tailWord_584408
  simp only [CollatzResearch.WordTrace]
  refine ⟨10657555433398549892656939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14210073911198066523542585 10657555433398549892656939)
  ·
    refine ⟨15986333150097824838985409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10657555433398549892656939 15986333150097824838985409)
    ·
      refine ⟨11989749862573368629239057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15986333150097824838985409 11989749862573368629239057)
      ·
        refine ⟨8992312396930026471929293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11989749862573368629239057 8992312396930026471929293)
        ·
          refine ⟨3372117148848759926973485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8992312396930026471929293 3372117148848759926973485)
          ·
            refine ⟨1264543930818284972615057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3372117148848759926973485 1264543930818284972615057)
            ·
              refine ⟨948407948113713729461293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1264543930818284972615057 948407948113713729461293)
              ·
                refine ⟨355652980542642648547985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 948407948113713729461293 355652980542642648547985)
                ·
                  refine ⟨266739735406981986410989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 355652980542642648547985 266739735406981986410989)
                  ·
                    rfl

theorem cell20_584408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2, 3, 2].length) (baseStart_584408 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_584408 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_584408 prefixEnd_584408 := by exact prefixLift 584408
  have htrace : WordTrace (prefixWord ++ tailWord_584408) baseStart_584408 baseEnd_584408 := by
    simpa [prefixWord, tailWord_584408, baseEnd_584408] using wordTrace_append hprefix tailTrace_584408
  have hstable : (prefixWord ++ tailWord_584408).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584408).length < 2 ^ (prefixWord ++ tailWord_584408).sum := by decide
  have hdescent : baseEnd_584408 < baseStart_584408 := by decide
  rcases family_descends (prefixWord ++ tailWord_584408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584429 : List Nat := [1, 5, 1, 2, 1, 1, 4, 1, 4]
def baseStart_584429 : Nat := 118140960795 + 584429 * 2 ^ 59
def prefixEnd_584429 : Nat := 4983230072969 + 3 ^ 40 * 584429 * 2
def baseEnd_584429 : Nat := 266749320379199246710903

theorem tailTrace_584429 : CollatzResearch.WordTrace tailWord_584429 prefixEnd_584429 266749320379199246710903 := by
  unfold tailWord_584429
  simp only [CollatzResearch.WordTrace]
  refine ⟨21315876799721020371828341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14210584533147346914552227 21315876799721020371828341)
  ·
    refine ⟨1998363449973845659858907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21315876799721020371828341 1998363449973845659858907)
    ·
      refine ⟨2997545174960768489788361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1998363449973845659858907 2997545174960768489788361)
      ·
        refine ⟨2248158881220576367341271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2997545174960768489788361 2248158881220576367341271)
        ·
          refine ⟨3372238321830864551011907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2248158881220576367341271 3372238321830864551011907)
          ·
            refine ⟨5058357482746296826517861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3372238321830864551011907 5058357482746296826517861)
            ·
              refine ⟨948442028014930654972099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5058357482746296826517861 948442028014930654972099)
              ·
                refine ⟨1422663042022395982458149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 948442028014930654972099 1422663042022395982458149)
                ·
                  refine ⟨266749320379199246710903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1422663042022395982458149 266749320379199246710903)
                  ·
                    rfl

theorem cell20_584429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_584429 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_584429 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_584429 prefixEnd_584429 := by exact prefixLift 584429
  have htrace : WordTrace (prefixWord ++ tailWord_584429) baseStart_584429 baseEnd_584429 := by
    simpa [prefixWord, tailWord_584429, baseEnd_584429] using wordTrace_append hprefix tailTrace_584429
  have hstable : (prefixWord ++ tailWord_584429).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584429).length < 2 ^ (prefixWord ++ tailWord_584429).sum := by decide
  have hdescent : baseEnd_584429 < baseStart_584429 := by decide
  rcases family_descends (prefixWord ++ tailWord_584429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584481 : List Nat := [1, 2, 3, 2, 1, 2, 2, 4, 3]
def baseStart_584481 : Nat := 118140960795 + 584481 * 2 ^ 59
def prefixEnd_584481 : Nat := 4983230072969 + 3 ^ 40 * 584481 * 2
def baseEnd_584481 : Nat := 266773054596118176977357

theorem tailTrace_584481 : CollatzResearch.WordTrace tailWord_584481 prefixEnd_584481 266773054596118176977357 := by
  unfold tailWord_584481
  simp only [CollatzResearch.WordTrace]
  refine ⟨21317773395532633252721297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14211848930355088835147531 21317773395532633252721297)
  ·
    refine ⟨15988330046649474939540973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21317773395532633252721297 15988330046649474939540973)
    ·
      refine ⟨5995623767493553102327865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15988330046649474939540973 5995623767493553102327865)
      ·
        refine ⟨4496717825620164826745899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5995623767493553102327865 4496717825620164826745899)
        ·
          refine ⟨6745076738430247240118849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4496717825620164826745899 6745076738430247240118849)
          ·
            refine ⟨5058807553822685430089137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6745076738430247240118849 5058807553822685430089137)
            ·
              refine ⟨3794105665367014072566853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5058807553822685430089137 3794105665367014072566853)
              ·
                refine ⟨711394812256315138606285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3794105665367014072566853 711394812256315138606285)
                ·
                  refine ⟨266773054596118176977357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 711394812256315138606285 266773054596118176977357)
                  ·
                    rfl

theorem cell20_584481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 4, 3].length) (baseStart_584481 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_584481 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_584481 prefixEnd_584481 := by exact prefixLift 584481
  have htrace : WordTrace (prefixWord ++ tailWord_584481) baseStart_584481 baseEnd_584481 := by
    simpa [prefixWord, tailWord_584481, baseEnd_584481] using wordTrace_append hprefix tailTrace_584481
  have hstable : (prefixWord ++ tailWord_584481).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584481).length < 2 ^ (prefixWord ++ tailWord_584481).sum := by decide
  have hdescent : baseEnd_584481 < baseStart_584481 := by decide
  rcases family_descends (prefixWord ++ tailWord_584481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584484 : List Nat := [2, 3, 1, 3, 3, 2, 1, 1, 4]
def baseStart_584484 : Nat := 118140960795 + 584484 * 2 ^ 59
def prefixEnd_584484 : Nat := 4983230072969 + 3 ^ 40 * 584484 * 2
def baseEnd_584484 : Nat := 266774423877863499877345

theorem tailTrace_584484 : CollatzResearch.WordTrace tailWord_584484 prefixEnd_584484 266774423877863499877345 := by
  unfold tailWord_584484
  simp only [CollatzResearch.WordTrace]
  refine ⟨10658941407260882382540253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14211921876347843176720337 10658941407260882382540253)
  ·
    refine ⟨3997103027722830893452595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10658941407260882382540253 3997103027722830893452595)
    ·
      refine ⟨5995654541584246340178893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3997103027722830893452595 5995654541584246340178893)
      ·
        refine ⟨2248370453094092377567085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5995654541584246340178893 2248370453094092377567085)
        ·
          refine ⟨843138919910284641587657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2248370453094092377567085 843138919910284641587657)
          ·
            refine ⟨632354189932713481190743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 843138919910284641587657 632354189932713481190743)
            ·
              refine ⟨948531284899070221786115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 632354189932713481190743 948531284899070221786115)
              ·
                refine ⟨1422796927348605332679173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 948531284899070221786115 1422796927348605332679173)
                ·
                  refine ⟨266774423877863499877345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1422796927348605332679173 266774423877863499877345)
                  ·
                    rfl

theorem cell20_584484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 1, 1, 4].length) (baseStart_584484 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_584484 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_584484 prefixEnd_584484 := by exact prefixLift 584484
  have htrace : WordTrace (prefixWord ++ tailWord_584484) baseStart_584484 baseEnd_584484 := by
    simpa [prefixWord, tailWord_584484, baseEnd_584484] using wordTrace_append hprefix tailTrace_584484
  have hstable : (prefixWord ++ tailWord_584484).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584484).length < 2 ^ (prefixWord ++ tailWord_584484).sum := by decide
  have hdescent : baseEnd_584484 < baseStart_584484 := by decide
  rcases family_descends (prefixWord ++ tailWord_584484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584494 : List Nat := [4, 1, 3, 2, 1, 3, 2, 1, 3]
def baseStart_584494 : Nat := 118140960795 + 584494 * 2 ^ 59
def prefixEnd_584494 : Nat := 4983230072969 + 3 ^ 40 * 584494 * 2
def baseEnd_584494 : Nat := 266778988150347909543971

theorem tailTrace_584494 : CollatzResearch.WordTrace tailWord_584494 prefixEnd_584494 266778988150347909543971 := by
  unfold tailWord_584494
  simp only [CollatzResearch.WordTrace]
  refine ⟨2664780943060692059118067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14212165029657024315296357 2664780943060692059118067)
  ·
    refine ⟨3997171414591038088677101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2664780943060692059118067 3997171414591038088677101)
    ·
      refine ⟨1498939280471639283253913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3997171414591038088677101 1498939280471639283253913)
      ·
        refine ⟨1124204460353729462440435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1498939280471639283253913 1124204460353729462440435)
        ·
          refine ⟨1686306690530594193660653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1124204460353729462440435 1686306690530594193660653)
          ·
            refine ⟨632365008948972822622745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1686306690530594193660653 632365008948972822622745)
            ·
              refine ⟨474273756711729616967059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 632365008948972822622745 474273756711729616967059)
              ·
                refine ⟨711410635067594425450589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 474273756711729616967059 711410635067594425450589)
                ·
                  refine ⟨266778988150347909543971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 711410635067594425450589 266778988150347909543971)
                  ·
                    rfl

theorem cell20_584494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 2, 1, 3].length) (baseStart_584494 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_584494 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_584494 prefixEnd_584494 := by exact prefixLift 584494
  have htrace : WordTrace (prefixWord ++ tailWord_584494) baseStart_584494 baseEnd_584494 := by
    simpa [prefixWord, tailWord_584494, baseEnd_584494] using wordTrace_append hprefix tailTrace_584494
  have hstable : (prefixWord ++ tailWord_584494).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584494).length < 2 ^ (prefixWord ++ tailWord_584494).sum := by decide
  have hdescent : baseEnd_584494 < baseStart_584494 := by decide
  rcases family_descends (prefixWord ++ tailWord_584494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584543 : List Nat := [1, 1, 2, 3, 1, 3, 3, 4, 2]
def baseStart_584543 : Nat := 118140960795 + 584543 * 2 ^ 59
def prefixEnd_584543 : Nat := 4983230072969 + 3 ^ 40 * 584543 * 2
def baseEnd_584543 : Nat := 266801353085521516910437

theorem tailTrace_584543 : CollatzResearch.WordTrace tailWord_584543 prefixEnd_584543 266801353085521516910437 := by
  unfold tailWord_584543
  simp only [CollatzResearch.WordTrace]
  refine ⟨21320034721308017841478283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14213356480872011894318855 21320034721308017841478283)
  ·
    refine ⟨31980052081962026762217425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21320034721308017841478283 31980052081962026762217425)
    ·
      refine ⟨23985039061471520071663069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31980052081962026762217425 23985039061471520071663069)
      ·
        refine ⟨8994389648051820026873651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23985039061471520071663069 8994389648051820026873651)
        ·
          refine ⟨13491584472077730040310477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8994389648051820026873651 13491584472077730040310477)
          ·
            refine ⟨5059344177029148765116429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13491584472077730040310477 5059344177029148765116429)
            ·
              refine ⟨1897254066385930786918661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5059344177029148765116429 1897254066385930786918661)
              ·
                refine ⟨355735137447362022547249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1897254066385930786918661 355735137447362022547249)
                ·
                  refine ⟨266801353085521516910437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 355735137447362022547249 266801353085521516910437)
                  ·
                    rfl

theorem cell20_584543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 4, 2].length) (baseStart_584543 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_584543 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_584543 prefixEnd_584543 := by exact prefixLift 584543
  have htrace : WordTrace (prefixWord ++ tailWord_584543) baseStart_584543 baseEnd_584543 := by
    simpa [prefixWord, tailWord_584543, baseEnd_584543] using wordTrace_append hprefix tailTrace_584543
  have hstable : (prefixWord ++ tailWord_584543).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584543).length < 2 ^ (prefixWord ++ tailWord_584543).sum := by decide
  have hdescent : baseEnd_584543 < baseStart_584543 := by decide
  rcases family_descends (prefixWord ++ tailWord_584543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584546 : List Nat := [3, 3, 2, 1, 4, 1, 1, 5]
def baseStart_584546 : Nat := 118140960795 + 584546 * 2 ^ 59
def prefixEnd_584546 : Nat := 4983230072969 + 3 ^ 40 * 584546 * 2
def baseEnd_584546 : Nat := 88934240789088946603475

theorem tailTrace_584546 : CollatzResearch.WordTrace tailWord_584546 prefixEnd_584546 88934240789088946603475 := by
  unfold tailWord_584546
  simp only [CollatzResearch.WordTrace]
  refine ⟨5330036035074287338459373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14213429426864766235891661 5330036035074287338459373)
  ·
    refine ⟨1998763513152857751922265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5330036035074287338459373 1998763513152857751922265)
    ·
      refine ⟨1499072634864643313941699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1998763513152857751922265 1499072634864643313941699)
      ·
        refine ⟨2248608952296964970912549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1499072634864643313941699 2248608952296964970912549)
        ·
          refine ⟨421614178555680932046103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2248608952296964970912549 421614178555680932046103)
          ·
            refine ⟨632421267833521398069155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 421614178555680932046103 632421267833521398069155)
            ·
              refine ⟨948631901750282097103733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 632421267833521398069155 948631901750282097103733)
              ·
                refine ⟨88934240789088946603475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 948631901750282097103733 88934240789088946603475)
                ·
                  rfl

theorem cell20_584546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 1, 5].length) (baseStart_584546 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_584546 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_584546 prefixEnd_584546 := by exact prefixLift 584546
  have htrace : WordTrace (prefixWord ++ tailWord_584546) baseStart_584546 baseEnd_584546 := by
    simpa [prefixWord, tailWord_584546, baseEnd_584546] using wordTrace_append hprefix tailTrace_584546
  have hstable : (prefixWord ++ tailWord_584546).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584546).length < 2 ^ (prefixWord ++ tailWord_584546).sum := by decide
  have hdescent : baseEnd_584546 < baseStart_584546 := by decide
  rcases family_descends (prefixWord ++ tailWord_584546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584581 : List Nat := [1, 3, 1, 1, 3, 3, 1, 5, 2]
def baseStart_584581 : Nat := 118140960795 + 584581 * 2 ^ 59
def prefixEnd_584581 : Nat := 4983230072969 + 3 ^ 40 * 584581 * 2
def baseEnd_584581 : Nat := 266818697320962273643615

theorem tailTrace_584581 : CollatzResearch.WordTrace tailWord_584581 prefixEnd_584581 266818697320962273643615 := by
  unfold tailWord_584581
  simp only [CollatzResearch.WordTrace]
  refine ⟨21321420695170350331361597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14214280463446900220907731 21321420695170350331361597)
  ·
    refine ⟨7995532760688881374260599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21321420695170350331361597 7995532760688881374260599)
    ·
      refine ⟨11993299141033322061390899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7995532760688881374260599 11993299141033322061390899)
      ·
        refine ⟨17989948711549983092086349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11993299141033322061390899 17989948711549983092086349)
        ·
          refine ⟨6746230766831243659532381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17989948711549983092086349 6746230766831243659532381)
          ·
            refine ⟨2529836537561716372324643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6746230766831243659532381 2529836537561716372324643)
            ·
              refine ⟨3794754806342574558486965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2529836537561716372324643 3794754806342574558486965)
              ·
                refine ⟨355758263094616364858153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3794754806342574558486965 355758263094616364858153)
                ·
                  refine ⟨266818697320962273643615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 355758263094616364858153 266818697320962273643615)
                  ·
                    rfl

theorem cell20_584581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 5, 2].length) (baseStart_584581 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_584581 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_584581 prefixEnd_584581 := by exact prefixLift 584581
  have htrace : WordTrace (prefixWord ++ tailWord_584581) baseStart_584581 baseEnd_584581 := by
    simpa [prefixWord, tailWord_584581, baseEnd_584581] using wordTrace_append hprefix tailTrace_584581
  have hstable : (prefixWord ++ tailWord_584581).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584581).length < 2 ^ (prefixWord ++ tailWord_584581).sum := by decide
  have hdescent : baseEnd_584581 < baseStart_584581 := by decide
  rcases family_descends (prefixWord ++ tailWord_584581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584612 : List Nat := [2, 3, 1, 2, 1, 2, 5, 1, 3]
def baseStart_584612 : Nat := 118140960795 + 584612 * 2 ^ 59
def prefixEnd_584612 : Nat := 4983230072969 + 3 ^ 40 * 584612 * 2
def baseEnd_584612 : Nat := 266832846565663943610155

theorem tailTrace_584612 : CollatzResearch.WordTrace tailWord_584612 prefixEnd_584612 266832846565663943610155 := by
  unfold tailWord_584612
  simp only [CollatzResearch.WordTrace]
  refine ⟨10661275679029021312870045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14215034238705361750493393 10661275679029021312870045)
  ·
    refine ⟨3997978379635882992326267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10661275679029021312870045 3997978379635882992326267)
    ·
      refine ⟨5996967569453824488489401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3997978379635882992326267 5996967569453824488489401)
      ·
        refine ⟨4497725677090368366367051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5996967569453824488489401 4497725677090368366367051)
        ·
          refine ⟨6746588515635552549550577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4497725677090368366367051 6746588515635552549550577)
          ·
            refine ⟨5059941386726664412162933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6746588515635552549550577 5059941386726664412162933)
            ·
              refine ⟨474369505005624788640275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5059941386726664412162933 474369505005624788640275)
              ·
                refine ⟨711554257508437182960413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 474369505005624788640275 711554257508437182960413)
                ·
                  refine ⟨266832846565663943610155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 711554257508437182960413 266832846565663943610155)
                  ·
                    rfl

theorem cell20_584612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 5, 1, 3].length) (baseStart_584612 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_584612 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_584612 prefixEnd_584612 := by exact prefixLift 584612
  have htrace : WordTrace (prefixWord ++ tailWord_584612) baseStart_584612 baseEnd_584612 := by
    simpa [prefixWord, tailWord_584612, baseEnd_584612] using wordTrace_append hprefix tailTrace_584612
  have hstable : (prefixWord ++ tailWord_584612).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584612).length < 2 ^ (prefixWord ++ tailWord_584612).sum := by decide
  have hdescent : baseEnd_584612 < baseStart_584612 := by decide
  rcases family_descends (prefixWord ++ tailWord_584612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584623 : List Nat := [1, 1, 2, 1, 2, 2, 2, 3, 6]
def baseStart_584623 : Nat := 118140960795 + 584623 * 2 ^ 59
def prefixEnd_584623 : Nat := 4983230072969 + 3 ^ 40 * 584623 * 2
def baseEnd_584623 : Nat := 266837867265396794243443

theorem tailTrace_584623 : CollatzResearch.WordTrace tailWord_584623 prefixEnd_584623 266837867265396794243443 := by
  unfold tailWord_584623
  simp only [CollatzResearch.WordTrace]
  refine ⟨21322952561018191504390523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14215301707345461002927015 21322952561018191504390523)
  ·
    refine ⟨31984428841527287256585785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21322952561018191504390523 31984428841527287256585785)
    ·
      refine ⟨23988321631145465442439339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31984428841527287256585785 23988321631145465442439339)
      ·
        refine ⟨35982482446718198163659009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23988321631145465442439339 35982482446718198163659009)
        ·
          refine ⟨26986861835038648622744257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35982482446718198163659009 26986861835038648622744257)
          ·
            refine ⟨20240146376278986467058193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26986861835038648622744257 20240146376278986467058193)
            ·
              refine ⟨15180109782209239850293645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20240146376278986467058193 15180109782209239850293645)
              ·
                refine ⟨5692541168328464943860117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15180109782209239850293645 5692541168328464943860117)
                ·
                  refine ⟨266837867265396794243443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5692541168328464943860117 266837867265396794243443)
                  ·
                    rfl

theorem cell20_584623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 3, 6].length) (baseStart_584623 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_584623 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_584623 prefixEnd_584623 := by exact prefixLift 584623
  have htrace : WordTrace (prefixWord ++ tailWord_584623) baseStart_584623 baseEnd_584623 := by
    simpa [prefixWord, tailWord_584623, baseEnd_584623] using wordTrace_append hprefix tailTrace_584623
  have hstable : (prefixWord ++ tailWord_584623).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584623).length < 2 ^ (prefixWord ++ tailWord_584623).sum := by decide
  have hdescent : baseEnd_584623 < baseStart_584623 := by decide
  rcases family_descends (prefixWord ++ tailWord_584623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584702 : List Nat := [4, 2, 2, 2, 2, 8]
def baseStart_584702 : Nat := 118140960795 + 584702 * 2 ^ 59
def prefixEnd_584702 : Nat := 4983230072969 + 3 ^ 40 * 584702 * 2
def baseEnd_584702 : Nat := 9884219445111986318881

theorem tailTrace_584702 : CollatzResearch.WordTrace tailWord_584702 prefixEnd_584702 9884219445111986318881 := by
  unfold tailWord_584702
  simp only [CollatzResearch.WordTrace]
  refine ⟨2665729240966498499564545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14217222618487991997677573 2665729240966498499564545)
  ·
    refine ⟨1999296930724873874673409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2665729240966498499564545 1999296930724873874673409)
    ·
      refine ⟨1499472698043655406005057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1999296930724873874673409 1499472698043655406005057)
      ·
        refine ⟨1124604523532741554503793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1499472698043655406005057 1124604523532741554503793)
        ·
          refine ⟨843453392649556165877845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1124604523532741554503793 843453392649556165877845)
          ·
            refine ⟨9884219445111986318881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 843453392649556165877845 9884219445111986318881)
            ·
              rfl

theorem cell20_584702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 8].length) (baseStart_584702 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_584702 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_584702 prefixEnd_584702 := by exact prefixLift 584702
  have htrace : WordTrace (prefixWord ++ tailWord_584702) baseStart_584702 baseEnd_584702 := by
    simpa [prefixWord, tailWord_584702, baseEnd_584702] using wordTrace_append hprefix tailTrace_584702
  have hstable : (prefixWord ++ tailWord_584702).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584702).length < 2 ^ (prefixWord ++ tailWord_584702).sum := by decide
  have hdescent : baseEnd_584702 < baseStart_584702 := by decide
  rcases family_descends (prefixWord ++ tailWord_584702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584709 : List Nat := [1, 3, 1, 1, 2, 3, 4, 2, 3]
def baseStart_584709 : Nat := 118140960795 + 584709 * 2 ^ 59
def prefixEnd_584709 : Nat := 4983230072969 + 3 ^ 40 * 584709 * 2
def baseEnd_584709 : Nat := 266877120008762717376425

theorem tailTrace_584709 : CollatzResearch.WordTrace tailWord_584709 prefixEnd_584709 266877120008762717376425 := by
  unfold tailWord_584709
  simp only [CollatzResearch.WordTrace]
  refine ⟨21326089238706628192021181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14217392825804418794680787 21326089238706628192021181)
  ·
    refine ⟨7997283464514985572007943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21326089238706628192021181 7997283464514985572007943)
    ·
      refine ⟨11995925196772478358011915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7997283464514985572007943 11995925196772478358011915)
      ·
        refine ⟨17993887795158717537017873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11995925196772478358011915 17993887795158717537017873)
        ·
          refine ⟨13495415846369038152763405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17993887795158717537017873 13495415846369038152763405)
          ·
            refine ⟨5060780942388389307286277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13495415846369038152763405 5060780942388389307286277)
            ·
              refine ⟨948896426697822995116177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5060780942388389307286277 948896426697822995116177)
              ·
                refine ⟨711672320023367246337133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 948896426697822995116177 711672320023367246337133)
                ·
                  refine ⟨266877120008762717376425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 711672320023367246337133 266877120008762717376425)
                  ·
                    rfl

theorem cell20_584709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4, 2, 3].length) (baseStart_584709 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_584709 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_584709 prefixEnd_584709 := by exact prefixLift 584709
  have htrace : WordTrace (prefixWord ++ tailWord_584709) baseStart_584709 baseEnd_584709 := by
    simpa [prefixWord, tailWord_584709, baseEnd_584709] using wordTrace_append hprefix tailTrace_584709
  have hstable : (prefixWord ++ tailWord_584709).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584709).length < 2 ^ (prefixWord ++ tailWord_584709).sum := by decide
  have hdescent : baseEnd_584709 < baseStart_584709 := by decide
  rcases family_descends (prefixWord ++ tailWord_584709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584712 : List Nat := [2, 1, 3, 2, 1, 3, 4, 2, 2]
def baseStart_584712 : Nat := 118140960795 + 584712 * 2 ^ 59
def prefixEnd_584712 : Nat := 4983230072969 + 3 ^ 40 * 584712 * 2
def baseEnd_584712 : Nat := 266878489290508040276413

theorem tailTrace_584712 : CollatzResearch.WordTrace tailWord_584712 prefixEnd_584712 266878489290508040276413 := by
  unfold tailWord_584712
  simp only [CollatzResearch.WordTrace]
  refine ⟨10663099328847879852190195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14217465771797173136253593 10663099328847879852190195)
  ·
    refine ⟨15994648993271819778285293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10663099328847879852190195 15994648993271819778285293)
    ·
      refine ⟨5997993372476932416856985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15994648993271819778285293 5997993372476932416856985)
      ·
        refine ⟨4498495029357699312642739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5997993372476932416856985 4498495029357699312642739)
        ·
          refine ⟨6747742544036548968964109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4498495029357699312642739 6747742544036548968964109)
          ·
            refine ⟨2530403454013705863361541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6747742544036548968964109 2530403454013705863361541)
            ·
              refine ⟨474450647627569849380289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2530403454013705863361541 474450647627569849380289)
              ·
                refine ⟨355837985720677387035217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 474450647627569849380289 355837985720677387035217)
                ·
                  refine ⟨266878489290508040276413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 355837985720677387035217 266878489290508040276413)
                  ·
                    rfl

theorem cell20_584712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 4, 2, 2].length) (baseStart_584712 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_584712 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_584712 prefixEnd_584712 := by exact prefixLift 584712
  have htrace : WordTrace (prefixWord ++ tailWord_584712) baseStart_584712 baseEnd_584712 := by
    simpa [prefixWord, tailWord_584712, baseEnd_584712] using wordTrace_append hprefix tailTrace_584712
  have hstable : (prefixWord ++ tailWord_584712).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584712).length < 2 ^ (prefixWord ++ tailWord_584712).sum := by decide
  have hdescent : baseEnd_584712 < baseStart_584712 := by decide
  rcases family_descends (prefixWord ++ tailWord_584712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584733 : List Nat := [1, 4, 2, 2, 3, 1, 1, 2, 4]
def baseStart_584733 : Nat := 118140960795 + 584733 * 2 ^ 59
def prefixEnd_584733 : Nat := 4983230072969 + 3 ^ 40 * 584733 * 2
def baseEnd_584733 : Nat := 266888074262725300576327

theorem tailTrace_584733 : CollatzResearch.WordTrace tailWord_584733 prefixEnd_584733 266888074262725300576327 := by
  unfold tailWord_584733
  simp only [CollatzResearch.WordTrace]
  refine ⟨21326964590619680290894853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14217976393746453527263235 21326964590619680290894853)
  ·
    refine ⟨3998805860741190054542785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21326964590619680290894853 3998805860741190054542785)
    ·
      refine ⟨2999104395555892540907089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3998805860741190054542785 2999104395555892540907089)
      ·
        refine ⟨2249328296666919405680317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2999104395555892540907089 2249328296666919405680317)
        ·
          refine ⟨843498111250094777130119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2249328296666919405680317 843498111250094777130119)
          ·
            refine ⟨1265247166875142165695179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 843498111250094777130119 1265247166875142165695179)
            ·
              refine ⟨1897870750312713248542769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1265247166875142165695179 1897870750312713248542769)
              ·
                refine ⟨1423403062734534936407077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1897870750312713248542769 1423403062734534936407077)
                ·
                  refine ⟨266888074262725300576327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1423403062734534936407077 266888074262725300576327)
                  ·
                    rfl

theorem cell20_584733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 2, 4].length) (baseStart_584733 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_584733 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_584733 prefixEnd_584733 := by exact prefixLift 584733
  have htrace : WordTrace (prefixWord ++ tailWord_584733) baseStart_584733 baseEnd_584733 := by
    simpa [prefixWord, tailWord_584733, baseEnd_584733] using wordTrace_append hprefix tailTrace_584733
  have hstable : (prefixWord ++ tailWord_584733).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584733).length < 2 ^ (prefixWord ++ tailWord_584733).sum := by decide
  have hdescent : baseEnd_584733 < baseStart_584733 := by decide
  rcases family_descends (prefixWord ++ tailWord_584733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584750 : List Nat := [4, 1, 3, 1, 1, 1, 4, 3, 2]
def baseStart_584750 : Nat := 118140960795 + 584750 * 2 ^ 59
def prefixEnd_584750 : Nat := 4983230072969 + 3 ^ 40 * 584750 * 2
def baseEnd_584750 : Nat := 266895833525948797009591

theorem tailTrace_584750 : CollatzResearch.WordTrace tailWord_584750 prefixEnd_584750 266895833525948797009591 := by
  unfold tailWord_584750
  simp only [CollatzResearch.WordTrace]
  refine ⟨2665948078944761524282963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14218389754372061462842469 2665948078944761524282963)
  ·
    refine ⟨3998922118417142286424445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2665948078944761524282963 3998922118417142286424445)
    ·
      refine ⟨1499595794406428357409167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3998922118417142286424445 1499595794406428357409167)
      ·
        refine ⟨2249393691609642536113751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1499595794406428357409167 2249393691609642536113751)
        ·
          refine ⟨3374090537414463804170627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2249393691609642536113751 3374090537414463804170627)
          ·
            refine ⟨5061135806121695706255941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3374090537414463804170627 5061135806121695706255941)
            ·
              refine ⟨948962963647817944922989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5061135806121695706255941 948962963647817944922989)
              ·
                refine ⟨355861111367931729346121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 948962963647817944922989 355861111367931729346121)
                ·
                  refine ⟨266895833525948797009591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 355861111367931729346121 266895833525948797009591)
                  ·
                    rfl

theorem cell20_584750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4, 3, 2].length) (baseStart_584750 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_584750 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_584750 prefixEnd_584750 := by exact prefixLift 584750
  have htrace : WordTrace (prefixWord ++ tailWord_584750) baseStart_584750 baseEnd_584750 := by
    simpa [prefixWord, tailWord_584750, baseEnd_584750] using wordTrace_append hprefix tailTrace_584750
  have hstable : (prefixWord ++ tailWord_584750).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584750).length < 2 ^ (prefixWord ++ tailWord_584750).sum := by decide
  have hdescent : baseEnd_584750 < baseStart_584750 := by decide
  rcases family_descends (prefixWord ++ tailWord_584750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584761 : List Nat := [1, 2, 1, 5, 2, 2, 7]
def baseStart_584761 : Nat := 118140960795 + 584761 * 2 ^ 59
def prefixEnd_584761 : Nat := 4983230072969 + 3 ^ 40 * 584761 * 2
def baseEnd_584761 : Nat := 29655650469520183071431

theorem tailTrace_584761 : CollatzResearch.WordTrace tailWord_584761 prefixEnd_584761 29655650469520183071431 := by
  unfold tailWord_584761
  simp only [CollatzResearch.WordTrace]
  refine ⟨21327985834518241072914137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14218657223012160715276091 21327985834518241072914137)
  ·
    refine ⟨15995989375888680804685603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21327985834518241072914137 15995989375888680804685603)
    ·
      refine ⟨23993984063833021207028405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15995989375888680804685603 23993984063833021207028405)
      ·
        refine ⟨2249436005984345738158913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23993984063833021207028405 2249436005984345738158913)
        ·
          refine ⟨1687077004488259303619185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2249436005984345738158913 1687077004488259303619185)
          ·
            refine ⟨1265307753366194477714389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1687077004488259303619185 1265307753366194477714389)
            ·
              refine ⟨29655650469520183071431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1265307753366194477714389 29655650469520183071431)
              ·
                rfl

theorem cell20_584761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 7].length) (baseStart_584761 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_584761 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_584761 prefixEnd_584761 := by exact prefixLift 584761
  have htrace : WordTrace (prefixWord ++ tailWord_584761) baseStart_584761 baseEnd_584761 := by
    simpa [prefixWord, tailWord_584761, baseEnd_584761] using wordTrace_append hprefix tailTrace_584761
  have hstable : (prefixWord ++ tailWord_584761).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584761).length < 2 ^ (prefixWord ++ tailWord_584761).sum := by decide
  have hdescent : baseEnd_584761 < baseStart_584761 := by decide
  rcases family_descends (prefixWord ++ tailWord_584761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584764 : List Nat := [2, 2, 2, 2, 2, 4, 1, 2, 3]
def baseStart_584764 : Nat := 118140960795 + 584764 * 2 ^ 59
def prefixEnd_584764 : Nat := 4983230072969 + 3 ^ 40 * 584764 * 2
def baseEnd_584764 : Nat := 266902223507426970542867

theorem tailTrace_584764 : CollatzResearch.WordTrace tailWord_584764 prefixEnd_584764 266902223507426970542867 := by
  unfold tailWord_584764
  simp only [CollatzResearch.WordTrace]
  refine ⟨10664047626753686292636673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14218730169004915056848897 10664047626753686292636673)
  ·
    refine ⟨7998035720065264719477505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10664047626753686292636673 7998035720065264719477505)
    ·
      refine ⟨5998526790048948539608129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7998035720065264719477505 5998526790048948539608129)
      ·
        refine ⟨4498895092536711404706097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5998526790048948539608129 4498895092536711404706097)
        ·
          refine ⟨3374171319402533553529573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4498895092536711404706097 3374171319402533553529573)
          ·
            refine ⟨632657122387975041286795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3374171319402533553529573 632657122387975041286795)
            ·
              refine ⟨948985683581962561930193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 632657122387975041286795 948985683581962561930193)
              ·
                refine ⟨711739262686471921447645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 948985683581962561930193 711739262686471921447645)
                ·
                  refine ⟨266902223507426970542867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 711739262686471921447645 266902223507426970542867)
                  ·
                    rfl

theorem cell20_584764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 1, 2, 3].length) (baseStart_584764 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_584764 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_584764 prefixEnd_584764 := by exact prefixLift 584764
  have htrace : WordTrace (prefixWord ++ tailWord_584764) baseStart_584764 baseEnd_584764 := by
    simpa [prefixWord, tailWord_584764, baseEnd_584764] using wordTrace_append hprefix tailTrace_584764
  have hstable : (prefixWord ++ tailWord_584764).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584764).length < 2 ^ (prefixWord ++ tailWord_584764).sum := by decide
  have hdescent : baseEnd_584764 < baseStart_584764 := by decide
  rcases family_descends (prefixWord ++ tailWord_584764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584768 : List Nat := [2, 1, 1, 2, 2, 3, 3, 1, 5]
def baseStart_584768 : Nat := 118140960795 + 584768 * 2 ^ 59
def prefixEnd_584768 : Nat := 4983230072969 + 3 ^ 40 * 584768 * 2
def baseEnd_584768 : Nat := 266904049216420734409517

theorem tailTrace_584768 : CollatzResearch.WordTrace tailWord_584768 prefixEnd_584768 266904049216420734409517 := by
  unfold tailWord_584768
  simp only [CollatzResearch.WordTrace]
  refine ⟨10664120572746440634209479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14218827430328587512279305 10664120572746440634209479)
  ·
    refine ⟨15996180859119660951314219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10664120572746440634209479 15996180859119660951314219)
    ·
      refine ⟨23994271288679491426971329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15996180859119660951314219 23994271288679491426971329)
      ·
        refine ⟨17995703466509618570228497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23994271288679491426971329 17995703466509618570228497)
        ·
          refine ⟨13496777599882213927671373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17995703466509618570228497 13496777599882213927671373)
          ·
            refine ⟨5061291599955830222876765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13496777599882213927671373 5061291599955830222876765)
            ·
              refine ⟨1897984349983436333578787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5061291599955830222876765 1897984349983436333578787)
              ·
                refine ⟨2846976524975154500368181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1897984349983436333578787 2846976524975154500368181)
                ·
                  refine ⟨266904049216420734409517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2846976524975154500368181 266904049216420734409517)
                  ·
                    rfl

theorem cell20_584768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 1, 5].length) (baseStart_584768 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_584768 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_584768 prefixEnd_584768 := by exact prefixLift 584768
  have htrace : WordTrace (prefixWord ++ tailWord_584768) baseStart_584768 baseEnd_584768 := by
    simpa [prefixWord, tailWord_584768, baseEnd_584768] using wordTrace_append hprefix tailTrace_584768
  have hstable : (prefixWord ++ tailWord_584768).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584768).length < 2 ^ (prefixWord ++ tailWord_584768).sum := by decide
  have hdescent : baseEnd_584768 < baseStart_584768 := by decide
  rcases family_descends (prefixWord ++ tailWord_584768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584781 : List Nat := [1, 6, 1, 1, 1, 3, 3, 1, 3]
def baseStart_584781 : Nat := 118140960795 + 584781 * 2 ^ 59
def prefixEnd_584781 : Nat := 4983230072969 + 3 ^ 40 * 584781 * 2
def baseEnd_584781 : Nat := 266909982770650466976131

theorem tailTrace_584781 : CollatzResearch.WordTrace tailWord_584781 prefixEnd_584781 266909982770650466976131 := by
  unfold tailWord_584781
  simp only [CollatzResearch.WordTrace]
  refine ⟨21328715294445784488642197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14219143529630522992428131 21328715294445784488642197)
  ·
    refine ⟨999783529427146147905103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 21328715294445784488642197 999783529427146147905103)
    ·
      refine ⟨1499675294140719221857655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 999783529427146147905103 1499675294140719221857655)
      ·
        refine ⟨2249512941211078832786483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1499675294140719221857655 2249512941211078832786483)
        ·
          refine ⟨3374269411816618249179725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2249512941211078832786483 3374269411816618249179725)
          ·
            refine ⟨1265351029431231843442397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3374269411816618249179725 1265351029431231843442397)
            ·
              refine ⟨474506636036711941290899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1265351029431231843442397 474506636036711941290899)
              ·
                refine ⟨711759954055067911936349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 474506636036711941290899 711759954055067911936349)
                ·
                  refine ⟨266909982770650466976131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 711759954055067911936349 266909982770650466976131)
                  ·
                    rfl

theorem cell20_584781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_584781 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_584781 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_584781 prefixEnd_584781 := by exact prefixLift 584781
  have htrace : WordTrace (prefixWord ++ tailWord_584781) baseStart_584781 baseEnd_584781 := by
    simpa [prefixWord, tailWord_584781, baseEnd_584781] using wordTrace_append hprefix tailTrace_584781
  have hstable : (prefixWord ++ tailWord_584781).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584781).length < 2 ^ (prefixWord ++ tailWord_584781).sum := by decide
  have hdescent : baseEnd_584781 < baseStart_584781 := by decide
  rcases family_descends (prefixWord ++ tailWord_584781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584809 : List Nat := [1, 2, 1, 1, 1, 6, 3, 3, 2]
def baseStart_584809 : Nat := 118140960795 + 584809 * 2 ^ 59
def prefixEnd_584809 : Nat := 4983230072969 + 3 ^ 40 * 584809 * 2
def baseEnd_584809 : Nat := 266922762733606814042683

theorem tailTrace_584809 : CollatzResearch.WordTrace tailWord_584809 prefixEnd_584809 266922762733606814042683 := by
  unfold tailWord_584809
  simp only [CollatzResearch.WordTrace]
  refine ⟨21329736538344345270661481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14219824358896230180440987 21329736538344345270661481)
  ·
    refine ⟨15997302403758258952996111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21329736538344345270661481 15997302403758258952996111)
    ·
      refine ⟨23995953605637388429494167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15997302403758258952996111 23995953605637388429494167)
      ·
        refine ⟨35993930408456082644241251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23995953605637388429494167 35993930408456082644241251)
        ·
          refine ⟨53990895612684123966361877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35993930408456082644241251 53990895612684123966361877)
          ·
            refine ⟨2530823231844568310923213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 53990895612684123966361877 2530823231844568310923213)
            ·
              refine ⟨949058711941713116596205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2530823231844568310923213 949058711941713116596205)
              ·
                refine ⟨355897016978142418723577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 949058711941713116596205 355897016978142418723577)
                ·
                  refine ⟨266922762733606814042683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 355897016978142418723577 266922762733606814042683)
                  ·
                    rfl

theorem cell20_584809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3, 3, 2].length) (baseStart_584809 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_584809 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_584809 prefixEnd_584809 := by exact prefixLift 584809
  have htrace : WordTrace (prefixWord ++ tailWord_584809) baseStart_584809 baseEnd_584809 := by
    simpa [prefixWord, tailWord_584809, baseEnd_584809] using wordTrace_append hprefix tailTrace_584809
  have hstable : (prefixWord ++ tailWord_584809).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584809).length < 2 ^ (prefixWord ++ tailWord_584809).sum := by decide
  have hdescent : baseEnd_584809 < baseStart_584809 := by decide
  rcases family_descends (prefixWord ++ tailWord_584809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584840 : List Nat := [2, 1, 3, 4, 2, 1, 1, 3, 3]
def baseStart_584840 : Nat := 118140960795 + 584840 * 2 ^ 59
def prefixEnd_584840 : Nat := 4983230072969 + 3 ^ 40 * 584840 * 2
def baseEnd_584840 : Nat := 266936911978308484009223

theorem tailTrace_584840 : CollatzResearch.WordTrace tailWord_584840 prefixEnd_584840 266936911978308484009223 := by
  unfold tailWord_584840
  simp only [CollatzResearch.WordTrace]
  refine ⟨10665433600616018782519987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14220578134154691710026649 10665433600616018782519987)
  ·
    refine ⟨15998150400924028173779981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10665433600616018782519987 15998150400924028173779981)
    ·
      refine ⟨5999306400346510565167493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15998150400924028173779981 5999306400346510565167493)
      ·
        refine ⟨1124869950064970730968905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5999306400346510565167493 1124869950064970730968905)
        ·
          refine ⟨843652462548728048226679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1124869950064970730968905 843652462548728048226679)
          ·
            refine ⟨1265478693823092072340019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 843652462548728048226679 1265478693823092072340019)
            ·
              refine ⟨1898218040734638108510029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1265478693823092072340019 1898218040734638108510029)
              ·
                refine ⟨711831765275489290691261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1898218040734638108510029 711831765275489290691261)
                ·
                  refine ⟨266936911978308484009223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 711831765275489290691261 266936911978308484009223)
                  ·
                    rfl

theorem cell20_584840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 3, 3].length) (baseStart_584840 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_584840 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_584840 prefixEnd_584840 := by exact prefixLift 584840
  have htrace : WordTrace (prefixWord ++ tailWord_584840) baseStart_584840 baseEnd_584840 := by
    simpa [prefixWord, tailWord_584840, baseEnd_584840] using wordTrace_append hprefix tailTrace_584840
  have hstable : (prefixWord ++ tailWord_584840).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584840).length < 2 ^ (prefixWord ++ tailWord_584840).sum := by decide
  have hdescent : baseEnd_584840 < baseStart_584840 := by decide
  rcases family_descends (prefixWord ++ tailWord_584840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584851 : List Nat := [1, 1, 1, 2, 1, 2, 4, 4, 4]
def baseStart_584851 : Nat := 118140960795 + 584851 * 2 ^ 59
def prefixEnd_584851 : Nat := 4983230072969 + 3 ^ 40 * 584851 * 2
def baseEnd_584851 : Nat := 266941932678041334642511

theorem tailTrace_584851 : CollatzResearch.WordTrace tailWord_584851 prefixEnd_584851 266941932678041334642511 := by
  unfold tailWord_584851
  simp only [CollatzResearch.WordTrace]
  refine ⟨21331268404192186443690407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14220845602794790962460271 21331268404192186443690407)
  ·
    refine ⟨31996902606288279665535611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21331268404192186443690407 31996902606288279665535611)
    ·
      refine ⟨47995353909432419498303417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31996902606288279665535611 47995353909432419498303417)
      ·
        refine ⟨35996515432074314623727563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47995353909432419498303417 35996515432074314623727563)
        ·
          refine ⟨53994773148111471935591345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35996515432074314623727563 53994773148111471935591345)
          ·
            refine ⟨40496079861083603951693509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53994773148111471935591345 40496079861083603951693509)
            ·
              refine ⟨7593014973953175740942533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40496079861083603951693509 7593014973953175740942533)
              ·
                refine ⟨1423690307616220451426725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7593014973953175740942533 1423690307616220451426725)
                ·
                  refine ⟨266941932678041334642511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1423690307616220451426725 266941932678041334642511)
                  ·
                    rfl

theorem cell20_584851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 4, 4].length) (baseStart_584851 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_584851 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_584851 prefixEnd_584851 := by exact prefixLift 584851
  have htrace : WordTrace (prefixWord ++ tailWord_584851) baseStart_584851 baseEnd_584851 := by
    simpa [prefixWord, tailWord_584851, baseEnd_584851] using wordTrace_append hprefix tailTrace_584851
  have hstable : (prefixWord ++ tailWord_584851).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584851).length < 2 ^ (prefixWord ++ tailWord_584851).sum := by decide
  have hdescent : baseEnd_584851 < baseStart_584851 := by decide
  rcases family_descends (prefixWord ++ tailWord_584851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584881 : List Nat := [1, 2, 2, 5, 1, 3, 2, 2, 2]
def baseStart_584881 : Nat := 118140960795 + 584881 * 2 ^ 59
def prefixEnd_584881 : Nat := 4983230072969 + 3 ^ 40 * 584881 * 2
def baseEnd_584881 : Nat := 266955625495494563642389

theorem tailTrace_584881 : CollatzResearch.WordTrace tailWord_584881 prefixEnd_584881 266955625495494563642389 := by
  unfold tailWord_584881
  simp only [CollatzResearch.WordTrace]
  refine ⟨21332362594083501567282497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14221575062722334378188331 21332362594083501567282497)
  ·
    refine ⟨15999271945562626175461873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21332362594083501567282497 15999271945562626175461873)
    ·
      refine ⟨11999453959171969631596405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15999271945562626175461873 11999453959171969631596405)
      ·
        refine ⟨1124948808672372152962163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11999453959171969631596405 1124948808672372152962163)
        ·
          refine ⟨1687423213008558229443245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1124948808672372152962163 1687423213008558229443245)
          ·
            refine ⟨632783704878209336041217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1687423213008558229443245 632783704878209336041217)
            ·
              refine ⟨474587778658657002030913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 632783704878209336041217 474587778658657002030913)
              ·
                refine ⟨355940833993992751523185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 474587778658657002030913 355940833993992751523185)
                ·
                  refine ⟨266955625495494563642389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 355940833993992751523185 266955625495494563642389)
                  ·
                    rfl

theorem cell20_584881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 2, 2, 2].length) (baseStart_584881 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_584881 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_584881 prefixEnd_584881 := by exact prefixLift 584881
  have htrace : WordTrace (prefixWord ++ tailWord_584881) baseStart_584881 baseEnd_584881 := by
    simpa [prefixWord, tailWord_584881, baseEnd_584881] using wordTrace_append hprefix tailTrace_584881
  have hstable : (prefixWord ++ tailWord_584881).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584881).length < 2 ^ (prefixWord ++ tailWord_584881).sum := by decide
  have hdescent : baseEnd_584881 < baseStart_584881 := by decide
  rcases family_descends (prefixWord ++ tailWord_584881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584892 : List Nat := [2, 2, 2, 3, 2, 3, 1, 5]
def baseStart_584892 : Nat := 118140960795 + 584892 * 2 ^ 59
def prefixEnd_584892 : Nat := 4983230072969 + 3 ^ 40 * 584892 * 2
def baseEnd_584892 : Nat := 88986882065075804758559

theorem tailTrace_584892 : CollatzResearch.WordTrace tailWord_584892 prefixEnd_584892 88986882065075804758559 := by
  unfold tailWord_584892
  simp only [CollatzResearch.WordTrace]
  refine ⟨10666381898521825222966465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14221842531362433630621953 10666381898521825222966465)
  ·
    refine ⟨7999786423891368917224849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10666381898521825222966465 7999786423891368917224849)
    ·
      refine ⟨5999839817918526687918637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7999786423891368917224849 5999839817918526687918637)
      ·
        refine ⟨2249939931719447507969489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5999839817918526687918637 2249939931719447507969489)
        ·
          refine ⟨1687454948789585630977117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2249939931719447507969489 1687454948789585630977117)
          ·
            refine ⟨632795605796094611616419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1687454948789585630977117 632795605796094611616419)
            ·
              refine ⟨949193408694141917424629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 632795605796094611616419 949193408694141917424629)
              ·
                refine ⟨88986882065075804758559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 949193408694141917424629 88986882065075804758559)
                ·
                  rfl

theorem cell20_584892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 1, 5].length) (baseStart_584892 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_584892 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_584892 prefixEnd_584892 := by exact prefixLift 584892
  have htrace : WordTrace (prefixWord ++ tailWord_584892) baseStart_584892 baseEnd_584892 := by
    simpa [prefixWord, tailWord_584892, baseEnd_584892] using wordTrace_append hprefix tailTrace_584892
  have hstable : (prefixWord ++ tailWord_584892).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584892).length < 2 ^ (prefixWord ++ tailWord_584892).sum := by decide
  have hdescent : baseEnd_584892 < baseStart_584892 := by decide
  rcases family_descends (prefixWord ++ tailWord_584892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584906 : List Nat := [3, 1, 2, 1, 3, 3, 1, 2, 4]
def baseStart_584906 : Nat := 118140960795 + 584906 * 2 ^ 59
def prefixEnd_584906 : Nat := 4983230072969 + 3 ^ 40 * 584906 * 2
def baseEnd_584906 : Nat := 266967036176705587808953

theorem tailTrace_584906 : CollatzResearch.WordTrace tailWord_584906 prefixEnd_584906 266967036176705587808953 := by
  unfold tailWord_584906
  simp only [CollatzResearch.WordTrace]
  refine ⟨5333318604748232709235643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14222182945995287224628381 5333318604748232709235643)
  ·
    refine ⟨7999977907122349063853465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5333318604748232709235643 7999977907122349063853465)
    ·
      refine ⟨5999983430341761797890099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7999977907122349063853465 5999983430341761797890099)
      ·
        refine ⟨8999975145512642696835149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5999983430341761797890099 8999975145512642696835149)
        ·
          refine ⟨3374990679567241011313181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8999975145512642696835149 3374990679567241011313181)
          ·
            refine ⟨1265621504837715379242443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3374990679567241011313181 1265621504837715379242443)
            ·
              refine ⟨1898432257256573068863665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1265621504837715379242443 1898432257256573068863665)
              ·
                refine ⟨1423824192942429801647749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1898432257256573068863665 1423824192942429801647749)
                ·
                  refine ⟨266967036176705587808953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1423824192942429801647749 266967036176705587808953)
                  ·
                    rfl

theorem cell20_584906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 2, 4].length) (baseStart_584906 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_584906 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_584906 prefixEnd_584906 := by exact prefixLift 584906
  have htrace : WordTrace (prefixWord ++ tailWord_584906) baseStart_584906 baseEnd_584906 := by
    simpa [prefixWord, tailWord_584906, baseEnd_584906] using wordTrace_append hprefix tailTrace_584906
  have hstable : (prefixWord ++ tailWord_584906).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584906).length < 2 ^ (prefixWord ++ tailWord_584906).sum := by decide
  have hdescent : baseEnd_584906 < baseStart_584906 := by decide
  rcases family_descends (prefixWord ++ tailWord_584906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584933 : List Nat := [1, 3, 1, 4, 4, 1, 1, 2, 3]
def baseStart_584933 : Nat := 118140960795 + 584933 * 2 ^ 59
def prefixEnd_584933 : Nat := 4983230072969 + 3 ^ 40 * 584933 * 2
def baseEnd_584933 : Nat := 266979359712413493908843

theorem tailTrace_584933 : CollatzResearch.WordTrace tailWord_584933 prefixEnd_584933 266979359712413493908843 := by
  unfold tailWord_584933
  simp only [CollatzResearch.WordTrace]
  refine ⟨21334259189895114448175453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14222839459930076298783635 21334259189895114448175453)
  ·
    refine ⟨8000347196210667918065795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21334259189895114448175453 8000347196210667918065795)
    ·
      refine ⟨12000520794316001877098693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8000347196210667918065795 12000520794316001877098693)
      ·
        refine ⟨2250097648934250351956005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12000520794316001877098693 2250097648934250351956005)
        ·
          refine ⟨421893309175171940991751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2250097648934250351956005 421893309175171940991751)
          ·
            refine ⟨632839963762757911487627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 421893309175171940991751 632839963762757911487627)
            ·
              refine ⟨949259945644136867231441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 632839963762757911487627 949259945644136867231441)
              ·
                refine ⟨711944959233102650423581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 949259945644136867231441 711944959233102650423581)
                ·
                  refine ⟨266979359712413493908843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 711944959233102650423581 266979359712413493908843)
                  ·
                    rfl

theorem cell20_584933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 1, 2, 3].length) (baseStart_584933 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_584933 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_584933 prefixEnd_584933 := by exact prefixLift 584933
  have htrace : WordTrace (prefixWord ++ tailWord_584933) baseStart_584933 baseEnd_584933 := by
    simpa [prefixWord, tailWord_584933, baseEnd_584933] using wordTrace_append hprefix tailTrace_584933
  have hstable : (prefixWord ++ tailWord_584933).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584933).length < 2 ^ (prefixWord ++ tailWord_584933).sum := by decide
  have hdescent : baseEnd_584933 < baseStart_584933 := by decide
  rcases family_descends (prefixWord ++ tailWord_584933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584965 : List Nat := [1, 3, 1, 1, 2, 1, 3, 4, 4]
def baseStart_584965 : Nat := 118140960795 + 584965 * 2 ^ 59
def prefixEnd_584965 : Nat := 4983230072969 + 3 ^ 40 * 584965 * 2
def baseEnd_584965 : Nat := 266993965384363604842045

theorem tailTrace_584965 : CollatzResearch.WordTrace tailWord_584965 prefixEnd_584965 266993965384363604842045 := by
  unfold tailWord_584965
  simp only [CollatzResearch.WordTrace]
  refine ⟨21335426325779183913340349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14223617550519455942226899 21335426325779183913340349)
  ·
    refine ⟨8000784872167193967502631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21335426325779183913340349 8000784872167193967502631)
    ·
      refine ⟨12001177308250790951253947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8000784872167193967502631 12001177308250790951253947)
      ·
        refine ⟨18001765962376186426880921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12001177308250790951253947 18001765962376186426880921)
        ·
          refine ⟨13501324471782139820160691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18001765962376186426880921 13501324471782139820160691)
          ·
            refine ⟨20251986707673209730241037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13501324471782139820160691 20251986707673209730241037)
            ·
              refine ⟨7594495015377453648840389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20251986707673209730241037 7594495015377453648840389)
              ·
                refine ⟨1423967815383272559157573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7594495015377453648840389 1423967815383272559157573)
                ·
                  refine ⟨266993965384363604842045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1423967815383272559157573 266993965384363604842045)
                  ·
                    rfl

theorem cell20_584965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 4, 4].length) (baseStart_584965 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_584965 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_584965 prefixEnd_584965 := by exact prefixLift 584965
  have htrace : WordTrace (prefixWord ++ tailWord_584965) baseStart_584965 baseEnd_584965 := by
    simpa [prefixWord, tailWord_584965, baseEnd_584965] using wordTrace_append hprefix tailTrace_584965
  have hstable : (prefixWord ++ tailWord_584965).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584965).length < 2 ^ (prefixWord ++ tailWord_584965).sum := by decide
  have hdescent : baseEnd_584965 < baseStart_584965 := by decide
  rcases family_descends (prefixWord ++ tailWord_584965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584989 : List Nat := [1, 4, 2, 3, 1, 1, 8]
def baseStart_584989 : Nat := 118140960795 + 584989 * 2 ^ 59
def prefixEnd_584989 : Nat := 4983230072969 + 3 ^ 40 * 584989 * 2
def baseEnd_584989 : Nat := 29667213293147354226883

theorem tailTrace_584989 : CollatzResearch.WordTrace tailWord_584989 prefixEnd_584989 29667213293147354226883 := by
  unfold tailWord_584989
  simp only [CollatzResearch.WordTrace]
  refine ⟨21336301677692236012214021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14224201118461490674809347 21336301677692236012214021)
  ·
    refine ⟨4000556564567294252290129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21336301677692236012214021 4000556564567294252290129)
    ·
      refine ⟨3000417423425470689217597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4000556564567294252290129 3000417423425470689217597)
      ·
        refine ⟨1125156533784551508456599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3000417423425470689217597 1125156533784551508456599)
        ·
          refine ⟨1687734800676827262684899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1125156533784551508456599 1687734800676827262684899)
          ·
            refine ⟨2531602201015240894027349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1687734800676827262684899 2531602201015240894027349)
            ·
              refine ⟨29667213293147354226883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2531602201015240894027349 29667213293147354226883)
              ·
                rfl

theorem cell20_584989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 8].length) (baseStart_584989 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_584989 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_584989 prefixEnd_584989 := by exact prefixLift 584989
  have htrace : WordTrace (prefixWord ++ tailWord_584989) baseStart_584989 baseEnd_584989 := by
    simpa [prefixWord, tailWord_584989, baseEnd_584989] using wordTrace_append hprefix tailTrace_584989
  have hstable : (prefixWord ++ tailWord_584989).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584989).length < 2 ^ (prefixWord ++ tailWord_584989).sum := by decide
  have hdescent : baseEnd_584989 < baseStart_584989 := by decide
  rcases family_descends (prefixWord ++ tailWord_584989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_584996 : List Nat := [2, 3, 1, 3, 1, 1, 1, 3, 5]
def baseStart_584996 : Nat := 118140960795 + 584996 * 2 ^ 59
def prefixEnd_584996 : Nat := 4983230072969 + 3 ^ 40 * 584996 * 2
def baseEnd_584996 : Nat := 267008114629065274808585

theorem tailTrace_584996 : CollatzResearch.WordTrace tailWord_584996 prefixEnd_584996 267008114629065274808585 := by
  unfold tailWord_584996
  simp only [CollatzResearch.WordTrace]
  refine ⟨10668278494333438103859421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14224371325777917471812561 10668278494333438103859421)
  ·
    refine ⟨4000604435375039288947283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10668278494333438103859421 4000604435375039288947283)
    ·
      refine ⟨6000906653062558933420925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4000604435375039288947283 6000906653062558933420925)
      ·
        refine ⟨2250339994898459600032847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6000906653062558933420925 2250339994898459600032847)
        ·
          refine ⟨3375509992347689400049271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2250339994898459600032847 3375509992347689400049271)
          ·
            refine ⟨5063264988521534100073907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3375509992347689400049271 5063264988521534100073907)
            ·
              refine ⟨7594897482782301150110861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5063264988521534100073907 7594897482782301150110861)
              ·
                refine ⟨2848086556043362931291573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7594897482782301150110861 2848086556043362931291573)
                ·
                  refine ⟨267008114629065274808585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2848086556043362931291573 267008114629065274808585)
                  ·
                    rfl

theorem cell20_584996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 3, 5].length) (baseStart_584996 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_584996 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_584996 prefixEnd_584996 := by exact prefixLift 584996
  have htrace : WordTrace (prefixWord ++ tailWord_584996) baseStart_584996 baseEnd_584996 := by
    simpa [prefixWord, tailWord_584996, baseEnd_584996] using wordTrace_append hprefix tailTrace_584996
  have hstable : (prefixWord ++ tailWord_584996).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_584996).length < 2 ^ (prefixWord ++ tailWord_584996).sum := by decide
  have hdescent : baseEnd_584996 < baseStart_584996 := by decide
  rcases family_descends (prefixWord ++ tailWord_584996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585013 : List Nat := [1, 3, 3, 1, 2, 3, 1, 3, 3]
def baseStart_585013 : Nat := 118140960795 + 585013 * 2 ^ 59
def prefixEnd_585013 : Nat := 4983230072969 + 3 ^ 40 * 585013 * 2
def baseEnd_585013 : Nat := 267015873892288771241849

theorem tailTrace_585013 : CollatzResearch.WordTrace tailWord_585013 prefixEnd_585013 267015873892288771241849 := by
  unfold tailWord_585013
  simp only [CollatzResearch.WordTrace]
  refine ⟨21337177029605288111087693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14224784686403525407391795 21337177029605288111087693)
  ·
    refine ⟨8001441386101983041657885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21337177029605288111087693 8001441386101983041657885)
    ·
      refine ⟨3000540519788243640621707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8001441386101983041657885 3000540519788243640621707)
      ·
        refine ⟨4500810779682365460932561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3000540519788243640621707 4500810779682365460932561)
        ·
          refine ⟨3375608084761774095699421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4500810779682365460932561 3375608084761774095699421)
          ·
            refine ⟨1265853031785665285887283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3375608084761774095699421 1265853031785665285887283)
            ·
              refine ⟨1898779547678497928830925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1265853031785665285887283 1898779547678497928830925)
              ·
                refine ⟨712042330379436723311597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1898779547678497928830925 712042330379436723311597)
                ·
                  refine ⟨267015873892288771241849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 712042330379436723311597 267015873892288771241849)
                  ·
                    rfl

theorem cell20_585013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 3, 3].length) (baseStart_585013 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_585013 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_585013 prefixEnd_585013 := by exact prefixLift 585013
  have htrace : WordTrace (prefixWord ++ tailWord_585013) baseStart_585013 baseEnd_585013 := by
    simpa [prefixWord, tailWord_585013, baseEnd_585013] using wordTrace_append hprefix tailTrace_585013
  have hstable : (prefixWord ++ tailWord_585013).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585013).length < 2 ^ (prefixWord ++ tailWord_585013).sum := by decide
  have hdescent : baseEnd_585013 < baseStart_585013 := by decide
  rcases family_descends (prefixWord ++ tailWord_585013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585046 : List Nat := [5, 2, 3, 1, 1, 2, 2, 2, 2]
def baseStart_585046 : Nat := 118140960795 + 585046 * 2 ^ 59
def prefixEnd_585046 : Nat := 4983230072969 + 3 ^ 40 * 585046 * 2
def baseEnd_585046 : Nat := 267030935991487323141715

theorem tailTrace_585046 : CollatzResearch.WordTrace tailWord_585046 prefixEnd_585046 267030935991487323141715 := by
  unfold tailWord_585046
  simp only [CollatzResearch.WordTrace]
  refine ⟨1333648789905358421689937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14225587092323823164692661 1333648789905358421689937)
  ·
    refine ⟨1000236592429018816267453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1333648789905358421689937 1000236592429018816267453)
    ·
      refine ⟨375088722160882056100295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1000236592429018816267453 375088722160882056100295)
      ·
        refine ⟨562633083241323084150443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 375088722160882056100295 562633083241323084150443)
        ·
          refine ⟨843949624861984626225665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 562633083241323084150443 843949624861984626225665)
          ·
            refine ⟨632962218646488469669249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 843949624861984626225665 632962218646488469669249)
            ·
              refine ⟨474721663984866352251937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 632962218646488469669249 474721663984866352251937)
              ·
                refine ⟨356041247988649764188953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 474721663984866352251937 356041247988649764188953)
                ·
                  refine ⟨267030935991487323141715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 356041247988649764188953 267030935991487323141715)
                  ·
                    rfl

theorem cell20_585046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 2, 2, 2].length) (baseStart_585046 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_585046 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_585046 prefixEnd_585046 := by exact prefixLift 585046
  have htrace : WordTrace (prefixWord ++ tailWord_585046) baseStart_585046 baseEnd_585046 := by
    simpa [prefixWord, tailWord_585046, baseEnd_585046] using wordTrace_append hprefix tailTrace_585046
  have hstable : (prefixWord ++ tailWord_585046).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585046).length < 2 ^ (prefixWord ++ tailWord_585046).sum := by decide
  have hdescent : baseEnd_585046 < baseStart_585046 := by decide
  rcases family_descends (prefixWord ++ tailWord_585046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585058 : List Nat := [3, 3, 2, 1, 1, 1, 2, 3, 4]
def baseStart_585058 : Nat := 118140960795 + 585058 * 2 ^ 59
def prefixEnd_585058 : Nat := 4983230072969 + 3 ^ 40 * 585058 * 2
def baseEnd_585058 : Nat := 267036413118468614741665

theorem tailTrace_585058 : CollatzResearch.WordTrace tailWord_585058 prefixEnd_585058 267036413118468614741665 := by
  unfold tailWord_585058
  simp only [CollatzResearch.WordTrace]
  refine ⟨5334704578610565199118957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14225878876294840530983885 5334704578610565199118957)
  ·
    refine ⟨2000514216978961949669609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5334704578610565199118957 2000514216978961949669609)
    ·
      refine ⟨1500385662734221462252207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2000514216978961949669609 1500385662734221462252207)
      ·
        refine ⟨2250578494101332193378311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1500385662734221462252207 2250578494101332193378311)
        ·
          refine ⟨3375867741151998290067467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2250578494101332193378311 3375867741151998290067467)
          ·
            refine ⟨5063801611727997435101201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3375867741151998290067467 5063801611727997435101201)
            ·
              refine ⟨3797851208795998076325901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5063801611727997435101201 3797851208795998076325901)
              ·
                refine ⟨1424194203298499278622213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3797851208795998076325901 1424194203298499278622213)
                ·
                  refine ⟨267036413118468614741665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1424194203298499278622213 267036413118468614741665)
                  ·
                    rfl

theorem cell20_585058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_585058 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_585058 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_585058 prefixEnd_585058 := by exact prefixLift 585058
  have htrace : WordTrace (prefixWord ++ tailWord_585058) baseStart_585058 baseEnd_585058 := by
    simpa [prefixWord, tailWord_585058, baseEnd_585058] using wordTrace_append hprefix tailTrace_585058
  have hstable : (prefixWord ++ tailWord_585058).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585058).length < 2 ^ (prefixWord ++ tailWord_585058).sum := by decide
  have hdescent : baseEnd_585058 < baseStart_585058 := by decide
  rcases family_descends (prefixWord ++ tailWord_585058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585072 : List Nat := [2, 1, 1, 1, 4, 2, 1, 5, 3]
def baseStart_585072 : Nat := 118140960795 + 585072 * 2 ^ 59
def prefixEnd_585072 : Nat := 4983230072969 + 3 ^ 40 * 585072 * 2
def baseEnd_585072 : Nat := 267042803099946788274941

theorem tailTrace_585072 : CollatzResearch.WordTrace tailWord_585072 prefixEnd_585072 267042803099946788274941 := by
  unfold tailWord_585072
  simp only [CollatzResearch.WordTrace]
  refine ⟨10669664468195770593742735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14226219290927694124990313 10669664468195770593742735)
  ·
    refine ⟨16004496702293655890614103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10669664468195770593742735 16004496702293655890614103)
    ·
      refine ⟨24006745053440483835921155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16004496702293655890614103 24006745053440483835921155)
      ·
        refine ⟨36010117580160725753881733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24006745053440483835921155 36010117580160725753881733)
        ·
          refine ⟨6751897046280136078852825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36010117580160725753881733 6751897046280136078852825)
          ·
            refine ⟨5063922784710102059139619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6751897046280136078852825 5063922784710102059139619)
            ·
              refine ⟨7595884177065153088709429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5063922784710102059139619 7595884177065153088709429)
              ·
                refine ⟨712114141599858102066509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7595884177065153088709429 712114141599858102066509)
                ·
                  refine ⟨267042803099946788274941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 712114141599858102066509 267042803099946788274941)
                  ·
                    rfl

theorem cell20_585072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 5, 3].length) (baseStart_585072 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_585072 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_585072 prefixEnd_585072 := by exact prefixLift 585072
  have htrace : WordTrace (prefixWord ++ tailWord_585072) baseStart_585072 baseEnd_585072 := by
    simpa [prefixWord, tailWord_585072, baseEnd_585072] using wordTrace_append hprefix tailTrace_585072
  have hstable : (prefixWord ++ tailWord_585072).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585072).length < 2 ^ (prefixWord ++ tailWord_585072).sum := by decide
  have hdescent : baseEnd_585072 < baseStart_585072 := by decide
  rcases family_descends (prefixWord ++ tailWord_585072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585079 : List Nat := [1, 1, 3, 1, 1, 2, 5, 2, 4]
def baseStart_585079 : Nat := 118140960795 + 585079 * 2 ^ 59
def prefixEnd_585079 : Nat := 4983230072969 + 3 ^ 40 * 585079 * 2
def baseEnd_585079 : Nat := 267045998090685875041579

theorem tailTrace_585079 : CollatzResearch.WordTrace tailWord_585079 prefixEnd_585079 267045998090685875041579 := by
  unfold tailWord_585079
  simp only [CollatzResearch.WordTrace]
  refine ⟨21339584247366181382990291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14226389498244120921993527 21339584247366181382990291)
  ·
    refine ⟨32009376371049272074485437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21339584247366181382990291 32009376371049272074485437)
    ·
      refine ⟨12003516139143477027932039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32009376371049272074485437 12003516139143477027932039)
      ·
        refine ⟨18005274208715215541898059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12003516139143477027932039 18005274208715215541898059)
        ·
          refine ⟨27007911313072823312847089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18005274208715215541898059 27007911313072823312847089)
          ·
            refine ⟨20255933484804617484635317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27007911313072823312847089 20255933484804617484635317)
            ·
              refine ⟨1898993764200432889184561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20255933484804617484635317 1898993764200432889184561)
              ·
                refine ⟨1424245323150324666888421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1898993764200432889184561 1424245323150324666888421)
                ·
                  refine ⟨267045998090685875041579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1424245323150324666888421 267045998090685875041579)
                  ·
                    rfl

theorem cell20_585079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 2, 4].length) (baseStart_585079 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_585079 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_585079 prefixEnd_585079 := by exact prefixLift 585079
  have htrace : WordTrace (prefixWord ++ tailWord_585079) baseStart_585079 baseEnd_585079 := by
    simpa [prefixWord, tailWord_585079, baseEnd_585079] using wordTrace_append hprefix tailTrace_585079
  have hstable : (prefixWord ++ tailWord_585079).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585079).length < 2 ^ (prefixWord ++ tailWord_585079).sum := by decide
  have hdescent : baseEnd_585079 < baseStart_585079 := by decide
  rcases family_descends (prefixWord ++ tailWord_585079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585106 : List Nat := [3, 2, 3, 3, 1, 1, 1, 1, 5]
def baseStart_585106 : Nat := 118140960795 + 585106 * 2 ^ 59
def prefixEnd_585106 : Nat := 4983230072969 + 3 ^ 40 * 585106 * 2
def baseEnd_585106 : Nat := 267058321626393781141469

theorem tailTrace_585106 : CollatzResearch.WordTrace tailWord_585106 prefixEnd_585106 267058321626393781141469 := by
  unfold tailWord_585106
  simp only [CollatzResearch.WordTrace]
  refine ⟨5335142254567091248555793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14227046012178909996148781 5335142254567091248555793)
  ·
    refine ⟨4001356690925318436416845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5335142254567091248555793 4001356690925318436416845)
    ·
      refine ⟨1500508759096994413656317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4001356690925318436416845 1500508759096994413656317)
      ·
        refine ⟨562690784661372905121119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1500508759096994413656317 562690784661372905121119)
        ·
          refine ⟨844036176992059357681679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 562690784661372905121119 844036176992059357681679)
          ·
            refine ⟨1266054265488089036522519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 844036176992059357681679 1266054265488089036522519)
            ·
              refine ⟨1899081398232133554783779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1266054265488089036522519 1899081398232133554783779)
              ·
                refine ⟨2848622097348200332175669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1899081398232133554783779 2848622097348200332175669)
                ·
                  refine ⟨267058321626393781141469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2848622097348200332175669 267058321626393781141469)
                  ·
                    rfl

theorem cell20_585106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 1, 5].length) (baseStart_585106 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_585106 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_585106 prefixEnd_585106 := by exact prefixLift 585106
  have htrace : WordTrace (prefixWord ++ tailWord_585106) baseStart_585106 baseEnd_585106 := by
    simpa [prefixWord, tailWord_585106, baseEnd_585106] using wordTrace_append hprefix tailTrace_585106
  have hstable : (prefixWord ++ tailWord_585106).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585106).length < 2 ^ (prefixWord ++ tailWord_585106).sum := by decide
  have hdescent : baseEnd_585106 < baseStart_585106 := by decide
  rcases family_descends (prefixWord ++ tailWord_585106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585124 : List Nat := [2, 3, 1, 2, 1, 1, 1, 9]
def baseStart_585124 : Nat := 118140960795 + 585124 * 2 ^ 59
def prefixEnd_585124 : Nat := 4983230072969 + 3 ^ 40 * 585124 * 2
def baseEnd_585124 : Nat := 89022179105621906180465

theorem tailTrace_585124 : CollatzResearch.WordTrace tailWord_585124 prefixEnd_585124 89022179105621906180465 := by
  unfold tailWord_585124
  simp only [CollatzResearch.WordTrace]
  refine ⟨10670612766101577034189213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14227483688135436045585617 10670612766101577034189213)
  ·
    refine ⟨4001479787288091387820955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10670612766101577034189213 4001479787288091387820955)
    ·
      refine ⟨6002219680932137081731433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4001479787288091387820955 6002219680932137081731433)
      ·
        refine ⟨4501664760699102811298575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6002219680932137081731433 4501664760699102811298575)
        ·
          refine ⟨6752497141048654216947863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4501664760699102811298575 6752497141048654216947863)
          ·
            refine ⟨10128745711572981325421795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6752497141048654216947863 10128745711572981325421795)
            ·
              refine ⟨15193118567359471988132693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10128745711572981325421795 15193118567359471988132693)
              ·
                refine ⟨89022179105621906180465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15193118567359471988132693 89022179105621906180465)
                ·
                  rfl

theorem cell20_585124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 9].length) (baseStart_585124 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_585124 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_585124 prefixEnd_585124 := by exact prefixLift 585124
  have htrace : WordTrace (prefixWord ++ tailWord_585124) baseStart_585124 baseEnd_585124 := by
    simpa [prefixWord, tailWord_585124, baseEnd_585124] using wordTrace_append hprefix tailTrace_585124
  have hstable : (prefixWord ++ tailWord_585124).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585124).length < 2 ^ (prefixWord ++ tailWord_585124).sum := by decide
  have hdescent : baseEnd_585124 < baseStart_585124 := by decide
  rcases family_descends (prefixWord ++ tailWord_585124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585141 : List Nat := [1, 3, 3, 2, 2, 2, 1, 6]
def baseStart_585141 : Nat := 118140960795 + 585141 * 2 ^ 59
def prefixEnd_585141 : Nat := 4983230072969 + 3 ^ 40 * 585141 * 2
def baseEnd_585141 : Nat := 89024765526696404991553

theorem tailTrace_585141 : CollatzResearch.WordTrace tailWord_585141 prefixEnd_585141 89024765526696404991553 := by
  unfold tailWord_585141
  simp only [CollatzResearch.WordTrace]
  refine ⟨21341845573141565971747277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14227897048761043981164851 21341845573141565971747277)
  ·
    refine ⟨8003192089928087239405229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21341845573141565971747277 8003192089928087239405229)
    ·
      refine ⟨3001197033723032714776961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8003192089928087239405229 3001197033723032714776961)
      ·
        refine ⟨2250897775292274536082721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3001197033723032714776961 2250897775292274536082721)
        ·
          refine ⟨1688173331469205902062041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2250897775292274536082721 1688173331469205902062041)
          ·
            refine ⟨1266129998601904426546531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1688173331469205902062041 1266129998601904426546531)
            ·
              refine ⟨1899194997902856639819797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1266129998601904426546531 1899194997902856639819797)
              ·
                refine ⟨89024765526696404991553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1899194997902856639819797 89024765526696404991553)
                ·
                  rfl

theorem cell20_585141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 6].length) (baseStart_585141 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_585141 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_585141 prefixEnd_585141 := by exact prefixLift 585141
  have htrace : WordTrace (prefixWord ++ tailWord_585141) baseStart_585141 baseEnd_585141 := by
    simpa [prefixWord, tailWord_585141, baseEnd_585141] using wordTrace_append hprefix tailTrace_585141
  have hstable : (prefixWord ++ tailWord_585141).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585141).length < 2 ^ (prefixWord ++ tailWord_585141).sum := by decide
  have hdescent : baseEnd_585141 < baseStart_585141 := by decide
  rcases family_descends (prefixWord ++ tailWord_585141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585162 : List Nat := [3, 1, 2, 1, 2, 3, 8]
def baseStart_585162 : Nat := 118140960795 + 585162 * 2 ^ 59
def prefixEnd_585162 : Nat := 4983230072969 + 3 ^ 40 * 585162 * 2
def baseEnd_585162 : Nat := 29675986839145163919397

theorem tailTrace_585162 : CollatzResearch.WordTrace tailWord_585162 prefixEnd_585162 29675986839145163919397 := by
  unfold tailWord_585162
  simp only [CollatzResearch.WordTrace]
  refine ⟨5335652876516371639565435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14228407670710324372174493 5335652876516371639565435)
  ·
    refine ⟨8003479314774557459348153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5335652876516371639565435 8003479314774557459348153)
    ·
      refine ⟨6002609486080918094511115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8003479314774557459348153 6002609486080918094511115)
      ·
        refine ⟨9003914229121377141766673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6002609486080918094511115 9003914229121377141766673)
        ·
          refine ⟨6752935671841032856325005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9003914229121377141766673 6752935671841032856325005)
          ·
            refine ⟨2532350876940387321121877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6752935671841032856325005 2532350876940387321121877)
            ·
              refine ⟨29675986839145163919397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2532350876940387321121877 29675986839145163919397)
              ·
                rfl

theorem cell20_585162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 8].length) (baseStart_585162 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_585162 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_585162 prefixEnd_585162 := by exact prefixLift 585162
  have htrace : WordTrace (prefixWord ++ tailWord_585162) baseStart_585162 baseEnd_585162 := by
    simpa [prefixWord, tailWord_585162, baseEnd_585162] using wordTrace_append hprefix tailTrace_585162
  have hstable : (prefixWord ++ tailWord_585162).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585162).length < 2 ^ (prefixWord ++ tailWord_585162).sum := by decide
  have hdescent : baseEnd_585162 < baseStart_585162 := by decide
  rcases family_descends (prefixWord ++ tailWord_585162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585200 : List Nat := [2, 1, 1, 1, 3, 4, 2, 6]
def baseStart_585200 : Nat := 118140960795 + 585200 * 2 ^ 59
def prefixEnd_585200 : Nat := 4983230072969 + 3 ^ 40 * 585200 * 2
def baseEnd_585200 : Nat := 89033741929249077335917

theorem tailTrace_585200 : CollatzResearch.WordTrace tailWord_585200 prefixEnd_585200 89033741929249077335917 := by
  unfold tailWord_585200
  simp only [CollatzResearch.WordTrace]
  refine ⟨10671998739963909524072527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14229331653285212698763369 10671998739963909524072527)
  ·
    refine ⟨16007998109945864286108791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10671998739963909524072527 16007998109945864286108791)
    ·
      refine ⟨24011997164918796429163187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16007998109945864286108791 24011997164918796429163187)
      ·
        refine ⟨36017995747378194643744781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24011997164918796429163187 36017995747378194643744781)
        ·
          refine ⟨13506748405266822991404293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36017995747378194643744781 13506748405266822991404293)
          ·
            refine ⟨2532515325987529310888305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13506748405266822991404293 2532515325987529310888305)
            ·
              refine ⟨1899386494490646983166229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2532515325987529310888305 1899386494490646983166229)
              ·
                refine ⟨89033741929249077335917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1899386494490646983166229 89033741929249077335917)
                ·
                  rfl

theorem cell20_585200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 6].length) (baseStart_585200 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_585200 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_585200 prefixEnd_585200 := by exact prefixLift 585200
  have htrace : WordTrace (prefixWord ++ tailWord_585200) baseStart_585200 baseEnd_585200 := by
    simpa [prefixWord, tailWord_585200, baseEnd_585200] using wordTrace_append hprefix tailTrace_585200
  have hstable : (prefixWord ++ tailWord_585200).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585200).length < 2 ^ (prefixWord ++ tailWord_585200).sum := by decide
  have hdescent : baseEnd_585200 < baseStart_585200 := by decide
  rcases family_descends (prefixWord ++ tailWord_585200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585207 : List Nat := [1, 1, 3, 1, 1, 1, 1, 6, 5]
def baseStart_585207 : Nat := 118140960795 + 585207 * 2 ^ 59
def prefixEnd_585207 : Nat := 4983230072969 + 3 ^ 40 * 585207 * 2
def baseEnd_585207 : Nat := 267104420778486318774389

theorem tailTrace_585207 : CollatzResearch.WordTrace tailWord_585207 prefixEnd_585207 267104420778486318774389 := by
  unfold tailWord_585207
  simp only [CollatzResearch.WordTrace]
  refine ⟨21344252790902459243649875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14229501860601639495766583 21344252790902459243649875)
  ·
    refine ⟨32016379186353688865474813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21344252790902459243649875 32016379186353688865474813)
    ·
      refine ⟨12006142194882633324553055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32016379186353688865474813 12006142194882633324553055)
      ·
        refine ⟨18009213292323949986829583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12006142194882633324553055 18009213292323949986829583)
        ·
          refine ⟨27013819938485924980244375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18009213292323949986829583 27013819938485924980244375)
          ·
            refine ⟨40520729907728887470366563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27013819938485924980244375 40520729907728887470366563)
            ·
              refine ⟨60781094861593331205549845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40520729907728887470366563 60781094861593331205549845)
              ·
                refine ⟨2849113821637187400260149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 60781094861593331205549845 2849113821637187400260149)
                ·
                  refine ⟨267104420778486318774389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2849113821637187400260149 267104420778486318774389)
                  ·
                    rfl

theorem cell20_585207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 6, 5].length) (baseStart_585207 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_585207 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_585207 prefixEnd_585207 := by exact prefixLift 585207
  have htrace : WordTrace (prefixWord ++ tailWord_585207) baseStart_585207 baseEnd_585207 := by
    simpa [prefixWord, tailWord_585207, baseEnd_585207] using wordTrace_append hprefix tailTrace_585207
  have hstable : (prefixWord ++ tailWord_585207).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585207).length < 2 ^ (prefixWord ++ tailWord_585207).sum := by decide
  have hdescent : baseEnd_585207 < baseStart_585207 := by decide
  rcases family_descends (prefixWord ++ tailWord_585207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585210 : List Nat := [3, 1, 1, 1, 1, 2, 4, 5, 2]
def baseStart_585210 : Nat := 118140960795 + 585210 * 2 ^ 59
def prefixEnd_585210 : Nat := 4983230072969 + 3 ^ 40 * 585210 * 2
def baseEnd_585210 : Nat := 267105790060231641674377

theorem tailTrace_585210 : CollatzResearch.WordTrace tailWord_585210 prefixEnd_585210 267105790060231641674377 := by
  unfold tailWord_585210
  simp only [CollatzResearch.WordTrace]
  refine ⟨5336090552472897689002271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14229574806594393837339389 5336090552472897689002271)
  ·
    refine ⟨8004135828709346533503407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5336090552472897689002271 8004135828709346533503407)
    ·
      refine ⟨12006203743064019800255111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8004135828709346533503407 12006203743064019800255111)
      ·
        refine ⟨18009305614596029700382667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12006203743064019800255111 18009305614596029700382667)
        ·
          refine ⟨27013958421894044550574001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18009305614596029700382667 27013958421894044550574001)
          ·
            refine ⟨20260468816420533412930501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27013958421894044550574001 20260468816420533412930501)
            ·
              refine ⟨3798837903078850014924469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20260468816420533412930501 3798837903078850014924469)
              ·
                refine ⟨356141053413642188899169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3798837903078850014924469 356141053413642188899169)
                ·
                  refine ⟨267105790060231641674377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 356141053413642188899169 267105790060231641674377)
                  ·
                    rfl

theorem cell20_585210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 5, 2].length) (baseStart_585210 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_585210 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_585210 prefixEnd_585210 := by exact prefixLift 585210
  have htrace : WordTrace (prefixWord ++ tailWord_585210) baseStart_585210 baseEnd_585210 := by
    simpa [prefixWord, tailWord_585210, baseEnd_585210] using wordTrace_append hprefix tailTrace_585210
  have hstable : (prefixWord ++ tailWord_585210).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585210).length < 2 ^ (prefixWord ++ tailWord_585210).sum := by decide
  have hdescent : baseEnd_585210 < baseStart_585210 := by decide
  rcases family_descends (prefixWord ++ tailWord_585210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585217 : List Nat := [1, 2, 4, 1, 5, 7]
def baseStart_585217 : Nat := 118140960795 + 585217 * 2 ^ 59
def prefixEnd_585217 : Nat := 4983230072969 + 3 ^ 40 * 585217 * 2
def baseEnd_585217 : Nat := 9892925372258175127445

theorem tailTrace_585217 : CollatzResearch.WordTrace tailWord_585217 prefixEnd_585217 9892925372258175127445 := by
  unfold tailWord_585217
  simp only [CollatzResearch.WordTrace]
  refine ⟨21344617520866230951513905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14229745013910820634342603 21344617520866230951513905)
  ·
    refine ⟨16008463140649673213635429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21344617520866230951513905 16008463140649673213635429)
    ·
      refine ⟨3001586838871813727556643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16008463140649673213635429 3001586838871813727556643)
      ·
        refine ⟨4502380258307720591334965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3001586838871813727556643 4502380258307720591334965)
        ·
          refine ⟨422098149216348805437653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4502380258307720591334965 422098149216348805437653)
          ·
            refine ⟨9892925372258175127445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 422098149216348805437653 9892925372258175127445)
            ·
              rfl

theorem cell20_585217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 7].length) (baseStart_585217 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_585217 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_585217 prefixEnd_585217 := by exact prefixLift 585217
  have htrace : WordTrace (prefixWord ++ tailWord_585217) baseStart_585217 baseEnd_585217 := by
    simpa [prefixWord, tailWord_585217, baseEnd_585217] using wordTrace_append hprefix tailTrace_585217
  have hstable : (prefixWord ++ tailWord_585217).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585217).length < 2 ^ (prefixWord ++ tailWord_585217).sum := by decide
  have hdescent : baseEnd_585217 < baseStart_585217 := by decide
  rcases family_descends (prefixWord ++ tailWord_585217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585220 : List Nat := [2, 3, 2, 3, 2, 1, 2, 2, 3]
def baseStart_585220 : Nat := 118140960795 + 585220 * 2 ^ 59
def prefixEnd_585220 : Nat := 4983230072969 + 3 ^ 40 * 585220 * 2
def baseEnd_585220 : Nat := 267110354332716051341003

theorem tailTrace_585220 : CollatzResearch.WordTrace tailWord_585220 prefixEnd_585220 267110354332716051341003 := by
  unfold tailWord_585220
  simp only [CollatzResearch.WordTrace]
  refine ⟨10672363469927681231936557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14229817959903574975915409 10672363469927681231936557)
  ·
    refine ⟨4002136301222880461976209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10672363469927681231936557 4002136301222880461976209)
    ·
      refine ⟨3001602225917160346482157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4002136301222880461976209 3001602225917160346482157)
      ·
        refine ⟨1125600834718935129930809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3001602225917160346482157 1125600834718935129930809)
        ·
          refine ⟨844200626039201347448107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1125600834718935129930809 844200626039201347448107)
          ·
            refine ⟨1266300939058802021172161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 844200626039201347448107 1266300939058802021172161)
            ·
              refine ⟨949725704294101515879121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1266300939058802021172161 949725704294101515879121)
              ·
                refine ⟨712294278220576136909341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 949725704294101515879121 712294278220576136909341)
                ·
                  refine ⟨267110354332716051341003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 712294278220576136909341 267110354332716051341003)
                  ·
                    rfl

theorem cell20_585220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 2, 3].length) (baseStart_585220 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_585220 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_585220 prefixEnd_585220 := by exact prefixLift 585220
  have htrace : WordTrace (prefixWord ++ tailWord_585220) baseStart_585220 baseEnd_585220 := by
    simpa [prefixWord, tailWord_585220, baseEnd_585220] using wordTrace_append hprefix tailTrace_585220
  have hstable : (prefixWord ++ tailWord_585220).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585220).length < 2 ^ (prefixWord ++ tailWord_585220).sum := by decide
  have hdescent : baseEnd_585220 < baseStart_585220 := by decide
  rcases family_descends (prefixWord ++ tailWord_585220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585224 : List Nat := [2, 1, 3, 2, 1, 1, 3, 4, 3]
def baseStart_585224 : Nat := 118140960795 + 585224 * 2 ^ 59
def prefixEnd_585224 : Nat := 4983230072969 + 3 ^ 40 * 585224 * 2
def baseEnd_585224 : Nat := 267112180041709815207653

theorem tailTrace_585224 : CollatzResearch.WordTrace tailWord_585224 prefixEnd_585224 267112180041709815207653 := by
  unfold tailWord_585224
  simp only [CollatzResearch.WordTrace]
  refine ⟨10672436415920435573509363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14229915221227247431345817 10672436415920435573509363)
  ·
    refine ⟨16008654623880653360264045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10672436415920435573509363 16008654623880653360264045)
    ·
      refine ⟨6003245483955245010099017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16008654623880653360264045 6003245483955245010099017)
      ·
        refine ⟨4502434112966433757574263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6003245483955245010099017 4502434112966433757574263)
        ·
          refine ⟨6753651169449650636361395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4502434112966433757574263 6753651169449650636361395)
          ·
            refine ⟨10130476754174475954542093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6753651169449650636361395 10130476754174475954542093)
            ·
              refine ⟨3798928782815428482953285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10130476754174475954542093 3798928782815428482953285)
              ·
                refine ⟨712299146777892840553741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3798928782815428482953285 712299146777892840553741)
                ·
                  refine ⟨267112180041709815207653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 712299146777892840553741 267112180041709815207653)
                  ·
                    rfl

theorem cell20_585224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 4, 3].length) (baseStart_585224 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_585224 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_585224 prefixEnd_585224 := by exact prefixLift 585224
  have htrace : WordTrace (prefixWord ++ tailWord_585224) baseStart_585224 baseEnd_585224 := by
    simpa [prefixWord, tailWord_585224, baseEnd_585224] using wordTrace_append hprefix tailTrace_585224
  have hstable : (prefixWord ++ tailWord_585224).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585224).length < 2 ^ (prefixWord ++ tailWord_585224).sum := by decide
  have hdescent : baseEnd_585224 < baseStart_585224 := by decide
  rcases family_descends (prefixWord ++ tailWord_585224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585227 : List Nat := [1, 1, 1, 1, 8, 1, 1, 4, 2]
def baseStart_585227 : Nat := 118140960795 + 585227 * 2 ^ 59
def prefixEnd_585227 : Nat := 4983230072969 + 3 ^ 40 * 585227 * 2
def baseEnd_585227 : Nat := 267113549323455138107641

theorem tailTrace_585227 : CollatzResearch.WordTrace tailWord_585227 prefixEnd_585227 267113549323455138107641 := by
  unfold tailWord_585227
  simp only [CollatzResearch.WordTrace]
  refine ⟨21344982250830002659377935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14229988167220001772918623 21344982250830002659377935)
  ·
    refine ⟨32017473376245003989066903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21344982250830002659377935 32017473376245003989066903)
    ·
      refine ⟨48026210064367505983600355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32017473376245003989066903 48026210064367505983600355)
      ·
        refine ⟨72039315096551258975400533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48026210064367505983600355 72039315096551258975400533)
        ·
          refine ⟨844210723787710066117975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 72039315096551258975400533 844210723787710066117975)
          ·
            refine ⟨1266316085681565099176963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 844210723787710066117975 1266316085681565099176963)
            ·
              refine ⟨1899474128522347648765445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1266316085681565099176963 1899474128522347648765445)
              ·
                refine ⟨356151399097940184143521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1899474128522347648765445 356151399097940184143521)
                ·
                  refine ⟨267113549323455138107641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 356151399097940184143521 267113549323455138107641)
                  ·
                    rfl

theorem cell20_585227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 4, 2].length) (baseStart_585227 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_585227 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_585227 prefixEnd_585227 := by exact prefixLift 585227
  have htrace : WordTrace (prefixWord ++ tailWord_585227) baseStart_585227 baseEnd_585227 := by
    simpa [prefixWord, tailWord_585227, baseEnd_585227] using wordTrace_append hprefix tailTrace_585227
  have hstable : (prefixWord ++ tailWord_585227).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585227).length < 2 ^ (prefixWord ++ tailWord_585227).sum := by decide
  have hdescent : baseEnd_585227 < baseStart_585227 := by decide
  rcases family_descends (prefixWord ++ tailWord_585227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585248 : List Nat := [2, 1, 1, 6, 1, 2, 1, 2, 4]
def baseStart_585248 : Nat := 118140960795 + 585248 * 2 ^ 59
def prefixEnd_585248 : Nat := 4983230072969 + 3 ^ 40 * 585248 * 2
def baseEnd_585248 : Nat := 267123134295672398407555

theorem tailTrace_585248 : CollatzResearch.WordTrace tailWord_585248 prefixEnd_585248 267123134295672398407555 := by
  unfold tailWord_585248
  simp only [CollatzResearch.WordTrace]
  refine ⟨10672874091876961622946199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14230498789169282163928265 10672874091876961622946199)
  ·
    refine ⟨16009311137815442434419299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10672874091876961622946199 16009311137815442434419299)
    ·
      refine ⟨24013966706723163651628949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16009311137815442434419299 24013966706723163651628949)
      ·
        refine ⟨1125654689377648296170107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 24013966706723163651628949 1125654689377648296170107)
        ·
          refine ⟨1688482034066472444255161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1125654689377648296170107 1688482034066472444255161)
          ·
            refine ⟨1266361525549854333191371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1688482034066472444255161 1266361525549854333191371)
            ·
              refine ⟨1899542288324781499787057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1266361525549854333191371 1899542288324781499787057)
              ·
                refine ⟨1424656716243586124840293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1899542288324781499787057 1424656716243586124840293)
                ·
                  refine ⟨267123134295672398407555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1424656716243586124840293 267123134295672398407555)
                  ·
                    rfl

theorem cell20_585248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 2, 4].length) (baseStart_585248 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_585248 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_585248 prefixEnd_585248 := by exact prefixLift 585248
  have htrace : WordTrace (prefixWord ++ tailWord_585248) baseStart_585248 baseEnd_585248 := by
    simpa [prefixWord, tailWord_585248, baseEnd_585248] using wordTrace_append hprefix tailTrace_585248
  have hstable : (prefixWord ++ tailWord_585248).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585248).length < 2 ^ (prefixWord ++ tailWord_585248).sum := by decide
  have hdescent : baseEnd_585248 < baseStart_585248 := by decide
  rcases family_descends (prefixWord ++ tailWord_585248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585279 : List Nat := [1, 1, 2, 2, 3, 5, 1, 2, 3]
def baseStart_585279 : Nat := 118140960795 + 585279 * 2 ^ 59
def prefixEnd_585279 : Nat := 4983230072969 + 3 ^ 40 * 585279 * 2
def baseEnd_585279 : Nat := 267137283540374068374095

theorem tailTrace_585279 : CollatzResearch.WordTrace tailWord_585279 prefixEnd_585279 267137283540374068374095 := by
  unfold tailWord_585279
  simp only [CollatzResearch.WordTrace]
  refine ⟨21346878846641615540270891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14231252564427743693513927 21346878846641615540270891)
  ·
    refine ⟨32020318269962423310406337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21346878846641615540270891 32020318269962423310406337)
    ·
      refine ⟨24015238702471817482804753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32020318269962423310406337 24015238702471817482804753)
      ·
        refine ⟨18011429026853863112103565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24015238702471817482804753 18011429026853863112103565)
        ·
          refine ⟨6754285885070198667038837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18011429026853863112103565 6754285885070198667038837)
          ·
            refine ⟨633214301725331125034891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6754285885070198667038837 633214301725331125034891)
            ·
              refine ⟨949821452587996687552337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 633214301725331125034891 949821452587996687552337)
              ·
                refine ⟨712366089440997515664253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 949821452587996687552337 712366089440997515664253)
                ·
                  refine ⟨267137283540374068374095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 712366089440997515664253 267137283540374068374095)
                  ·
                    rfl

theorem cell20_585279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 1, 2, 3].length) (baseStart_585279 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_585279 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_585279 prefixEnd_585279 := by exact prefixLift 585279
  have htrace : WordTrace (prefixWord ++ tailWord_585279) baseStart_585279 baseEnd_585279 := by
    simpa [prefixWord, tailWord_585279, baseEnd_585279] using wordTrace_append hprefix tailTrace_585279
  have hstable : (prefixWord ++ tailWord_585279).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585279).length < 2 ^ (prefixWord ++ tailWord_585279).sum := by decide
  have hdescent : baseEnd_585279 < baseStart_585279 := by decide
  rcases family_descends (prefixWord ++ tailWord_585279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585320 : List Nat := [2, 1, 4, 3, 1, 3, 1, 3, 2]
def baseStart_585320 : Nat := 118140960795 + 585320 * 2 ^ 59
def prefixEnd_585320 : Nat := 4983230072969 + 3 ^ 40 * 585320 * 2
def baseEnd_585320 : Nat := 267155997057560148007261

theorem tailTrace_585320 : CollatzResearch.WordTrace tailWord_585320 prefixEnd_585320 267155997057560148007261 := by
  unfold tailWord_585320
  simp only [CollatzResearch.WordTrace]
  refine ⟨10674187119746539771256707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14232249492995386361675609 10674187119746539771256707)
  ·
    refine ⟨16011280679619809656885061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10674187119746539771256707 16011280679619809656885061)
    ·
      refine ⟨3002115127428714310665949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16011280679619809656885061 3002115127428714310665949)
      ·
        refine ⟨1125793172785767866499731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3002115127428714310665949 1125793172785767866499731)
        ·
          refine ⟨1688689759178651799749597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1125793172785767866499731 1688689759178651799749597)
          ·
            refine ⟨633258659691994424906099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1688689759178651799749597 633258659691994424906099)
            ·
              refine ⟨949887989537991637359149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 633258659691994424906099 949887989537991637359149)
              ·
                refine ⟨356207996076746864009681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 949887989537991637359149 356207996076746864009681)
                ·
                  refine ⟨267155997057560148007261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 356207996076746864009681 267155997057560148007261)
                  ·
                    rfl

theorem cell20_585320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 1, 3, 2].length) (baseStart_585320 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_585320 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_585320 prefixEnd_585320 := by exact prefixLift 585320
  have htrace : WordTrace (prefixWord ++ tailWord_585320) baseStart_585320 baseEnd_585320 := by
    simpa [prefixWord, tailWord_585320, baseEnd_585320] using wordTrace_append hprefix tailTrace_585320
  have hstable : (prefixWord ++ tailWord_585320).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585320).length < 2 ^ (prefixWord ++ tailWord_585320).sum := by decide
  have hdescent : baseEnd_585320 < baseStart_585320 := by decide
  rcases family_descends (prefixWord ++ tailWord_585320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585321 : List Nat := [1, 2, 1, 1, 1, 4, 3, 2, 5]
def baseStart_585321 : Nat := 118140960795 + 585321 * 2 ^ 59
def prefixEnd_585321 : Nat := 4983230072969 + 3 ^ 40 * 585321 * 2
def baseEnd_585321 : Nat := 267156453484808588973923

theorem tailTrace_585321 : CollatzResearch.WordTrace tailWord_585321 prefixEnd_585321 267156453484808588973923 := by
  unfold tailWord_585321
  simp only [CollatzResearch.WordTrace]
  refine ⟨21348410712489456713299817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14232273808326304475533211 21348410712489456713299817)
  ·
    refine ⟨16011308034367092534974863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21348410712489456713299817 16011308034367092534974863)
    ·
      refine ⟨24016962051550638802462295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16011308034367092534974863 24016962051550638802462295)
      ·
        refine ⟨36025443077325958203693443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24016962051550638802462295 36025443077325958203693443)
        ·
          refine ⟨54038164615988937305540165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36025443077325958203693443 54038164615988937305540165)
          ·
            refine ⟨10132155865497925744788781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54038164615988937305540165 10132155865497925744788781)
            ·
              refine ⟨3799558449561722154295793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10132155865497925744788781 3799558449561722154295793)
              ·
                refine ⟨2849668837171291615721845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3799558449561722154295793 2849668837171291615721845)
                ·
                  refine ⟨267156453484808588973923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2849668837171291615721845 267156453484808588973923)
                  ·
                    rfl

theorem cell20_585321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 2, 5].length) (baseStart_585321 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_585321 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_585321 prefixEnd_585321 := by exact prefixLift 585321
  have htrace : WordTrace (prefixWord ++ tailWord_585321) baseStart_585321 baseEnd_585321 := by
    simpa [prefixWord, tailWord_585321, baseEnd_585321] using wordTrace_append hprefix tailTrace_585321
  have hstable : (prefixWord ++ tailWord_585321).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585321).length < 2 ^ (prefixWord ++ tailWord_585321).sum := by decide
  have hdescent : baseEnd_585321 < baseStart_585321 := by decide
  rcases family_descends (prefixWord ++ tailWord_585321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585452 : List Nat := [2, 2, 1, 1, 2, 2, 5, 2, 3]
def baseStart_585452 : Nat := 118140960795 + 585452 * 2 ^ 59
def prefixEnd_585452 : Nat := 4983230072969 + 3 ^ 40 * 585452 * 2
def baseEnd_585452 : Nat := 267216245454354355606721

theorem tailTrace_585452 : CollatzResearch.WordTrace tailWord_585452 prefixEnd_585452 267216245454354355606721 := by
  unfold tailWord_585452
  simp only [CollatzResearch.WordTrace]
  refine ⟨10676594337507433043159305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14235459116676577390879073 10676594337507433043159305)
  ·
    refine ⟨8007445753130574782369479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10676594337507433043159305 8007445753130574782369479)
    ·
      refine ⟨12011168629695862173554219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8007445753130574782369479 12011168629695862173554219)
      ·
        refine ⟨18016752944543793260331329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12011168629695862173554219 18016752944543793260331329)
        ·
          refine ⟨13512564708407844945248497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18016752944543793260331329 13512564708407844945248497)
          ·
            refine ⟨10134423531305883708936373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13512564708407844945248497 10134423531305883708936373)
            ·
              refine ⟨950102206059926597712785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10134423531305883708936373 950102206059926597712785)
              ·
                refine ⟨712576654544944948284589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 950102206059926597712785 712576654544944948284589)
                ·
                  refine ⟨267216245454354355606721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 712576654544944948284589 267216245454354355606721)
                  ·
                    rfl

theorem cell20_585452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 3].length) (baseStart_585452 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_585452 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_585452 prefixEnd_585452 := by exact prefixLift 585452
  have htrace : WordTrace (prefixWord ++ tailWord_585452) baseStart_585452 baseEnd_585452 := by
    simpa [prefixWord, tailWord_585452, baseEnd_585452] using wordTrace_append hprefix tailTrace_585452
  have hstable : (prefixWord ++ tailWord_585452).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585452).length < 2 ^ (prefixWord ++ tailWord_585452).sum := by decide
  have hdescent : baseEnd_585452 < baseStart_585452 := by decide
  rcases family_descends (prefixWord ++ tailWord_585452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585479 : List Nat := [1, 1, 4, 4, 3, 1, 2, 4]
def baseStart_585479 : Nat := 118140960795 + 585479 * 2 ^ 59
def prefixEnd_585479 : Nat := 4983230072969 + 3 ^ 40 * 585479 * 2
def baseEnd_585479 : Nat := 89076189663354087235537

theorem tailTrace_585479 : CollatzResearch.WordTrace tailWord_585479 prefixEnd_585479 89076189663354087235537 := by
  unfold tailWord_585479
  simp only [CollatzResearch.WordTrace]
  refine ⟨21354173445917049697551491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14236115630611366465034327 21354173445917049697551491)
  ·
    refine ⟨32031260168875574546327237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21354173445917049697551491 32031260168875574546327237)
    ·
      refine ⟨6005861281664170227436357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32031260168875574546327237 6005861281664170227436357)
      ·
        refine ⟨1126098990312031917644317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6005861281664170227436357 1126098990312031917644317)
        ·
          refine ⟨422287121367011969116619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1126098990312031917644317 422287121367011969116619)
          ·
            refine ⟨633430682050517953674929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 422287121367011969116619 633430682050517953674929)
            ·
              refine ⟨475073011537888465256197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 633430682050517953674929 475073011537888465256197)
              ·
                refine ⟨89076189663354087235537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 475073011537888465256197 89076189663354087235537)
                ·
                  rfl

theorem cell20_585479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 2, 4].length) (baseStart_585479 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_585479 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_585479 prefixEnd_585479 := by exact prefixLift 585479
  have htrace : WordTrace (prefixWord ++ tailWord_585479) baseStart_585479 baseEnd_585479 := by
    simpa [prefixWord, tailWord_585479, baseEnd_585479] using wordTrace_append hprefix tailTrace_585479
  have hstable : (prefixWord ++ tailWord_585479).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585479).length < 2 ^ (prefixWord ++ tailWord_585479).sum := by decide
  have hdescent : baseEnd_585479 < baseStart_585479 := by decide
  rcases family_descends (prefixWord ++ tailWord_585479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585485 : List Nat := [1, 7, 2, 1, 1, 2, 1, 3, 2]
def baseStart_585485 : Nat := 118140960795 + 585485 * 2 ^ 59
def prefixEnd_585485 : Nat := 4983230072969 + 3 ^ 40 * 585485 * 2
def baseEnd_585485 : Nat := 267231307553552907506587

theorem tailTrace_585485 : CollatzResearch.WordTrace tailWord_585485 prefixEnd_585485 267231307553552907506587 := by
  unfold tailWord_585485
  simp only [CollatzResearch.WordTrace]
  refine ⟨21354392283895312722269909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14236261522596875148179939 21354392283895312722269909)
  ·
    refine ⟨500493569153796391928201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 21354392283895312722269909 500493569153796391928201)
    ·
      refine ⟨375370176865347293946151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 500493569153796391928201 375370176865347293946151)
      ·
        refine ⟨563055265298020940919227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 375370176865347293946151 563055265298020940919227)
        ·
          refine ⟨844582897947031411378841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 563055265298020940919227 844582897947031411378841)
          ·
            refine ⟨633437173460273558534131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 844582897947031411378841 633437173460273558534131)
            ·
              refine ⟨950155760190410337801197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 633437173460273558534131 950155760190410337801197)
              ·
                refine ⟨356308410071403876675449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 950155760190410337801197 356308410071403876675449)
                ·
                  refine ⟨267231307553552907506587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 356308410071403876675449 267231307553552907506587)
                  ·
                    rfl

theorem cell20_585485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_585485 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_585485 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_585485 prefixEnd_585485 := by exact prefixLift 585485
  have htrace : WordTrace (prefixWord ++ tailWord_585485) baseStart_585485 baseEnd_585485 := by
    simpa [prefixWord, tailWord_585485, baseEnd_585485] using wordTrace_append hprefix tailTrace_585485
  have hstable : (prefixWord ++ tailWord_585485).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585485).length < 2 ^ (prefixWord ++ tailWord_585485).sum := by decide
  have hdescent : baseEnd_585485 < baseStart_585485 := by decide
  rcases family_descends (prefixWord ++ tailWord_585485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585493 : List Nat := [1, 3, 2, 1, 2, 5, 1, 3, 2]
def baseStart_585493 : Nat := 118140960795 + 585493 * 2 ^ 59
def prefixEnd_585493 : Nat := 4983230072969 + 3 ^ 40 * 585493 * 2
def baseEnd_585493 : Nat := 267234958971540435239887

theorem tailTrace_585493 : CollatzResearch.WordTrace tailWord_585493 prefixEnd_585493 267234958971540435239887 := by
  unfold tailWord_585493
  simp only [CollatzResearch.WordTrace]
  refine ⟨21354684067866330088561133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14236456045244220059040755 21354684067866330088561133)
  ·
    refine ⟨8008006525449873783210425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21354684067866330088561133 8008006525449873783210425)
    ·
      refine ⟨6006004894087405337407819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8008006525449873783210425 6006004894087405337407819)
      ·
        refine ⟨9009007341131108006111729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6006004894087405337407819 9009007341131108006111729)
        ·
          refine ⟨6756755505848331004583797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9009007341131108006111729 6756755505848331004583797)
          ·
            refine ⟨633445828673281031679731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6756755505848331004583797 633445828673281031679731)
            ·
              refine ⟨950168743009921547519597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 633445828673281031679731 950168743009921547519597)
              ·
                refine ⟨356313278628720580319849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 950168743009921547519597 356313278628720580319849)
                ·
                  refine ⟨267234958971540435239887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 356313278628720580319849 267234958971540435239887)
                  ·
                    rfl

theorem cell20_585493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 1, 3, 2].length) (baseStart_585493 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_585493 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_585493 prefixEnd_585493 := by exact prefixLift 585493
  have htrace : WordTrace (prefixWord ++ tailWord_585493) baseStart_585493 baseEnd_585493 := by
    simpa [prefixWord, tailWord_585493, baseEnd_585493] using wordTrace_append hprefix tailTrace_585493
  have hstable : (prefixWord ++ tailWord_585493).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585493).length < 2 ^ (prefixWord ++ tailWord_585493).sum := by decide
  have hdescent : baseEnd_585493 < baseStart_585493 := by decide
  rcases family_descends (prefixWord ++ tailWord_585493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585524 : List Nat := [2, 5, 1, 1, 2, 1, 4, 1, 3]
def baseStart_585524 : Nat := 118140960795 + 585524 * 2 ^ 59
def prefixEnd_585524 : Nat := 4983230072969 + 3 ^ 40 * 585524 * 2
def baseEnd_585524 : Nat := 267249108216242105206427

theorem tailTrace_585524 : CollatzResearch.WordTrace tailWord_585524 prefixEnd_585524 267249108216242105206427 := by
  unfold tailWord_585524
  simp only [CollatzResearch.WordTrace]
  refine ⟨10677907365377011191469813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14237209820502681588626417 10677907365377011191469813)
  ·
    refine ⟨1001053815504094799200295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10677907365377011191469813 1001053815504094799200295)
    ·
      refine ⟨1501580723256142198800443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1001053815504094799200295 1501580723256142198800443)
      ·
        refine ⟨2252371084884213298200665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1501580723256142198800443 2252371084884213298200665)
        ·
          refine ⟨1689278313663159973650499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2252371084884213298200665 1689278313663159973650499)
          ·
            refine ⟨2533917470494739960475749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1689278313663159973650499 2533917470494739960475749)
            ·
              refine ⟨475109525717763742589203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2533917470494739960475749 475109525717763742589203)
              ·
                refine ⟨712664288576645613883805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 475109525717763742589203 712664288576645613883805)
                ·
                  refine ⟨267249108216242105206427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 712664288576645613883805 267249108216242105206427)
                  ·
                    rfl

theorem cell20_585524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_585524 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_585524 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_585524 prefixEnd_585524 := by exact prefixLift 585524
  have htrace : WordTrace (prefixWord ++ tailWord_585524) baseStart_585524 baseEnd_585524 := by
    simpa [prefixWord, tailWord_585524, baseEnd_585524] using wordTrace_append hprefix tailTrace_585524
  have hstable : (prefixWord ++ tailWord_585524).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585524).length < 2 ^ (prefixWord ++ tailWord_585524).sum := by decide
  have hdescent : baseEnd_585524 < baseStart_585524 := by decide
  rcases family_descends (prefixWord ++ tailWord_585524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585528 : List Nat := [2, 1, 2, 1, 3, 4, 1, 3, 3]
def baseStart_585528 : Nat := 118140960795 + 585528 * 2 ^ 59
def prefixEnd_585528 : Nat := 4983230072969 + 3 ^ 40 * 585528 * 2
def baseEnd_585528 : Nat := 267250933925235869073077

theorem tailTrace_585528 : CollatzResearch.WordTrace tailWord_585528 prefixEnd_585528 267250933925235869073077 := by
  unfold tailWord_585528
  simp only [CollatzResearch.WordTrace]
  refine ⟨10677980311369765533042619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14237307081826354044056825 10677980311369765533042619)
  ·
    refine ⟨16016970467054648299563929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10677980311369765533042619 16016970467054648299563929)
    ·
      refine ⟨12012727850290986224672947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16016970467054648299563929 12012727850290986224672947)
      ·
        refine ⟨18019091775436479337009421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12012727850290986224672947 18019091775436479337009421)
        ·
          refine ⟨6757159415788679751378533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18019091775436479337009421 6757159415788679751378533)
          ·
            refine ⟨1266967390460377453383475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6757159415788679751378533 1266967390460377453383475)
            ·
              refine ⟨1900451085690566180075213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1266967390460377453383475 1900451085690566180075213)
              ·
                refine ⟨712669157133962317528205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1900451085690566180075213 712669157133962317528205)
                ·
                  refine ⟨267250933925235869073077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 712669157133962317528205 267250933925235869073077)
                  ·
                    rfl

theorem cell20_585528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 3, 3].length) (baseStart_585528 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_585528 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_585528 prefixEnd_585528 := by exact prefixLift 585528
  have htrace : WordTrace (prefixWord ++ tailWord_585528) baseStart_585528 baseEnd_585528 := by
    simpa [prefixWord, tailWord_585528, baseEnd_585528] using wordTrace_append hprefix tailTrace_585528
  have hstable : (prefixWord ++ tailWord_585528).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585528).length < 2 ^ (prefixWord ++ tailWord_585528).sum := by decide
  have hdescent : baseEnd_585528 < baseStart_585528 := by decide
  rcases family_descends (prefixWord ++ tailWord_585528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585580 : List Nat := [2, 2, 1, 1, 4, 2, 3, 5]
def baseStart_585580 : Nat := 118140960795 + 585580 * 2 ^ 59
def prefixEnd_585580 : Nat := 4983230072969 + 3 ^ 40 * 585580 * 2
def baseEnd_585580 : Nat := 89091556047384933113177

theorem tailTrace_585580 : CollatzResearch.WordTrace tailWord_585580 prefixEnd_585580 89091556047384933113177 := by
  unfold tailWord_585580
  simp only [CollatzResearch.WordTrace]
  refine ⟨10678928609275571973489097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14238571479034095964652129 10678928609275571973489097)
  ·
    refine ⟨8009196456956678980116823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10678928609275571973489097 8009196456956678980116823)
    ·
      refine ⟨12013794685435018470175235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8009196456956678980116823 12013794685435018470175235)
      ·
        refine ⟨18020692028152527705262853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12013794685435018470175235 18020692028152527705262853)
        ·
          refine ⟨3378879755278598944736785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18020692028152527705262853 3378879755278598944736785)
          ·
            refine ⟨2534159816458949208552589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3378879755278598944736785 2534159816458949208552589)
            ·
              refine ⟨950309931172105953207221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2534159816458949208552589 950309931172105953207221)
              ·
                refine ⟨89091556047384933113177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 950309931172105953207221 89091556047384933113177)
                ·
                  rfl

theorem cell20_585580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3, 5].length) (baseStart_585580 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_585580 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_585580 prefixEnd_585580 := by exact prefixLift 585580
  have htrace : WordTrace (prefixWord ++ tailWord_585580) baseStart_585580 baseEnd_585580 := by
    simpa [prefixWord, tailWord_585580, baseEnd_585580] using wordTrace_append hprefix tailTrace_585580
  have hstable : (prefixWord ++ tailWord_585580).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585580).length < 2 ^ (prefixWord ++ tailWord_585580).sum := by decide
  have hdescent : baseEnd_585580 < baseStart_585580 := by decide
  rcases family_descends (prefixWord ++ tailWord_585580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585594 : List Nat := [3, 1, 1, 1, 1, 1, 5, 1, 6]
def baseStart_585594 : Nat := 118140960795 + 585594 * 2 ^ 59
def prefixEnd_585594 : Nat := 4983230072969 + 3 ^ 40 * 585594 * 2
def baseEnd_585594 : Nat := 267281058123632972872807

theorem tailTrace_585594 : CollatzResearch.WordTrace tailWord_585594 prefixEnd_585594 267281058123632972872807 := by
  unfold tailWord_585594
  simp only [CollatzResearch.WordTrace]
  refine ⟨5339591960125106084496959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14238911893666949558658557 5339591960125106084496959)
  ·
    refine ⟨8009387940187659126745439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5339591960125106084496959 8009387940187659126745439)
    ·
      refine ⟨12014081910281488690118159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8009387940187659126745439 12014081910281488690118159)
      ·
        refine ⟨18021122865422233035177239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12014081910281488690118159 18021122865422233035177239)
        ·
          refine ⟨27031684298133349552765859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18021122865422233035177239 27031684298133349552765859)
          ·
            refine ⟨40547526447200024329148789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27031684298133349552765859 40547526447200024329148789)
            ·
              refine ⟨3801330604425002280857699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40547526447200024329148789 3801330604425002280857699)
              ·
                refine ⟨5701995906637503421286549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3801330604425002280857699 5701995906637503421286549)
                ·
                  refine ⟨267281058123632972872807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5701995906637503421286549 267281058123632972872807)
                  ·
                    rfl

theorem cell20_585594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 1, 6].length) (baseStart_585594 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_585594 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_585594 prefixEnd_585594 := by exact prefixLift 585594
  have htrace : WordTrace (prefixWord ++ tailWord_585594) baseStart_585594 baseEnd_585594 := by
    simpa [prefixWord, tailWord_585594, baseEnd_585594] using wordTrace_append hprefix tailTrace_585594
  have hstable : (prefixWord ++ tailWord_585594).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585594).length < 2 ^ (prefixWord ++ tailWord_585594).sum := by decide
  have hdescent : baseEnd_585594 < baseStart_585594 := by decide
  rcases family_descends (prefixWord ++ tailWord_585594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585607 : List Nat := [1, 1, 4, 2, 4, 1, 2, 3, 2]
def baseStart_585607 : Nat := 118140960795 + 585607 * 2 ^ 59
def prefixEnd_585607 : Nat := 4983230072969 + 3 ^ 40 * 585607 * 2
def baseEnd_585607 : Nat := 267286991677862705439421

theorem tailTrace_585607 : CollatzResearch.WordTrace tailWord_585607 prefixEnd_585607 267286991677862705439421 := by
  unfold tailWord_585607
  simp only [CollatzResearch.WordTrace]
  refine ⟨21358841989453327558211075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14239227992968885038807383 21358841989453327558211075)
  ·
    refine ⟨32038262984179991337316613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21358841989453327558211075 32038262984179991337316613)
    ·
      refine ⟨6007174309533748375746865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32038262984179991337316613 6007174309533748375746865)
      ·
        refine ⟨4505380732150311281810149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6007174309533748375746865 4505380732150311281810149)
        ·
          refine ⟨844758887278183365339403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4505380732150311281810149 844758887278183365339403)
          ·
            refine ⟨1267138330917275048009105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 844758887278183365339403 1267138330917275048009105)
            ·
              refine ⟨950353748187956286006829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1267138330917275048009105 950353748187956286006829)
              ·
                refine ⟨356382655570483607252561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 950353748187956286006829 356382655570483607252561)
                ·
                  refine ⟨267286991677862705439421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 356382655570483607252561 267286991677862705439421)
                  ·
                    rfl

theorem cell20_585607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 2, 3, 2].length) (baseStart_585607 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_585607 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_585607 prefixEnd_585607 := by exact prefixLift 585607
  have htrace : WordTrace (prefixWord ++ tailWord_585607) baseStart_585607 baseEnd_585607 := by
    simpa [prefixWord, tailWord_585607, baseEnd_585607] using wordTrace_append hprefix tailTrace_585607
  have hstable : (prefixWord ++ tailWord_585607).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585607).length < 2 ^ (prefixWord ++ tailWord_585607).sum := by decide
  have hdescent : baseEnd_585607 < baseStart_585607 := by decide
  rcases family_descends (prefixWord ++ tailWord_585607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585628 : List Nat := [2, 2, 3, 3, 1, 2, 2, 1, 4]
def baseStart_585628 : Nat := 118140960795 + 585628 * 2 ^ 59
def prefixEnd_585628 : Nat := 4983230072969 + 3 ^ 40 * 585628 * 2
def baseEnd_585628 : Nat := 267296576650079965739335

theorem tailTrace_585628 : CollatzResearch.WordTrace tailWord_585628 prefixEnd_585628 267296576650079965739335 := by
  unfold tailWord_585628
  simp only [CollatzResearch.WordTrace]
  refine ⟨10679803961188624072362769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14239738614918165429817025 10679803961188624072362769)
  ·
    refine ⟨8009852970891468054272077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10679803961188624072362769 8009852970891468054272077)
    ·
      refine ⟨3003694864084300520352029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8009852970891468054272077 3003694864084300520352029)
      ·
        refine ⟨1126385574031612695132011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3003694864084300520352029 1126385574031612695132011)
        ·
          refine ⟨1689578361047419042698017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1126385574031612695132011 1689578361047419042698017)
          ·
            refine ⟨1267183770785564282023513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1689578361047419042698017 1267183770785564282023513)
            ·
              refine ⟨950387828089173211517635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1267183770785564282023513 950387828089173211517635)
              ·
                refine ⟨1425581742133759817276453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 950387828089173211517635 1425581742133759817276453)
                ·
                  refine ⟨267296576650079965739335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1425581742133759817276453 267296576650079965739335)
                  ·
                    rfl

theorem cell20_585628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2, 1, 4].length) (baseStart_585628 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_585628 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_585628 prefixEnd_585628 := by exact prefixLift 585628
  have htrace : WordTrace (prefixWord ++ tailWord_585628) baseStart_585628 baseEnd_585628 := by
    simpa [prefixWord, tailWord_585628, baseEnd_585628] using wordTrace_append hprefix tailTrace_585628
  have hstable : (prefixWord ++ tailWord_585628).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585628).length < 2 ^ (prefixWord ++ tailWord_585628).sum := by decide
  have hdescent : baseEnd_585628 < baseStart_585628 := by decide
  rcases family_descends (prefixWord ++ tailWord_585628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585649 : List Nat := [1, 2, 2, 4, 2, 1, 2, 2, 4]
def baseStart_585649 : Nat := 118140960795 + 585649 * 2 ^ 59
def prefixEnd_585649 : Nat := 4983230072969 + 3 ^ 40 * 585649 * 2
def baseEnd_585649 : Nat := 267306161622297226039249

theorem tailTrace_585649 : CollatzResearch.WordTrace tailWord_585649 prefixEnd_585649 267306161622297226039249 := by
  unfold tailWord_585649
  simp only [CollatzResearch.WordTrace]
  refine ⟨21360373855301168731240001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14240249236867445820826667 21360373855301168731240001)
  ·
    refine ⟨16020280391475876548430001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21360373855301168731240001 16020280391475876548430001)
    ·
      refine ⟨12015210293606907411322501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16020280391475876548430001 12015210293606907411322501)
      ·
        refine ⟨2252851930051295139622969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12015210293606907411322501 2252851930051295139622969)
        ·
          refine ⟨1689638947538471354717227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2252851930051295139622969 1689638947538471354717227)
          ·
            refine ⟨2534458421307707032075841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1689638947538471354717227 2534458421307707032075841)
            ·
              refine ⟨1900843815980780274056881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2534458421307707032075841 1900843815980780274056881)
              ·
                refine ⟨1425632861985585205542661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1900843815980780274056881 1425632861985585205542661)
                ·
                  refine ⟨267306161622297226039249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1425632861985585205542661 267306161622297226039249)
                  ·
                    rfl

theorem cell20_585649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 2, 4].length) (baseStart_585649 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_585649 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_585649 prefixEnd_585649 := by exact prefixLift 585649
  have htrace : WordTrace (prefixWord ++ tailWord_585649) baseStart_585649 baseEnd_585649 := by
    simpa [prefixWord, tailWord_585649, baseEnd_585649] using wordTrace_append hprefix tailTrace_585649
  have hstable : (prefixWord ++ tailWord_585649).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585649).length < 2 ^ (prefixWord ++ tailWord_585649).sum := by decide
  have hdescent : baseEnd_585649 < baseStart_585649 := by decide
  rcases family_descends (prefixWord ++ tailWord_585649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585652 : List Nat := [2, 5, 2, 1, 2, 1, 1, 6]
def baseStart_585652 : Nat := 118140960795 + 585652 * 2 ^ 59
def prefixEnd_585652 : Nat := 4983230072969 + 3 ^ 40 * 585652 * 2
def baseEnd_585652 : Nat := 89102510301347516313079

theorem tailTrace_585652 : CollatzResearch.WordTrace tailWord_585652 prefixEnd_585652 89102510301347516313079 := by
  unfold tailWord_585652
  simp only [CollatzResearch.WordTrace]
  refine ⟨10680241637145150121799605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14240322182860200162399473 10680241637145150121799605)
  ·
    refine ⟨1001272653482357823918713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10680241637145150121799605 1001272653482357823918713)
    ·
      refine ⟨750954490111768367939035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1001272653482357823918713 750954490111768367939035)
      ·
        refine ⟨1126431735167652551908553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 750954490111768367939035 1126431735167652551908553)
        ·
          refine ⟨844823801375739413931415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1126431735167652551908553 844823801375739413931415)
          ·
            refine ⟨1267235702063609120897123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 844823801375739413931415 1267235702063609120897123)
            ·
              refine ⟨1900853553095413681345685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1267235702063609120897123 1900853553095413681345685)
              ·
                refine ⟨89102510301347516313079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1900853553095413681345685 89102510301347516313079)
                ·
                  rfl

theorem cell20_585652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 6].length) (baseStart_585652 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_585652 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_585652 prefixEnd_585652 := by exact prefixLift 585652
  have htrace : WordTrace (prefixWord ++ tailWord_585652) baseStart_585652 baseEnd_585652 := by
    simpa [prefixWord, tailWord_585652, baseEnd_585652] using wordTrace_append hprefix tailTrace_585652
  have hstable : (prefixWord ++ tailWord_585652).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585652).length < 2 ^ (prefixWord ++ tailWord_585652).sum := by decide
  have hdescent : baseEnd_585652 < baseStart_585652 := by decide
  rcases family_descends (prefixWord ++ tailWord_585652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585693 : List Nat := [1, 4, 3, 1, 4, 1, 2, 1, 3]
def baseStart_585693 : Nat := 118140960795 + 585693 * 2 ^ 59
def prefixEnd_585693 : Nat := 4983230072969 + 3 ^ 40 * 585693 * 2
def baseEnd_585693 : Nat := 267326244421228628572403

theorem tailTrace_585693 : CollatzResearch.WordTrace tailWord_585693 prefixEnd_585693 267326244421228628572403 := by
  unfold tailWord_585693
  simp only [CollatzResearch.WordTrace]
  refine ⟨21361978667141764245841733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14241319111427842830561155 21361978667141764245841733)
  ·
    refine ⟨4005371000089080796095325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21361978667141764245841733 4005371000089080796095325)
    ·
      refine ⟨1502014125033405298535747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4005371000089080796095325 1502014125033405298535747)
      ·
        refine ⟨2253021187550107947803621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1502014125033405298535747 2253021187550107947803621)
        ·
          refine ⟨422441472665645240213179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2253021187550107947803621 422441472665645240213179)
          ·
            refine ⟨633662208998467860319769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 422441472665645240213179 633662208998467860319769)
            ·
              refine ⟨475246656748850895239827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 633662208998467860319769 475246656748850895239827)
              ·
                refine ⟨712869985123276342859741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 475246656748850895239827 712869985123276342859741)
                ·
                  refine ⟨267326244421228628572403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 712869985123276342859741 267326244421228628572403)
                  ·
                    rfl

theorem cell20_585693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 2, 1, 3].length) (baseStart_585693 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_585693 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_585693 prefixEnd_585693 := by exact prefixLift 585693
  have htrace : WordTrace (prefixWord ++ tailWord_585693) baseStart_585693 baseEnd_585693 := by
    simpa [prefixWord, tailWord_585693, baseEnd_585693] using wordTrace_append hprefix tailTrace_585693
  have hstable : (prefixWord ++ tailWord_585693).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585693).length < 2 ^ (prefixWord ++ tailWord_585693).sum := by decide
  have hdescent : baseEnd_585693 < baseStart_585693 := by decide
  rcases family_descends (prefixWord ++ tailWord_585693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585708 : List Nat := [2, 2, 1, 1, 2, 1, 1, 6, 4]
def baseStart_585708 : Nat := 118140960795 + 585708 * 2 ^ 59
def prefixEnd_585708 : Nat := 4983230072969 + 3 ^ 40 * 585708 * 2
def baseEnd_585708 : Nat := 267333090829955243072341

theorem tailTrace_585708 : CollatzResearch.WordTrace tailWord_585708 prefixEnd_585708 267333090829955243072341 := by
  unfold tailWord_585708
  simp only [CollatzResearch.WordTrace]
  refine ⟨10681262881043710903818889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14241683841391614538425185 10681262881043710903818889)
  ·
    refine ⟨8010947160782783177864167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10681262881043710903818889 8010947160782783177864167)
    ·
      refine ⟨12016420741174174766796251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8010947160782783177864167 12016420741174174766796251)
      ·
        refine ⟨18024631111761262150194377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12016420741174174766796251 18024631111761262150194377)
        ·
          refine ⟨13518473333820946612645783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18024631111761262150194377 13518473333820946612645783)
          ·
            refine ⟨20277710000731419918968675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13518473333820946612645783 20277710000731419918968675)
            ·
              refine ⟨30416565001097129878453013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20277710000731419918968675 30416565001097129878453013)
              ·
                refine ⟨1425776484426427963052485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 30416565001097129878453013 1425776484426427963052485)
                ·
                  refine ⟨267333090829955243072341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1425776484426427963052485 267333090829955243072341)
                  ·
                    rfl

theorem cell20_585708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 4].length) (baseStart_585708 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_585708 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_585708 prefixEnd_585708 := by exact prefixLift 585708
  have htrace : WordTrace (prefixWord ++ tailWord_585708) baseStart_585708 baseEnd_585708 := by
    simpa [prefixWord, tailWord_585708, baseEnd_585708] using wordTrace_append hprefix tailTrace_585708
  have hstable : (prefixWord ++ tailWord_585708).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585708).length < 2 ^ (prefixWord ++ tailWord_585708).sum := by decide
  have hdescent : baseEnd_585708 < baseStart_585708 := by decide
  rcases family_descends (prefixWord ++ tailWord_585708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585732 : List Nat := [2, 3, 2, 4, 9]
def baseStart_585732 : Nat := 118140960795 + 585732 * 2 ^ 59
def prefixEnd_585732 : Nat := 4983230072969 + 3 ^ 40 * 585732 * 2
def baseEnd_585732 : Nat := 3300543766468121312003

theorem tailTrace_585732 : CollatzResearch.WordTrace tailWord_585732 prefixEnd_585732 3300543766468121312003 := by
  unfold tailWord_585732
  simp only [CollatzResearch.WordTrace]
  refine ⟨10681700557000236953255725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14242267409333649271007633 10681700557000236953255725)
  ·
    refine ⟨4005637708875088857470897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10681700557000236953255725 4005637708875088857470897)
    ·
      refine ⟨3004228281656316643103173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4005637708875088857470897 3004228281656316643103173)
      ·
        refine ⟨563292802810559370581845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3004228281656316643103173 563292802810559370581845)
        ·
          refine ⟨3300543766468121312003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 563292802810559370581845 3300543766468121312003)
          ·
            rfl

theorem cell20_585732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 9].length) (baseStart_585732 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_585732 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_585732 prefixEnd_585732 := by exact prefixLift 585732
  have htrace : WordTrace (prefixWord ++ tailWord_585732) baseStart_585732 baseEnd_585732 := by
    simpa [prefixWord, tailWord_585732, baseEnd_585732] using wordTrace_append hprefix tailTrace_585732
  have hstable : (prefixWord ++ tailWord_585732).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585732).length < 2 ^ (prefixWord ++ tailWord_585732).sum := by decide
  have hdescent : baseEnd_585732 < baseStart_585732 := by decide
  rcases family_descends (prefixWord ++ tailWord_585732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585734 : List Nat := [6, 2, 1, 2, 1, 1, 1, 4, 2]
def baseStart_585734 : Nat := 118140960795 + 585734 * 2 ^ 59
def prefixEnd_585734 : Nat := 4983230072969 + 3 ^ 40 * 585734 * 2
def baseEnd_585734 : Nat := 267344957938414708205569

theorem tailTrace_585734 : CollatzResearch.WordTrace tailWord_585734 prefixEnd_585734 267344957938414708205569 := by
  unfold tailWord_585734
  simp only [CollatzResearch.WordTrace]
  refine ⟨667608564374788382752633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 14242316039995485498722837 667608564374788382752633)
  ·
    refine ⟨500706423281091287064475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 667608564374788382752633 500706423281091287064475)
    ·
      refine ⟨751059634921636930596713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 500706423281091287064475 751059634921636930596713)
      ·
        refine ⟨563294726191227697947535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 751059634921636930596713 563294726191227697947535)
        ·
          refine ⟨844942089286841546921303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 563294726191227697947535 844942089286841546921303)
          ·
            refine ⟨1267413133930262320381955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 844942089286841546921303 1267413133930262320381955)
            ·
              refine ⟨1901119700895393480572933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1267413133930262320381955 1901119700895393480572933)
              ·
                refine ⟨356459943917886277607425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1901119700895393480572933 356459943917886277607425)
                ·
                  refine ⟨267344957938414708205569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 356459943917886277607425 267344957938414708205569)
                  ·
                    rfl

theorem cell20_585734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_585734 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_585734 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_585734 prefixEnd_585734 := by exact prefixLift 585734
  have htrace : WordTrace (prefixWord ++ tailWord_585734) baseStart_585734 baseEnd_585734 := by
    simpa [prefixWord, tailWord_585734, baseEnd_585734] using wordTrace_append hprefix tailTrace_585734
  have hstable : (prefixWord ++ tailWord_585734).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585734).length < 2 ^ (prefixWord ++ tailWord_585734).sum := by decide
  have hdescent : baseEnd_585734 < baseStart_585734 := by decide
  rcases family_descends (prefixWord ++ tailWord_585734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585738 : List Nat := [3, 1, 2, 2, 4, 2, 2, 2, 2]
def baseStart_585738 : Nat := 118140960795 + 585738 * 2 ^ 59
def prefixEnd_585738 : Nat := 4983230072969 + 3 ^ 40 * 585738 * 2
def baseEnd_585738 : Nat := 267346783647408472072219

theorem tailTrace_585738 : CollatzResearch.WordTrace tailWord_585738 prefixEnd_585738 267346783647408472072219 := by
  unfold tailWord_585738
  simp only [CollatzResearch.WordTrace]
  refine ⟨5340904987994684232807467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14242413301319157954153245 5340904987994684232807467)
  ·
    refine ⟨8011357481992026349211201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5340904987994684232807467 8011357481992026349211201)
    ·
      refine ⟨6008518111494019761908401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8011357481992026349211201 6008518111494019761908401)
      ·
        refine ⟨4506388583620514821431301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6008518111494019761908401 4506388583620514821431301)
        ·
          refine ⟨844947859428846529018369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4506388583620514821431301 844947859428846529018369)
          ·
            refine ⟨633710894571634896763777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 844947859428846529018369 633710894571634896763777)
            ·
              refine ⟨475283170928726172572833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 633710894571634896763777 475283170928726172572833)
              ·
                refine ⟨356462378196544629429625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 475283170928726172572833 356462378196544629429625)
                ·
                  refine ⟨267346783647408472072219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 356462378196544629429625 267346783647408472072219)
                  ·
                    rfl

theorem cell20_585738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 2, 2, 2].length) (baseStart_585738 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_585738 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_585738 prefixEnd_585738 := by exact prefixLift 585738
  have htrace : WordTrace (prefixWord ++ tailWord_585738) baseStart_585738 baseEnd_585738 := by
    simpa [prefixWord, tailWord_585738, baseEnd_585738] using wordTrace_append hprefix tailTrace_585738
  have hstable : (prefixWord ++ tailWord_585738).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585738).length < 2 ^ (prefixWord ++ tailWord_585738).sum := by decide
  have hdescent : baseEnd_585738 < baseStart_585738 := by decide
  rcases family_descends (prefixWord ++ tailWord_585738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585742 : List Nat := [4, 1, 1, 2, 2, 1, 3, 4, 2]
def baseStart_585742 : Nat := 118140960795 + 585742 * 2 ^ 59
def prefixEnd_585742 : Nat := 4983230072969 + 3 ^ 40 * 585742 * 2
def baseEnd_585742 : Nat := 267348609356402235938869

theorem tailTrace_585742 : CollatzResearch.WordTrace tailWord_585742 prefixEnd_585742 267348609356402235938869 := by
  unfold tailWord_585742
  simp only [CollatzResearch.WordTrace]
  refine ⟨2670470730495530701796935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14242510562642830409583653 2670470730495530701796935)
  ·
    refine ⟨4005706095743296052695403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2670470730495530701796935 4005706095743296052695403)
    ·
      refine ⟨6008559143614944079043105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4005706095743296052695403 6008559143614944079043105)
      ·
        refine ⟨4506419357711208059282329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6008559143614944079043105 4506419357711208059282329)
        ·
          refine ⟨3379814518283406044461747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4506419357711208059282329 3379814518283406044461747)
          ·
            refine ⟨5069721777425109066692621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3379814518283406044461747 5069721777425109066692621)
            ·
              refine ⟨1901145666534415900009733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5069721777425109066692621 1901145666534415900009733)
              ·
                refine ⟨356464812475202981251825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1901145666534415900009733 356464812475202981251825)
                ·
                  refine ⟨267348609356402235938869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 356464812475202981251825 267348609356402235938869)
                  ·
                    rfl

theorem cell20_585742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 4, 2].length) (baseStart_585742 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_585742 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_585742 prefixEnd_585742 := by exact prefixLift 585742
  have htrace : WordTrace (prefixWord ++ tailWord_585742) baseStart_585742 baseEnd_585742 := by
    simpa [prefixWord, tailWord_585742, baseEnd_585742] using wordTrace_append hprefix tailTrace_585742
  have hstable : (prefixWord ++ tailWord_585742).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585742).length < 2 ^ (prefixWord ++ tailWord_585742).sum := by decide
  have hdescent : baseEnd_585742 < baseStart_585742 := by decide
  rcases family_descends (prefixWord ++ tailWord_585742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585749 : List Nat := [1, 3, 2, 1, 5, 2, 1, 5]
def baseStart_585749 : Nat := 118140960795 + 585749 * 2 ^ 59
def prefixEnd_585749 : Nat := 4983230072969 + 3 ^ 40 * 585749 * 2
def baseEnd_585749 : Nat := 89117268115713774235169

theorem tailTrace_585749 : CollatzResearch.WordTrace tailWord_585749 prefixEnd_585749 89117268115713774235169 := by
  unfold tailWord_585749
  simp only [CollatzResearch.WordTrace]
  refine ⟨21364021154938885809880301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14242680769959257206586867 21364021154938885809880301)
  ·
    refine ⟨8011507933102082178705113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21364021154938885809880301 8011507933102082178705113)
    ·
      refine ⟨6008630949826561634028835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8011507933102082178705113 6008630949826561634028835)
      ·
        refine ⟨9012946424739842451043253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6008630949826561634028835 9012946424739842451043253)
        ·
          refine ⟨844963727319360229785305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9012946424739842451043253 844963727319360229785305)
          ·
            refine ⟨633722795489520172338979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 844963727319360229785305 633722795489520172338979)
            ·
              refine ⟨950584193234280258508469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 633722795489520172338979 950584193234280258508469)
              ·
                refine ⟨89117268115713774235169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 950584193234280258508469 89117268115713774235169)
                ·
                  rfl

theorem cell20_585749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 1, 5].length) (baseStart_585749 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_585749 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_585749 prefixEnd_585749 := by exact prefixLift 585749
  have htrace : WordTrace (prefixWord ++ tailWord_585749) baseStart_585749 baseEnd_585749 := by
    simpa [prefixWord, tailWord_585749, baseEnd_585749] using wordTrace_append hprefix tailTrace_585749
  have hstable : (prefixWord ++ tailWord_585749).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585749).length < 2 ^ (prefixWord ++ tailWord_585749).sum := by decide
  have hdescent : baseEnd_585749 < baseStart_585749 := by decide
  rcases family_descends (prefixWord ++ tailWord_585749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585756 : List Nat := [2, 2, 3, 1, 3, 1, 2, 3, 3]
def baseStart_585756 : Nat := 118140960795 + 585756 * 2 ^ 59
def prefixEnd_585756 : Nat := 4983230072969 + 3 ^ 40 * 585756 * 2
def baseEnd_585756 : Nat := 267354999337880409472145

theorem tailTrace_585756 : CollatzResearch.WordTrace tailWord_585756 prefixEnd_585756 267354999337880409472145 := by
  unfold tailWord_585756
  simp only [CollatzResearch.WordTrace]
  refine ⟨10682138232956763002692561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14242850977275684003590081 10682138232956763002692561)
  ·
    refine ⟨8011603674717572252019421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10682138232956763002692561 8011603674717572252019421)
    ·
      refine ⟨3004351378019089594507283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8011603674717572252019421 3004351378019089594507283)
      ·
        refine ⟨4506527067028634391760925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3004351378019089594507283 4506527067028634391760925)
        ·
          refine ⟨1689947650135737896910347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4506527067028634391760925 1689947650135737896910347)
          ·
            refine ⟨2534921475203606845365521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1689947650135737896910347 2534921475203606845365521)
            ·
              refine ⟨1901191106402705134024141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2534921475203606845365521 1901191106402705134024141)
              ·
                refine ⟨712946664901014425259053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1901191106402705134024141 712946664901014425259053)
                ·
                  refine ⟨267354999337880409472145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 712946664901014425259053 267354999337880409472145)
                  ·
                    rfl

theorem cell20_585756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 3, 3].length) (baseStart_585756 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_585756 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_585756 prefixEnd_585756 := by exact prefixLift 585756
  have htrace : WordTrace (prefixWord ++ tailWord_585756) baseStart_585756 baseEnd_585756 := by
    simpa [prefixWord, tailWord_585756, baseEnd_585756] using wordTrace_append hprefix tailTrace_585756
  have hstable : (prefixWord ++ tailWord_585756).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585756).length < 2 ^ (prefixWord ++ tailWord_585756).sum := by decide
  have hdescent : baseEnd_585756 < baseStart_585756 := by decide
  rcases family_descends (prefixWord ++ tailWord_585756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585790 : List Nat := [4, 2, 1, 3, 2, 2, 1, 2, 3]
def baseStart_585790 : Nat := 118140960795 + 585790 * 2 ^ 59
def prefixEnd_585790 : Nat := 4983230072969 + 3 ^ 40 * 585790 * 2
def baseEnd_585790 : Nat := 267370517864327402338673

theorem tailTrace_585790 : CollatzResearch.WordTrace tailWord_585790 prefixEnd_585790 267370517864327402338673 := by
  unfold tailWord_585790
  simp only [CollatzResearch.WordTrace]
  refine ⟨2670689568473793726515353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14243677698526899874748549 2670689568473793726515353)
  ·
    refine ⟨2003017176355345294886515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2670689568473793726515353 2003017176355345294886515)
    ·
      refine ⟨3004525764533017942329773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2003017176355345294886515 3004525764533017942329773)
      ·
        refine ⟨1126697161699881728373665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3004525764533017942329773 1126697161699881728373665)
        ·
          refine ⟨845022871274911296280249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1126697161699881728373665 845022871274911296280249)
          ·
            refine ⟨633767153456183472210187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 845022871274911296280249 633767153456183472210187)
            ·
              refine ⟨950650730184275208315281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 633767153456183472210187 950650730184275208315281)
              ·
                refine ⟨712988047638206406236461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 950650730184275208315281 712988047638206406236461)
                ·
                  refine ⟨267370517864327402338673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 712988047638206406236461 267370517864327402338673)
                  ·
                    rfl

theorem cell20_585790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 1, 2, 3].length) (baseStart_585790 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_585790 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_585790 prefixEnd_585790 := by exact prefixLift 585790
  have htrace : WordTrace (prefixWord ++ tailWord_585790) baseStart_585790 baseEnd_585790 := by
    simpa [prefixWord, tailWord_585790, baseEnd_585790] using wordTrace_append hprefix tailTrace_585790
  have hstable : (prefixWord ++ tailWord_585790).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585790).length < 2 ^ (prefixWord ++ tailWord_585790).sum := by decide
  have hdescent : baseEnd_585790 < baseStart_585790 := by decide
  rcases family_descends (prefixWord ++ tailWord_585790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585801 : List Nat := [1, 2, 1, 1, 2, 2, 3, 6, 2]
def baseStart_585801 : Nat := 118140960795 + 585801 * 2 ^ 59
def prefixEnd_585801 : Nat := 4983230072969 + 3 ^ 40 * 585801 * 2
def baseEnd_585801 : Nat := 267375538564060252971961

theorem tailTrace_585801 : CollatzResearch.WordTrace tailWord_585801 prefixEnd_585801 267375538564060252971961 := by
  unfold tailWord_585801
  simp only [CollatzResearch.WordTrace]
  refine ⟨21365917750750498690773257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14243945167166999127182171 21365917750750498690773257)
  ·
    refine ⟨16024438313062874018079943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21365917750750498690773257 16024438313062874018079943)
    ·
      refine ⟨24036657469594311027119915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16024438313062874018079943 24036657469594311027119915)
      ·
        refine ⟨36054986204391466540679873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24036657469594311027119915 36054986204391466540679873)
        ·
          refine ⟨27041239653293599905509905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36054986204391466540679873 27041239653293599905509905)
          ·
            refine ⟨20280929739970199929132429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27041239653293599905509905 20280929739970199929132429)
            ·
              refine ⟨7605348652488824973424661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20280929739970199929132429 7605348652488824973424661)
              ·
                refine ⟨356500718085413670629281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7605348652488824973424661 356500718085413670629281)
                ·
                  refine ⟨267375538564060252971961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 356500718085413670629281 267375538564060252971961)
                  ·
                    rfl

theorem cell20_585801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 6, 2].length) (baseStart_585801 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_585801 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_585801 prefixEnd_585801 := by exact prefixLift 585801
  have htrace : WordTrace (prefixWord ++ tailWord_585801) baseStart_585801 baseEnd_585801 := by
    simpa [prefixWord, tailWord_585801, baseEnd_585801] using wordTrace_append hprefix tailTrace_585801
  have hstable : (prefixWord ++ tailWord_585801).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585801).length < 2 ^ (prefixWord ++ tailWord_585801).sum := by decide
  have hdescent : baseEnd_585801 < baseStart_585801 := by decide
  rcases family_descends (prefixWord ++ tailWord_585801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585815 : List Nat := [1, 1, 3, 2, 2, 1, 2, 5, 3]
def baseStart_585815 : Nat := 118140960795 + 585815 * 2 ^ 59
def prefixEnd_585815 : Nat := 4983230072969 + 3 ^ 40 * 585815 * 2
def baseEnd_585815 : Nat := 267381928545538426505237

theorem tailTrace_585815 : CollatzResearch.WordTrace tailWord_585815 prefixEnd_585815 267381928545538426505237 := by
  unfold tailWord_585815
  simp only [CollatzResearch.WordTrace]
  refine ⟨21366428372699779081782899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14244285581799852721188599 21366428372699779081782899)
  ·
    refine ⟨32049642559049668622674349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21366428372699779081782899 32049642559049668622674349)
    ·
      refine ⟨12018615959643625733502881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32049642559049668622674349 12018615959643625733502881)
      ·
        refine ⟨9013961969732719300127161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12018615959643625733502881 9013961969732719300127161)
        ·
          refine ⟨6760471477299539475095371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9013961969732719300127161 6760471477299539475095371)
          ·
            refine ⟨10140707215949309212643057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6760471477299539475095371 10140707215949309212643057)
            ·
              refine ⟨7605530411961981909482293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10140707215949309212643057 7605530411961981909482293)
              ·
                refine ⟨713018476121435804013965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7605530411961981909482293 713018476121435804013965)
                ·
                  refine ⟨267381928545538426505237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 713018476121435804013965 267381928545538426505237)
                  ·
                    rfl

theorem cell20_585815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 5, 3].length) (baseStart_585815 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_585815 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_585815 prefixEnd_585815 := by exact prefixLift 585815
  have htrace : WordTrace (prefixWord ++ tailWord_585815) baseStart_585815 baseEnd_585815 := by
    simpa [prefixWord, tailWord_585815, baseEnd_585815] using wordTrace_append hprefix tailTrace_585815
  have hstable : (prefixWord ++ tailWord_585815).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585815).length < 2 ^ (prefixWord ++ tailWord_585815).sum := by decide
  have hdescent : baseEnd_585815 < baseStart_585815 := by decide
  rcases family_descends (prefixWord ++ tailWord_585815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585846 : List Nat := [5, 1, 1, 2, 1, 2, 8]
def baseStart_585846 : Nat := 118140960795 + 585846 * 2 ^ 59
def prefixEnd_585846 : Nat := 4983230072969 + 3 ^ 40 * 585846 * 2
def baseEnd_585846 : Nat := 29710675310026677385753

theorem tailTrace_585846 : CollatzResearch.WordTrace tailWord_585846 prefixEnd_585846 29710675310026677385753 := by
  unfold tailWord_585846
  simp only [CollatzResearch.WordTrace]
  refine ⟨1335472439724216961010087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14245039357058314250774261 1335472439724216961010087)
  ·
    refine ⟨2003208659586325441515131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1335472439724216961010087 2003208659586325441515131)
    ·
      refine ⟨3004812989379488162272697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2003208659586325441515131 3004812989379488162272697)
      ·
        refine ⟨2253609742034616121704523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3004812989379488162272697 2253609742034616121704523)
        ·
          refine ⟨3380414613051924182556785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2253609742034616121704523 3380414613051924182556785)
          ·
            refine ⟨2535310959788943136917589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3380414613051924182556785 2535310959788943136917589)
            ·
              refine ⟨29710675310026677385753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2535310959788943136917589 29710675310026677385753)
              ·
                rfl

theorem cell20_585846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 8].length) (baseStart_585846 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_585846 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_585846 prefixEnd_585846 := by exact prefixLift 585846
  have htrace : WordTrace (prefixWord ++ tailWord_585846) baseStart_585846 baseEnd_585846 := by
    simpa [prefixWord, tailWord_585846, baseEnd_585846] using wordTrace_append hprefix tailTrace_585846
  have hstable : (prefixWord ++ tailWord_585846).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585846).length < 2 ^ (prefixWord ++ tailWord_585846).sum := by decide
  have hdescent : baseEnd_585846 < baseStart_585846 := by decide
  rcases family_descends (prefixWord ++ tailWord_585846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585853 : List Nat := [1, 4, 1, 1, 3, 2, 2, 1, 5]
def baseStart_585853 : Nat := 118140960795 + 585853 * 2 ^ 59
def prefixEnd_585853 : Nat := 4983230072969 + 3 ^ 40 * 585853 * 2
def baseEnd_585853 : Nat := 267399272780979183238415

theorem tailTrace_585853 : CollatzResearch.WordTrace tailWord_585853 prefixEnd_585853 267399272780979183238415 := by
  unfold tailWord_585853
  simp only [CollatzResearch.WordTrace]
  refine ⟨21367814346562111571666213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14245209564374741047777475 21367814346562111571666213)
  ·
    refine ⟨4006465189980395919687415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21367814346562111571666213 4006465189980395919687415)
    ·
      refine ⟨6009697784970593879531123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4006465189980395919687415 6009697784970593879531123)
      ·
        refine ⟨9014546677455890819296685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6009697784970593879531123 9014546677455890819296685)
        ·
          refine ⟨3380455004045959057236257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9014546677455890819296685 3380455004045959057236257)
          ·
            refine ⟨2535341253034469292927193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3380455004045959057236257 2535341253034469292927193)
            ·
              refine ⟨1901505939775851969695395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2535341253034469292927193 1901505939775851969695395)
              ·
                refine ⟨2852258909663777954543093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1901505939775851969695395 2852258909663777954543093)
                ·
                  refine ⟨267399272780979183238415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2852258909663777954543093 267399272780979183238415)
                  ·
                    rfl

theorem cell20_585853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 1, 5].length) (baseStart_585853 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_585853 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_585853 prefixEnd_585853 := by exact prefixLift 585853
  have htrace : WordTrace (prefixWord ++ tailWord_585853) baseStart_585853 baseEnd_585853 := by
    simpa [prefixWord, tailWord_585853, baseEnd_585853] using wordTrace_append hprefix tailTrace_585853
  have hstable : (prefixWord ++ tailWord_585853).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585853).length < 2 ^ (prefixWord ++ tailWord_585853).sum := by decide
  have hdescent : baseEnd_585853 < baseStart_585853 := by decide
  rcases family_descends (prefixWord ++ tailWord_585853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585905 : List Nat := [1, 2, 2, 5, 10]
def baseStart_585905 : Nat := 118140960795 + 585905 * 2 ^ 59
def prefixEnd_585905 : Nat := 4983230072969 + 3 ^ 40 * 585905 * 2
def baseEnd_585905 : Nat := 3301518604912322388949

theorem tailTrace_585905 : CollatzResearch.WordTrace tailWord_585905 prefixEnd_585905 3301518604912322388949 := by
  unfold tailWord_585905
  simp only [CollatzResearch.WordTrace]
  refine ⟨21369710942373724452559169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14246473961582482968372779 21369710942373724452559169)
  ·
    refine ⟨16027283206780293339419377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21369710942373724452559169 16027283206780293339419377)
    ·
      refine ⟨12020462405085220004564533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16027283206780293339419377 12020462405085220004564533)
      ·
        refine ⟨1126918350476739375427925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12020462405085220004564533 1126918350476739375427925)
        ·
          refine ⟨3301518604912322388949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1126918350476739375427925 3301518604912322388949)
          ·
            rfl

theorem cell20_585905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 10].length) (baseStart_585905 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_585905 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_585905 prefixEnd_585905 := by exact prefixLift 585905
  have htrace : WordTrace (prefixWord ++ tailWord_585905) baseStart_585905 baseEnd_585905 := by
    simpa [prefixWord, tailWord_585905, baseEnd_585905] using wordTrace_append hprefix tailTrace_585905
  have hstable : (prefixWord ++ tailWord_585905).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585905).length < 2 ^ (prefixWord ++ tailWord_585905).sum := by decide
  have hdescent : baseEnd_585905 < baseStart_585905 := by decide
  rcases family_descends (prefixWord ++ tailWord_585905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585911 : List Nat := [1, 1, 3, 1, 4, 4, 2, 2, 2]
def baseStart_585911 : Nat := 118140960795 + 585911 * 2 ^ 59
def prefixEnd_585911 : Nat := 4983230072969 + 3 ^ 40 * 585911 * 2
def baseEnd_585911 : Nat := 267425745561388759304845

theorem tailTrace_585911 : CollatzResearch.WordTrace tailWord_585911 prefixEnd_585911 267425745561388759304845 := by
  unfold tailWord_585911
  simp only [CollatzResearch.WordTrace]
  refine ⟨21369929780351987477277587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14246619853567991651518391 21369929780351987477277587)
  ·
    refine ⟨32054894670527981215916381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21369929780351987477277587 32054894670527981215916381)
    ·
      refine ⟨12020585501447992955968643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32054894670527981215916381 12020585501447992955968643)
      ·
        refine ⟨18030878252171989433952965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12020585501447992955968643 18030878252171989433952965)
        ·
          refine ⟨3380789672282248018866181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18030878252171989433952965 3380789672282248018866181)
          ·
            refine ⟨633898063552921503537409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3380789672282248018866181 633898063552921503537409)
            ·
              refine ⟨475423547664691127653057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 633898063552921503537409 475423547664691127653057)
              ·
                refine ⟨356567660748518345739793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 475423547664691127653057 356567660748518345739793)
                ·
                  refine ⟨267425745561388759304845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 356567660748518345739793 267425745561388759304845)
                  ·
                    rfl

theorem cell20_585911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 2, 2, 2].length) (baseStart_585911 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_585911 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_585911 prefixEnd_585911 := by exact prefixLift 585911
  have htrace : WordTrace (prefixWord ++ tailWord_585911) baseStart_585911 baseEnd_585911 := by
    simpa [prefixWord, tailWord_585911, baseEnd_585911] using wordTrace_append hprefix tailTrace_585911
  have hstable : (prefixWord ++ tailWord_585911).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585911).length < 2 ^ (prefixWord ++ tailWord_585911).sum := by decide
  have hdescent : baseEnd_585911 < baseStart_585911 := by decide
  rcases family_descends (prefixWord ++ tailWord_585911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585915 : List Nat := [1, 1, 1, 1, 1, 2, 7, 4, 2]
def baseStart_585915 : Nat := 118140960795 + 585915 * 2 ^ 59
def prefixEnd_585915 : Nat := 4983230072969 + 3 ^ 40 * 585915 * 2
def baseEnd_585915 : Nat := 267427571270382523171495

theorem tailTrace_585915 : CollatzResearch.WordTrace tailWord_585915 prefixEnd_585915 267427571270382523171495 := by
  unfold tailWord_585915
  simp only [CollatzResearch.WordTrace]
  refine ⟨21370075672337496160423199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14246717114891664106948799 21370075672337496160423199)
  ·
    refine ⟨32055113508506244240634799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21370075672337496160423199 32055113508506244240634799)
    ·
      refine ⟨48082670262759366360952199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32055113508506244240634799 48082670262759366360952199)
      ·
        refine ⟨72124005394139049541428299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48082670262759366360952199 72124005394139049541428299)
        ·
          refine ⟨108186008091208574312142449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72124005394139049541428299 108186008091208574312142449)
          ·
            refine ⟨81139506068406430734106837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108186008091208574312142449 81139506068406430734106837)
            ·
              refine ⟨1901707173478275720330629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 81139506068406430734106837 1901707173478275720330629)
              ·
                refine ⟨356570095027176697561993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1901707173478275720330629 356570095027176697561993)
                ·
                  refine ⟨267427571270382523171495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 356570095027176697561993 267427571270382523171495)
                  ·
                    rfl

theorem cell20_585915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 4, 2].length) (baseStart_585915 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_585915 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_585915 prefixEnd_585915 := by exact prefixLift 585915
  have htrace : WordTrace (prefixWord ++ tailWord_585915) baseStart_585915 baseEnd_585915 := by
    simpa [prefixWord, tailWord_585915, baseEnd_585915] using wordTrace_append hprefix tailTrace_585915
  have hstable : (prefixWord ++ tailWord_585915).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585915).length < 2 ^ (prefixWord ++ tailWord_585915).sum := by decide
  have hdescent : baseEnd_585915 < baseStart_585915 := by decide
  rcases family_descends (prefixWord ++ tailWord_585915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585918 : List Nat := [4, 2, 1, 1, 5, 1, 1, 5]
def baseStart_585918 : Nat := 118140960795 + 585918 * 2 ^ 59
def prefixEnd_585918 : Nat := 4983230072969 + 3 ^ 40 * 585918 * 2
def baseEnd_585918 : Nat := 89142980184042615357161

theorem tailTrace_585918 : CollatzResearch.WordTrace tailWord_585918 prefixEnd_585918 89142980184042615357161 := by
  unfold tailWord_585918
  simp only [CollatzResearch.WordTrace]
  refine ⟨2671273136415828459097801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14246790060884418448521605 2671273136415828459097801)
  ·
    refine ⟨2003454852311871344323351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2671273136415828459097801 2003454852311871344323351)
    ·
      refine ⟨3005182278467807016485027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2003454852311871344323351 3005182278467807016485027)
      ·
        refine ⟨4507773417701710524727541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3005182278467807016485027 4507773417701710524727541)
        ·
          refine ⟨422603757909535361693207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4507773417701710524727541 422603757909535361693207)
          ·
            refine ⟨633905636864303042539811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 422603757909535361693207 633905636864303042539811)
            ·
              refine ⟨950858455296454563809717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 633905636864303042539811 950858455296454563809717)
              ·
                refine ⟨89142980184042615357161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 950858455296454563809717 89142980184042615357161)
                ·
                  rfl

theorem cell20_585918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 1, 5].length) (baseStart_585918 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_585918 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_585918 prefixEnd_585918 := by exact prefixLift 585918
  have htrace : WordTrace (prefixWord ++ tailWord_585918) baseStart_585918 baseEnd_585918 := by
    simpa [prefixWord, tailWord_585918, baseEnd_585918] using wordTrace_append hprefix tailTrace_585918
  have hstable : (prefixWord ++ tailWord_585918).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585918).length < 2 ^ (prefixWord ++ tailWord_585918).sum := by decide
  have hdescent : baseEnd_585918 < baseStart_585918 := by decide
  rcases family_descends (prefixWord ++ tailWord_585918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585932 : List Nat := [2, 2, 1, 6, 1, 1, 1, 2, 4]
def baseStart_585932 : Nat := 118140960795 + 585932 * 2 ^ 59
def prefixEnd_585932 : Nat := 4983230072969 + 3 ^ 40 * 585932 * 2
def baseEnd_585932 : Nat := 267435330533606019604759

theorem tailTrace_585932 : CollatzResearch.WordTrace tailWord_585932 prefixEnd_585932 267435330533606019604759 := by
  unfold tailWord_585932
  simp only [CollatzResearch.WordTrace]
  refine ⟨10685347856637954031896025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14247130475517272042528033 10685347856637954031896025)
  ·
    refine ⟨8014010892478465523922019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10685347856637954031896025 8014010892478465523922019)
    ·
      refine ⟨12021016338717698285883029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8014010892478465523922019 12021016338717698285883029)
      ·
        refine ⟨563485140877392107150767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 12021016338717698285883029 563485140877392107150767)
        ·
          refine ⟨845227711316088160726151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 563485140877392107150767 845227711316088160726151)
          ·
            refine ⟨1267841566974132241089227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 845227711316088160726151 1267841566974132241089227)
            ·
              refine ⟨1901762350461198361633841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1267841566974132241089227 1901762350461198361633841)
              ·
                refine ⟨1426321762845898771225381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1901762350461198361633841 1426321762845898771225381)
                ·
                  refine ⟨267435330533606019604759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1426321762845898771225381 267435330533606019604759)
                  ·
                    rfl

theorem cell20_585932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 2, 4].length) (baseStart_585932 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_585932 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_585932 prefixEnd_585932 := by exact prefixLift 585932
  have htrace : WordTrace (prefixWord ++ tailWord_585932) baseStart_585932 baseEnd_585932 := by
    simpa [prefixWord, tailWord_585932, baseEnd_585932] using wordTrace_append hprefix tailTrace_585932
  have hstable : (prefixWord ++ tailWord_585932).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585932).length < 2 ^ (prefixWord ++ tailWord_585932).sum := by decide
  have hdescent : baseEnd_585932 < baseStart_585932 := by decide
  rcases family_descends (prefixWord ++ tailWord_585932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585949 : List Nat := [1, 4, 3, 2, 1, 2, 2, 3, 2]
def baseStart_585949 : Nat := 118140960795 + 585949 * 2 ^ 59
def prefixEnd_585949 : Nat := 4983230072969 + 3 ^ 40 * 585949 * 2
def baseEnd_585949 : Nat := 267443089796829516038023

theorem tailTrace_585949 : CollatzResearch.WordTrace tailWord_585949 prefixEnd_585949 267443089796829516038023 := by
  unfold tailWord_585949
  simp only [CollatzResearch.WordTrace]
  refine ⟨21371315754214319967160901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14247543836142879978107267 21371315754214319967160901)
  ·
    refine ⟨4007121703915184993842669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21371315754214319967160901 4007121703915184993842669)
    ·
      refine ⟨1502670638968194372691001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4007121703915184993842669 1502670638968194372691001)
      ·
        refine ⟨1127002979226145779518251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1502670638968194372691001 1127002979226145779518251)
        ·
          refine ⟨1690504468839218669277377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1127002979226145779518251 1690504468839218669277377)
          ·
            refine ⟨1267878351629414001958033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1690504468839218669277377 1267878351629414001958033)
            ·
              refine ⟨950908763722060501468525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1267878351629414001958033 950908763722060501468525)
              ·
                refine ⟨356590786395772688050697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 950908763722060501468525 356590786395772688050697)
                ·
                  refine ⟨267443089796829516038023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 356590786395772688050697 267443089796829516038023)
                  ·
                    rfl

theorem cell20_585949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2, 3, 2].length) (baseStart_585949 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_585949 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_585949 prefixEnd_585949 := by exact prefixLift 585949
  have htrace : WordTrace (prefixWord ++ tailWord_585949) baseStart_585949 baseEnd_585949 := by
    simpa [prefixWord, tailWord_585949, baseEnd_585949] using wordTrace_append hprefix tailTrace_585949
  have hstable : (prefixWord ++ tailWord_585949).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585949).length < 2 ^ (prefixWord ++ tailWord_585949).sum := by decide
  have hdescent : baseEnd_585949 < baseStart_585949 := by decide
  rcases family_descends (prefixWord ++ tailWord_585949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585967 : List Nat := [1, 1, 2, 1, 6, 2, 1, 1, 5]
def baseStart_585967 : Nat := 118140960795 + 585967 * 2 ^ 59
def prefixEnd_585967 : Nat := 4983230072969 + 3 ^ 40 * 585967 * 2
def baseEnd_585967 : Nat := 267451305487301453437949

theorem tailTrace_585967 : CollatzResearch.WordTrace tailWord_585967 prefixEnd_585967 267451305487301453437949 := by
  unfold tailWord_585967
  simp only [CollatzResearch.WordTrace]
  refine ⟨21371972268149109041316155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14247981512099406027544103 21371972268149109041316155)
  ·
    refine ⟨32057958402223663561974233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21371972268149109041316155 32057958402223663561974233)
    ·
      refine ⟨24043468801667747671480675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32057958402223663561974233 24043468801667747671480675)
      ·
        refine ⟨36065203202501621507221013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24043468801667747671480675 36065203202501621507221013)
        ·
          refine ⟨1690556400117263508150985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 36065203202501621507221013 1690556400117263508150985)
          ·
            refine ⟨1267917300087947631113239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1690556400117263508150985 1267917300087947631113239)
            ·
              refine ⟨1901875950131921446669859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1267917300087947631113239 1901875950131921446669859)
              ·
                refine ⟨2852813925197882170004789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1901875950131921446669859 2852813925197882170004789)
                ·
                  refine ⟨267451305487301453437949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2852813925197882170004789 267451305487301453437949)
                  ·
                    rfl

theorem cell20_585967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 1, 5].length) (baseStart_585967 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_585967 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_585967 prefixEnd_585967 := by exact prefixLift 585967
  have htrace : WordTrace (prefixWord ++ tailWord_585967) baseStart_585967 baseEnd_585967 := by
    simpa [prefixWord, tailWord_585967, baseEnd_585967] using wordTrace_append hprefix tailTrace_585967
  have hstable : (prefixWord ++ tailWord_585967).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585967).length < 2 ^ (prefixWord ++ tailWord_585967).sum := by decide
  have hdescent : baseEnd_585967 < baseStart_585967 := by decide
  rcases family_descends (prefixWord ++ tailWord_585967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_585970 : List Nat := [3, 2, 1, 3, 2, 1, 2, 4, 2]
def baseStart_585970 : Nat := 118140960795 + 585970 * 2 ^ 59
def prefixEnd_585970 : Nat := 4983230072969 + 3 ^ 40 * 585970 * 2
def baseEnd_585970 : Nat := 267452674769046776337937

theorem tailTrace_585970 : CollatzResearch.WordTrace tailWord_585970 prefixEnd_585970 267452674769046776337937 := by
  unfold tailWord_585970
  simp only [CollatzResearch.WordTrace]
  refine ⟨5343020421784560138418841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14248054458092160369116909 5343020421784560138418841)
  ·
    refine ⟨4007265316338420103814131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5343020421784560138418841 4007265316338420103814131)
    ·
      refine ⟨6010897974507630155721197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4007265316338420103814131 6010897974507630155721197)
      ·
        refine ⟨2254086740440361308395449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6010897974507630155721197 2254086740440361308395449)
        ·
          refine ⟨1690565055330270981296587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2254086740440361308395449 1690565055330270981296587)
          ·
            refine ⟨2535847582995406471944881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1690565055330270981296587 2535847582995406471944881)
            ·
              refine ⟨1901885687246554853958661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2535847582995406471944881 1901885687246554853958661)
              ·
                refine ⟨356603566358729035117249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1901885687246554853958661 356603566358729035117249)
                ·
                  refine ⟨267452674769046776337937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 356603566358729035117249 267452674769046776337937)
                  ·
                    rfl

theorem cell20_585970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 4, 2].length) (baseStart_585970 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_585970 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_585970 prefixEnd_585970 := by exact prefixLift 585970
  have htrace : WordTrace (prefixWord ++ tailWord_585970) baseStart_585970 baseEnd_585970 := by
    simpa [prefixWord, tailWord_585970, baseEnd_585970] using wordTrace_append hprefix tailTrace_585970
  have hstable : (prefixWord ++ tailWord_585970).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_585970).length < 2 ^ (prefixWord ++ tailWord_585970).sum := by decide
  have hdescent : baseEnd_585970 < baseStart_585970 := by decide
  rcases family_descends (prefixWord ++ tailWord_585970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586036 : List Nat := [2, 5, 1, 1, 1, 2, 1, 7]
def baseStart_586036 : Nat := 118140960795 + 586036 * 2 ^ 59
def prefixEnd_586036 : Nat := 4983230072969 + 3 ^ 40 * 586036 * 2
def baseEnd_586036 : Nat := 89160932989147960045889

theorem tailTrace_586036 : CollatzResearch.WordTrace tailWord_586036 prefixEnd_586036 89160932989147960045889 := by
  unfold tailWord_586036
  simp only [CollatzResearch.WordTrace]
  refine ⟨10687244452449566912788981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14249659269932755883718641 10687244452449566912788981)
  ·
    refine ⟨1001929167417146898073967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10687244452449566912788981 1001929167417146898073967)
    ·
      refine ⟨1502893751125720347110951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1001929167417146898073967 1502893751125720347110951)
      ·
        refine ⟨2254340626688580520666427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1502893751125720347110951 2254340626688580520666427)
        ·
          refine ⟨3381510940032870780999641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2254340626688580520666427 3381510940032870780999641)
          ·
            refine ⟨2536133205024653085749731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3381510940032870780999641 2536133205024653085749731)
            ·
              refine ⟨3804199807536979628624597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2536133205024653085749731 3804199807536979628624597)
              ·
                refine ⟨89160932989147960045889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3804199807536979628624597 89160932989147960045889)
                ·
                  rfl

theorem cell20_586036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 7].length) (baseStart_586036 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_586036 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_586036 prefixEnd_586036 := by exact prefixLift 586036
  have htrace : WordTrace (prefixWord ++ tailWord_586036) baseStart_586036 baseEnd_586036 := by
    simpa [prefixWord, tailWord_586036, baseEnd_586036] using wordTrace_append hprefix tailTrace_586036
  have hstable : (prefixWord ++ tailWord_586036).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586036).length < 2 ^ (prefixWord ++ tailWord_586036).sum := by decide
  have hdescent : baseEnd_586036 < baseStart_586036 := by decide
  rcases family_descends (prefixWord ++ tailWord_586036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586080 : List Nat := [2, 1, 1, 3, 6, 1, 2, 2, 2]
def baseStart_586080 : Nat := 118140960795 + 586080 * 2 ^ 59
def prefixEnd_586080 : Nat := 4983230072969 + 3 ^ 40 * 586080 * 2
def baseEnd_586080 : Nat := 267502881766375282670821

theorem tailTrace_586080 : CollatzResearch.WordTrace tailWord_586080 prefixEnd_586080 267502881766375282670821 := by
  unfold tailWord_586080
  simp only [CollatzResearch.WordTrace]
  refine ⟨10688046858369864670089847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14250729144493152893453129 10688046858369864670089847)
  ·
    refine ⟨16032070287554797005134771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10688046858369864670089847 16032070287554797005134771)
    ·
      refine ⟨24048105431332195507702157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16032070287554797005134771 24048105431332195507702157)
      ·
        refine ⟨9018039536749573315388309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24048105431332195507702157 9018039536749573315388309)
        ·
          refine ⟨422720603285136249158827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 9018039536749573315388309 422720603285136249158827)
          ·
            refine ⟨634080904927704373738241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 422720603285136249158827 634080904927704373738241)
            ·
              refine ⟨475560678695778280303681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 634080904927704373738241 475560678695778280303681)
              ·
                refine ⟨356670509021833710227761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 475560678695778280303681 356670509021833710227761)
                ·
                  refine ⟨267502881766375282670821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 356670509021833710227761 267502881766375282670821)
                  ·
                    rfl

theorem cell20_586080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 2, 2, 2].length) (baseStart_586080 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_586080 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_586080 prefixEnd_586080 := by exact prefixLift 586080
  have htrace : WordTrace (prefixWord ++ tailWord_586080) baseStart_586080 baseEnd_586080 := by
    simpa [prefixWord, tailWord_586080, baseEnd_586080] using wordTrace_append hprefix tailTrace_586080
  have hstable : (prefixWord ++ tailWord_586080).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586080).length < 2 ^ (prefixWord ++ tailWord_586080).sum := by decide
  have hdescent : baseEnd_586080 < baseStart_586080 := by decide
  rcases family_descends (prefixWord ++ tailWord_586080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586132 : List Nat := [2, 4, 2, 1, 4, 1, 1, 2, 3]
def baseStart_586132 : Nat := 118140960795 + 586132 * 2 ^ 59
def prefixEnd_586132 : Nat := 4983230072969 + 3 ^ 40 * 586132 * 2
def baseEnd_586132 : Nat := 267526615983294212937275

theorem tailTrace_586132 : CollatzResearch.WordTrace tailWord_586132 prefixEnd_586132 267526615983294212937275 := by
  unfold tailWord_586132
  simp only [CollatzResearch.WordTrace]
  refine ⟨10688995156275671110536325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14251993541700894814048433 10688995156275671110536325)
  ·
    refine ⟨2004186591801688333225561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10688995156275671110536325 2004186591801688333225561)
    ·
      refine ⟨1503139943851266249919171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2004186591801688333225561 1503139943851266249919171)
      ·
        refine ⟨2254709915776899374878757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1503139943851266249919171 2254709915776899374878757)
        ·
          refine ⟨422758109208168632789767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2254709915776899374878757 422758109208168632789767)
          ·
            refine ⟨634137163812252949184651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 422758109208168632789767 634137163812252949184651)
            ·
              refine ⟨951205745718379423776977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 634137163812252949184651 951205745718379423776977)
              ·
                refine ⟨713404309288784567832733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 951205745718379423776977 713404309288784567832733)
                ·
                  refine ⟨267526615983294212937275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 713404309288784567832733 267526615983294212937275)
                  ·
                    rfl

theorem cell20_586132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 1, 2, 3].length) (baseStart_586132 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_586132 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_586132 prefixEnd_586132 := by exact prefixLift 586132
  have htrace : WordTrace (prefixWord ++ tailWord_586132) baseStart_586132 baseEnd_586132 := by
    simpa [prefixWord, tailWord_586132, baseEnd_586132] using wordTrace_append hprefix tailTrace_586132
  have hstable : (prefixWord ++ tailWord_586132).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586132).length < 2 ^ (prefixWord ++ tailWord_586132).sum := by decide
  have hdescent : baseEnd_586132 < baseStart_586132 := by decide
  rcases family_descends (prefixWord ++ tailWord_586132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586136 : List Nat := [2, 1, 2, 5, 1, 1, 3, 2, 3]
def baseStart_586136 : Nat := 118140960795 + 586136 * 2 ^ 59
def prefixEnd_586136 : Nat := 4983230072969 + 3 ^ 40 * 586136 * 2
def baseEnd_586136 : Nat := 267528441692287976803925

theorem tailTrace_586136 : CollatzResearch.WordTrace tailWord_586136 prefixEnd_586136 267528441692287976803925 := by
  unfold tailWord_586136
  simp only [CollatzResearch.WordTrace]
  refine ⟨10689068102268425452109131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14252090803024567269478841 10689068102268425452109131)
  ·
    refine ⟨16033602153402638178163697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10689068102268425452109131 16033602153402638178163697)
    ·
      refine ⟨12025201615051978633622773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16033602153402638178163697 12025201615051978633622773)
      ·
        refine ⟨1127362651411122996902135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12025201615051978633622773 1127362651411122996902135)
        ·
          refine ⟨1691043977116684495353203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1127362651411122996902135 1691043977116684495353203)
          ·
            refine ⟨2536565965675026743029805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1691043977116684495353203 2536565965675026743029805)
            ·
              refine ⟨951212237128135028636177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2536565965675026743029805 951212237128135028636177)
              ·
                refine ⟨713409177846101271477133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 951212237128135028636177 713409177846101271477133)
                ·
                  refine ⟨267528441692287976803925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 713409177846101271477133 267528441692287976803925)
                  ·
                    rfl

theorem cell20_586136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3, 2, 3].length) (baseStart_586136 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_586136 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_586136 prefixEnd_586136 := by exact prefixLift 586136
  have htrace : WordTrace (prefixWord ++ tailWord_586136) baseStart_586136 baseEnd_586136 := by
    simpa [prefixWord, tailWord_586136, baseEnd_586136] using wordTrace_append hprefix tailTrace_586136
  have hstable : (prefixWord ++ tailWord_586136).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586136).length < 2 ^ (prefixWord ++ tailWord_586136).sum := by decide
  have hdescent : baseEnd_586136 < baseStart_586136 := by decide
  rcases family_descends (prefixWord ++ tailWord_586136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586143 : List Nat := [1, 1, 2, 5, 1, 1, 1, 6, 2]
def baseStart_586143 : Nat := 118140960795 + 586143 * 2 ^ 59
def prefixEnd_586143 : Nat := 4983230072969 + 3 ^ 40 * 586143 * 2
def baseEnd_586143 : Nat := 267531636683027063570563

theorem tailTrace_586143 : CollatzResearch.WordTrace tailWord_586143 prefixEnd_586143 267531636683027063570563 := by
  unfold tailWord_586143
  simp only [CollatzResearch.WordTrace]
  refine ⟨21378391515511491099723083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14252261010340994066482055 21378391515511491099723083)
  ·
    refine ⟨32067587273267236649584625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21378391515511491099723083 32067587273267236649584625)
    ·
      refine ⟨24050690454950427487188469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32067587273267236649584625 24050690454950427487188469)
      ·
        refine ⟨2254752230151602576923919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24050690454950427487188469 2254752230151602576923919)
        ·
          refine ⟨3382128345227403865385879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2254752230151602576923919 3382128345227403865385879)
          ·
            refine ⟨5073192517841105798078819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3382128345227403865385879 5073192517841105798078819)
            ·
              refine ⟨7609788776761658697118229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5073192517841105798078819 7609788776761658697118229)
              ·
                refine ⟨356708848910702751427417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7609788776761658697118229 356708848910702751427417)
                ·
                  refine ⟨267531636683027063570563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 356708848910702751427417 267531636683027063570563)
                  ·
                    rfl

theorem cell20_586143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 6, 2].length) (baseStart_586143 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_586143 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_586143 prefixEnd_586143 := by exact prefixLift 586143
  have htrace : WordTrace (prefixWord ++ tailWord_586143) baseStart_586143 baseEnd_586143 := by
    simpa [prefixWord, tailWord_586143, baseEnd_586143] using wordTrace_append hprefix tailTrace_586143
  have hstable : (prefixWord ++ tailWord_586143).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586143).length < 2 ^ (prefixWord ++ tailWord_586143).sum := by decide
  have hdescent : baseEnd_586143 < baseStart_586143 := by decide
  rcases family_descends (prefixWord ++ tailWord_586143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586185 : List Nat := [1, 2, 1, 1, 2, 1, 4, 2, 6]
def baseStart_586185 : Nat := 118140960795 + 586185 * 2 ^ 59
def prefixEnd_586185 : Nat := 4983230072969 + 3 ^ 40 * 586185 * 2
def baseEnd_586185 : Nat := 267550806627461584170391

theorem tailTrace_586185 : CollatzResearch.WordTrace tailWord_586185 prefixEnd_586185 267550806627461584170391 := by
  unfold tailWord_586185
  simp only [CollatzResearch.WordTrace]
  refine ⟨21379923381359332272752009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14253282254239554848501339 21379923381359332272752009)
  ·
    refine ⟨16034942536019499204564007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21379923381359332272752009 16034942536019499204564007)
    ·
      refine ⟨24052413804029248806846011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16034942536019499204564007 24052413804029248806846011)
      ·
        refine ⟨36078620706043873210269017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24052413804029248806846011 36078620706043873210269017)
        ·
          refine ⟨27058965529532904907701763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36078620706043873210269017 27058965529532904907701763)
          ·
            refine ⟨40588448294299357361552645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27058965529532904907701763 40588448294299357361552645)
            ·
              refine ⟨7610334055181129505291121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40588448294299357361552645 7610334055181129505291121)
              ·
                refine ⟨5707750541385847128968341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7610334055181129505291121 5707750541385847128968341)
                ·
                  refine ⟨267550806627461584170391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5707750541385847128968341 267550806627461584170391)
                  ·
                    rfl

theorem cell20_586185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 2, 6].length) (baseStart_586185 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_586185 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_586185 prefixEnd_586185 := by exact prefixLift 586185
  have htrace : WordTrace (prefixWord ++ tailWord_586185) baseStart_586185 baseEnd_586185 := by
    simpa [prefixWord, tailWord_586185, baseEnd_586185] using wordTrace_append hprefix tailTrace_586185
  have hstable : (prefixWord ++ tailWord_586185).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586185).length < 2 ^ (prefixWord ++ tailWord_586185).sum := by decide
  have hdescent : baseEnd_586185 < baseStart_586185 := by decide
  rcases family_descends (prefixWord ++ tailWord_586185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586188 : List Nat := [2, 2, 1, 4, 3, 2, 6]
def baseStart_586188 : Nat := 118140960795 + 586188 * 2 ^ 59
def prefixEnd_586188 : Nat := 4983230072969 + 3 ^ 40 * 586188 * 2
def baseEnd_586188 : Nat := 29728019545467434118931

theorem tailTrace_586188 : CollatzResearch.WordTrace tailWord_586188 prefixEnd_586188 29728019545467434118931 := by
  unfold tailWord_586188
  simp only [CollatzResearch.WordTrace]
  refine ⟨10690016400174231892555609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14253355200232309190074145 10690016400174231892555609)
  ·
    refine ⟨8017512300130673919416707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10690016400174231892555609 8017512300130673919416707)
    ·
      refine ⟨12026268450196010879125061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8017512300130673919416707 12026268450196010879125061)
      ·
        refine ⟨2254925334411752039835949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12026268450196010879125061 2254925334411752039835949)
        ·
          refine ⟨845597000404407014938481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2254925334411752039835949 845597000404407014938481)
          ·
            refine ⟨634197750303305261203861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 845597000404407014938481 634197750303305261203861)
            ·
              refine ⟨29728019545467434118931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 634197750303305261203861 29728019545467434118931)
              ·
                rfl

theorem cell20_586188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 6].length) (baseStart_586188 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_586188 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_586188 prefixEnd_586188 := by exact prefixLift 586188
  have htrace : WordTrace (prefixWord ++ tailWord_586188) baseStart_586188 baseEnd_586188 := by
    simpa [prefixWord, tailWord_586188, baseEnd_586188] using wordTrace_append hprefix tailTrace_586188
  have hstable : (prefixWord ++ tailWord_586188).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586188).length < 2 ^ (prefixWord ++ tailWord_586188).sum := by decide
  have hdescent : baseEnd_586188 < baseStart_586188 := by decide
  rcases family_descends (prefixWord ++ tailWord_586188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586194 : List Nat := [3, 2, 2, 4, 1, 1, 3, 2, 2]
def baseStart_586194 : Nat := 118140960795 + 586194 * 2 ^ 59
def prefixEnd_586194 : Nat := 4983230072969 + 3 ^ 40 * 586194 * 2
def baseEnd_586194 : Nat := 267554914472697552870355

theorem tailTrace_586194 : CollatzResearch.WordTrace tailWord_586194 prefixEnd_586194 267554914472697552870355 := by
  unfold tailWord_586194
  simp only [CollatzResearch.WordTrace]
  refine ⟨5345062909581681702457409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14253501092217817873219757 5345062909581681702457409)
  ·
    refine ⟨4008797182186261276843057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5345062909581681702457409 4008797182186261276843057)
    ·
      refine ⟨3006597886639695957632293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4008797182186261276843057 3006597886639695957632293)
      ·
        refine ⟨563737103744942992056055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3006597886639695957632293 563737103744942992056055)
        ·
          refine ⟨845605655617414488084083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 563737103744942992056055 845605655617414488084083)
          ·
            refine ⟨1268408483426121732126125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 845605655617414488084083 1268408483426121732126125)
            ·
              refine ⟨475653181284795649547297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1268408483426121732126125 475653181284795649547297)
              ·
                refine ⟨356739885963596737160473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 475653181284795649547297 356739885963596737160473)
                ·
                  refine ⟨267554914472697552870355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 356739885963596737160473 267554914472697552870355)
                  ·
                    rfl

theorem cell20_586194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 3, 2, 2].length) (baseStart_586194 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_586194 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_586194 prefixEnd_586194 := by exact prefixLift 586194
  have htrace : WordTrace (prefixWord ++ tailWord_586194) baseStart_586194 baseEnd_586194 := by
    simpa [prefixWord, tailWord_586194, baseEnd_586194] using wordTrace_append hprefix tailTrace_586194
  have hstable : (prefixWord ++ tailWord_586194).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586194).length < 2 ^ (prefixWord ++ tailWord_586194).sum := by decide
  have hdescent : baseEnd_586194 < baseStart_586194 := by decide
  rcases family_descends (prefixWord ++ tailWord_586194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586209 : List Nat := [1, 2, 3, 1, 2, 2, 4, 5]
def baseStart_586209 : Nat := 118140960795 + 586209 * 2 ^ 59
def prefixEnd_586209 : Nat := 4983230072969 + 3 ^ 40 * 586209 * 2
def baseEnd_586209 : Nat := 89187253627141389123431

theorem tailTrace_586209 : CollatzResearch.WordTrace tailWord_586209 prefixEnd_586209 89187253627141389123431 := by
  unfold tailWord_586209
  simp only [CollatzResearch.WordTrace]
  refine ⟨21380798733272384371625681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14253865822181589581083787 21380798733272384371625681)
  ·
    refine ⟨16035599049954288278719261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21380798733272384371625681 16035599049954288278719261)
    ·
      refine ⟨6013349643732858104519723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16035599049954288278719261 6013349643732858104519723)
      ·
        refine ⟨9020024465599287156779585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6013349643732858104519723 9020024465599287156779585)
        ·
          refine ⟨6765018349199465367584689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9020024465599287156779585 6765018349199465367584689)
          ·
            refine ⟨5073763761899599025688517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6765018349199465367584689 5073763761899599025688517)
            ·
              refine ⟨951330705356174817316597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5073763761899599025688517 951330705356174817316597)
              ·
                refine ⟨89187253627141389123431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 951330705356174817316597 89187253627141389123431)
                ·
                  rfl

theorem cell20_586209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4, 5].length) (baseStart_586209 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_586209 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_586209 prefixEnd_586209 := by exact prefixLift 586209
  have htrace : WordTrace (prefixWord ++ tailWord_586209) baseStart_586209 baseEnd_586209 := by
    simpa [prefixWord, tailWord_586209, baseEnd_586209] using wordTrace_append hprefix tailTrace_586209
  have hstable : (prefixWord ++ tailWord_586209).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586209).length < 2 ^ (prefixWord ++ tailWord_586209).sum := by decide
  have hdescent : baseEnd_586209 < baseStart_586209 := by decide
  rcases family_descends (prefixWord ++ tailWord_586209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586223 : List Nat := [1, 1, 2, 1, 4, 1, 1, 3, 6]
def baseStart_586223 : Nat := 118140960795 + 586223 * 2 ^ 59
def prefixEnd_586223 : Nat := 4983230072969 + 3 ^ 40 * 586223 * 2
def baseEnd_586223 : Nat := 267568150862902340903569

theorem tailTrace_586223 : CollatzResearch.WordTrace tailWord_586223 prefixEnd_586223 267568150862902340903569 := by
  unfold tailWord_586223
  simp only [CollatzResearch.WordTrace]
  refine ⟨21381309355221664762635323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14254206236814443175090215 21381309355221664762635323)
  ·
    refine ⟨32071964032832497143952985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21381309355221664762635323 32071964032832497143952985)
    ·
      refine ⟨24053973024624372857964739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32071964032832497143952985 24053973024624372857964739)
      ·
        refine ⟨36080959536936559286947109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24053973024624372857964739 36080959536936559286947109)
        ·
          refine ⟨6765179913175604866302583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36080959536936559286947109 6765179913175604866302583)
          ·
            refine ⟨10147769869763407299453875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6765179913175604866302583 10147769869763407299453875)
            ·
              refine ⟨15221654804645110949180813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10147769869763407299453875 15221654804645110949180813)
              ·
                refine ⟨5708120551741916605942805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15221654804645110949180813 5708120551741916605942805)
                ·
                  refine ⟨267568150862902340903569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5708120551741916605942805 267568150862902340903569)
                  ·
                    rfl

theorem cell20_586223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 3, 6].length) (baseStart_586223 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_586223 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_586223 prefixEnd_586223 := by exact prefixLift 586223
  have htrace : WordTrace (prefixWord ++ tailWord_586223) baseStart_586223 baseEnd_586223 := by
    simpa [prefixWord, tailWord_586223, baseEnd_586223] using wordTrace_append hprefix tailTrace_586223
  have hstable : (prefixWord ++ tailWord_586223).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586223).length < 2 ^ (prefixWord ++ tailWord_586223).sum := by decide
  have hdescent : baseEnd_586223 < baseStart_586223 := by decide
  rcases family_descends (prefixWord ++ tailWord_586223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586246 : List Nat := [6, 2, 1, 1, 1, 1, 1, 4, 3]
def baseStart_586246 : Nat := 118140960795 + 586246 * 2 ^ 59
def prefixEnd_586246 : Nat := 4983230072969 + 3 ^ 40 * 586246 * 2
def baseEnd_586246 : Nat := 267578648689616483136809

theorem tailTrace_586246 : CollatzResearch.WordTrace tailWord_586246 prefixEnd_586246 267578648689616483136809 := by
  unfold tailWord_586246
  simp only [CollatzResearch.WordTrace]
  refine ⟨668192132316823115335081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 14254765489425559793815061 668192132316823115335081)
  ·
    refine ⟨501144099237617336501311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 668192132316823115335081 501144099237617336501311)
    ·
      refine ⟨751716148856426004751967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 501144099237617336501311 751716148856426004751967)
      ·
        refine ⟨1127574223284639007127951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 751716148856426004751967 1127574223284639007127951)
        ·
          refine ⟨1691361334926958510691927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1127574223284639007127951 1691361334926958510691927)
          ·
            refine ⟨2537042002390437766037891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1691361334926958510691927 2537042002390437766037891)
            ·
              refine ⟨3805563003585656649056837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2537042002390437766037891 3805563003585656649056837)
              ·
                refine ⟨713543063172310621698157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3805563003585656649056837 713543063172310621698157)
                ·
                  refine ⟨267578648689616483136809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 713543063172310621698157 267578648689616483136809)
                  ·
                    rfl

theorem cell20_586246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_586246 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_586246 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_586246 prefixEnd_586246 := by exact prefixLift 586246
  have htrace : WordTrace (prefixWord ++ tailWord_586246) baseStart_586246 baseEnd_586246 := by
    simpa [prefixWord, tailWord_586246, baseEnd_586246] using wordTrace_append hprefix tailTrace_586246
  have hstable : (prefixWord ++ tailWord_586246).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586246).length < 2 ^ (prefixWord ++ tailWord_586246).sum := by decide
  have hdescent : baseEnd_586246 < baseStart_586246 := by decide
  rcases family_descends (prefixWord ++ tailWord_586246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586247 : List Nat := [1, 1, 4, 3, 3, 8]
def baseStart_586247 : Nat := 118140960795 + 586247 * 2 ^ 59
def prefixEnd_586247 : Nat := 4983230072969 + 3 ^ 40 * 586247 * 2
def baseEnd_586247 : Nat := 9910337226550552744573

theorem tailTrace_586247 : CollatzResearch.WordTrace tailWord_586247 prefixEnd_586247 9910337226550552744573 := by
  unfold tailWord_586247
  simp only [CollatzResearch.WordTrace]
  refine ⟨21382184707134716861508995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14254789804756477907672663 21382184707134716861508995)
  ·
    refine ⟨32073277060702075292263493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21382184707134716861508995 32073277060702075292263493)
    ·
      refine ⟨6013739448881639117299405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32073277060702075292263493 6013739448881639117299405)
      ·
        refine ⟨2255152293330614668987277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6013739448881639117299405 2255152293330614668987277)
        ·
          refine ⟨845682109998980500870229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2255152293330614668987277 845682109998980500870229)
          ·
            refine ⟨9910337226550552744573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 845682109998980500870229 9910337226550552744573)
            ·
              rfl

theorem cell20_586247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 8].length) (baseStart_586247 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_586247 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_586247 prefixEnd_586247 := by exact prefixLift 586247
  have htrace : WordTrace (prefixWord ++ tailWord_586247) baseStart_586247 baseEnd_586247 := by
    simpa [prefixWord, tailWord_586247, baseEnd_586247] using wordTrace_append hprefix tailTrace_586247
  have hstable : (prefixWord ++ tailWord_586247).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586247).length < 2 ^ (prefixWord ++ tailWord_586247).sum := by decide
  have hdescent : baseEnd_586247 < baseStart_586247 := by decide
  rcases family_descends (prefixWord ++ tailWord_586247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586264 : List Nat := [2, 1, 2, 3, 3, 3, 1, 5]
def baseStart_586264 : Nat := 118140960795 + 586264 * 2 ^ 59
def prefixEnd_586264 : Nat := 4983230072969 + 3 ^ 40 * 586264 * 2
def baseEnd_586264 : Nat := 89195621460029473512245

theorem tailTrace_586264 : CollatzResearch.WordTrace tailWord_586264 prefixEnd_586264 89195621460029473512245 := by
  unfold tailWord_586264
  simp only [CollatzResearch.WordTrace]
  refine ⟨10691402374036564382438923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14255203165382085843251897 10691402374036564382438923)
  ·
    refine ⟨16037103561054846573658385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10691402374036564382438923 16037103561054846573658385)
    ·
      refine ⟨12027827670791134930243789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16037103561054846573658385 12027827670791134930243789)
      ·
        refine ⟨4510435376546675598841421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12027827670791134930243789 4510435376546675598841421)
        ·
          refine ⟨1691413266205003349565533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4510435376546675598841421 1691413266205003349565533)
          ·
            refine ⟨634279974826876256087075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1691413266205003349565533 634279974826876256087075)
            ·
              refine ⟨951419962240314384130613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 634279974826876256087075 951419962240314384130613)
              ·
                refine ⟨89195621460029473512245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 951419962240314384130613 89195621460029473512245)
                ·
                  rfl

theorem cell20_586264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 1, 5].length) (baseStart_586264 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_586264 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_586264 prefixEnd_586264 := by exact prefixLift 586264
  have htrace : WordTrace (prefixWord ++ tailWord_586264) baseStart_586264 baseEnd_586264 := by
    simpa [prefixWord, tailWord_586264, baseEnd_586264] using wordTrace_append hprefix tailTrace_586264
  have hstable : (prefixWord ++ tailWord_586264).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586264).length < 2 ^ (prefixWord ++ tailWord_586264).sum := by decide
  have hdescent : baseEnd_586264 < baseStart_586264 := by decide
  rcases family_descends (prefixWord ++ tailWord_586264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586295 : List Nat := [1, 1, 3, 1, 2, 3, 4, 3, 2]
def baseStart_586295 : Nat := 118140960795 + 586295 * 2 ^ 59
def prefixEnd_586295 : Nat := 4983230072969 + 3 ^ 40 * 586295 * 2
def baseEnd_586295 : Nat := 267601013624790090503275

theorem tailTrace_586295 : CollatzResearch.WordTrace tailWord_586295 prefixEnd_586295 267601013624790090503275 := by
  unfold tailWord_586295
  simp only [CollatzResearch.WordTrace]
  refine ⟨21383935410960821059256339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14255956940640547372837559 21383935410960821059256339)
  ·
    refine ⟨32075903116441231588884509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21383935410960821059256339 32075903116441231588884509)
    ·
      refine ⟨12028463668665461845831691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32075903116441231588884509 12028463668665461845831691)
      ·
        refine ⟨18042695502998192768747537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12028463668665461845831691 18042695502998192768747537)
        ·
          refine ⟨13532021627248644576560653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18042695502998192768747537 13532021627248644576560653)
          ·
            refine ⟨5074508110218241716210245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13532021627248644576560653 5074508110218241716210245)
            ·
              refine ⟨951470270665920321789421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5074508110218241716210245 951470270665920321789421)
              ·
                refine ⟨356801351499720120671033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 951470270665920321789421 356801351499720120671033)
                ·
                  refine ⟨267601013624790090503275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 356801351499720120671033 267601013624790090503275)
                  ·
                    rfl

theorem cell20_586295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4, 3, 2].length) (baseStart_586295 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_586295 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_586295 prefixEnd_586295 := by exact prefixLift 586295
  have htrace : WordTrace (prefixWord ++ tailWord_586295) baseStart_586295 baseEnd_586295 := by
    simpa [prefixWord, tailWord_586295, baseEnd_586295] using wordTrace_append hprefix tailTrace_586295
  have hstable : (prefixWord ++ tailWord_586295).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586295).length < 2 ^ (prefixWord ++ tailWord_586295).sum := by decide
  have hdescent : baseEnd_586295 < baseStart_586295 := by decide
  rcases family_descends (prefixWord ++ tailWord_586295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586309 : List Nat := [1, 3, 1, 1, 1, 5, 3, 2, 3]
def baseStart_586309 : Nat := 118140960795 + 586309 * 2 ^ 59
def prefixEnd_586309 : Nat := 4983230072969 + 3 ^ 40 * 586309 * 2
def baseEnd_586309 : Nat := 267607403606268264036551

theorem tailTrace_586309 : CollatzResearch.WordTrace tailWord_586309 prefixEnd_586309 267607403606268264036551 := by
  unfold tailWord_586309
  simp only [CollatzResearch.WordTrace]
  refine ⟨21384446032910101450265981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14256297355273400966843987 21384446032910101450265981)
  ·
    refine ⟨8019167262341288043849743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21384446032910101450265981 8019167262341288043849743)
    ·
      refine ⟨12028750893511932065774615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8019167262341288043849743 12028750893511932065774615)
      ·
        refine ⟨18043126340267898098661923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12028750893511932065774615 18043126340267898098661923)
        ·
          refine ⟨27064689510401847147992885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18043126340267898098661923 27064689510401847147992885)
          ·
            refine ⟨2537314641600173170124333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27064689510401847147992885 2537314641600173170124333)
            ·
              refine ⟨951492990600064938796625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2537314641600173170124333 951492990600064938796625)
              ·
                refine ⟨713619742950048704097469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 951492990600064938796625 713619742950048704097469)
                ·
                  refine ⟨267607403606268264036551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 713619742950048704097469 267607403606268264036551)
                  ·
                    rfl

theorem cell20_586309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3, 2, 3].length) (baseStart_586309 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_586309 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_586309 prefixEnd_586309 := by exact prefixLift 586309
  have htrace : WordTrace (prefixWord ++ tailWord_586309) baseStart_586309 baseEnd_586309 := by
    simpa [prefixWord, tailWord_586309, baseEnd_586309] using wordTrace_append hprefix tailTrace_586309
  have hstable : (prefixWord ++ tailWord_586309).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586309).length < 2 ^ (prefixWord ++ tailWord_586309).sum := by decide
  have hdescent : baseEnd_586309 < baseStart_586309 := by decide
  rcases family_descends (prefixWord ++ tailWord_586309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586316 : List Nat := [2, 2, 1, 3, 1, 2, 4, 1, 4]
def baseStart_586316 : Nat := 118140960795 + 586316 * 2 ^ 59
def prefixEnd_586316 : Nat := 4983230072969 + 3 ^ 40 * 586316 * 2
def baseEnd_586316 : Nat := 267610598597007350803189

theorem tailTrace_586316 : CollatzResearch.WordTrace tailWord_586316 prefixEnd_586316 267610598597007350803189 := by
  unfold tailWord_586316
  simp only [CollatzResearch.WordTrace]
  refine ⟨10692350671942370822885401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14256467562589827763847201 10692350671942370822885401)
  ·
    refine ⟨8019263003956778117164051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10692350671942370822885401 8019263003956778117164051)
    ·
      refine ⟨12028894505935167175746077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8019263003956778117164051 12028894505935167175746077)
      ·
        refine ⟨4510835439725687690904779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12028894505935167175746077 4510835439725687690904779)
        ·
          refine ⟨6766253159588531536357169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4510835439725687690904779 6766253159588531536357169)
          ·
            refine ⟨5074689869691398652267877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6766253159588531536357169 5074689869691398652267877)
            ·
              refine ⟨951504350567137247300227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5074689869691398652267877 951504350567137247300227)
              ·
                refine ⟨1427256525850705870950341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 951504350567137247300227 1427256525850705870950341)
                ·
                  refine ⟨267610598597007350803189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1427256525850705870950341 267610598597007350803189)
                  ·
                    rfl

theorem cell20_586316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4, 1, 4].length) (baseStart_586316 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_586316 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_586316 prefixEnd_586316 := by exact prefixLift 586316
  have htrace : WordTrace (prefixWord ++ tailWord_586316) baseStart_586316 baseEnd_586316 := by
    simpa [prefixWord, tailWord_586316, baseEnd_586316] using wordTrace_append hprefix tailTrace_586316
  have hstable : (prefixWord ++ tailWord_586316).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586316).length < 2 ^ (prefixWord ++ tailWord_586316).sum := by decide
  have hdescent : baseEnd_586316 < baseStart_586316 := by decide
  rcases family_descends (prefixWord ++ tailWord_586316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586350 : List Nat := [4, 1, 2, 2, 2, 1, 3, 3, 2]
def baseStart_586350 : Nat := 118140960795 + 586350 * 2 ^ 59
def prefixEnd_586350 : Nat := 4983230072969 + 3 ^ 40 * 586350 * 2
def baseEnd_586350 : Nat := 267626117123454343669717

theorem tailTrace_586350 : CollatzResearch.WordTrace tailWord_586350 prefixEnd_586350 267626117123454343669717 := by
  unfold tailWord_586350
  simp only [CollatzResearch.WordTrace]
  refine ⟨2673242678220195681563563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14257294283841043635005669 2673242678220195681563563)
  ·
    refine ⟨4009864017330293522345345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2673242678220195681563563 4009864017330293522345345)
    ·
      refine ⟨3007398012997720141759009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4009864017330293522345345 3007398012997720141759009)
      ·
        refine ⟨2255548509748290106319257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3007398012997720141759009 2255548509748290106319257)
        ·
          refine ⟨1691661382311217579739443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2255548509748290106319257 1691661382311217579739443)
          ·
            refine ⟨2537492073466826369609165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1691661382311217579739443 2537492073466826369609165)
            ·
              refine ⟨951559527550059888603437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2537492073466826369609165 951559527550059888603437)
              ·
                refine ⟨356834822831272458226289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 951559527550059888603437 356834822831272458226289)
                ·
                  refine ⟨267626117123454343669717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 356834822831272458226289 267626117123454343669717)
                  ·
                    rfl

theorem cell20_586350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3, 3, 2].length) (baseStart_586350 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_586350 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_586350 prefixEnd_586350 := by exact prefixLift 586350
  have htrace : WordTrace (prefixWord ++ tailWord_586350) baseStart_586350 baseEnd_586350 := by
    simpa [prefixWord, tailWord_586350, baseEnd_586350] using wordTrace_append hprefix tailTrace_586350
  have hstable : (prefixWord ++ tailWord_586350).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586350).length < 2 ^ (prefixWord ++ tailWord_586350).sum := by decide
  have hdescent : baseEnd_586350 < baseStart_586350 := by decide
  rcases family_descends (prefixWord ++ tailWord_586350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586357 : List Nat := [1, 3, 4, 2, 3, 1, 6]
def baseStart_586357 : Nat := 118140960795 + 586357 * 2 ^ 59
def prefixEnd_586357 : Nat := 4983230072969 + 3 ^ 40 * 586357 * 2
def baseEnd_586357 : Nat := 29736590234910381159595

theorem tailTrace_586357 : CollatzResearch.WordTrace tailWord_586357 prefixEnd_586357 29736590234910381159595 := by
  unfold tailWord_586357
  simp only [CollatzResearch.WordTrace]
  refine ⟨21386196736736205648013325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14257464491157470432008883 21386196736736205648013325)
  ·
    refine ⟨8019823776276077118004997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21386196736736205648013325 8019823776276077118004997)
    ·
      refine ⟨1503716958051764459625937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8019823776276077118004997 1503716958051764459625937)
      ·
        refine ⟨1127787718538823344719453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1503716958051764459625937 1127787718538823344719453)
        ·
          refine ⟨422920394452058754269795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1127787718538823344719453 422920394452058754269795)
          ·
            refine ⟨634380591678088131404693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 422920394452058754269795 634380591678088131404693)
            ·
              refine ⟨29736590234910381159595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 634380591678088131404693 29736590234910381159595)
              ·
                rfl

theorem cell20_586357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 6].length) (baseStart_586357 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_586357 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_586357 prefixEnd_586357 := by exact prefixLift 586357
  have htrace : WordTrace (prefixWord ++ tailWord_586357) baseStart_586357 baseEnd_586357 := by
    simpa [prefixWord, tailWord_586357, baseEnd_586357] using wordTrace_append hprefix tailTrace_586357
  have hstable : (prefixWord ++ tailWord_586357).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586357).length < 2 ^ (prefixWord ++ tailWord_586357).sum := by decide
  have hdescent : baseEnd_586357 < baseStart_586357 := by decide
  rcases family_descends (prefixWord ++ tailWord_586357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586361 : List Nat := [1, 2, 1, 3, 3, 4, 6]
def baseStart_586361 : Nat := 118140960795 + 586361 * 2 ^ 59
def prefixEnd_586361 : Nat := 4983230072969 + 3 ^ 40 * 586361 * 2
def baseEnd_586361 : Nat := 29736793091465243811445

theorem tailTrace_586361 : CollatzResearch.WordTrace tailWord_586361 prefixEnd_586361 29736793091465243811445 := by
  unfold tailWord_586361
  simp only [CollatzResearch.WordTrace]
  refine ⟨21386342628721714331158937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14257561752481142887439291 21386342628721714331158937)
  ·
    refine ⟨16039756971541285748369203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21386342628721714331158937 16039756971541285748369203)
    ·
      refine ⟨24059635457311928622553805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16039756971541285748369203 24059635457311928622553805)
      ·
        refine ⟨9022363296491973233457677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24059635457311928622553805 9022363296491973233457677)
        ·
          refine ⟨3383386236184489962546629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9022363296491973233457677 3383386236184489962546629)
          ·
            refine ⟨634384919284591867977493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3383386236184489962546629 634384919284591867977493)
            ·
              refine ⟨29736793091465243811445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 634384919284591867977493 29736793091465243811445)
              ·
                rfl

theorem cell20_586361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 6].length) (baseStart_586361 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_586361 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_586361 prefixEnd_586361 := by exact prefixLift 586361
  have htrace : WordTrace (prefixWord ++ tailWord_586361) baseStart_586361 baseEnd_586361 := by
    simpa [prefixWord, tailWord_586361, baseEnd_586361] using wordTrace_append hprefix tailTrace_586361
  have hstable : (prefixWord ++ tailWord_586361).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586361).length < 2 ^ (prefixWord ++ tailWord_586361).sum := by decide
  have hdescent : baseEnd_586361 < baseStart_586361 := by decide
  rcases family_descends (prefixWord ++ tailWord_586361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586368 : List Nat := [2, 1, 1, 2, 1, 5, 2, 1, 5]
def baseStart_586368 : Nat := 118140960795 + 586368 * 2 ^ 59
def prefixEnd_586368 : Nat := 4983230072969 + 3 ^ 40 * 586368 * 2
def baseEnd_586368 : Nat := 267634332813926281069643

theorem tailTrace_586368 : CollatzResearch.WordTrace tailWord_586368 prefixEnd_586368 267634332813926281069643 := by
  unfold tailWord_586368
  simp only [CollatzResearch.WordTrace]
  refine ⟨10693298969848177263331879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14257731959797569684442505 10693298969848177263331879)
  ·
    refine ⟨16039948454772265894997819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10693298969848177263331879 16039948454772265894997819)
    ·
      refine ⟨24059922682158398842496729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16039948454772265894997819 24059922682158398842496729)
      ·
        refine ⟨18044942011618799131872547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24059922682158398842496729 18044942011618799131872547)
        ·
          refine ⟨27067413017428198697808821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18044942011618799131872547 27067413017428198697808821)
          ·
            refine ⟨2537569970383893627919577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27067413017428198697808821 2537569970383893627919577)
            ·
              refine ⟨1903177477787920220939683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2537569970383893627919577 1903177477787920220939683)
              ·
                refine ⟨2854766216681880331409525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1903177477787920220939683 2854766216681880331409525)
                ·
                  refine ⟨267634332813926281069643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2854766216681880331409525 267634332813926281069643)
                  ·
                    rfl

theorem cell20_586368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 1, 5].length) (baseStart_586368 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_586368 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_586368 prefixEnd_586368 := by exact prefixLift 586368
  have htrace : WordTrace (prefixWord ++ tailWord_586368) baseStart_586368 baseEnd_586368 := by
    simpa [prefixWord, tailWord_586368, baseEnd_586368] using wordTrace_append hprefix tailTrace_586368
  have hstable : (prefixWord ++ tailWord_586368).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586368).length < 2 ^ (prefixWord ++ tailWord_586368).sum := by decide
  have hdescent : baseEnd_586368 < baseStart_586368 := by decide
  rcases family_descends (prefixWord ++ tailWord_586368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586378 : List Nat := [3, 1, 2, 3, 3, 1, 2, 5]
def baseStart_586378 : Nat := 118140960795 + 586378 * 2 ^ 59
def prefixEnd_586378 : Nat := 4983230072969 + 3 ^ 40 * 586378 * 2
def baseEnd_586378 : Nat := 89212965695470230245423

theorem tailTrace_586378 : CollatzResearch.WordTrace tailWord_586378 prefixEnd_586378 89212965695470230245423 := by
  unfold tailWord_586378
  simp only [CollatzResearch.WordTrace]
  refine ⟨5346740667415031558631947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14257975113106750823018525 5346740667415031558631947)
  ·
    refine ⟨8020111001122547337947921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5346740667415031558631947 8020111001122547337947921)
    ·
      refine ⟨6015083250841910503460941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8020111001122547337947921 6015083250841910503460941)
      ·
        refine ⟨2255656219065716438797853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6015083250841910503460941 2255656219065716438797853)
        ·
          refine ⟨845871082149643664549195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2255656219065716438797853 845871082149643664549195)
          ·
            refine ⟨1268806623224465496823793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 845871082149643664549195 1268806623224465496823793)
            ·
              refine ⟨951604967418349122617845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1268806623224465496823793 951604967418349122617845)
              ·
                refine ⟨89212965695470230245423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 951604967418349122617845 89212965695470230245423)
                ·
                  rfl

theorem cell20_586378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 2, 5].length) (baseStart_586378 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_586378 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_586378 prefixEnd_586378 := by exact prefixLift 586378
  have htrace : WordTrace (prefixWord ++ tailWord_586378) baseStart_586378 baseEnd_586378 := by
    simpa [prefixWord, tailWord_586378, baseEnd_586378] using wordTrace_append hprefix tailTrace_586378
  have hstable : (prefixWord ++ tailWord_586378).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586378).length < 2 ^ (prefixWord ++ tailWord_586378).sum := by decide
  have hdescent : baseEnd_586378 < baseStart_586378 := by decide
  rcases family_descends (prefixWord ++ tailWord_586378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586430 : List Nat := [4, 2, 1, 1, 2, 1, 2, 3, 4]
def baseStart_586430 : Nat := 118140960795 + 586430 * 2 ^ 59
def prefixEnd_586430 : Nat := 4983230072969 + 3 ^ 40 * 586430 * 2
def baseEnd_586430 : Nat := 267662631303329621002723

theorem tailTrace_586430 : CollatzResearch.WordTrace tailWord_586430 prefixEnd_586430 267662631303329621002723 := by
  unfold tailWord_586430
  simp only [CollatzResearch.WordTrace]
  refine ⟨2673607408183967389427593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14259239510314492743613829 2673607408183967389427593)
  ·
    refine ⟨2005205556137975542070695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2673607408183967389427593 2005205556137975542070695)
    ·
      refine ⟨3007808334206963313106043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2005205556137975542070695 3007808334206963313106043)
      ·
        refine ⟨4511712501310444969659065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3007808334206963313106043 4511712501310444969659065)
        ·
          refine ⟨3383784375982833727244299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4511712501310444969659065 3383784375982833727244299)
          ·
            refine ⟨5075676563974250590866449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3383784375982833727244299 5075676563974250590866449)
            ·
              refine ⟨3806757422980687943149837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5075676563974250590866449 3806757422980687943149837)
              ·
                refine ⟨1427534033617757978681189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3806757422980687943149837 1427534033617757978681189)
                ·
                  refine ⟨267662631303329621002723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1427534033617757978681189 267662631303329621002723)
                  ·
                    rfl

theorem cell20_586430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_586430 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_586430 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_586430 prefixEnd_586430 := by exact prefixLift 586430
  have htrace : WordTrace (prefixWord ++ tailWord_586430) baseStart_586430 baseEnd_586430 := by
    simpa [prefixWord, tailWord_586430, baseEnd_586430] using wordTrace_append hprefix tailTrace_586430
  have hstable : (prefixWord ++ tailWord_586430).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586430).length < 2 ^ (prefixWord ++ tailWord_586430).sum := by decide
  have hdescent : baseEnd_586430 < baseStart_586430 := by decide
  rcases family_descends (prefixWord ++ tailWord_586430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586478 : List Nat := [4, 1, 2, 1, 1, 5, 1, 2, 3]
def baseStart_586478 : Nat := 118140960795 + 586478 * 2 ^ 59
def prefixEnd_586478 : Nat := 4983230072969 + 3 ^ 40 * 586478 * 2
def baseEnd_586478 : Nat := 267684539811254787402527

theorem tailTrace_586478 : CollatzResearch.WordTrace tailWord_586478 prefixEnd_586478 267684539811254787402527 := by
  unfold tailWord_586478
  simp only [CollatzResearch.WordTrace]
  refine ⟨2673826246162230414146011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14260406646198562208778725 2673826246162230414146011)
  ·
    refine ⟨4010739369243345621219017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2673826246162230414146011 4010739369243345621219017)
    ·
      refine ⟨3008054526932509215914263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4010739369243345621219017 3008054526932509215914263)
      ·
        refine ⟨4512081790398763823871395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3008054526932509215914263 4512081790398763823871395)
        ·
          refine ⟨6768122685598145735807093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4512081790398763823871395 6768122685598145735807093)
          ·
            refine ⟨634511501774826162731915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6768122685598145735807093 634511501774826162731915)
            ·
              refine ⟨951767252662239244097873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 634511501774826162731915 951767252662239244097873)
              ·
                refine ⟨713825439496679433073405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 951767252662239244097873 713825439496679433073405)
                ·
                  refine ⟨267684539811254787402527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 713825439496679433073405 267684539811254787402527)
                  ·
                    rfl

theorem cell20_586478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 1, 2, 3].length) (baseStart_586478 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_586478 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_586478 prefixEnd_586478 := by exact prefixLift 586478
  have htrace : WordTrace (prefixWord ++ tailWord_586478) baseStart_586478 baseEnd_586478 := by
    simpa [prefixWord, tailWord_586478, baseEnd_586478] using wordTrace_append hprefix tailTrace_586478
  have hstable : (prefixWord ++ tailWord_586478).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586478).length < 2 ^ (prefixWord ++ tailWord_586478).sum := by decide
  have hdescent : baseEnd_586478 < baseStart_586478 := by decide
  rcases family_descends (prefixWord ++ tailWord_586478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586513 : List Nat := [1, 2, 2, 1, 1, 3, 6, 4]
def baseStart_586513 : Nat := 118140960795 + 586513 * 2 ^ 59
def prefixEnd_586513 : Nat := 4983230072969 + 3 ^ 40 * 586513 * 2
def baseEnd_586513 : Nat := 89233504921650073745239

theorem tailTrace_586513 : CollatzResearch.WordTrace tailWord_586513 prefixEnd_586513 89233504921650073745239 := by
  unfold tailWord_586513
  simp only [CollatzResearch.WordTrace]
  refine ⟨21391886524171044290692193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14261257682780696193794795 21391886524171044290692193)
  ·
    refine ⟨16043914893128283218019145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21391886524171044290692193 16043914893128283218019145)
    ·
      refine ⟨12032936169846212413514359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16043914893128283218019145 12032936169846212413514359)
      ·
        refine ⟨18049404254769318620271539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12032936169846212413514359 18049404254769318620271539)
        ·
          refine ⟨27074106382153977930407309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18049404254769318620271539 27074106382153977930407309)
          ·
            refine ⟨10152789893307741723902741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27074106382153977930407309 10152789893307741723902741)
            ·
              refine ⟨475912026248800393307941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 10152789893307741723902741 475912026248800393307941)
              ·
                refine ⟨89233504921650073745239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 475912026248800393307941 89233504921650073745239)
                ·
                  rfl

theorem cell20_586513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 6, 4].length) (baseStart_586513 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_586513 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_586513 prefixEnd_586513 := by exact prefixLift 586513
  have htrace : WordTrace (prefixWord ++ tailWord_586513) baseStart_586513 baseEnd_586513 := by
    simpa [prefixWord, tailWord_586513, baseEnd_586513] using wordTrace_append hprefix tailTrace_586513
  have hstable : (prefixWord ++ tailWord_586513).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586513).length < 2 ^ (prefixWord ++ tailWord_586513).sum := by decide
  have hdescent : baseEnd_586513 < baseStart_586513 := by decide
  rcases family_descends (prefixWord ++ tailWord_586513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586519 : List Nat := [1, 1, 3, 4, 4, 1, 1, 3, 2]
def baseStart_586519 : Nat := 118140960795 + 586519 * 2 ^ 59
def prefixEnd_586519 : Nat := 4983230072969 + 3 ^ 40 * 586519 * 2
def baseEnd_586519 : Nat := 267703253328440867035693

theorem tailTrace_586519 : CollatzResearch.WordTrace tailWord_586519 prefixEnd_586519 267703253328440867035693 := by
  unfold tailWord_586519
  simp only [CollatzResearch.WordTrace]
  refine ⟨21392105362149307315410611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14261403574766204876940407 21392105362149307315410611)
  ·
    refine ⟨32088158043223960973115917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21392105362149307315410611 32088158043223960973115917)
    ·
      refine ⟨12033059266208985364918469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32088158043223960973115917 12033059266208985364918469)
      ·
        refine ⟨2256198612414184755922213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12033059266208985364918469 2256198612414184755922213)
        ·
          refine ⟨423037239827659641735415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2256198612414184755922213 423037239827659641735415)
          ·
            refine ⟨634555859741489462603123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 423037239827659641735415 634555859741489462603123)
            ·
              refine ⟨951833789612234193904685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 634555859741489462603123 951833789612234193904685)
              ·
                refine ⟨356937671104587822714257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 951833789612234193904685 356937671104587822714257)
                ·
                  refine ⟨267703253328440867035693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 356937671104587822714257 267703253328440867035693)
                  ·
                    rfl

theorem cell20_586519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 1, 3, 2].length) (baseStart_586519 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_586519 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_586519 prefixEnd_586519 := by exact prefixLift 586519
  have htrace : WordTrace (prefixWord ++ tailWord_586519) baseStart_586519 baseEnd_586519 := by
    simpa [prefixWord, tailWord_586519, baseEnd_586519] using wordTrace_append hprefix tailTrace_586519
  have hstable : (prefixWord ++ tailWord_586519).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586519).length < 2 ^ (prefixWord ++ tailWord_586519).sum := by decide
  have hdescent : baseEnd_586519 < baseStart_586519 := by decide
  rcases family_descends (prefixWord ++ tailWord_586519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586544 : List Nat := [2, 1, 1, 1, 2, 2, 1, 8, 2]
def baseStart_586544 : Nat := 118140960795 + 586544 * 2 ^ 59
def prefixEnd_586544 : Nat := 4983230072969 + 3 ^ 40 * 586544 * 2
def baseEnd_586544 : Nat := 267714664009651891202257

theorem tailTrace_586544 : CollatzResearch.WordTrace tailWord_586544 prefixEnd_586544 267714664009651891202257 := by
  unfold tailWord_586544
  simp only [CollatzResearch.WordTrace]
  refine ⟨10696508593529368292535343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14262011458039157723380457 10696508593529368292535343)
  ·
    refine ⟨16044762890294052438803015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10696508593529368292535343 16044762890294052438803015)
    ·
      refine ⟨24067144335441078658204523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16044762890294052438803015 24067144335441078658204523)
      ·
        refine ⟨36100716503161617987306785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24067144335441078658204523 36100716503161617987306785)
        ·
          refine ⟨27075537377371213490480089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36100716503161617987306785 27075537377371213490480089)
          ·
            refine ⟨20306653033028410117860067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27075537377371213490480089 20306653033028410117860067)
            ·
              refine ⟨30459979549542615176790101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20306653033028410117860067 30459979549542615176790101)
              ·
                refine ⟨356952885346202521603009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 30459979549542615176790101 356952885346202521603009)
                ·
                  refine ⟨267714664009651891202257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 356952885346202521603009 267714664009651891202257)
                  ·
                    rfl

theorem cell20_586544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 8, 2].length) (baseStart_586544 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_586544 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_586544 prefixEnd_586544 := by exact prefixLift 586544
  have htrace : WordTrace (prefixWord ++ tailWord_586544) baseStart_586544 baseEnd_586544 := by
    simpa [prefixWord, tailWord_586544, baseEnd_586544] using wordTrace_append hprefix tailTrace_586544
  have hstable : (prefixWord ++ tailWord_586544).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586544).length < 2 ^ (prefixWord ++ tailWord_586544).sum := by decide
  have hdescent : baseEnd_586544 < baseStart_586544 := by decide
  rcases family_descends (prefixWord ++ tailWord_586544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586550 : List Nat := [5, 1, 2, 2, 2, 2, 2, 1, 3]
def baseStart_586550 : Nat := 118140960795 + 586550 * 2 ^ 59
def prefixEnd_586550 : Nat := 4983230072969 + 3 ^ 40 * 586550 * 2
def baseEnd_586550 : Nat := 267717402573142537002233

theorem tailTrace_586550 : CollatzResearch.WordTrace tailWord_586550 prefixEnd_586550 267717402573142537002233 := by
  unfold tailWord_586550
  simp only [CollatzResearch.WordTrace]
  refine ⟨1337077251564812475611819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14262157350024666406526069 1337077251564812475611819)
  ·
    refine ⟨2005615877347218713417729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1337077251564812475611819 2005615877347218713417729)
    ·
      refine ⟨1504211908010414035063297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2005615877347218713417729 1504211908010414035063297)
      ·
        refine ⟨1128158931007810526297473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1504211908010414035063297 1128158931007810526297473)
        ·
          refine ⟨846119198255857894723105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1128158931007810526297473 846119198255857894723105)
          ·
            refine ⟨634589398691893421042329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 846119198255857894723105 634589398691893421042329)
            ·
              refine ⟨475942049018920065781747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 634589398691893421042329 475942049018920065781747)
              ·
                refine ⟨713913073528380098672621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 475942049018920065781747 713913073528380098672621)
                ·
                  refine ⟨267717402573142537002233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 713913073528380098672621 267717402573142537002233)
                  ·
                    rfl

theorem cell20_586550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 2, 1, 3].length) (baseStart_586550 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_586550 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_586550 prefixEnd_586550 := by exact prefixLift 586550
  have htrace : WordTrace (prefixWord ++ tailWord_586550) baseStart_586550 baseEnd_586550 := by
    simpa [prefixWord, tailWord_586550, baseEnd_586550] using wordTrace_append hprefix tailTrace_586550
  have hstable : (prefixWord ++ tailWord_586550).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586550).length < 2 ^ (prefixWord ++ tailWord_586550).sum := by decide
  have hdescent : baseEnd_586550 < baseStart_586550 := by decide
  rcases family_descends (prefixWord ++ tailWord_586550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586579 : List Nat := [1, 1, 1, 2, 1, 1, 3, 3, 7]
def baseStart_586579 : Nat := 118140960795 + 586579 * 2 ^ 59
def prefixEnd_586579 : Nat := 4983230072969 + 3 ^ 40 * 586579 * 2
def baseEnd_586579 : Nat := 267730638963347325035447

theorem tailTrace_586579 : CollatzResearch.WordTrace tailWord_586579 prefixEnd_586579 267730638963347325035447 := by
  unfold tailWord_586579
  simp only [CollatzResearch.WordTrace]
  refine ⟨21394293741931937562594791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14262862494621291708396527 21394293741931937562594791)
  ·
    refine ⟨32091440612897906343892187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21394293741931937562594791 32091440612897906343892187)
    ·
      refine ⟨48137160919346859515838281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32091440612897906343892187 48137160919346859515838281)
      ·
        refine ⟨36102870689510144636878711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48137160919346859515838281 36102870689510144636878711)
        ·
          refine ⟨54154306034265216955318067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36102870689510144636878711 54154306034265216955318067)
          ·
            refine ⟨81231459051397825432977101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54154306034265216955318067 81231459051397825432977101)
            ·
              refine ⟨30461797144274184537366413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81231459051397825432977101 30461797144274184537366413)
              ·
                refine ⟨11423173929102819201512405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30461797144274184537366413 11423173929102819201512405)
                ·
                  refine ⟨267730638963347325035447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11423173929102819201512405 267730638963347325035447)
                  ·
                    rfl

theorem cell20_586579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 7].length) (baseStart_586579 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_586579 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_586579 prefixEnd_586579 := by exact prefixLift 586579
  have htrace : WordTrace (prefixWord ++ tailWord_586579) baseStart_586579 baseEnd_586579 := by
    simpa [prefixWord, tailWord_586579, baseEnd_586579] using wordTrace_append hprefix tailTrace_586579
  have hstable : (prefixWord ++ tailWord_586579).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586579).length < 2 ^ (prefixWord ++ tailWord_586579).sum := by decide
  have hdescent : baseEnd_586579 < baseStart_586579 := by decide
  rcases family_descends (prefixWord ++ tailWord_586579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586599 : List Nat := [1, 1, 5, 1, 2, 3, 1, 4, 2]
def baseStart_586599 : Nat := 118140960795 + 586599 * 2 ^ 59
def prefixEnd_586599 : Nat := 4983230072969 + 3 ^ 40 * 586599 * 2
def baseEnd_586599 : Nat := 267739767508316144368699

theorem tailTrace_586599 : CollatzResearch.WordTrace tailWord_586599 prefixEnd_586599 267739767508316144368699 := by
  unfold tailWord_586599
  simp only [CollatzResearch.WordTrace]
  refine ⟨21395023201859480978322851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14263348801239653985548567 21395023201859480978322851)
  ·
    refine ⟨32092534802789221467484277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21395023201859480978322851 32092534802789221467484277)
    ·
      refine ⟨3008675137761489512576651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32092534802789221467484277 3008675137761489512576651)
      ·
        refine ⟨4513012706642234268864977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3008675137761489512576651 4513012706642234268864977)
        ·
          refine ⟨3384759529981675701648733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4513012706642234268864977 3384759529981675701648733)
          ·
            refine ⟨1269284823743128388118275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3384759529981675701648733 1269284823743128388118275)
            ·
              refine ⟨1903927235614692582177413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1269284823743128388118275 1903927235614692582177413)
              ·
                refine ⟨356986356677754859158265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1903927235614692582177413 356986356677754859158265)
                ·
                  refine ⟨267739767508316144368699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 356986356677754859158265 267739767508316144368699)
                  ·
                    rfl

theorem cell20_586599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 4, 2].length) (baseStart_586599 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_586599 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_586599 prefixEnd_586599 := by exact prefixLift 586599
  have htrace : WordTrace (prefixWord ++ tailWord_586599) baseStart_586599 baseEnd_586599 := by
    simpa [prefixWord, tailWord_586599, baseEnd_586599] using wordTrace_append hprefix tailTrace_586599
  have hstable : (prefixWord ++ tailWord_586599).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586599).length < 2 ^ (prefixWord ++ tailWord_586599).sum := by decide
  have hdescent : baseEnd_586599 < baseStart_586599 := by decide
  rcases family_descends (prefixWord ++ tailWord_586599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586613 : List Nat := [1, 3, 4, 1, 1, 2, 2, 3, 3]
def baseStart_586613 : Nat := 118140960795 + 586613 * 2 ^ 59
def prefixEnd_586613 : Nat := 4983230072969 + 3 ^ 40 * 586613 * 2
def baseEnd_586613 : Nat := 267746157489794317901975

theorem tailTrace_586613 : CollatzResearch.WordTrace tailWord_586613 prefixEnd_586613 267746157489794317901975 := by
  unfold tailWord_586613
  simp only [CollatzResearch.WordTrace]
  refine ⟨21395533823808761369332493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14263689215872507579554995 21395533823808761369332493)
  ·
    refine ⟨8023325183928285513499685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21395533823808761369332493 8023325183928285513499685)
    ·
      refine ⟨1504373471986553533781191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8023325183928285513499685 1504373471986553533781191)
      ·
        refine ⟨2256560207979830300671787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1504373471986553533781191 2256560207979830300671787)
        ·
          refine ⟨3384840311969745451007681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2256560207979830300671787 3384840311969745451007681)
          ·
            refine ⟨2538630233977309088255761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3384840311969745451007681 2538630233977309088255761)
            ·
              refine ⟨1903972675482981816191821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2538630233977309088255761 1903972675482981816191821)
              ·
                refine ⟨713989753306118181071933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1903972675482981816191821 713989753306118181071933)
                ·
                  refine ⟨267746157489794317901975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 713989753306118181071933 267746157489794317901975)
                  ·
                    rfl

theorem cell20_586613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 3, 3].length) (baseStart_586613 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_586613 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_586613 prefixEnd_586613 := by exact prefixLift 586613
  have htrace : WordTrace (prefixWord ++ tailWord_586613) baseStart_586613 baseEnd_586613 := by
    simpa [prefixWord, tailWord_586613, baseEnd_586613] using wordTrace_append hprefix tailTrace_586613
  have hstable : (prefixWord ++ tailWord_586613).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586613).length < 2 ^ (prefixWord ++ tailWord_586613).sum := by decide
  have hdescent : baseEnd_586613 < baseStart_586613 := by decide
  rcases family_descends (prefixWord ++ tailWord_586613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586627 : List Nat := [1, 1, 1, 3, 4, 1, 5, 4]
def baseStart_586627 : Nat := 118140960795 + 586627 * 2 ^ 59
def prefixEnd_586627 : Nat := 4983230072969 + 3 ^ 40 * 586627 * 2
def baseEnd_586627 : Nat := 89250849157090830478417

theorem tailTrace_586627 : CollatzResearch.WordTrace tailWord_586627 prefixEnd_586627 89250849157090830478417 := by
  unfold tailWord_586627
  simp only [CollatzResearch.WordTrace]
  refine ⟨21396044445758041760342135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14264029630505361173561423 21396044445758041760342135)
  ·
    refine ⟨32094066668637062640513203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21396044445758041760342135 32094066668637062640513203)
    ·
      refine ⟨48141100002955593960769805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32094066668637062640513203 48141100002955593960769805)
      ·
        refine ⟨18052912501108347735288677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48141100002955593960769805 18052912501108347735288677)
        ·
          refine ⟨3384921093957815200366627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18052912501108347735288677 3384921093957815200366627)
          ·
            refine ⟨5077381640936722800549941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3384921093957815200366627 5077381640936722800549941)
            ·
              refine ⟨476004528837817762551557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5077381640936722800549941 476004528837817762551557)
              ·
                refine ⟨89250849157090830478417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 476004528837817762551557 89250849157090830478417)
                ·
                  rfl

theorem cell20_586627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 5, 4].length) (baseStart_586627 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_586627 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_586627 prefixEnd_586627 := by exact prefixLift 586627
  have htrace : WordTrace (prefixWord ++ tailWord_586627) baseStart_586627 baseEnd_586627 := by
    simpa [prefixWord, tailWord_586627, baseEnd_586627] using wordTrace_append hprefix tailTrace_586627
  have hstable : (prefixWord ++ tailWord_586627).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586627).length < 2 ^ (prefixWord ++ tailWord_586627).sum := by decide
  have hdescent : baseEnd_586627 < baseStart_586627 := by decide
  rcases family_descends (prefixWord ++ tailWord_586627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586658 : List Nat := [3, 3, 1, 2, 2, 1, 1, 3, 4]
def baseStart_586658 : Nat := 118140960795 + 586658 * 2 ^ 59
def prefixEnd_586658 : Nat := 4983230072969 + 3 ^ 40 * 586658 * 2
def baseEnd_586658 : Nat := 267766696715974161401791

theorem tailTrace_586658 : CollatzResearch.WordTrace tailWord_586658 prefixEnd_586658 267766696715974161401791 := by
  unfold tailWord_586658
  simp only [CollatzResearch.WordTrace]
  refine ⟨5349293777161433513680157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14264783405763822703147085 5349293777161433513680157)
  ·
    refine ⟨2005985166435537567630059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5349293777161433513680157 2005985166435537567630059)
    ·
      refine ⟨3008977749653306351445089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2005985166435537567630059 3008977749653306351445089)
      ·
        refine ⟨2256733312239979763583817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3008977749653306351445089 2256733312239979763583817)
        ·
          refine ⟨1692549984179984822687863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2256733312239979763583817 1692549984179984822687863)
          ·
            refine ⟨2538824976269977234031795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1692549984179984822687863 2538824976269977234031795)
            ·
              refine ⟨3808237464404965851047693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2538824976269977234031795 3808237464404965851047693)
              ·
                refine ⟨1428089049151862194142885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3808237464404965851047693 1428089049151862194142885)
                ·
                  refine ⟨267766696715974161401791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1428089049151862194142885 267766696715974161401791)
                  ·
                    rfl

theorem cell20_586658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_586658 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_586658 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_586658 prefixEnd_586658 := by exact prefixLift 586658
  have htrace : WordTrace (prefixWord ++ tailWord_586658) baseStart_586658 baseEnd_586658 := by
    simpa [prefixWord, tailWord_586658, baseEnd_586658] using wordTrace_append hprefix tailTrace_586658
  have hstable : (prefixWord ++ tailWord_586658).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586658).length < 2 ^ (prefixWord ++ tailWord_586658).sum := by decide
  have hdescent : baseEnd_586658 < baseStart_586658 := by decide
  rcases family_descends (prefixWord ++ tailWord_586658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586678 : List Nat := [5, 1, 4, 1, 1, 1, 1, 6]
def baseStart_586678 : Nat := 118140960795 + 586678 * 2 ^ 59
def prefixEnd_586678 : Nat := 4983230072969 + 3 ^ 40 * 586678 * 2
def baseEnd_586678 : Nat := 89258608420314326911681

theorem tailTrace_586678 : CollatzResearch.WordTrace tailWord_586678 prefixEnd_586678 89258608420314326911681 := by
  unfold tailWord_586678
  simp only [CollatzResearch.WordTrace]
  refine ⟨1337369035535829841903043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14265269712382184980299125 1337369035535829841903043)
  ·
    refine ⟨2006053553303744762854565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1337369035535829841903043 2006053553303744762854565)
    ·
      refine ⟨376135041244452143035231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2006053553303744762854565 376135041244452143035231)
      ·
        refine ⟨564202561866678214552847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 376135041244452143035231 564202561866678214552847)
        ·
          refine ⟨846303842800017321829271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 564202561866678214552847 846303842800017321829271)
          ·
            refine ⟨1269455764200025982743907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 846303842800017321829271 1269455764200025982743907)
            ·
              refine ⟨1904183646300038974115861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1269455764200025982743907 1904183646300038974115861)
              ·
                refine ⟨89258608420314326911681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1904183646300038974115861 89258608420314326911681)
                ·
                  rfl

theorem cell20_586678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 6].length) (baseStart_586678 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_586678 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_586678 prefixEnd_586678 := by exact prefixLift 586678
  have htrace : WordTrace (prefixWord ++ tailWord_586678) baseStart_586678 baseEnd_586678 := by
    simpa [prefixWord, tailWord_586678, baseEnd_586678] using wordTrace_append hprefix tailTrace_586678
  have hstable : (prefixWord ++ tailWord_586678).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586678).length < 2 ^ (prefixWord ++ tailWord_586678).sum := by decide
  have hdescent : baseEnd_586678 < baseStart_586678 := by decide
  rcases family_descends (prefixWord ++ tailWord_586678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586679 : List Nat := [1, 1, 3, 1, 3, 1, 4, 2, 4]
def baseStart_586679 : Nat := 118140960795 + 586679 * 2 ^ 59
def prefixEnd_586679 : Nat := 4983230072969 + 3 ^ 40 * 586679 * 2
def baseEnd_586679 : Nat := 267776281688191421701705

theorem tailTrace_586679 : CollatzResearch.WordTrace tailWord_586679 prefixEnd_586679 267776281688191421701705 := by
  unfold tailWord_586679
  simp only [CollatzResearch.WordTrace]
  refine ⟨21397941041569654641235091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14265294027713103094156727 21397941041569654641235091)
  ·
    refine ⟨32096911562354481961852637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21397941041569654641235091 32096911562354481961852637)
    ·
      refine ⟨12036341835882930735694739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32096911562354481961852637 12036341835882930735694739)
      ·
        refine ⟨18054512753824396103542109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12036341835882930735694739 18054512753824396103542109)
        ·
          refine ⟨6770442282684148538828291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18054512753824396103542109 6770442282684148538828291)
          ·
            refine ⟨10155663424026222808242437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6770442282684148538828291 10155663424026222808242437)
            ·
              refine ⟨1904186892004916776545457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10155663424026222808242437 1904186892004916776545457)
              ·
                refine ⟨1428140169003687582409093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1904186892004916776545457 1428140169003687582409093)
                ·
                  refine ⟨267776281688191421701705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1428140169003687582409093 267776281688191421701705)
                  ·
                    rfl

theorem cell20_586679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 2, 4].length) (baseStart_586679 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_586679 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_586679 prefixEnd_586679 := by exact prefixLift 586679
  have htrace : WordTrace (prefixWord ++ tailWord_586679) baseStart_586679 baseEnd_586679 := by
    simpa [prefixWord, tailWord_586679, baseEnd_586679] using wordTrace_append hprefix tailTrace_586679
  have hstable : (prefixWord ++ tailWord_586679).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586679).length < 2 ^ (prefixWord ++ tailWord_586679).sum := by decide
  have hdescent : baseEnd_586679 < baseStart_586679 := by decide
  rcases family_descends (prefixWord ++ tailWord_586679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586727 : List Nat := [1, 1, 5, 2, 2, 2, 1, 3, 3]
def baseStart_586727 : Nat := 118140960795 + 586727 * 2 ^ 59
def prefixEnd_586727 : Nat := 4983230072969 + 3 ^ 40 * 586727 * 2
def baseEnd_586727 : Nat := 267798190196116588101509

theorem tailTrace_586727 : CollatzResearch.WordTrace tailWord_586727 prefixEnd_586727 267798190196116588101509 := by
  unfold tailWord_586727
  simp only [CollatzResearch.WordTrace]
  refine ⟨21399691745395758838982435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14266461163597172559321623 21399691745395758838982435)
  ·
    refine ⟨32099537618093638258473653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21399691745395758838982435 32099537618093638258473653)
    ·
      refine ⟨3009331651696278586731905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32099537618093638258473653 3009331651696278586731905)
      ·
        refine ⟨2256998738772208940048929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3009331651696278586731905 2256998738772208940048929)
        ·
          refine ⟨1692749054079156705036697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2256998738772208940048929 1692749054079156705036697)
          ·
            refine ⟨1269561790559367528777523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1692749054079156705036697 1269561790559367528777523)
            ·
              refine ⟨1904342685839051293166285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1269561790559367528777523 1904342685839051293166285)
              ·
                refine ⟨714128507189644234937357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1904342685839051293166285 714128507189644234937357)
                ·
                  refine ⟨267798190196116588101509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 714128507189644234937357 267798190196116588101509)
                  ·
                    rfl

theorem cell20_586727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 3, 3].length) (baseStart_586727 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_586727 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_586727 prefixEnd_586727 := by exact prefixLift 586727
  have htrace : WordTrace (prefixWord ++ tailWord_586727) baseStart_586727 baseEnd_586727 := by
    simpa [prefixWord, tailWord_586727, baseEnd_586727] using wordTrace_append hprefix tailTrace_586727
  have hstable : (prefixWord ++ tailWord_586727).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586727).length < 2 ^ (prefixWord ++ tailWord_586727).sum := by decide
  have hdescent : baseEnd_586727 < baseStart_586727 := by decide
  rcases family_descends (prefixWord ++ tailWord_586727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586758 : List Nat := [6, 2, 1, 11]
def baseStart_586758 : Nat := 118140960795 + 586758 * 2 ^ 59
def prefixEnd_586758 : Nat := 4983230072969 + 3 ^ 40 * 586758 * 2
def baseEnd_586758 : Nat := 1102108392760568963243

theorem tailTrace_586758 : CollatzResearch.WordTrace tailWord_586758 prefixEnd_586758 1102108392760568963243 := by
  unfold tailWord_586758
  simp only [CollatzResearch.WordTrace]
  refine ⟨668775700258857847917529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 14267214938855634088907285 668775700258857847917529)
  ·
    refine ⟨501581775194143385938147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 668775700258857847917529 501581775194143385938147)
    ·
      refine ⟨752372662791215078907221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 501581775194143385938147 752372662791215078907221)
      ·
        refine ⟨1102108392760568963243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 11 752372662791215078907221 1102108392760568963243)
        ·
          rfl

theorem cell20_586758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 11].length) (baseStart_586758 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_586758 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_586758 prefixEnd_586758 := by exact prefixLift 586758
  have htrace : WordTrace (prefixWord ++ tailWord_586758) baseStart_586758 baseEnd_586758 := by
    simpa [prefixWord, tailWord_586758, baseEnd_586758] using wordTrace_append hprefix tailTrace_586758
  have hstable : (prefixWord ++ tailWord_586758).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586758).length < 2 ^ (prefixWord ++ tailWord_586758).sum := by decide
  have hdescent : baseEnd_586758 < baseStart_586758 := by decide
  rcases family_descends (prefixWord ++ tailWord_586758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586762 : List Nat := [3, 1, 2, 2, 3, 9]
def baseStart_586762 : Nat := 118140960795 + 586762 * 2 ^ 59
def prefixEnd_586762 : Nat := 4983230072969 + 3 ^ 40 * 586762 * 2
def baseEnd_586762 : Nat := 9919043153696741553137

theorem tailTrace_586762 : CollatzResearch.WordTrace tailWord_586762 prefixEnd_586762 9919043153696741553137 := by
  unfold tailWord_586762
  simp only [CollatzResearch.WordTrace]
  refine ⟨5350242075067239954126635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14267312200179306544337693 5350242075067239954126635)
  ·
    refine ⟨8025363112600859931189953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5350242075067239954126635 8025363112600859931189953)
    ·
      refine ⟨6019022334450644948392465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8025363112600859931189953 6019022334450644948392465)
      ·
        refine ⟨4514266750837983711294349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6019022334450644948392465 4514266750837983711294349)
        ·
          refine ⟨1692850031564243891735381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4514266750837983711294349 1692850031564243891735381)
          ·
            refine ⟨9919043153696741553137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1692850031564243891735381 9919043153696741553137)
            ·
              rfl

theorem cell20_586762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 9].length) (baseStart_586762 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_586762 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_586762 prefixEnd_586762 := by exact prefixLift 586762
  have htrace : WordTrace (prefixWord ++ tailWord_586762) baseStart_586762 baseEnd_586762 := by
    simpa [prefixWord, tailWord_586762, baseEnd_586762] using wordTrace_append hprefix tailTrace_586762
  have hstable : (prefixWord ++ tailWord_586762).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586762).length < 2 ^ (prefixWord ++ tailWord_586762).sum := by decide
  have hdescent : baseEnd_586762 < baseStart_586762 := by decide
  rcases family_descends (prefixWord ++ tailWord_586762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586769 : List Nat := [1, 2, 2, 1, 1, 2, 1, 5, 5]
def baseStart_586769 : Nat := 118140960795 + 586769 * 2 ^ 59
def prefixEnd_586769 : Nat := 4983230072969 + 3 ^ 40 * 586769 * 2
def baseEnd_586769 : Nat := 267817360140551108701337

theorem tailTrace_586769 : CollatzResearch.WordTrace tailWord_586769 prefixEnd_586769 267817360140551108701337 := by
  unfold tailWord_586769
  simp only [CollatzResearch.WordTrace]
  refine ⟨21401223611243600012011361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14267482407495733341340907 21401223611243600012011361)
  ·
    refine ⟨16050917708432700009008521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21401223611243600012011361 16050917708432700009008521)
    ·
      refine ⟨12038188281324525006756391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16050917708432700009008521 12038188281324525006756391)
      ·
        refine ⟨18057282421986787510134587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12038188281324525006756391 18057282421986787510134587)
        ·
          refine ⟨27085923632980181265201881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18057282421986787510134587 27085923632980181265201881)
          ·
            refine ⟨20314442724735135948901411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27085923632980181265201881 20314442724735135948901411)
            ·
              refine ⟨30471664087102703923352117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20314442724735135948901411 30471664087102703923352117)
              ·
                refine ⟨2856718508165878492814261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30471664087102703923352117 2856718508165878492814261)
                ·
                  refine ⟨267817360140551108701337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2856718508165878492814261 267817360140551108701337)
                  ·
                    rfl

theorem cell20_586769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 5, 5].length) (baseStart_586769 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_586769 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_586769 prefixEnd_586769 := by exact prefixLift 586769
  have htrace : WordTrace (prefixWord ++ tailWord_586769) baseStart_586769 baseEnd_586769 := by
    simpa [prefixWord, tailWord_586769, baseEnd_586769] using wordTrace_append hprefix tailTrace_586769
  have hstable : (prefixWord ++ tailWord_586769).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586769).length < 2 ^ (prefixWord ++ tailWord_586769).sum := by decide
  have hdescent : baseEnd_586769 < baseStart_586769 := by decide
  rcases family_descends (prefixWord ++ tailWord_586769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586806 : List Nat := [5, 1, 2, 1, 1, 3, 2, 3, 2]
def baseStart_586806 : Nat := 118140960795 + 586806 * 2 ^ 59
def prefixEnd_586806 : Nat := 4983230072969 + 3 ^ 40 * 586806 * 2
def baseEnd_586806 : Nat := 267834247948743424467853

theorem tailTrace_586806 : CollatzResearch.WordTrace tailWord_586806 prefixEnd_586806 267834247948743424467853 := by
  unfold tailWord_586806
  simp only [CollatzResearch.WordTrace]
  refine ⟨1337660819506847208194267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14268382074739703554072181 1337660819506847208194267)
  ·
    refine ⟨2006491229260270812291401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1337660819506847208194267 2006491229260270812291401)
    ·
      refine ⟨1504868421945203109218551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2006491229260270812291401 1504868421945203109218551)
      ·
        refine ⟨2257302632917804663827827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1504868421945203109218551 2257302632917804663827827)
        ·
          refine ⟨3385953949376706995741741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2257302632917804663827827 3385953949376706995741741)
          ·
            refine ⟨1269732731016265123403153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3385953949376706995741741 1269732731016265123403153)
            ·
              refine ⟨952299548262198842552365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1269732731016265123403153 952299548262198842552365)
              ·
                refine ⟨357112330598324565957137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 952299548262198842552365 357112330598324565957137)
                ·
                  refine ⟨267834247948743424467853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 357112330598324565957137 267834247948743424467853)
                  ·
                    rfl

theorem cell20_586806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2, 3, 2].length) (baseStart_586806 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_586806 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_586806 prefixEnd_586806 := by exact prefixLift 586806
  have htrace : WordTrace (prefixWord ++ tailWord_586806) baseStart_586806 baseEnd_586806 := by
    simpa [prefixWord, tailWord_586806, baseEnd_586806] using wordTrace_append hprefix tailTrace_586806
  have hstable : (prefixWord ++ tailWord_586806).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586806).length < 2 ^ (prefixWord ++ tailWord_586806).sum := by decide
  have hdescent : baseEnd_586806 < baseStart_586806 := by decide
  rcases family_descends (prefixWord ++ tailWord_586806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586807 : List Nat := [1, 1, 3, 1, 2, 2, 1, 4, 5]
def baseStart_586807 : Nat := 118140960795 + 586807 * 2 ^ 59
def prefixEnd_586807 : Nat := 4983230072969 + 3 ^ 40 * 586807 * 2
def baseEnd_586807 : Nat := 267834704375991865434515

theorem tailTrace_586807 : CollatzResearch.WordTrace tailWord_586807 prefixEnd_586807 267834704375991865434515 := by
  unfold tailWord_586807
  simp only [CollatzResearch.WordTrace]
  refine ⟨21402609585105932501894675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14268406390070621667929783 21402609585105932501894675)
  ·
    refine ⟨32103914377658898752842013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21402609585105932501894675 32103914377658898752842013)
    ·
      refine ⟨12038967891622087032315755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32103914377658898752842013 12038967891622087032315755)
      ·
        refine ⟨18058451837433130548473633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12038967891622087032315755 18058451837433130548473633)
        ·
          refine ⟨13543838878074847911355225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18058451837433130548473633 13543838878074847911355225)
          ·
            refine ⟨10157879158556135933516419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13543838878074847911355225 10157879158556135933516419)
            ·
              refine ⟨15236818737834203900274629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10157879158556135933516419 15236818737834203900274629)
              ·
                refine ⟨2856903513343913231301493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15236818737834203900274629 2856903513343913231301493)
                ·
                  refine ⟨267834704375991865434515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2856903513343913231301493 267834704375991865434515)
                  ·
                    rfl

theorem cell20_586807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 4, 5].length) (baseStart_586807 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_586807 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_586807 prefixEnd_586807 := by exact prefixLift 586807
  have htrace : WordTrace (prefixWord ++ tailWord_586807) baseStart_586807 baseEnd_586807 := by
    simpa [prefixWord, tailWord_586807, baseEnd_586807] using wordTrace_append hprefix tailTrace_586807
  have hstable : (prefixWord ++ tailWord_586807).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586807).length < 2 ^ (prefixWord ++ tailWord_586807).sum := by decide
  have hdescent : baseEnd_586807 < baseStart_586807 := by decide
  rcases family_descends (prefixWord ++ tailWord_586807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586810 : List Nat := [3, 1, 1, 1, 3, 1, 3, 5, 2]
def baseStart_586810 : Nat := 118140960795 + 586810 * 2 ^ 59
def prefixEnd_586810 : Nat := 4983230072969 + 3 ^ 40 * 586810 * 2
def baseEnd_586810 : Nat := 267836073657737188334503

theorem tailTrace_586810 : CollatzResearch.WordTrace tailWord_586810 prefixEnd_586810 267836073657737188334503 := by
  unfold tailWord_586810
  simp only [CollatzResearch.WordTrace]
  refine ⟨5350679751023766003563471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14268479336063376009502589 5350679751023766003563471)
  ·
    refine ⟨8026019626535649005345207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5350679751023766003563471 8026019626535649005345207)
    ·
      refine ⟨12039029439803473508017811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8026019626535649005345207 12039029439803473508017811)
      ·
        refine ⟨18058544159705210262026717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12039029439803473508017811 18058544159705210262026717)
        ·
          refine ⟨6771954059889453848260019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18058544159705210262026717 6771954059889453848260019)
          ·
            refine ⟨10157931089834180772390029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6771954059889453848260019 10157931089834180772390029)
            ·
              refine ⟨3809224158687817789646261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10157931089834180772390029 3809224158687817789646261)
              ·
                refine ⟨357114764876982917779337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3809224158687817789646261 357114764876982917779337)
                ·
                  refine ⟨267836073657737188334503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 357114764876982917779337 267836073657737188334503)
                  ·
                    rfl

theorem cell20_586810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 5, 2].length) (baseStart_586810 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_586810 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_586810 prefixEnd_586810 := by exact prefixLift 586810
  have htrace : WordTrace (prefixWord ++ tailWord_586810) baseStart_586810 baseEnd_586810 := by
    simpa [prefixWord, tailWord_586810, baseEnd_586810] using wordTrace_append hprefix tailTrace_586810
  have hstable : (prefixWord ++ tailWord_586810).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586810).length < 2 ^ (prefixWord ++ tailWord_586810).sum := by decide
  have hdescent : baseEnd_586810 < baseStart_586810 := by decide
  rcases family_descends (prefixWord ++ tailWord_586810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586817 : List Nat := [1, 2, 5, 1, 3, 1, 7]
def baseStart_586817 : Nat := 118140960795 + 586817 * 2 ^ 59
def prefixEnd_586817 : Nat := 4983230072969 + 3 ^ 40 * 586817 * 2
def baseEnd_586817 : Nat := 29759918738719586122349

theorem tailTrace_586817 : CollatzResearch.WordTrace tailWord_586817 prefixEnd_586817 29759918738719586122349 := by
  unfold tailWord_586817
  simp only [CollatzResearch.WordTrace]
  refine ⟨21402974315069704209758705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14268649543379802806505803 21402974315069704209758705)
  ·
    refine ⟨16052230736302278157319029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21402974315069704209758705 16052230736302278157319029)
    ·
      refine ⟨1504896631528338577248659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16052230736302278157319029 1504896631528338577248659)
      ·
        refine ⟨2257344947292507865872989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1504896631528338577248659 2257344947292507865872989)
        ·
          refine ⟨846504355234690449702371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2257344947292507865872989 846504355234690449702371)
          ·
            refine ⟨1269756532852035674553557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 846504355234690449702371 1269756532852035674553557)
            ·
              refine ⟨29759918738719586122349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1269756532852035674553557 29759918738719586122349)
              ·
                rfl

theorem cell20_586817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 7].length) (baseStart_586817 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_586817 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_586817 prefixEnd_586817 := by exact prefixLift 586817
  have htrace : WordTrace (prefixWord ++ tailWord_586817) baseStart_586817 baseEnd_586817 := by
    simpa [prefixWord, tailWord_586817, baseEnd_586817] using wordTrace_append hprefix tailTrace_586817
  have hstable : (prefixWord ++ tailWord_586817).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586817).length < 2 ^ (prefixWord ++ tailWord_586817).sum := by decide
  have hdescent : baseEnd_586817 < baseStart_586817 := by decide
  rcases family_descends (prefixWord ++ tailWord_586817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586855 : List Nat := [1, 1, 5, 1, 1, 3, 4, 4]
def baseStart_586855 : Nat := 118140960795 + 586855 * 2 ^ 59
def prefixEnd_586855 : Nat := 4983230072969 + 3 ^ 40 * 586855 * 2
def baseEnd_586855 : Nat := 89285537627972343944773

theorem tailTrace_586855 : CollatzResearch.WordTrace tailWord_586855 prefixEnd_586855 89285537627972343944773 := by
  unfold tailWord_586855
  simp only [CollatzResearch.WordTrace]
  refine ⟨21404360288932036699642019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14269573525954691133094679 21404360288932036699642019)
  ·
    refine ⟨32106540433398055049463029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21404360288932036699642019 32106540433398055049463029)
    ·
      refine ⟨3009988165631067660887159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32106540433398055049463029 3009988165631067660887159)
      ·
        refine ⟨4514982248446601491330739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3009988165631067660887159 4514982248446601491330739)
        ·
          refine ⟨6772473372669902236996109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4514982248446601491330739 6772473372669902236996109)
          ·
            refine ⟨2539677514751213338873541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6772473372669902236996109 2539677514751213338873541)
            ·
              refine ⟨476189534015852501038789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2539677514751213338873541 476189534015852501038789)
              ·
                refine ⟨89285537627972343944773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 476189534015852501038789 89285537627972343944773)
                ·
                  rfl

theorem cell20_586855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 4, 4].length) (baseStart_586855 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_586855 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_586855 prefixEnd_586855 := by exact prefixLift 586855
  have htrace : WordTrace (prefixWord ++ tailWord_586855) baseStart_586855 baseEnd_586855 := by
    simpa [prefixWord, tailWord_586855, baseEnd_586855] using wordTrace_append hprefix tailTrace_586855
  have hstable : (prefixWord ++ tailWord_586855).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586855).length < 2 ^ (prefixWord ++ tailWord_586855).sum := by decide
  have hdescent : baseEnd_586855 < baseStart_586855 := by decide
  rcases family_descends (prefixWord ++ tailWord_586855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586862 : List Nat := [4, 1, 2, 2, 1, 2, 1, 2, 5]
def baseStart_586862 : Nat := 118140960795 + 586862 * 2 ^ 59
def prefixEnd_586862 : Nat := 4983230072969 + 3 ^ 40 * 586862 * 2
def baseEnd_586862 : Nat := 267859807874656118600957

theorem tailTrace_586862 : CollatzResearch.WordTrace tailWord_586862 prefixEnd_586862 267859807874656118600957 := by
  unfold tailWord_586862
  simp only [CollatzResearch.WordTrace]
  refine ⟨2675576949988334611893355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14269743733271117930097893 2675576949988334611893355)
  ·
    refine ⟨4013365424982501917840033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2675576949988334611893355 4013365424982501917840033)
    ·
      refine ⟨3010024068736876438380025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4013365424982501917840033 3010024068736876438380025)
      ·
        refine ⟨2257518051552657328785019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3010024068736876438380025 2257518051552657328785019)
        ·
          refine ⟨3386277077328985993177529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2257518051552657328785019 3386277077328985993177529)
          ·
            refine ⟨2539707807996739494883147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3386277077328985993177529 2539707807996739494883147)
            ·
              refine ⟨3809561711995109242324721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2539707807996739494883147 3809561711995109242324721)
              ·
                refine ⟨2857171283996331931743541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3809561711995109242324721 2857171283996331931743541)
                ·
                  refine ⟨267859807874656118600957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2857171283996331931743541 267859807874656118600957)
                  ·
                    rfl

theorem cell20_586862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 2, 5].length) (baseStart_586862 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_586862 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_586862 prefixEnd_586862 := by exact prefixLift 586862
  have htrace : WordTrace (prefixWord ++ tailWord_586862) baseStart_586862 baseEnd_586862 := by
    simpa [prefixWord, tailWord_586862, baseEnd_586862] using wordTrace_append hprefix tailTrace_586862
  have hstable : (prefixWord ++ tailWord_586862).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586862).length < 2 ^ (prefixWord ++ tailWord_586862).sum := by decide
  have hdescent : baseEnd_586862 < baseStart_586862 := by decide
  rcases family_descends (prefixWord ++ tailWord_586862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586878 : List Nat := [4, 2, 4, 1, 2, 1, 1, 1, 4]
def baseStart_586878 : Nat := 118140960795 + 586878 * 2 ^ 59
def prefixEnd_586878 : Nat := 4983230072969 + 3 ^ 40 * 586878 * 2
def baseEnd_586878 : Nat := 267867110710631174067559

theorem tailTrace_586878 : CollatzResearch.WordTrace tailWord_586878 prefixEnd_586878 267867110710631174067559 := by
  unfold tailWord_586878
  simp only [CollatzResearch.WordTrace]
  refine ⟨2675649895981088953466161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14270132778565807751819525 2675649895981088953466161)
  ·
    refine ⟨2006737421985816715099621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2675649895981088953466161 2006737421985816715099621)
    ·
      refine ⟨376263266622340634081179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2006737421985816715099621 376263266622340634081179)
      ·
        refine ⟨564394899933510951121769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 376263266622340634081179 564394899933510951121769)
        ·
          refine ⟨423296174950133213341327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 564394899933510951121769 423296174950133213341327)
          ·
            refine ⟨634944262425199820011991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 423296174950133213341327 634944262425199820011991)
            ·
              refine ⟨952416393637799730017987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 634944262425199820011991 952416393637799730017987)
              ·
                refine ⟨1428624590456699595026981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 952416393637799730017987 1428624590456699595026981)
                ·
                  refine ⟨267867110710631174067559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1428624590456699595026981 267867110710631174067559)
                  ·
                    rfl

theorem cell20_586878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 1, 1, 4].length) (baseStart_586878 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_586878 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_586878 prefixEnd_586878 := by exact prefixLift 586878
  have htrace : WordTrace (prefixWord ++ tailWord_586878) baseStart_586878 baseEnd_586878 := by
    simpa [prefixWord, tailWord_586878, baseEnd_586878] using wordTrace_append hprefix tailTrace_586878
  have hstable : (prefixWord ++ tailWord_586878).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586878).length < 2 ^ (prefixWord ++ tailWord_586878).sum := by decide
  have hdescent : baseEnd_586878 < baseStart_586878 := by decide
  rcases family_descends (prefixWord ++ tailWord_586878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586883 : List Nat := [1, 1, 1, 3, 3, 2, 1, 3, 5]
def baseStart_586883 : Nat := 118140960795 + 586883 * 2 ^ 59
def prefixEnd_586883 : Nat := 4983230072969 + 3 ^ 40 * 586883 * 2
def baseEnd_586883 : Nat := 267869392846873378900871

theorem tailTrace_586883 : CollatzResearch.WordTrace tailWord_586883 prefixEnd_586883 267869392846873378900871 := by
  unfold tailWord_586883
  simp only [CollatzResearch.WordTrace]
  refine ⟨21405381532830597481661303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14270254355220398321107535 21405381532830597481661303)
  ·
    refine ⟨32108072299245896222491955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21405381532830597481661303 32108072299245896222491955)
    ·
      refine ⟨48162108448868844333737933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32108072299245896222491955 48162108448868844333737933)
      ·
        refine ⟨18060790668325816625151725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48162108448868844333737933 18060790668325816625151725)
        ·
          refine ⟨6772796500622181234431897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18060790668325816625151725 6772796500622181234431897)
          ·
            refine ⟨5079597375466635925823923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6772796500622181234431897 5079597375466635925823923)
            ·
              refine ⟨7619396063199953888735885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5079597375466635925823923 7619396063199953888735885)
              ·
                refine ⟨2857273523699982708275957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7619396063199953888735885 2857273523699982708275957)
                ·
                  refine ⟨267869392846873378900871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2857273523699982708275957 267869392846873378900871)
                  ·
                    rfl

theorem cell20_586883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 3, 5].length) (baseStart_586883 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_586883 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_586883 prefixEnd_586883 := by exact prefixLift 586883
  have htrace : WordTrace (prefixWord ++ tailWord_586883) baseStart_586883 baseEnd_586883 := by
    simpa [prefixWord, tailWord_586883, baseEnd_586883] using wordTrace_append hprefix tailTrace_586883
  have hstable : (prefixWord ++ tailWord_586883).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586883).length < 2 ^ (prefixWord ++ tailWord_586883).sum := by decide
  have hdescent : baseEnd_586883 < baseStart_586883 := by decide
  rcases family_descends (prefixWord ++ tailWord_586883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586928 : List Nat := [2, 1, 1, 1, 2, 1, 2, 4, 6]
def baseStart_586928 : Nat := 118140960795 + 586928 * 2 ^ 59
def prefixEnd_586928 : Nat := 4983230072969 + 3 ^ 40 * 586928 * 2
def baseEnd_586928 : Nat := 267889932073053222400687

theorem tailTrace_586928 : CollatzResearch.WordTrace tailWord_586928 prefixEnd_586928 267889932073053222400687 := by
  unfold tailWord_586928
  simp only [CollatzResearch.WordTrace]
  refine ⟨10703511408833785083524719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14271348545111713444699625 10703511408833785083524719)
  ·
    refine ⟨16055267113250677625287079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10703511408833785083524719 16055267113250677625287079)
    ·
      refine ⟨24082900669876016437930619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16055267113250677625287079 24082900669876016437930619)
      ·
        refine ⟨36124351004814024656895929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24082900669876016437930619 36124351004814024656895929)
        ·
          refine ⟨27093263253610518492671947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36124351004814024656895929 27093263253610518492671947)
          ·
            refine ⟨40639894880415777739007921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27093263253610518492671947 40639894880415777739007921)
            ·
              refine ⟨30479921160311833304255941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40639894880415777739007921 30479921160311833304255941)
              ·
                refine ⟨5714985217558468744547989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30479921160311833304255941 5714985217558468744547989)
                ·
                  refine ⟨267889932073053222400687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5714985217558468744547989 267889932073053222400687)
                  ·
                    rfl

theorem cell20_586928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 4, 6].length) (baseStart_586928 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_586928 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_586928 prefixEnd_586928 := by exact prefixLift 586928
  have htrace : WordTrace (prefixWord ++ tailWord_586928) baseStart_586928 baseEnd_586928 := by
    simpa [prefixWord, tailWord_586928, baseEnd_586928] using wordTrace_append hprefix tailTrace_586928
  have hstable : (prefixWord ++ tailWord_586928).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586928).length < 2 ^ (prefixWord ++ tailWord_586928).sum := by decide
  have hdescent : baseEnd_586928 < baseStart_586928 := by decide
  rcases family_descends (prefixWord ++ tailWord_586928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586941 : List Nat := [1, 4, 1, 2, 1, 1, 6, 2, 2]
def baseStart_586941 : Nat := 118140960795 + 586941 * 2 ^ 59
def prefixEnd_586941 : Nat := 4983230072969 + 3 ^ 40 * 586941 * 2
def baseEnd_586941 : Nat := 267895865627282954967301

theorem tailTrace_586941 : CollatzResearch.WordTrace tailWord_586941 prefixEnd_586941 267895865627282954967301 := by
  unfold tailWord_586941
  simp only [CollatzResearch.WordTrace]
  refine ⟨21407496966620473387272677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14271664644413648924848451 21407496966620473387272677)
  ·
    refine ⟨4013905681241338760113627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21407496966620473387272677 4013905681241338760113627)
    ·
      refine ⟨6020858521862008140170441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4013905681241338760113627 6020858521862008140170441)
      ·
        refine ⟨4515643891396506105127831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6020858521862008140170441 4515643891396506105127831)
        ·
          refine ⟨6773465837094759157691747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4515643891396506105127831 6773465837094759157691747)
          ·
            refine ⟨10160198755642138736537621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6773465837094759157691747 10160198755642138736537621)
            ·
              refine ⟨476259316670725253275201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 10160198755642138736537621 476259316670725253275201)
              ·
                refine ⟨357194487503043939956401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 476259316670725253275201 357194487503043939956401)
                ·
                  refine ⟨267895865627282954967301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 357194487503043939956401 267895865627282954967301)
                  ·
                    rfl

theorem cell20_586941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 6, 2, 2].length) (baseStart_586941 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_586941 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_586941 prefixEnd_586941 := by exact prefixLift 586941
  have htrace : WordTrace (prefixWord ++ tailWord_586941) baseStart_586941 baseEnd_586941 := by
    simpa [prefixWord, tailWord_586941, baseEnd_586941] using wordTrace_append hprefix tailTrace_586941
  have hstable : (prefixWord ++ tailWord_586941).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586941).length < 2 ^ (prefixWord ++ tailWord_586941).sum := by decide
  have hdescent : baseEnd_586941 < baseStart_586941 := by decide
  rcases family_descends (prefixWord ++ tailWord_586941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586948 : List Nat := [2, 3, 3, 1, 3, 2, 1, 5]
def baseStart_586948 : Nat := 118140960795 + 586948 * 2 ^ 59
def prefixEnd_586948 : Nat := 4983230072969 + 3 ^ 40 * 586948 * 2
def baseEnd_586948 : Nat := 89299686872674013911313

theorem tailTrace_586948 : CollatzResearch.WordTrace tailWord_586948 prefixEnd_586948 89299686872674013911313 := by
  unfold tailWord_586948
  simp only [CollatzResearch.WordTrace]
  refine ⟨10703876138797556791388749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14271834851730075721851665 10703876138797556791388749)
  ·
    refine ⟨4013953552049083796770781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10703876138797556791388749 4013953552049083796770781)
    ·
      refine ⟨1505232582018406423789043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4013953552049083796770781 1505232582018406423789043)
      ·
        refine ⟨2257848873027609635683565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1505232582018406423789043 2257848873027609635683565)
        ·
          refine ⟨846693327385353613381337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2257848873027609635683565 846693327385353613381337)
          ·
            refine ⟨635019995539015210036003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 846693327385353613381337 635019995539015210036003)
            ·
              refine ⟨952529993308522815054005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 635019995539015210036003 952529993308522815054005)
              ·
                refine ⟨89299686872674013911313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 952529993308522815054005 89299686872674013911313)
                ·
                  rfl

theorem cell20_586948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 1, 5].length) (baseStart_586948 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_586948 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_586948 prefixEnd_586948 := by exact prefixLift 586948
  have htrace : WordTrace (prefixWord ++ tailWord_586948) baseStart_586948 baseEnd_586948 := by
    simpa [prefixWord, tailWord_586948, baseEnd_586948] using wordTrace_append hprefix tailTrace_586948
  have hstable : (prefixWord ++ tailWord_586948).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586948).length < 2 ^ (prefixWord ++ tailWord_586948).sum := by decide
  have hdescent : baseEnd_586948 < baseStart_586948 := by decide
  rcases family_descends (prefixWord ++ tailWord_586948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_586952 : List Nat := [2, 1, 3, 1, 2, 1, 5, 5]
def baseStart_586952 : Nat := 118140960795 + 586952 * 2 ^ 59
def prefixEnd_586952 : Nat := 4983230072969 + 3 ^ 40 * 586952 * 2
def baseEnd_586952 : Nat := 89300295442338601866863

theorem tailTrace_586952 : CollatzResearch.WordTrace tailWord_586952 prefixEnd_586952 89300295442338601866863 := by
  unfold tailWord_586952
  simp only [CollatzResearch.WordTrace]
  refine ⟨10703949084790311132961555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14271932113053748177282073 10703949084790311132961555)
  ·
    refine ⟨16055923627185466699442333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10703949084790311132961555 16055923627185466699442333)
    ·
      refine ⟨6020971360194550012290875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16055923627185466699442333 6020971360194550012290875)
      ·
        refine ⟨9031457040291825018436313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6020971360194550012290875 9031457040291825018436313)
        ·
          refine ⟨6773592780218868763827235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9031457040291825018436313 6773592780218868763827235)
          ·
            refine ⟨10160389170328303145740853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6773592780218868763827235 10160389170328303145740853)
            ·
              refine ⟨952536484718278419913205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10160389170328303145740853 952536484718278419913205)
              ·
                refine ⟨89300295442338601866863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 952536484718278419913205 89300295442338601866863)
                ·
                  rfl

theorem cell20_586952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5, 5].length) (baseStart_586952 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_586952 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_586952 prefixEnd_586952 := by exact prefixLift 586952
  have htrace : WordTrace (prefixWord ++ tailWord_586952) baseStart_586952 baseEnd_586952 := by
    simpa [prefixWord, tailWord_586952, baseEnd_586952] using wordTrace_append hprefix tailTrace_586952
  have hstable : (prefixWord ++ tailWord_586952).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_586952).length < 2 ^ (prefixWord ++ tailWord_586952).sum := by decide
  have hdescent : baseEnd_586952 < baseStart_586952 := by decide
  rcases family_descends (prefixWord ++ tailWord_586952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587059 : List Nat := [1, 1, 1, 2, 5, 2, 3, 1, 4]
def baseStart_587059 : Nat := 118140960795 + 587059 * 2 ^ 59
def prefixEnd_587059 : Nat := 4983230072969 + 3 ^ 40 * 587059 * 2
def baseEnd_587059 : Nat := 267949724042598989033485

theorem tailTrace_587059 : CollatzResearch.WordTrace tailWord_587059 prefixEnd_587059 267949724042598989033485 := by
  unfold tailWord_587059
  simp only [CollatzResearch.WordTrace]
  refine ⟨21411800780192979540068231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14274533853461986360045487 21411800780192979540068231)
  ·
    refine ⟨32117701170289469310102347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21411800780192979540068231 32117701170289469310102347)
    ·
      refine ⟨48176551755434203965153521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32117701170289469310102347 48176551755434203965153521)
      ·
        refine ⟨36132413816575652973865141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48176551755434203965153521 36132413816575652973865141)
        ·
          refine ⟨3387413795303967466299857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36132413816575652973865141 3387413795303967466299857)
          ·
            refine ⟨2540560346477975599724893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3387413795303967466299857 2540560346477975599724893)
            ·
              refine ⟨952710129929240849896835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2540560346477975599724893 952710129929240849896835)
              ·
                refine ⟨1429065194893861274845253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 952710129929240849896835 1429065194893861274845253)
                ·
                  refine ⟨267949724042598989033485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1429065194893861274845253 267949724042598989033485)
                  ·
                    rfl

theorem cell20_587059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3, 1, 4].length) (baseStart_587059 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_587059 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_587059 prefixEnd_587059 := by exact prefixLift 587059
  have htrace : WordTrace (prefixWord ++ tailWord_587059) baseStart_587059 baseEnd_587059 := by
    simpa [prefixWord, tailWord_587059, baseEnd_587059] using wordTrace_append hprefix tailTrace_587059
  have hstable : (prefixWord ++ tailWord_587059).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587059).length < 2 ^ (prefixWord ++ tailWord_587059).sum := by decide
  have hdescent : baseEnd_587059 < baseStart_587059 := by decide
  rcases family_descends (prefixWord ++ tailWord_587059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587065 : List Nat := [1, 2, 1, 6, 3, 1, 2, 1, 3]
def baseStart_587065 : Nat := 118140960795 + 587065 * 2 ^ 59
def prefixEnd_587065 : Nat := 4983230072969 + 3 ^ 40 * 587065 * 2
def baseEnd_587065 : Nat := 267952462606089634833461

theorem tailTrace_587065 : CollatzResearch.WordTrace tailWord_587065 prefixEnd_587065 267952462606089634833461 := by
  unfold tailWord_587065
  simp only [CollatzResearch.WordTrace]
  refine ⟨21412019618171242564786649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14274679745447495043191099 21412019618171242564786649)
  ·
    refine ⟨16059014713628431923589987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21412019618171242564786649 16059014713628431923589987)
    ·
      refine ⟨24088522070442647885384981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16059014713628431923589987 24088522070442647885384981)
      ·
        refine ⟨1129149472051999119627421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 24088522070442647885384981 1129149472051999119627421)
        ·
          refine ⟨423431052019499669860283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1129149472051999119627421 423431052019499669860283)
          ·
            refine ⟨635146578029249504790425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 423431052019499669860283 635146578029249504790425)
            ·
              refine ⟨476359933521937128592819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 635146578029249504790425 476359933521937128592819)
              ·
                refine ⟨714539900282905692889229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 476359933521937128592819 714539900282905692889229)
                ·
                  refine ⟨267952462606089634833461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 714539900282905692889229 267952462606089634833461)
                  ·
                    rfl

theorem cell20_587065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 2, 1, 3].length) (baseStart_587065 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_587065 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_587065 prefixEnd_587065 := by exact prefixLift 587065
  have htrace : WordTrace (prefixWord ++ tailWord_587065) baseStart_587065 baseEnd_587065 := by
    simpa [prefixWord, tailWord_587065, baseEnd_587065] using wordTrace_append hprefix tailTrace_587065
  have hstable : (prefixWord ++ tailWord_587065).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587065).length < 2 ^ (prefixWord ++ tailWord_587065).sum := by decide
  have hdescent : baseEnd_587065 < baseStart_587065 := by decide
  rcases family_descends (prefixWord ++ tailWord_587065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587066 : List Nat := [3, 1, 1, 1, 4, 1, 4, 5]
def baseStart_587066 : Nat := 118140960795 + 587066 * 2 ^ 59
def prefixEnd_587066 : Nat := 4983230072969 + 3 ^ 40 * 587066 * 2
def baseEnd_587066 : Nat := 89317639677779358600041

theorem tailTrace_587066 : CollatzResearch.WordTrace tailWord_587066 prefixEnd_587066 89317639677779358600041 := by
  unfold tailWord_587066
  simp only [CollatzResearch.WordTrace]
  refine ⟨5353014022791904933893263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14274704060778413157048701 5353014022791904933893263)
  ·
    refine ⟨8029521034187857400839895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5353014022791904933893263 8029521034187857400839895)
    ·
      refine ⟨12044281551281786101259843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8029521034187857400839895 12044281551281786101259843)
      ·
        refine ⟨18066422326922679151889765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12044281551281786101259843 18066422326922679151889765)
        ·
          refine ⟨3387454186298002340979331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18066422326922679151889765 3387454186298002340979331)
          ·
            refine ⟨5081181279447003511468997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3387454186298002340979331 5081181279447003511468997)
            ·
              refine ⟨952721489896313158400437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5081181279447003511468997 952721489896313158400437)
              ·
                refine ⟨89317639677779358600041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 952721489896313158400437 89317639677779358600041)
                ·
                  rfl

theorem cell20_587066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4, 5].length) (baseStart_587066 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_587066 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_587066 prefixEnd_587066 := by exact prefixLift 587066
  have htrace : WordTrace (prefixWord ++ tailWord_587066) baseStart_587066 baseEnd_587066 := by
    simpa [prefixWord, tailWord_587066, baseEnd_587066] using wordTrace_append hprefix tailTrace_587066
  have hstable : (prefixWord ++ tailWord_587066).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587066).length < 2 ^ (prefixWord ++ tailWord_587066).sum := by decide
  have hdescent : baseEnd_587066 < baseStart_587066 := by decide
  rcases family_descends (prefixWord ++ tailWord_587066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587080 : List Nat := [2, 1, 3, 1, 1, 2, 1, 3, 6]
def baseStart_587080 : Nat := 118140960795 + 587080 * 2 ^ 59
def prefixEnd_587080 : Nat := 4983230072969 + 3 ^ 40 * 587080 * 2
def baseEnd_587080 : Nat := 267959309014816249333399

theorem tailTrace_587080 : CollatzResearch.WordTrace tailWord_587080 prefixEnd_587080 267959309014816249333399 := by
  unfold tailWord_587080
  simp only [CollatzResearch.WordTrace]
  refine ⟨10706283356558450063291347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14275044475411266751055129 10706283356558450063291347)
  ·
    refine ⟨16059425034837675094937021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10706283356558450063291347 16059425034837675094937021)
    ·
      refine ⟨6022284388064128160601383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16059425034837675094937021 6022284388064128160601383)
      ·
        refine ⟨9033426582096192240902075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6022284388064128160601383 9033426582096192240902075)
        ·
          refine ⟨13550139873144288361353113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9033426582096192240902075 13550139873144288361353113)
          ·
            refine ⟨10162604904858216271014835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13550139873144288361353113 10162604904858216271014835)
            ·
              refine ⟨15243907357287324406522253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10162604904858216271014835 15243907357287324406522253)
              ·
                refine ⟨5716465258982746652445845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15243907357287324406522253 5716465258982746652445845)
                ·
                  refine ⟨267959309014816249333399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5716465258982746652445845 267959309014816249333399)
                  ·
                    rfl

theorem cell20_587080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 3, 6].length) (baseStart_587080 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_587080 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_587080 prefixEnd_587080 := by exact prefixLift 587080
  have htrace : WordTrace (prefixWord ++ tailWord_587080) baseStart_587080 baseEnd_587080 := by
    simpa [prefixWord, tailWord_587080, baseEnd_587080] using wordTrace_append hprefix tailTrace_587080
  have hstable : (prefixWord ++ tailWord_587080).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587080).length < 2 ^ (prefixWord ++ tailWord_587080).sum := by decide
  have hdescent : baseEnd_587080 < baseStart_587080 := by decide
  rcases family_descends (prefixWord ++ tailWord_587080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587187 : List Nat := [1, 1, 1, 2, 3, 1, 1, 7, 3]
def baseStart_587187 : Nat := 118140960795 + 587187 * 2 ^ 59
def prefixEnd_587187 : Nat := 4983230072969 + 3 ^ 40 * 587187 * 2
def baseEnd_587187 : Nat := 268008146730399432766295

theorem tailTrace_587187 : CollatzResearch.WordTrace tailWord_587187 prefixEnd_587187 268008146730399432766295 := by
  unfold tailWord_587187
  simp only [CollatzResearch.WordTrace]
  refine ⟨21416469323729257400727815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14277646215819504933818543 21416469323729257400727815)
  ·
    refine ⟨32124703985593886101091723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21416469323729257400727815 32124703985593886101091723)
    ·
      refine ⟨48187055978390829151637585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32124703985593886101091723 48187055978390829151637585)
      ·
        refine ⟨36140291983793121863728189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48187055978390829151637585 36140291983793121863728189)
        ·
          refine ⟨13552609493922420698898071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36140291983793121863728189 13552609493922420698898071)
          ·
            refine ⟨20328914240883631048347107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13552609493922420698898071 20328914240883631048347107)
            ·
              refine ⟨30493371361325446572520661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20328914240883631048347107 30493371361325446572520661)
              ·
                refine ⟨714688391281065154043453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 30493371361325446572520661 714688391281065154043453)
                ·
                  refine ⟨268008146730399432766295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 714688391281065154043453 268008146730399432766295)
                  ·
                    rfl

theorem cell20_587187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 7, 3].length) (baseStart_587187 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_587187 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_587187 prefixEnd_587187 := by exact prefixLift 587187
  have htrace : WordTrace (prefixWord ++ tailWord_587187) baseStart_587187 baseEnd_587187 := by
    simpa [prefixWord, tailWord_587187, baseEnd_587187] using wordTrace_append hprefix tailTrace_587187
  have hstable : (prefixWord ++ tailWord_587187).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587187).length < 2 ^ (prefixWord ++ tailWord_587187).sum := by decide
  have hdescent : baseEnd_587187 < baseStart_587187 := by decide
  rcases family_descends (prefixWord ++ tailWord_587187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587204 : List Nat := [2, 3, 3, 2, 1, 1, 1, 2, 5]
def baseStart_587204 : Nat := 118140960795 + 587204 * 2 ^ 59
def prefixEnd_587204 : Nat := 4983230072969 + 3 ^ 40 * 587204 * 2
def baseEnd_587204 : Nat := 268015905993622929199559

theorem tailTrace_587204 : CollatzResearch.WordTrace tailWord_587204 prefixEnd_587204 268015905993622929199559 := by
  unfold tailWord_587204
  simp only [CollatzResearch.WordTrace]
  refine ⟨10708544682333834652048333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14278059576445112869397777 10708544682333834652048333)
  ·
    refine ⟨4015704255875187994518125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10708544682333834652048333 4015704255875187994518125)
    ·
      refine ⟨1505889095953195497944297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4015704255875187994518125 1505889095953195497944297)
      ·
        refine ⟨1129416821964896623458223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1505889095953195497944297 1129416821964896623458223)
        ·
          refine ⟨1694125232947344935187335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1129416821964896623458223 1694125232947344935187335)
          ·
            refine ⟨2541187849421017402781003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1694125232947344935187335 2541187849421017402781003)
            ·
              refine ⟨3811781774131526104171505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2541187849421017402781003 3811781774131526104171505)
              ·
                refine ⟨2858836330598644578128629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3811781774131526104171505 2858836330598644578128629)
                ·
                  refine ⟨268015905993622929199559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2858836330598644578128629 268015905993622929199559)
                  ·
                    rfl

theorem cell20_587204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 2, 5].length) (baseStart_587204 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_587204 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_587204 prefixEnd_587204 := by exact prefixLift 587204
  have htrace : WordTrace (prefixWord ++ tailWord_587204) baseStart_587204 baseEnd_587204 := by
    simpa [prefixWord, tailWord_587204, baseEnd_587204] using wordTrace_append hprefix tailTrace_587204
  have hstable : (prefixWord ++ tailWord_587204).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587204).length < 2 ^ (prefixWord ++ tailWord_587204).sum := by decide
  have hdescent : baseEnd_587204 < baseStart_587204 := by decide
  rcases family_descends (prefixWord ++ tailWord_587204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587225 : List Nat := [1, 2, 1, 2, 4, 2, 2, 1, 5]
def baseStart_587225 : Nat := 118140960795 + 587225 * 2 ^ 59
def prefixEnd_587225 : Nat := 4983230072969 + 3 ^ 40 * 587225 * 2
def baseEnd_587225 : Nat := 268025490965840189499473

theorem tailTrace_587225 : CollatzResearch.WordTrace tailWord_587225 prefixEnd_587225 268025490965840189499473 := by
  unfold tailWord_587225
  simp only [CollatzResearch.WordTrace]
  refine ⟨21417855297591589890611129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14278570198394393260407419 21417855297591589890611129)
  ·
    refine ⟨16063391473193692417958347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21417855297591589890611129 16063391473193692417958347)
    ·
      refine ⟨24095087209790538626937521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16063391473193692417958347 24095087209790538626937521)
      ·
        refine ⟨18071315407342903970203141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24095087209790538626937521 18071315407342903970203141)
        ·
          refine ⟨3388371638876794494413089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18071315407342903970203141 3388371638876794494413089)
          ·
            refine ⟨2541278729157595870809817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3388371638876794494413089 2541278729157595870809817)
            ·
              refine ⟨1905959046868196903107363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2541278729157595870809817 1905959046868196903107363)
              ·
                refine ⟨2858938570302295354661045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1905959046868196903107363 2858938570302295354661045)
                ·
                  refine ⟨268025490965840189499473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2858938570302295354661045 268025490965840189499473)
                  ·
                    rfl

theorem cell20_587225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 1, 5].length) (baseStart_587225 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_587225 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_587225 prefixEnd_587225 := by exact prefixLift 587225
  have htrace : WordTrace (prefixWord ++ tailWord_587225) baseStart_587225 baseEnd_587225 := by
    simpa [prefixWord, tailWord_587225, baseEnd_587225] using wordTrace_append hprefix tailTrace_587225
  have hstable : (prefixWord ++ tailWord_587225).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587225).length < 2 ^ (prefixWord ++ tailWord_587225).sum := by decide
  have hdescent : baseEnd_587225 < baseStart_587225 := by decide
  rcases family_descends (prefixWord ++ tailWord_587225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587232 : List Nat := [2, 1, 1, 3, 1, 1, 2, 5, 4]
def baseStart_587232 : Nat := 118140960795 + 587232 * 2 ^ 59
def prefixEnd_587232 : Nat := 4983230072969 + 3 ^ 40 * 587232 * 2
def baseEnd_587232 : Nat := 268028685956579276266111

theorem tailTrace_587232 : CollatzResearch.WordTrace tailWord_587232 prefixEnd_587232 268028685956579276266111 := by
  unfold tailWord_587232
  simp only [CollatzResearch.WordTrace]
  refine ⟨10709055304283115043057975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14278740405710820057410633 10709055304283115043057975)
  ·
    refine ⟨16063582956424672564586963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10709055304283115043057975 16063582956424672564586963)
    ·
      refine ⟨24095374434637008846880445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16063582956424672564586963 24095374434637008846880445)
      ·
        refine ⟨9035765412988878317580167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24095374434637008846880445 9035765412988878317580167)
        ·
          refine ⟨13553648119483317476370251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9035765412988878317580167 13553648119483317476370251)
          ·
            refine ⟨20330472179224976214555377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13553648119483317476370251 20330472179224976214555377)
            ·
              refine ⟨15247854134418732160916533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20330472179224976214555377 15247854134418732160916533)
              ·
                refine ⟨1429486325101756140085925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15247854134418732160916533 1429486325101756140085925)
                ·
                  refine ⟨268028685956579276266111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1429486325101756140085925 268028685956579276266111)
                  ·
                    rfl

theorem cell20_587232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 5, 4].length) (baseStart_587232 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_587232 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_587232 prefixEnd_587232 := by exact prefixLift 587232
  have htrace : WordTrace (prefixWord ++ tailWord_587232) baseStart_587232 baseEnd_587232 := by
    simpa [prefixWord, tailWord_587232, baseEnd_587232] using wordTrace_append hprefix tailTrace_587232
  have hstable : (prefixWord ++ tailWord_587232).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587232).length < 2 ^ (prefixWord ++ tailWord_587232).sum := by decide
  have hdescent : baseEnd_587232 < baseStart_587232 := by decide
  rcases family_descends (prefixWord ++ tailWord_587232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587283 : List Nat := [1, 1, 1, 2, 1, 8, 2, 2, 2]
def baseStart_587283 : Nat := 118140960795 + 587283 * 2 ^ 59
def prefixEnd_587283 : Nat := 4983230072969 + 3 ^ 40 * 587283 * 2
def baseEnd_587283 : Nat := 268051963746249765565903

theorem tailTrace_587283 : CollatzResearch.WordTrace tailWord_587283 prefixEnd_587283 268051963746249765565903 := by
  unfold tailWord_587283
  simp only [CollatzResearch.WordTrace]
  refine ⟨21419970731381465796222503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14279980487587643864148335 21419970731381465796222503)
  ·
    refine ⟨32129956097072198694333755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21419970731381465796222503 32129956097072198694333755)
    ·
      refine ⟨48194934145608298041500633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32129956097072198694333755 48194934145608298041500633)
      ·
        refine ⟨36146200609206223531125475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48194934145608298041500633 36146200609206223531125475)
        ·
          refine ⟨54219300913809335296688213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36146200609206223531125475 54219300913809335296688213)
          ·
            refine ⟨635382432583703148008065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 54219300913809335296688213 635382432583703148008065)
            ·
              refine ⟨476536824437777361006049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 635382432583703148008065 476536824437777361006049)
              ·
                refine ⟨357402618328333020754537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 476536824437777361006049 357402618328333020754537)
                ·
                  refine ⟨268051963746249765565903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 357402618328333020754537 268051963746249765565903)
                  ·
                    rfl

theorem cell20_587283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 2, 2, 2].length) (baseStart_587283 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_587283 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_587283 prefixEnd_587283 := by exact prefixLift 587283
  have htrace : WordTrace (prefixWord ++ tailWord_587283) baseStart_587283 baseEnd_587283 := by
    simpa [prefixWord, tailWord_587283, baseEnd_587283] using wordTrace_append hprefix tailTrace_587283
  have hstable : (prefixWord ++ tailWord_587283).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587283).length < 2 ^ (prefixWord ++ tailWord_587283).sum := by decide
  have hdescent : baseEnd_587283 < baseStart_587283 := by decide
  rcases family_descends (prefixWord ++ tailWord_587283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587304 : List Nat := [2, 1, 5, 2, 2, 1, 1, 2, 4]
def baseStart_587304 : Nat := 118140960795 + 587304 * 2 ^ 59
def prefixEnd_587304 : Nat := 4983230072969 + 3 ^ 40 * 587304 * 2
def baseEnd_587304 : Nat := 268061548718467025865817

theorem tailTrace_587304 : CollatzResearch.WordTrace tailWord_587304 prefixEnd_587304 268061548718467025865817 := by
  unfold tailWord_587304
  simp only [CollatzResearch.WordTrace]
  refine ⟨10710368332152693191368483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14280491109536924255157977 10710368332152693191368483)
  ·
    refine ⟨16065552498229039787052725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10710368332152693191368483 16065552498229039787052725)
    ·
      refine ⟨1506145546708972480036193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16065552498229039787052725 1506145546708972480036193)
      ·
        refine ⟨1129609160031729360027145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1506145546708972480036193 1129609160031729360027145)
        ·
          refine ⟨847206870023797020020359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1129609160031729360027145 847206870023797020020359)
          ·
            refine ⟨1270810305035695530030539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 847206870023797020020359 1270810305035695530030539)
            ·
              refine ⟨1906215457553543295045809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1270810305035695530030539 1906215457553543295045809)
              ·
                refine ⟨1429661593165157471284357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1906215457553543295045809 1429661593165157471284357)
                ·
                  refine ⟨268061548718467025865817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1429661593165157471284357 268061548718467025865817)
                  ·
                    rfl

theorem cell20_587304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 2, 4].length) (baseStart_587304 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_587304 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_587304 prefixEnd_587304 := by exact prefixLift 587304
  have htrace : WordTrace (prefixWord ++ tailWord_587304) baseStart_587304 baseEnd_587304 := by
    simpa [prefixWord, tailWord_587304, baseEnd_587304] using wordTrace_append hprefix tailTrace_587304
  have hstable : (prefixWord ++ tailWord_587304).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587304).length < 2 ^ (prefixWord ++ tailWord_587304).sum := by decide
  have hdescent : baseEnd_587304 < baseStart_587304 := by decide
  rcases family_descends (prefixWord ++ tailWord_587304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587335 : List Nat := [1, 1, 4, 1, 5, 2, 1, 2, 3]
def baseStart_587335 : Nat := 118140960795 + 587335 * 2 ^ 59
def prefixEnd_587335 : Nat := 4983230072969 + 3 ^ 40 * 587335 * 2
def baseEnd_587335 : Nat := 268075697963168695832357

theorem tailTrace_587335 : CollatzResearch.WordTrace tailWord_587335 prefixEnd_587335 268075697963168695832357 := by
  unfold tailWord_587335
  simp only [CollatzResearch.WordTrace]
  refine ⟨21421867327193078677115459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14281244884795385784743639 21421867327193078677115459)
  ·
    refine ⟨32132800990789618015673189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21421867327193078677115459 32132800990789618015673189)
    ·
      refine ⟨6024900185773053377938723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32132800990789618015673189 6024900185773053377938723)
      ·
        refine ⟨9037350278659580066908085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6024900185773053377938723 9037350278659580066908085)
        ·
          refine ⟨847251588624335631272633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9037350278659580066908085 847251588624335631272633)
          ·
            refine ⟨635438691468251723454475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 847251588624335631272633 635438691468251723454475)
            ·
              refine ⟨953158037202377585181713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 635438691468251723454475 953158037202377585181713)
              ·
                refine ⟨714868527901783188886285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 953158037202377585181713 714868527901783188886285)
                ·
                  refine ⟨268075697963168695832357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 714868527901783188886285 268075697963168695832357)
                  ·
                    rfl

theorem cell20_587335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 1, 2, 3].length) (baseStart_587335 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_587335 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_587335 prefixEnd_587335 := by exact prefixLift 587335
  have htrace : WordTrace (prefixWord ++ tailWord_587335) baseStart_587335 baseEnd_587335 := by
    simpa [prefixWord, tailWord_587335, baseEnd_587335] using wordTrace_append hprefix tailTrace_587335
  have hstable : (prefixWord ++ tailWord_587335).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587335).length < 2 ^ (prefixWord ++ tailWord_587335).sum := by decide
  have hdescent : baseEnd_587335 < baseStart_587335 := by decide
  rcases family_descends (prefixWord ++ tailWord_587335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587370 : List Nat := [3, 1, 3, 2, 1, 3, 1, 6]
def baseStart_587370 : Nat := 118140960795 + 587370 * 2 ^ 59
def prefixEnd_587370 : Nat := 4983230072969 + 3 ^ 40 * 587370 * 2
def baseEnd_587370 : Nat := 89363890972288043221849

theorem tailTrace_587370 : CollatzResearch.WordTrace tailWord_587370 prefixEnd_587370 89363890972288043221849 := by
  unfold tailWord_587370
  simp only [CollatzResearch.WordTrace]
  refine ⟨5355785970516569913659891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14282095921377519769759709 5355785970516569913659891)
  ·
    refine ⟨8033678955774854870489837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5355785970516569913659891 8033678955774854870489837)
    ·
      refine ⟨3012629608415570576433689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8033678955774854870489837 3012629608415570576433689)
      ·
        refine ⟨2259472206311677932325267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3012629608415570576433689 2259472206311677932325267)
        ·
          refine ⟨3389208309467516898487901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2259472206311677932325267 3389208309467516898487901)
          ·
            refine ⟨1270953116050318836932963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3389208309467516898487901 1270953116050318836932963)
            ·
              refine ⟨1906429674075478255399445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1270953116050318836932963 1906429674075478255399445)
              ·
                refine ⟨89363890972288043221849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1906429674075478255399445 89363890972288043221849)
                ·
                  rfl

theorem cell20_587370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 6].length) (baseStart_587370 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_587370 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_587370 prefixEnd_587370 := by exact prefixLift 587370
  have htrace : WordTrace (prefixWord ++ tailWord_587370) baseStart_587370 baseEnd_587370 := by
    simpa [prefixWord, tailWord_587370, baseEnd_587370] using wordTrace_append hprefix tailTrace_587370
  have hstable : (prefixWord ++ tailWord_587370).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587370).length < 2 ^ (prefixWord ++ tailWord_587370).sum := by decide
  have hdescent : baseEnd_587370 < baseStart_587370 := by decide
  rcases family_descends (prefixWord ++ tailWord_587370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587401 : List Nat := [1, 2, 1, 1, 4, 1, 2, 6, 2]
def baseStart_587401 : Nat := 118140960795 + 587401 * 2 ^ 59
def prefixEnd_587401 : Nat := 4983230072969 + 3 ^ 40 * 587401 * 2
def baseEnd_587401 : Nat := 268105822161565799632087

theorem tailTrace_587401 : CollatzResearch.WordTrace tailWord_587401 prefixEnd_587401 268105822161565799632087 := by
  unfold tailWord_587401
  simp only [CollatzResearch.WordTrace]
  refine ⟨21424274544953971949018057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14282849696635981299345371 21424274544953971949018057)
  ·
    refine ⟨16068205908715478961763543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21424274544953971949018057 16068205908715478961763543)
    ·
      refine ⟨24102308863073218442645315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16068205908715478961763543 24102308863073218442645315)
      ·
        refine ⟨36153463294609827663967973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24102308863073218442645315 36153463294609827663967973)
        ·
          refine ⟨6778774367739342686993995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36153463294609827663967973 6778774367739342686993995)
          ·
            refine ⟨10168161551609014030490993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6778774367739342686993995 10168161551609014030490993)
            ·
              refine ⟨7626121163706760522868245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10168161551609014030490993 7626121163706760522868245)
              ·
                refine ⟨357474429548754399509449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7626121163706760522868245 357474429548754399509449)
                ·
                  refine ⟨268105822161565799632087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 357474429548754399509449 268105822161565799632087)
                  ·
                    rfl

theorem cell20_587401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 6, 2].length) (baseStart_587401 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_587401 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_587401 prefixEnd_587401 := by exact prefixLift 587401
  have htrace : WordTrace (prefixWord ++ tailWord_587401) baseStart_587401 baseEnd_587401 := by
    simpa [prefixWord, tailWord_587401, baseEnd_587401] using wordTrace_append hprefix tailTrace_587401
  have hstable : (prefixWord ++ tailWord_587401).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587401).length < 2 ^ (prefixWord ++ tailWord_587401).sum := by decide
  have hdescent : baseEnd_587401 < baseStart_587401 := by decide
  rcases family_descends (prefixWord ++ tailWord_587401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587429 : List Nat := [1, 3, 1, 2, 1, 2, 4, 6]
def baseStart_587429 : Nat := 118140960795 + 587429 * 2 ^ 59
def prefixEnd_587429 : Nat := 4983230072969 + 3 ^ 40 * 587429 * 2
def baseEnd_587429 : Nat := 89372867374840715566213

theorem tailTrace_587429 : CollatzResearch.WordTrace tailWord_587429 prefixEnd_587429 89372867374840715566213 := by
  unfold tailWord_587429
  simp only [CollatzResearch.WordTrace]
  refine ⟨21425295788852532731037341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14283530525901688487358227 21425295788852532731037341)
  ·
    refine ⟨8034485920819699774139003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21425295788852532731037341 8034485920819699774139003)
    ·
      refine ⟨12051728881229549661208505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8034485920819699774139003 12051728881229549661208505)
      ·
        refine ⟨9038796660922162245906379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12051728881229549661208505 9038796660922162245906379)
        ·
          refine ⟨13558194991383243368859569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9038796660922162245906379 13558194991383243368859569)
          ·
            refine ⟨10168646243537432526644677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13558194991383243368859569 10168646243537432526644677)
            ·
              refine ⟨1906621170663268598745877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10168646243537432526644677 1906621170663268598745877)
              ·
                refine ⟨89372867374840715566213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1906621170663268598745877 89372867374840715566213)
                ·
                  rfl

theorem cell20_587429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 6].length) (baseStart_587429 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_587429 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_587429 prefixEnd_587429 := by exact prefixLift 587429
  have htrace : WordTrace (prefixWord ++ tailWord_587429) baseStart_587429 baseEnd_587429 := by
    simpa [prefixWord, tailWord_587429, baseEnd_587429] using wordTrace_append hprefix tailTrace_587429
  have hstable : (prefixWord ++ tailWord_587429).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587429).length < 2 ^ (prefixWord ++ tailWord_587429).sum := by decide
  have hdescent : baseEnd_587429 < baseStart_587429 := by decide
  rcases family_descends (prefixWord ++ tailWord_587429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587439 : List Nat := [1, 1, 2, 1, 2, 4, 2, 5, 2]
def baseStart_587439 : Nat := 118140960795 + 587439 * 2 ^ 59
def prefixEnd_587439 : Nat := 4983230072969 + 3 ^ 40 * 587439 * 2
def baseEnd_587439 : Nat := 268123166397006556365265

theorem tailTrace_587439 : CollatzResearch.WordTrace tailWord_587439 prefixEnd_587439 268123166397006556365265 := by
  unfold tailWord_587439
  simp only [CollatzResearch.WordTrace]
  refine ⟨21425660518816304438901371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14283773679210869625934247 21425660518816304438901371)
  ·
    refine ⟨32138490778224456658352057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21425660518816304438901371 32138490778224456658352057)
    ·
      refine ⟨24103868083668342493764043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32138490778224456658352057 24103868083668342493764043)
      ·
        refine ⟨36155802125502513740646065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24103868083668342493764043 36155802125502513740646065)
        ·
          refine ⟨27116851594126885305484549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36155802125502513740646065 27116851594126885305484549)
          ·
            refine ⟨5084409673898790994778353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27116851594126885305484549 5084409673898790994778353)
            ·
              refine ⟨3813307255424093246083765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5084409673898790994778353 3813307255424093246083765)
              ·
                refine ⟨357497555196008741820353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3813307255424093246083765 357497555196008741820353)
                ·
                  refine ⟨268123166397006556365265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 357497555196008741820353 268123166397006556365265)
                  ·
                    rfl

theorem cell20_587439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 5, 2].length) (baseStart_587439 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_587439 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_587439 prefixEnd_587439 := by exact prefixLift 587439
  have htrace : WordTrace (prefixWord ++ tailWord_587439) baseStart_587439 baseEnd_587439 := by
    simpa [prefixWord, tailWord_587439, baseEnd_587439] using wordTrace_append hprefix tailTrace_587439
  have hstable : (prefixWord ++ tailWord_587439).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587439).length < 2 ^ (prefixWord ++ tailWord_587439).sum := by decide
  have hdescent : baseEnd_587439 < baseStart_587439 := by decide
  rcases family_descends (prefixWord ++ tailWord_587439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587505 : List Nat := [1, 2, 2, 2, 2, 4, 7]
def baseStart_587505 : Nat := 118140960795 + 587505 * 2 ^ 59
def prefixEnd_587505 : Nat := 4983230072969 + 3 ^ 40 * 587505 * 2
def baseEnd_587505 : Nat := 29794810066155962240555

theorem tailTrace_587505 : CollatzResearch.WordTrace tailWord_587505 prefixEnd_587505 29794810066155962240555 := by
  unfold tailWord_587505
  simp only [CollatzResearch.WordTrace]
  refine ⟨21428067736577197710803969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14285378491051465140535979 21428067736577197710803969)
  ·
    refine ⟨16071050802432898283102977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21428067736577197710803969 16071050802432898283102977)
    ·
      refine ⟨12053288101824673712327233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16071050802432898283102977 12053288101824673712327233)
      ·
        refine ⟨9039966076368505284245425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12053288101824673712327233 9039966076368505284245425)
        ·
          refine ⟨6779974557276378963184069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9039966076368505284245425 6779974557276378963184069)
          ·
            refine ⟨1271245229489321055597013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6779974557276378963184069 1271245229489321055597013)
            ·
              refine ⟨29794810066155962240555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1271245229489321055597013 29794810066155962240555)
              ·
                rfl

theorem cell20_587505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 7].length) (baseStart_587505 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_587505 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_587505 prefixEnd_587505 := by exact prefixLift 587505
  have htrace : WordTrace (prefixWord ++ tailWord_587505) baseStart_587505 baseEnd_587505 := by
    simpa [prefixWord, tailWord_587505, baseEnd_587505] using wordTrace_append hprefix tailTrace_587505
  have hstable : (prefixWord ++ tailWord_587505).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587505).length < 2 ^ (prefixWord ++ tailWord_587505).sum := by decide
  have hdescent : baseEnd_587505 < baseStart_587505 := by decide
  rcases family_descends (prefixWord ++ tailWord_587505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587522 : List Nat := [3, 4, 1, 1, 1, 1, 2, 7]
def baseStart_587522 : Nat := 118140960795 + 587522 * 2 ^ 59
def prefixEnd_587522 : Nat := 4983230072969 + 3 ^ 40 * 587522 * 2
def baseEnd_587522 : Nat := 89387016619542385532753

theorem tailTrace_587522 : CollatzResearch.WordTrace tailWord_587522 prefixEnd_587522 89387016619542385532753 := by
  unfold tailWord_587522
  simp only [CollatzResearch.WordTrace]
  refine ⟨5357171944378902403543205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14285791851677073076115213 5357171944378902403543205)
  ·
    refine ⟨1004469739571044200664351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5357171944378902403543205 1004469739571044200664351)
    ·
      refine ⟨1506704609356566300996527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1004469739571044200664351 1506704609356566300996527)
      ·
        refine ⟨2260056914034849451494791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1506704609356566300996527 2260056914034849451494791)
        ·
          refine ⟨3390085371052274177242187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2260056914034849451494791 3390085371052274177242187)
          ·
            refine ⟨5085128056578411265863281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3390085371052274177242187 5085128056578411265863281)
            ·
              refine ⟨3813846042433808449397461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5085128056578411265863281 3813846042433808449397461)
              ·
                refine ⟨89387016619542385532753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3813846042433808449397461 89387016619542385532753)
                ·
                  rfl

theorem cell20_587522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 7].length) (baseStart_587522 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_587522 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_587522 prefixEnd_587522 := by exact prefixLift 587522
  have htrace : WordTrace (prefixWord ++ tailWord_587522) baseStart_587522 baseEnd_587522 := by
    simpa [prefixWord, tailWord_587522, baseEnd_587522] using wordTrace_append hprefix tailTrace_587522
  have hstable : (prefixWord ++ tailWord_587522).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587522).length < 2 ^ (prefixWord ++ tailWord_587522).sum := by decide
  have hdescent : baseEnd_587522 < baseStart_587522 := by decide
  rcases family_descends (prefixWord ++ tailWord_587522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587560 : List Nat := [2, 1, 5, 1, 1, 4, 6]
def baseStart_587560 : Nat := 118140960795 + 587560 * 2 ^ 59
def prefixEnd_587560 : Nat := 4983230072969 + 3 ^ 40 * 587560 * 2
def baseEnd_587560 : Nat := 29797599343785323703493

theorem tailTrace_587560 : CollatzResearch.WordTrace tailWord_587560 prefixEnd_587560 29797599343785323703493 := by
  unfold tailWord_587560
  simp only [CollatzResearch.WordTrace]
  refine ⟨10715036875688971052028067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14286715834251961402704089 10715036875688971052028067)
  ·
    refine ⟨16072555313533456578042101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10715036875688971052028067 16072555313533456578042101)
    ·
      refine ⟨1506802060643761554191447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16072555313533456578042101 1506802060643761554191447)
      ·
        refine ⟨2260203090965642331287171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1506802060643761554191447 2260203090965642331287171)
        ·
          refine ⟨3390304636448463496930757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2260203090965642331287171 3390304636448463496930757)
          ·
            refine ⟨635682119334086905674517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3390304636448463496930757 635682119334086905674517)
            ·
              refine ⟨29797599343785323703493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 635682119334086905674517 29797599343785323703493)
              ·
                rfl

theorem cell20_587560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 6].length) (baseStart_587560 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_587560 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_587560 prefixEnd_587560 := by exact prefixLift 587560
  have htrace : WordTrace (prefixWord ++ tailWord_587560) baseStart_587560 baseEnd_587560 := by
    simpa [prefixWord, tailWord_587560, baseEnd_587560] using wordTrace_append hprefix tailTrace_587560
  have hstable : (prefixWord ++ tailWord_587560).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587560).length < 2 ^ (prefixWord ++ tailWord_587560).sum := by decide
  have hdescent : baseEnd_587560 < baseStart_587560 := by decide
  rcases family_descends (prefixWord ++ tailWord_587560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587566 : List Nat := [4, 1, 3, 2, 2, 1, 3, 2, 2]
def baseStart_587566 : Nat := 118140960795 + 587566 * 2 ^ 59
def prefixEnd_587566 : Nat := 4983230072969 + 3 ^ 40 * 587566 * 2
def baseEnd_587566 : Nat := 268181132657558559131413

theorem tailTrace_587566 : CollatzResearch.WordTrace tailWord_587566 prefixEnd_587566 268181132657558559131413 := by
  unfold tailWord_587566
  simp only [CollatzResearch.WordTrace]
  refine ⟨2678786573669525641096819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14286861726237470085849701 2678786573669525641096819)
  ·
    refine ⟨4018179860504288461645229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2678786573669525641096819 4018179860504288461645229)
    ·
      refine ⟨1506817447689108173116961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4018179860504288461645229 1506817447689108173116961)
      ·
        refine ⟨1130113085766831129837721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1506817447689108173116961 1130113085766831129837721)
        ·
          refine ⟨847584814325123347378291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1130113085766831129837721 847584814325123347378291)
          ·
            refine ⟨1271377221487685021067437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 847584814325123347378291 1271377221487685021067437)
            ·
              refine ⟨476766458057881882900289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1271377221487685021067437 476766458057881882900289)
              ·
                refine ⟨357574843543411412175217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 476766458057881882900289 357574843543411412175217)
                ·
                  refine ⟨268181132657558559131413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 357574843543411412175217 268181132657558559131413)
                  ·
                    rfl

theorem cell20_587566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 3, 2, 2].length) (baseStart_587566 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_587566 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_587566 prefixEnd_587566 := by exact prefixLift 587566
  have htrace : WordTrace (prefixWord ++ tailWord_587566) baseStart_587566 baseEnd_587566 := by
    simpa [prefixWord, tailWord_587566, baseEnd_587566] using wordTrace_append hprefix tailTrace_587566
  have hstable : (prefixWord ++ tailWord_587566).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587566).length < 2 ^ (prefixWord ++ tailWord_587566).sum := by decide
  have hdescent : baseEnd_587566 < baseStart_587566 := by decide
  rcases family_descends (prefixWord ++ tailWord_587566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587577 : List Nat := [1, 2, 1, 7, 1, 1, 2, 5]
def baseStart_587577 : Nat := 118140960795 + 587577 * 2 ^ 59
def prefixEnd_587577 : Nat := 4983230072969 + 3 ^ 40 * 587577 * 2
def baseEnd_587577 : Nat := 89395384452430469921567

theorem tailTrace_587577 : CollatzResearch.WordTrace tailWord_587577 prefixEnd_587577 89395384452430469921567 := by
  unfold tailWord_587577
  simp only [CollatzResearch.WordTrace]
  refine ⟨21430693792316354007424985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14287129194877569338283323 21430693792316354007424985)
  ·
    refine ⟨16073020344237265505568739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21430693792316354007424985 16073020344237265505568739)
    ·
      refine ⟨24109530516355898258353109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16073020344237265505568739 24109530516355898258353109)
      ·
        refine ⟨565067121477091365430151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 24109530516355898258353109 565067121477091365430151)
        ·
          refine ⟨847600682215637048145227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 565067121477091365430151 847600682215637048145227)
          ·
            refine ⟨1271401023323455572217841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 847600682215637048145227 1271401023323455572217841)
            ·
              refine ⟨953550767492591679163381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1271401023323455572217841 953550767492591679163381)
              ·
                refine ⟨89395384452430469921567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 953550767492591679163381 89395384452430469921567)
                ·
                  rfl

theorem cell20_587577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 2, 5].length) (baseStart_587577 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_587577 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_587577 prefixEnd_587577 := by exact prefixLift 587577
  have htrace : WordTrace (prefixWord ++ tailWord_587577) baseStart_587577 baseEnd_587577 := by
    simpa [prefixWord, tailWord_587577, baseEnd_587577] using wordTrace_append hprefix tailTrace_587577
  have hstable : (prefixWord ++ tailWord_587577).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587577).length < 2 ^ (prefixWord ++ tailWord_587577).sum := by decide
  have hdescent : baseEnd_587577 < baseStart_587577 := by decide
  rcases family_descends (prefixWord ++ tailWord_587577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587619 : List Nat := [1, 1, 1, 5, 4, 8]
def baseStart_587619 : Nat := 118140960795 + 587619 * 2 ^ 59
def prefixEnd_587619 : Nat := 4983230072969 + 3 ^ 40 * 587619 * 2
def baseEnd_587619 : Nat := 9933530492656515939427

theorem tailTrace_587619 : CollatzResearch.WordTrace tailWord_587619 prefixEnd_587619 9933530492656515939427 := by
  unfold tailWord_587619
  simp only [CollatzResearch.WordTrace]
  refine ⟨21432225658164195180453911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14288150438776130120302607 21432225658164195180453911)
  ·
    refine ⟨32148338487246292770680867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21432225658164195180453911 32148338487246292770680867)
    ·
      refine ⟨48222507730869439156021301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32148338487246292770680867 48222507730869439156021301)
      ·
        refine ⟨4520860099769009920876997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 48222507730869439156021301 4520860099769009920876997)
        ·
          refine ⟨847661268706689360164437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4520860099769009920876997 847661268706689360164437)
          ·
            refine ⟨9933530492656515939427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 847661268706689360164437 9933530492656515939427)
            ·
              rfl

theorem cell20_587619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 8].length) (baseStart_587619 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_587619 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_587619 prefixEnd_587619 := by exact prefixLift 587619
  have htrace : WordTrace (prefixWord ++ tailWord_587619) baseStart_587619 baseEnd_587619 := by
    simpa [prefixWord, tailWord_587619, baseEnd_587619] using wordTrace_append hprefix tailTrace_587619
  have hstable : (prefixWord ++ tailWord_587619).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587619).length < 2 ^ (prefixWord ++ tailWord_587619).sum := by decide
  have hdescent : baseEnd_587619 < baseStart_587619 := by decide
  rcases family_descends (prefixWord ++ tailWord_587619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587646 : List Nat := [4, 2, 3, 1, 1, 2, 1, 2, 4]
def baseStart_587646 : Nat := 118140960795 + 587646 * 2 ^ 59
def prefixEnd_587646 : Nat := 4983230072969 + 3 ^ 40 * 587646 * 2
def baseEnd_587646 : Nat := 268217646837433836464419

theorem tailTrace_587646 : CollatzResearch.WordTrace tailWord_587646 prefixEnd_587646 268217646837433836464419 := by
  unfold tailWord_587646
  simp only [CollatzResearch.WordTrace]
  refine ⟨2679151303633297348960849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14288806952710919194457861 2679151303633297348960849)
  ·
    refine ⟨2009363477724973011720637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2679151303633297348960849 2009363477724973011720637)
    ·
      refine ⟨753511304146864879395239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2009363477724973011720637 753511304146864879395239)
      ·
        refine ⟨1130266956220297319092859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 753511304146864879395239 1130266956220297319092859)
        ·
          refine ⟨1695400434330445978639289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1130266956220297319092859 1695400434330445978639289)
          ·
            refine ⟨1271550325747834483979467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1695400434330445978639289 1271550325747834483979467)
            ·
              refine ⟨1907325488621751725969201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1271550325747834483979467 1907325488621751725969201)
              ·
                refine ⟨1430494116466313794476901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1907325488621751725969201 1430494116466313794476901)
                ·
                  refine ⟨268217646837433836464419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1430494116466313794476901 268217646837433836464419)
                  ·
                    rfl

theorem cell20_587646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 2, 4].length) (baseStart_587646 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_587646 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_587646 prefixEnd_587646 := by exact prefixLift 587646
  have htrace : WordTrace (prefixWord ++ tailWord_587646) baseStart_587646 baseEnd_587646 := by
    simpa [prefixWord, tailWord_587646, baseEnd_587646] using wordTrace_append hprefix tailTrace_587646
  have hstable : (prefixWord ++ tailWord_587646).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587646).length < 2 ^ (prefixWord ++ tailWord_587646).sum := by decide
  have hdescent : baseEnd_587646 < baseStart_587646 := by decide
  rcases family_descends (prefixWord ++ tailWord_587646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587670 : List Nat := [5, 3, 1, 1, 2, 1, 7]
def baseStart_587670 : Nat := 118140960795 + 587670 * 2 ^ 59
def prefixEnd_587670 : Nat := 4983230072969 + 3 ^ 40 * 587670 * 2
def baseEnd_587670 : Nat := 29803177899044046629369

theorem tailTrace_587670 : CollatzResearch.WordTrace tailWord_587670 prefixEnd_587670 29803177899044046629369 := by
  unfold tailWord_587670
  simp only [CollatzResearch.WordTrace]
  refine ⟨1339630361311214430660029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14289390520652953927040309 1339630361311214430660029)
  ·
    refine ⟨502361385491705411497511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1339630361311214430660029 502361385491705411497511)
    ·
      refine ⟨753542078237558117246267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 502361385491705411497511 753542078237558117246267)
      ·
        refine ⟨1130313117356337175869401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 753542078237558117246267 1130313117356337175869401)
        ·
          refine ⟨847734838017252881902051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1130313117356337175869401 847734838017252881902051)
          ·
            refine ⟨1271602257025879322853077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 847734838017252881902051 1271602257025879322853077)
            ·
              refine ⟨29803177899044046629369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1271602257025879322853077 29803177899044046629369)
              ·
                rfl

theorem cell20_587670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 7].length) (baseStart_587670 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_587670 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_587670 prefixEnd_587670 := by exact prefixLift 587670
  have htrace : WordTrace (prefixWord ++ tailWord_587670) baseStart_587670 baseEnd_587670 := by
    simpa [prefixWord, tailWord_587670, baseEnd_587670] using wordTrace_append hprefix tailTrace_587670
  have hstable : (prefixWord ++ tailWord_587670).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587670).length < 2 ^ (prefixWord ++ tailWord_587670).sum := by decide
  have hdescent : baseEnd_587670 < baseStart_587670 := by decide
  rcases family_descends (prefixWord ++ tailWord_587670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587708 : List Nat := [2, 2, 2, 5, 1, 2, 2, 4]
def baseStart_587708 : Nat := 118140960795 + 587708 * 2 ^ 59
def prefixEnd_587708 : Nat := 4983230072969 + 3 ^ 40 * 587708 * 2
def baseEnd_587708 : Nat := 89415315108945725465833

theorem tailTrace_587708 : CollatzResearch.WordTrace tailWord_587708 prefixEnd_587708 89415315108945725465833 := by
  unfold tailWord_587708
  simp only [CollatzResearch.WordTrace]
  refine ⟨10717735877420881690221889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14290314503227842253629185 10717735877420881690221889)
  ·
    refine ⟨8038301908065661267666417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10717735877420881690221889 8038301908065661267666417)
    ·
      refine ⟨6028726431049245950749813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8038301908065661267666417 6028726431049245950749813)
      ·
        refine ⟨565193102910866807882795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6028726431049245950749813 565193102910866807882795)
        ·
          refine ⟨847789654366300211824193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 565193102910866807882795 847789654366300211824193)
          ·
            refine ⟨635842240774725158868145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 847789654366300211824193 635842240774725158868145)
            ·
              refine ⟨476881680581043869151109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 635842240774725158868145 476881680581043869151109)
              ·
                refine ⟨89415315108945725465833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 476881680581043869151109 89415315108945725465833)
                ·
                  rfl

theorem cell20_587708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 2, 4].length) (baseStart_587708 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_587708 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_587708 prefixEnd_587708 := by exact prefixLift 587708
  have htrace : WordTrace (prefixWord ++ tailWord_587708) baseStart_587708 baseEnd_587708 := by
    simpa [prefixWord, tailWord_587708, baseEnd_587708] using wordTrace_append hprefix tailTrace_587708
  have hstable : (prefixWord ++ tailWord_587708).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587708).length < 2 ^ (prefixWord ++ tailWord_587708).sum := by decide
  have hdescent : baseEnd_587708 < baseStart_587708 := by decide
  rcases family_descends (prefixWord ++ tailWord_587708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587733 : List Nat := [1, 3, 2, 3, 2, 1, 8]
def baseStart_587733 : Nat := 118140960795 + 587733 * 2 ^ 59
def prefixEnd_587733 : Nat := 4983230072969 + 3 ^ 40 * 587733 * 2
def baseEnd_587733 : Nat := 29806372889783133396007

theorem tailTrace_587733 : CollatzResearch.WordTrace tailWord_587733 prefixEnd_587733 29806372889783133396007 := by
  unfold tailWord_587733
  simp only [CollatzResearch.WordTrace]
  refine ⟨21436383579751192650103853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14290922386500795100069235 21436383579751192650103853)
  ·
    refine ⟨8038643842406697243788945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21436383579751192650103853 8038643842406697243788945)
    ·
      refine ⟨6028982881805022932841709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8038643842406697243788945 6028982881805022932841709)
      ·
        refine ⟨2260868580676883599815641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6028982881805022932841709 2260868580676883599815641)
        ·
          refine ⟨1695651435507662699861731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2260868580676883599815641 1695651435507662699861731)
          ·
            refine ⟨2543477153261494049792597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1695651435507662699861731 2543477153261494049792597)
            ·
              refine ⟨29806372889783133396007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2543477153261494049792597 29806372889783133396007)
              ·
                rfl

theorem cell20_587733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 8].length) (baseStart_587733 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_587733 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_587733 prefixEnd_587733 := by exact prefixLift 587733
  have htrace : WordTrace (prefixWord ++ tailWord_587733) baseStart_587733 baseEnd_587733 := by
    simpa [prefixWord, tailWord_587733, baseEnd_587733] using wordTrace_append hprefix tailTrace_587733
  have hstable : (prefixWord ++ tailWord_587733).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587733).length < 2 ^ (prefixWord ++ tailWord_587733).sum := by decide
  have hdescent : baseEnd_587733 < baseStart_587733 := by decide
  rcases family_descends (prefixWord ++ tailWord_587733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587743 : List Nat := [1, 1, 2, 3, 4, 3, 1, 1, 4]
def baseStart_587743 : Nat := 118140960795 + 587743 * 2 ^ 59
def prefixEnd_587743 : Nat := 4983230072969 + 3 ^ 40 * 587743 * 2
def baseEnd_587743 : Nat := 268261920280532610230689

theorem tailTrace_587743 : CollatzResearch.WordTrace tailWord_587743 prefixEnd_587743 268261920280532610230689 := by
  unfold tailWord_587743
  simp only [CollatzResearch.WordTrace]
  refine ⟨21436748309714964357967883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14291165539809976238645255 21436748309714964357967883)
  ·
    refine ⟨32155122464572446536951825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21436748309714964357967883 32155122464572446536951825)
    ·
      refine ⟨24116341848429334902713869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32155122464572446536951825 24116341848429334902713869)
      ·
        refine ⟨9043628193161000588517701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24116341848429334902713869 9043628193161000588517701)
        ·
          refine ⟨1695680286217687610347069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9043628193161000588517701 1695680286217687610347069)
          ·
            refine ⟨635880107331632853880151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1695680286217687610347069 635880107331632853880151)
            ·
              refine ⟨953820160997449280820227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 635880107331632853880151 953820160997449280820227)
              ·
                refine ⟨1430730241496173921230341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 953820160997449280820227 1430730241496173921230341)
                ·
                  refine ⟨268261920280532610230689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1430730241496173921230341 268261920280532610230689)
                  ·
                    rfl

theorem cell20_587743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 1, 1, 4].length) (baseStart_587743 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_587743 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_587743 prefixEnd_587743 := by exact prefixLift 587743
  have htrace : WordTrace (prefixWord ++ tailWord_587743) baseStart_587743 baseEnd_587743 := by
    simpa [prefixWord, tailWord_587743, baseEnd_587743] using wordTrace_append hprefix tailTrace_587743
  have hstable : (prefixWord ++ tailWord_587743).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587743).length < 2 ^ (prefixWord ++ tailWord_587743).sum := by decide
  have hdescent : baseEnd_587743 < baseStart_587743 := by decide
  rcases family_descends (prefixWord ++ tailWord_587743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587826 : List Nat := [3, 2, 1, 1, 2, 4, 3, 4]
def baseStart_587826 : Nat := 118140960795 + 587826 * 2 ^ 59
def prefixEnd_587826 : Nat := 4983230072969 + 3 ^ 40 * 587826 * 2
def baseEnd_587826 : Nat := 89433267914051070154561

theorem tailTrace_587826 : CollatzResearch.WordTrace tailWord_587826 prefixEnd_587826 89433267914051070154561 := by
  unfold tailWord_587826
  simp only [CollatzResearch.WordTrace]
  refine ⟨5359943892103567383309833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14293183712276179688826221 5359943892103567383309833)
  ·
    refine ⟨4019957919077675537482375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5359943892103567383309833 4019957919077675537482375)
    ·
      refine ⟨6029936878616513306223563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4019957919077675537482375 6029936878616513306223563)
      ·
        refine ⟨9044905317924769959335345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6029936878616513306223563 9044905317924769959335345)
        ·
          refine ⟨6783678988443577469501509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9044905317924769959335345 6783678988443577469501509)
          ·
            refine ⟨1271939810333170775531533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6783678988443577469501509 1271939810333170775531533)
            ·
              refine ⟨476977428874939040824325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1271939810333170775531533 476977428874939040824325)
              ·
                refine ⟨89433267914051070154561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 476977428874939040824325 89433267914051070154561)
                ·
                  rfl

theorem cell20_587826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 3, 4].length) (baseStart_587826 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_587826 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_587826 prefixEnd_587826 := by exact prefixLift 587826
  have htrace : WordTrace (prefixWord ++ tailWord_587826) baseStart_587826 baseEnd_587826 := by
    simpa [prefixWord, tailWord_587826, baseEnd_587826] using wordTrace_append hprefix tailTrace_587826
  have hstable : (prefixWord ++ tailWord_587826).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587826).length < 2 ^ (prefixWord ++ tailWord_587826).sum := by decide
  have hdescent : baseEnd_587826 < baseStart_587826 := by decide
  rcases family_descends (prefixWord ++ tailWord_587826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587885 : List Nat := [1, 5, 1, 1, 2, 1, 3, 6]
def baseStart_587885 : Nat := 118140960795 + 587885 * 2 ^ 59
def prefixEnd_587885 : Nat := 4983230072969 + 3 ^ 40 * 587885 * 2
def baseEnd_587885 : Nat := 89442244316603742498925

theorem tailTrace_587885 : CollatzResearch.WordTrace tailWord_587885 prefixEnd_587885 89442244316603742498925 := by
  unfold tailWord_587885
  simp only [CollatzResearch.WordTrace]
  refine ⟨21441927475200522609637109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14294618316800348406424739 21441927475200522609637109)
  ·
    refine ⟨2010180700800048994653479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21441927475200522609637109 2010180700800048994653479)
    ·
      refine ⟨3015271051200073491980219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2010180700800048994653479 3015271051200073491980219)
      ·
        refine ⟨4522906576800110237970329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3015271051200073491980219 4522906576800110237970329)
        ·
          refine ⟨3392179932600082678477747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4522906576800110237970329 3392179932600082678477747)
          ·
            refine ⟨5088269898900124017716621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3392179932600082678477747 5088269898900124017716621)
            ·
              refine ⟨1908101212087546506643733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5088269898900124017716621 1908101212087546506643733)
              ·
                refine ⟨89442244316603742498925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1908101212087546506643733 89442244316603742498925)
                ·
                  rfl

theorem cell20_587885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 6].length) (baseStart_587885 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_587885 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_587885 prefixEnd_587885 := by exact prefixLift 587885
  have htrace : WordTrace (prefixWord ++ tailWord_587885) baseStart_587885 baseEnd_587885 := by
    simpa [prefixWord, tailWord_587885, baseEnd_587885] using wordTrace_append hprefix tailTrace_587885
  have hstable : (prefixWord ++ tailWord_587885).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587885).length < 2 ^ (prefixWord ++ tailWord_587885).sum := by decide
  have hdescent : baseEnd_587885 < baseStart_587885 := by decide
  rcases family_descends (prefixWord ++ tailWord_587885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587895 : List Nat := [1, 1, 3, 1, 1, 5, 3, 3, 2]
def baseStart_587895 : Nat := 118140960795 + 587895 * 2 ^ 59
def prefixEnd_587895 : Nat := 4983230072969 + 3 ^ 40 * 587895 * 2
def baseEnd_587895 : Nat := 268331297222295637163401

theorem tailTrace_587895 : CollatzResearch.WordTrace tailWord_587895 prefixEnd_587895 268331297222295637163401 := by
  unfold tailWord_587895
  simp only [CollatzResearch.WordTrace]
  refine ⟨21442292205164294317501139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14294861470109529545000759 21442292205164294317501139)
  ·
    refine ⟨32163438307746441476251709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21442292205164294317501139 32163438307746441476251709)
    ·
      refine ⟨12061289365404915553594391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32163438307746441476251709 12061289365404915553594391)
      ·
        refine ⟨18091934048107373330391587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12061289365404915553594391 18091934048107373330391587)
        ·
          refine ⟨27137901072161059995587381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18091934048107373330391587 27137901072161059995587381)
          ·
            refine ⟨2544178225515099374586317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27137901072161059995587381 2544178225515099374586317)
            ·
              refine ⟨954066834568162265469869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2544178225515099374586317 954066834568162265469869)
              ·
                refine ⟨357775062963060849551201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 954066834568162265469869 357775062963060849551201)
                ·
                  refine ⟨268331297222295637163401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 357775062963060849551201 268331297222295637163401)
                  ·
                    rfl

theorem cell20_587895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3, 3, 2].length) (baseStart_587895 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_587895 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_587895 prefixEnd_587895 := by exact prefixLift 587895
  have htrace : WordTrace (prefixWord ++ tailWord_587895) baseStart_587895 baseEnd_587895 := by
    simpa [prefixWord, tailWord_587895, baseEnd_587895] using wordTrace_append hprefix tailTrace_587895
  have hstable : (prefixWord ++ tailWord_587895).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587895).length < 2 ^ (prefixWord ++ tailWord_587895).sum := by decide
  have hdescent : baseEnd_587895 < baseStart_587895 := by decide
  rcases family_descends (prefixWord ++ tailWord_587895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587964 : List Nat := [2, 2, 2, 3, 3, 1, 2, 2, 3]
def baseStart_587964 : Nat := 118140960795 + 587964 * 2 ^ 59
def prefixEnd_587964 : Nat := 4983230072969 + 3 ^ 40 * 587964 * 2
def baseEnd_587964 : Nat := 268362790702438063863119

theorem tailTrace_587964 : CollatzResearch.WordTrace tailWord_587964 prefixEnd_587964 268362790702438063863119 := by
  unfold tailWord_587964
  simp only [CollatzResearch.WordTrace]
  refine ⟨10722404420957159550881473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14296539227942879401175297 10722404420957159550881473)
  ·
    refine ⟨8041803315717869663161105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10722404420957159550881473 8041803315717869663161105)
    ·
      refine ⟨6031352486788402247370829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8041803315717869663161105 6031352486788402247370829)
      ·
        refine ⟨2261757182545650842764061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6031352486788402247370829 2261757182545650842764061)
        ·
          refine ⟨848158943454619066036523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2261757182545650842764061 848158943454619066036523)
          ·
            refine ⟨1272238415181928599054785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 848158943454619066036523 1272238415181928599054785)
            ·
              refine ⟨954178811386446449291089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1272238415181928599054785 954178811386446449291089)
              ·
                refine ⟨715634108539834836968317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 954178811386446449291089 715634108539834836968317)
                ·
                  refine ⟨268362790702438063863119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 715634108539834836968317 268362790702438063863119)
                  ·
                    rfl

theorem cell20_587964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 2, 2, 3].length) (baseStart_587964 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_587964 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_587964 prefixEnd_587964 := by exact prefixLift 587964
  have htrace : WordTrace (prefixWord ++ tailWord_587964) baseStart_587964 baseEnd_587964 := by
    simpa [prefixWord, tailWord_587964, baseEnd_587964] using wordTrace_append hprefix tailTrace_587964
  have hstable : (prefixWord ++ tailWord_587964).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587964).length < 2 ^ (prefixWord ++ tailWord_587964).sum := by decide
  have hdescent : baseEnd_587964 < baseStart_587964 := by decide
  rcases family_descends (prefixWord ++ tailWord_587964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_587992 : List Nat := [2, 1, 2, 2, 4, 2, 1, 2, 4]
def baseStart_587992 : Nat := 118140960795 + 587992 * 2 ^ 59
def prefixEnd_587992 : Nat := 4983230072969 + 3 ^ 40 * 587992 * 2
def baseEnd_587992 : Nat := 268375570665394410929671

theorem tailTrace_587992 : CollatzResearch.WordTrace tailWord_587992 prefixEnd_587992 268375570665394410929671 := by
  unfold tailWord_587992
  simp only [CollatzResearch.WordTrace]
  refine ⟨10722915042906439941891115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14297220057208586589188153 10722915042906439941891115)
  ·
    refine ⟨16084372564359659912836673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10722915042906439941891115 16084372564359659912836673)
    ·
      refine ⟨12063279423269744934627505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16084372564359659912836673 12063279423269744934627505)
      ·
        refine ⟨9047459567452308700970629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12063279423269744934627505 9047459567452308700970629)
        ·
          refine ⟨1696398668897307881431993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9047459567452308700970629 1696398668897307881431993)
          ·
            refine ⟨1272299001672980911073995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1696398668897307881431993 1272299001672980911073995)
            ·
              refine ⟨1908448502509471366610993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1272299001672980911073995 1908448502509471366610993)
              ·
                refine ⟨1431336376882103524958245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1908448502509471366610993 1431336376882103524958245)
                ·
                  refine ⟨268375570665394410929671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1431336376882103524958245 268375570665394410929671)
                  ·
                    rfl

theorem cell20_587992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 2, 4].length) (baseStart_587992 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_587992 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_587992 prefixEnd_587992 := by exact prefixLift 587992
  have htrace : WordTrace (prefixWord ++ tailWord_587992) baseStart_587992 baseEnd_587992 := by
    simpa [prefixWord, tailWord_587992, baseEnd_587992] using wordTrace_append hprefix tailTrace_587992
  have hstable : (prefixWord ++ tailWord_587992).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_587992).length < 2 ^ (prefixWord ++ tailWord_587992).sum := by decide
  have hdescent : baseEnd_587992 < baseStart_587992 := by decide
  rcases family_descends (prefixWord ++ tailWord_587992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588040 : List Nat := [2, 1, 3, 2, 3, 2, 3, 1, 3]
def baseStart_588040 : Nat := 118140960795 + 588040 * 2 ^ 59
def prefixEnd_588040 : Nat := 4983230072969 + 3 ^ 40 * 588040 * 2
def baseEnd_588040 : Nat := 268397479173319577329475

theorem tailTrace_588040 : CollatzResearch.WordTrace tailWord_588040 prefixEnd_588040 268397479173319577329475 := by
  unfold tailWord_588040
  simp only [CollatzResearch.WordTrace]
  refine ⟨10723790394819492040764787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14298387193092656054353049 10723790394819492040764787)
  ·
    refine ⟨16085685592229238061147181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10723790394819492040764787 16085685592229238061147181)
    ·
      refine ⟨6032132097085964272930193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16085685592229238061147181 6032132097085964272930193)
      ·
        refine ⟨4524099072814473204697645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6032132097085964272930193 4524099072814473204697645)
        ·
          refine ⟨1696537152305427451761617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4524099072814473204697645 1696537152305427451761617)
          ·
            refine ⟨1272402864229070588821213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1696537152305427451761617 1272402864229070588821213)
            ·
              refine ⟨477151074085901470807955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1272402864229070588821213 477151074085901470807955)
              ·
                refine ⟨715726611128852206211933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 477151074085901470807955 715726611128852206211933)
                ·
                  refine ⟨268397479173319577329475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 715726611128852206211933 268397479173319577329475)
                  ·
                    rfl

theorem cell20_588040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 3, 1, 3].length) (baseStart_588040 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_588040 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_588040 prefixEnd_588040 := by exact prefixLift 588040
  have htrace : WordTrace (prefixWord ++ tailWord_588040) baseStart_588040 baseEnd_588040 := by
    simpa [prefixWord, tailWord_588040, baseEnd_588040] using wordTrace_append hprefix tailTrace_588040
  have hstable : (prefixWord ++ tailWord_588040).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588040).length < 2 ^ (prefixWord ++ tailWord_588040).sum := by decide
  have hdescent : baseEnd_588040 < baseStart_588040 := by decide
  rcases family_descends (prefixWord ++ tailWord_588040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588064 : List Nat := [2, 1, 1, 5, 2, 3, 1, 3, 2]
def baseStart_588064 : Nat := 118140960795 + 588064 * 2 ^ 59
def prefixEnd_588064 : Nat := 4983230072969 + 3 ^ 40 * 588064 * 2
def baseEnd_588064 : Nat := 268408433427282160529377

theorem tailTrace_588064 : CollatzResearch.WordTrace tailWord_588064 prefixEnd_588064 268408433427282160529377 := by
  unfold tailWord_588064
  simp only [CollatzResearch.WordTrace]
  refine ⟨10724228070776018090201623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14298970761034690786935497 10724228070776018090201623)
  ·
    refine ⟨16086342106164027135302435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10724228070776018090201623 16086342106164027135302435)
    ·
      refine ⟨24129513159246040702953653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16086342106164027135302435 24129513159246040702953653)
      ·
        refine ⟨2262141858679316315901905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24129513159246040702953653 2262141858679316315901905)
        ·
          refine ⟨1696606394009487236926429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2262141858679316315901905 1696606394009487236926429)
          ·
            refine ⟨636227397753557713847411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1696606394009487236926429 636227397753557713847411)
            ·
              refine ⟨954341096630336570771117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 636227397753557713847411 954341096630336570771117)
              ·
                refine ⟨357877911236376214039169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 954341096630336570771117 357877911236376214039169)
                ·
                  refine ⟨268408433427282160529377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 357877911236376214039169 268408433427282160529377)
                  ·
                    rfl

theorem cell20_588064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 1, 3, 2].length) (baseStart_588064 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_588064 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_588064 prefixEnd_588064 := by exact prefixLift 588064
  have htrace : WordTrace (prefixWord ++ tailWord_588064) baseStart_588064 baseEnd_588064 := by
    simpa [prefixWord, tailWord_588064, baseEnd_588064] using wordTrace_append hprefix tailTrace_588064
  have hstable : (prefixWord ++ tailWord_588064).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588064).length < 2 ^ (prefixWord ++ tailWord_588064).sum := by decide
  have hdescent : baseEnd_588064 < baseStart_588064 := by decide
  rcases family_descends (prefixWord ++ tailWord_588064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588099 : List Nat := [1, 1, 1, 3, 1, 3, 6, 1, 3]
def baseStart_588099 : Nat := 118140960795 + 588099 * 2 ^ 59
def prefixEnd_588099 : Nat := 4983230072969 + 3 ^ 40 * 588099 * 2
def baseEnd_588099 : Nat := 268424408380977594362567

theorem tailTrace_588099 : CollatzResearch.WordTrace tailWord_588099 prefixEnd_588099 268424408380977594362567 := by
  unfold tailWord_588099
  simp only [CollatzResearch.WordTrace]
  refine ⟨21449732696425237157927351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14299821797616824771951567 21449732696425237157927351)
  ·
    refine ⟨32174599044637855736891027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21449732696425237157927351 32174599044637855736891027)
    ·
      refine ⟨48261898566956783605336541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32174599044637855736891027 48261898566956783605336541)
      ·
        refine ⟨18098211962608793852001203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48261898566956783605336541 18098211962608793852001203)
        ·
          refine ⟨27147317943913190778001805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18098211962608793852001203 27147317943913190778001805)
          ·
            refine ⟨10180244228967446541750677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27147317943913190778001805 10180244228967446541750677)
            ·
              refine ⟨477198948232849056644563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 10180244228967446541750677 477198948232849056644563)
              ·
                refine ⟨715798422349273584966845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 477198948232849056644563 715798422349273584966845)
                ·
                  refine ⟨268424408380977594362567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 715798422349273584966845 268424408380977594362567)
                  ·
                    rfl

theorem cell20_588099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 6, 1, 3].length) (baseStart_588099 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_588099 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_588099 prefixEnd_588099 := by exact prefixLift 588099
  have htrace : WordTrace (prefixWord ++ tailWord_588099) baseStart_588099 baseEnd_588099 := by
    simpa [prefixWord, tailWord_588099, baseEnd_588099] using wordTrace_append hprefix tailTrace_588099
  have hstable : (prefixWord ++ tailWord_588099).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588099).length < 2 ^ (prefixWord ++ tailWord_588099).sum := by decide
  have hdescent : baseEnd_588099 < baseStart_588099 := by decide
  rcases family_descends (prefixWord ++ tailWord_588099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588126 : List Nat := [4, 4, 2, 1, 1, 8]
def baseStart_588126 : Nat := 118140960795 + 588126 * 2 ^ 59
def prefixEnd_588126 : Nat := 4983230072969 + 3 ^ 40 * 588126 * 2
def baseEnd_588126 : Nat := 9942101182099462980091

theorem tailTrace_588126 : CollatzResearch.WordTrace tailWord_588126 prefixEnd_588126 9942101182099462980091 := by
  unfold tailWord_588126
  simp only [CollatzResearch.WordTrace]
  refine ⟨2681339683415927596145029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14300478311551613846106821 2681339683415927596145029)
  ·
    refine ⟨502751190640486424277193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2681339683415927596145029 502751190640486424277193)
    ·
      refine ⟨377063392980364818207895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 502751190640486424277193 377063392980364818207895)
      ·
        refine ⟨565595089470547227311843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 377063392980364818207895 565595089470547227311843)
        ·
          refine ⟨848392634205820840967765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 565595089470547227311843 848392634205820840967765)
          ·
            refine ⟨9942101182099462980091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 848392634205820840967765 9942101182099462980091)
            ·
              rfl

theorem cell20_588126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 8].length) (baseStart_588126 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_588126 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_588126 prefixEnd_588126 := by exact prefixLift 588126
  have htrace : WordTrace (prefixWord ++ tailWord_588126) baseStart_588126 baseEnd_588126 := by
    simpa [prefixWord, tailWord_588126, baseEnd_588126] using wordTrace_append hprefix tailTrace_588126
  have hstable : (prefixWord ++ tailWord_588126).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588126).length < 2 ^ (prefixWord ++ tailWord_588126).sum := by decide
  have hdescent : baseEnd_588126 < baseStart_588126 := by decide
  rcases family_descends (prefixWord ++ tailWord_588126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588189 : List Nat := [1, 4, 2, 1, 4, 1, 7]
def baseStart_588189 : Nat := 118140960795 + 588189 * 2 ^ 59
def prefixEnd_588189 : Nat := 4983230072969 + 3 ^ 40 * 588189 * 2
def baseEnd_588189 : Nat := 29829498537037475706911

theorem tailTrace_588189 : CollatzResearch.WordTrace tailWord_588189 prefixEnd_588189 29829498537037475706911 := by
  unfold tailWord_588189
  simp only [CollatzResearch.WordTrace]
  refine ⟨21453015266099182528703621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14302010177399455019135747 21453015266099182528703621)
  ·
    refine ⟨4022440362393596724131929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21453015266099182528703621 4022440362393596724131929)
    ·
      refine ⟨3016830271795197543098947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4022440362393596724131929 3016830271795197543098947)
      ·
        refine ⟨4525245407692796314648421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3016830271795197543098947 4525245407692796314648421)
        ·
          refine ⟨848483513942399308996579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4525245407692796314648421 848483513942399308996579)
          ·
            refine ⟨1272725270913598963494869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 848483513942399308996579 1272725270913598963494869)
            ·
              refine ⟨29829498537037475706911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1272725270913598963494869 29829498537037475706911)
              ·
                rfl

theorem cell20_588189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 7].length) (baseStart_588189 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_588189 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_588189 prefixEnd_588189 := by exact prefixLift 588189
  have htrace : WordTrace (prefixWord ++ tailWord_588189) baseStart_588189 baseEnd_588189 := by
    simpa [prefixWord, tailWord_588189, baseEnd_588189] using wordTrace_append hprefix tailTrace_588189
  have hstable : (prefixWord ++ tailWord_588189).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588189).length < 2 ^ (prefixWord ++ tailWord_588189).sum := by decide
  have hdescent : baseEnd_588189 < baseStart_588189 := by decide
  rcases family_descends (prefixWord ++ tailWord_588189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588199 : List Nat := [1, 1, 6, 1, 1, 2, 2, 4, 2]
def baseStart_588199 : Nat := 118140960795 + 588199 * 2 ^ 59
def prefixEnd_588199 : Nat := 4983230072969 + 3 ^ 40 * 588199 * 2
def baseEnd_588199 : Nat := 268470051105821691028825

theorem tailTrace_588199 : CollatzResearch.WordTrace tailWord_588199 prefixEnd_588199 268470051105821691028825 := by
  unfold tailWord_588199
  simp only [CollatzResearch.WordTrace]
  refine ⟨21453379996062954236567651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14302253330708636157711767 21453379996062954236567651)
  ·
    refine ⟨32180069994094431354851477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21453379996062954236567651 32180069994094431354851477)
    ·
      refine ⟨1508440780973176469758663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 32180069994094431354851477 1508440780973176469758663)
      ·
        refine ⟨2262661171459764704637995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1508440780973176469758663 2262661171459764704637995)
        ·
          refine ⟨3393991757189647056956993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2262661171459764704637995 3393991757189647056956993)
          ·
            refine ⟨2545493817892235292717745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3393991757189647056956993 2545493817892235292717745)
            ·
              refine ⟨1909120363419176469538309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2545493817892235292717745 1909120363419176469538309)
              ·
                refine ⟨357960068141095588038433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1909120363419176469538309 357960068141095588038433)
                ·
                  refine ⟨268470051105821691028825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 357960068141095588038433 268470051105821691028825)
                  ·
                    rfl

theorem cell20_588199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 4, 2].length) (baseStart_588199 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_588199 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_588199 prefixEnd_588199 := by exact prefixLift 588199
  have htrace : WordTrace (prefixWord ++ tailWord_588199) baseStart_588199 baseEnd_588199 := by
    simpa [prefixWord, tailWord_588199, baseEnd_588199] using wordTrace_append hprefix tailTrace_588199
  have hstable : (prefixWord ++ tailWord_588199).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588199).length < 2 ^ (prefixWord ++ tailWord_588199).sum := by decide
  have hdescent : baseEnd_588199 < baseStart_588199 := by decide
  rcases family_descends (prefixWord ++ tailWord_588199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588210 : List Nat := [3, 2, 1, 1, 1, 1, 4, 7]
def baseStart_588210 : Nat := 118140960795 + 588210 * 2 ^ 59
def prefixEnd_588210 : Nat := 4983230072969 + 3 ^ 40 * 588210 * 2
def baseEnd_588210 : Nat := 89491690601851513887371

theorem tailTrace_588210 : CollatzResearch.WordTrace tailWord_588210 prefixEnd_588210 89491690601851513887371 := by
  unfold tailWord_588210
  simp only [CollatzResearch.WordTrace]
  refine ⟨5363445299755775778804521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14302520799348735410145389 5363445299755775778804521)
  ·
    refine ⟨4022583974816831834103391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5363445299755775778804521 4022583974816831834103391)
    ·
      refine ⟨6033875962225247751155087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4022583974816831834103391 6033875962225247751155087)
      ·
        refine ⟨9050813943337871626732631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6033875962225247751155087 9050813943337871626732631)
        ·
          refine ⟨13576220915006807440098947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9050813943337871626732631 13576220915006807440098947)
          ·
            refine ⟨20364331372510211160148421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13576220915006807440098947 20364331372510211160148421)
            ·
              refine ⟨3818312132345664592527829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20364331372510211160148421 3818312132345664592527829)
              ·
                refine ⟨89491690601851513887371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3818312132345664592527829 89491690601851513887371)
                ·
                  rfl

theorem cell20_588210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 7].length) (baseStart_588210 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_588210 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_588210 prefixEnd_588210 := by exact prefixLift 588210
  have htrace : WordTrace (prefixWord ++ tailWord_588210) baseStart_588210 baseEnd_588210 := by
    simpa [prefixWord, tailWord_588210, baseEnd_588210] using wordTrace_append hprefix tailTrace_588210
  have hstable : (prefixWord ++ tailWord_588210).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588210).length < 2 ^ (prefixWord ++ tailWord_588210).sum := by decide
  have hdescent : baseEnd_588210 < baseStart_588210 := by decide
  rcases family_descends (prefixWord ++ tailWord_588210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588220 : List Nat := [2, 2, 2, 4, 1, 1, 2, 2, 4]
def baseStart_588220 : Nat := 118140960795 + 588220 * 2 ^ 59
def prefixEnd_588220 : Nat := 4983230072969 + 3 ^ 40 * 588220 * 2
def baseEnd_588220 : Nat := 268479636078038951328739

theorem tailTrace_588220 : CollatzResearch.WordTrace tailWord_588220 prefixEnd_588220 268479636078038951328739 := by
  unfold tailWord_588220
  simp only [CollatzResearch.WordTrace]
  refine ⟨10727072964493437411541057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14302763952657916548721409 10727072964493437411541057)
  ·
    refine ⟨8045304723370078058655793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10727072964493437411541057 8045304723370078058655793)
    ·
      refine ⟨6033978542527558543991845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8045304723370078058655793 6033978542527558543991845)
      ·
        refine ⟨1131370976723917226998471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6033978542527558543991845 1131370976723917226998471)
        ·
          refine ⟨1697056465085875840497707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1131370976723917226998471 1697056465085875840497707)
          ·
            refine ⟨2545584697628813760746561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1697056465085875840497707 2545584697628813760746561)
            ·
              refine ⟨1909188523221610320559921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2545584697628813760746561 1909188523221610320559921)
              ·
                refine ⟨1431891392416207740419941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1909188523221610320559921 1431891392416207740419941)
                ·
                  refine ⟨268479636078038951328739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1431891392416207740419941 268479636078038951328739)
                  ·
                    rfl

theorem cell20_588220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 2, 4].length) (baseStart_588220 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_588220 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_588220 prefixEnd_588220 := by exact prefixLift 588220
  have htrace : WordTrace (prefixWord ++ tailWord_588220) baseStart_588220 baseEnd_588220 := by
    simpa [prefixWord, tailWord_588220, baseEnd_588220] using wordTrace_append hprefix tailTrace_588220
  have hstable : (prefixWord ++ tailWord_588220).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588220).length < 2 ^ (prefixWord ++ tailWord_588220).sum := by decide
  have hdescent : baseEnd_588220 < baseStart_588220 := by decide
  rcases family_descends (prefixWord ++ tailWord_588220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588272 : List Nat := [2, 1, 1, 1, 3, 3, 3, 3, 3]
def baseStart_588272 : Nat := 118140960795 + 588272 * 2 ^ 59
def prefixEnd_588272 : Nat := 4983230072969 + 3 ^ 40 * 588272 * 2
def baseEnd_588272 : Nat := 268503370294957881595193

theorem tailTrace_588272 : CollatzResearch.WordTrace tailWord_588272 prefixEnd_588272 268503370294957881595193 := by
  unfold tailWord_588272
  simp only [CollatzResearch.WordTrace]
  refine ⟨10728021262399243851987535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14304028349865658469316713 10728021262399243851987535)
  ·
    refine ⟨16092031893598865777981303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10728021262399243851987535 16092031893598865777981303)
    ·
      refine ⟨24138047840398298666971955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16092031893598865777981303 24138047840398298666971955)
      ·
        refine ⟨36207071760597448000457933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24138047840398298666971955 36207071760597448000457933)
        ·
          refine ⟨13577651910224043000171725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36207071760597448000457933 13577651910224043000171725)
          ·
            refine ⟨5091619466334016125064397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13577651910224043000171725 5091619466334016125064397)
            ·
              refine ⟨1909357299875256046899149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5091619466334016125064397 1909357299875256046899149)
              ·
                refine ⟨716008987453221017587181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1909357299875256046899149 716008987453221017587181)
                ·
                  refine ⟨268503370294957881595193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 716008987453221017587181 268503370294957881595193)
                  ·
                    rfl

theorem cell20_588272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 3, 3].length) (baseStart_588272 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_588272 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_588272 prefixEnd_588272 := by exact prefixLift 588272
  have htrace : WordTrace (prefixWord ++ tailWord_588272) baseStart_588272 baseEnd_588272 := by
    simpa [prefixWord, tailWord_588272, baseEnd_588272] using wordTrace_append hprefix tailTrace_588272
  have hstable : (prefixWord ++ tailWord_588272).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588272).length < 2 ^ (prefixWord ++ tailWord_588272).sum := by decide
  have hdescent : baseEnd_588272 < baseStart_588272 := by decide
  rcases family_descends (prefixWord ++ tailWord_588272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588293 : List Nat := [1, 3, 1, 1, 2, 2, 2, 1, 7]
def baseStart_588293 : Nat := 118140960795 + 588293 * 2 ^ 59
def prefixEnd_588293 : Nat := 4983230072969 + 3 ^ 40 * 588293 * 2
def baseEnd_588293 : Nat := 268512955267175141895107

theorem tailTrace_588293 : CollatzResearch.WordTrace tailWord_588293 prefixEnd_588293 268512955267175141895107 := by
  unfold tailWord_588293
  simp only [CollatzResearch.WordTrace]
  refine ⟨21456808457722408290489533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14304538971814938860326355 21456808457722408290489533)
  ·
    refine ⟨8046303171645903108933575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21456808457722408290489533 8046303171645903108933575)
    ·
      refine ⟨12069454757468854663400363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8046303171645903108933575 12069454757468854663400363)
      ·
        refine ⟨18104182136203281995100545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12069454757468854663400363 18104182136203281995100545)
        ·
          refine ⟨13578136602152461496325409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18104182136203281995100545 13578136602152461496325409)
          ·
            refine ⟨10183602451614346122244057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13578136602152461496325409 10183602451614346122244057)
            ·
              refine ⟨7637701838710759591683043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10183602451614346122244057 7637701838710759591683043)
              ·
                refine ⟨11456552758066139387524565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7637701838710759591683043 11456552758066139387524565)
                ·
                  refine ⟨268512955267175141895107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11456552758066139387524565 268512955267175141895107)
                  ·
                    rfl

theorem cell20_588293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 7].length) (baseStart_588293 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_588293 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_588293 prefixEnd_588293 := by exact prefixLift 588293
  have htrace : WordTrace (prefixWord ++ tailWord_588293) baseStart_588293 baseEnd_588293 := by
    simpa [prefixWord, tailWord_588293, baseEnd_588293] using wordTrace_append hprefix tailTrace_588293
  have hstable : (prefixWord ++ tailWord_588293).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588293).length < 2 ^ (prefixWord ++ tailWord_588293).sum := by decide
  have hdescent : baseEnd_588293 < baseStart_588293 := by decide
  rcases family_descends (prefixWord ++ tailWord_588293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588296 : List Nat := [2, 1, 3, 2, 1, 1, 1, 7, 2]
def baseStart_588296 : Nat := 118140960795 + 588296 * 2 ^ 59
def prefixEnd_588296 : Nat := 4983230072969 + 3 ^ 40 * 588296 * 2
def baseEnd_588296 : Nat := 268514324548920464795095

theorem tailTrace_588296 : CollatzResearch.WordTrace tailWord_588296 prefixEnd_588296 268514324548920464795095 := by
  unfold tailWord_588296
  simp only [CollatzResearch.WordTrace]
  refine ⟨10728458938355769901424371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14304611917807693201899161 10728458938355769901424371)
  ·
    refine ⟨16092688407533654852136557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10728458938355769901424371 16092688407533654852136557)
    ·
      refine ⟨6034758152825120569551209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16092688407533654852136557 6034758152825120569551209)
      ·
        refine ⟨4526068614618840427163407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6034758152825120569551209 4526068614618840427163407)
        ·
          refine ⟨6789102921928260640745111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4526068614618840427163407 6789102921928260640745111)
          ·
            refine ⟨10183654382892390961117667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6789102921928260640745111 10183654382892390961117667)
            ·
              refine ⟨15275481574338586441676501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10183654382892390961117667 15275481574338586441676501)
              ·
                refine ⟨358019099398560619726793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 15275481574338586441676501 358019099398560619726793)
                ·
                  refine ⟨268514324548920464795095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 358019099398560619726793 268514324548920464795095)
                  ·
                    rfl

theorem cell20_588296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 7, 2].length) (baseStart_588296 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_588296 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_588296 prefixEnd_588296 := by exact prefixLift 588296
  have htrace : WordTrace (prefixWord ++ tailWord_588296) baseStart_588296 baseEnd_588296 := by
    simpa [prefixWord, tailWord_588296, baseEnd_588296] using wordTrace_append hprefix tailTrace_588296
  have hstable : (prefixWord ++ tailWord_588296).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588296).length < 2 ^ (prefixWord ++ tailWord_588296).sum := by decide
  have hdescent : baseEnd_588296 < baseStart_588296 := by decide
  rcases family_descends (prefixWord ++ tailWord_588296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588320 : List Nat := [2, 1, 1, 6, 2, 2, 1, 5]
def baseStart_588320 : Nat := 118140960795 + 588320 * 2 ^ 59
def prefixEnd_588320 : Nat := 4983230072969 + 3 ^ 40 * 588320 * 2
def baseEnd_588320 : Nat := 89508426267627682664999

theorem tailTrace_588320 : CollatzResearch.WordTrace tailWord_588320 prefixEnd_588320 89508426267627682664999 := by
  unfold tailWord_588320
  simp only [CollatzResearch.WordTrace]
  refine ⟨10728896614312295950861207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14305195485749727934481609 10728896614312295950861207)
  ·
    refine ⟨16093344921468443926291811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10728896614312295950861207 16093344921468443926291811)
    ·
      refine ⟨24140017382202665889437717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16093344921468443926291811 24140017382202665889437717)
      ·
        refine ⟨1131563314790749963567393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 24140017382202665889437717 1131563314790749963567393)
        ·
          refine ⟨848672486093062472675545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1131563314790749963567393 848672486093062472675545)
          ·
            refine ⟨636504364569796854506659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 848672486093062472675545 636504364569796854506659)
            ·
              refine ⟨954756546854695281759989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 636504364569796854506659 954756546854695281759989)
              ·
                refine ⟨89508426267627682664999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 954756546854695281759989 89508426267627682664999)
                ·
                  rfl

theorem cell20_588320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 1, 5].length) (baseStart_588320 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_588320 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_588320 prefixEnd_588320 := by exact prefixLift 588320
  have htrace : WordTrace (prefixWord ++ tailWord_588320) baseStart_588320 baseEnd_588320 := by
    simpa [prefixWord, tailWord_588320, baseEnd_588320] using wordTrace_append hprefix tailTrace_588320
  have hstable : (prefixWord ++ tailWord_588320).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588320).length < 2 ^ (prefixWord ++ tailWord_588320).sum := by decide
  have hdescent : baseEnd_588320 < baseStart_588320 := by decide
  rcases family_descends (prefixWord ++ tailWord_588320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588341 : List Nat := [1, 3, 3, 1, 1, 2, 5, 4]
def baseStart_588341 : Nat := 118140960795 + 588341 * 2 ^ 59
def prefixEnd_588341 : Nat := 4983230072969 + 3 ^ 40 * 588341 * 2
def baseEnd_588341 : Nat := 89511621258366769431637

theorem tailTrace_588341 : CollatzResearch.WordTrace tailWord_588341 prefixEnd_588341 89511621258366769431637 := by
  unfold tailWord_588341
  simp only [CollatzResearch.WordTrace]
  refine ⟨21458559161548512488236877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14305706107699008325491251 21458559161548512488236877)
  ·
    refine ⟨8046959685580692183088829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21458559161548512488236877 8046959685580692183088829)
    ·
      refine ⟨3017609882092759568658311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8046959685580692183088829 3017609882092759568658311)
      ·
        refine ⟨4526414823139139352987467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3017609882092759568658311 4526414823139139352987467)
        ·
          refine ⟨6789622234708709029481201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4526414823139139352987467 6789622234708709029481201)
          ·
            refine ⟨5092216676031531772110901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6789622234708709029481201 5092216676031531772110901)
            ·
              refine ⟨477395313377956103635397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5092216676031531772110901 477395313377956103635397)
              ·
                refine ⟨89511621258366769431637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 477395313377956103635397 89511621258366769431637)
                ·
                  rfl

theorem cell20_588341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 5, 4].length) (baseStart_588341 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_588341 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_588341 prefixEnd_588341 := by exact prefixLift 588341
  have htrace : WordTrace (prefixWord ++ tailWord_588341) baseStart_588341 baseEnd_588341 := by
    simpa [prefixWord, tailWord_588341, baseEnd_588341] using wordTrace_append hprefix tailTrace_588341
  have hstable : (prefixWord ++ tailWord_588341).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588341).length < 2 ^ (prefixWord ++ tailWord_588341).sum := by decide
  have hdescent : baseEnd_588341 < baseStart_588341 := by decide
  rcases family_descends (prefixWord ++ tailWord_588341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588358 : List Nat := [6, 1, 1, 1, 2, 2, 7]
def baseStart_588358 : Nat := 118140960795 + 588358 * 2 ^ 59
def prefixEnd_588358 : Nat := 4983230072969 + 3 ^ 40 * 588358 * 2
def baseEnd_588358 : Nat := 29838069226480422747575

theorem tailTrace_588358 : CollatzResearch.WordTrace tailWord_588358 prefixEnd_588358 29838069226480422747575 := by
  unfold tailWord_588358
  simp only [CollatzResearch.WordTrace]
  refine ⟨670599350077716387237679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 14306119468324616261070485 670599350077716387237679)
  ·
    refine ⟨1005899025116574580856519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 670599350077716387237679 1005899025116574580856519)
    ·
      refine ⟨1508848537674861871284779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1005899025116574580856519 1508848537674861871284779)
      ·
        refine ⟨2263272806512292806927169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1508848537674861871284779 2263272806512292806927169)
        ·
          refine ⟨1697454604884219605195377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2263272806512292806927169 1697454604884219605195377)
          ·
            refine ⟨1273090953663164703896533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1697454604884219605195377 1273090953663164703896533)
            ·
              refine ⟨29838069226480422747575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1273090953663164703896533 29838069226480422747575)
              ·
                rfl

theorem cell20_588358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 7].length) (baseStart_588358 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_588358 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_588358 prefixEnd_588358 := by exact prefixLift 588358
  have htrace : WordTrace (prefixWord ++ tailWord_588358) baseStart_588358 baseEnd_588358 := by
    simpa [prefixWord, tailWord_588358, baseEnd_588358] using wordTrace_append hprefix tailTrace_588358
  have hstable : (prefixWord ++ tailWord_588358).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588358).length < 2 ^ (prefixWord ++ tailWord_588358).sum := by decide
  have hdescent : baseEnd_588358 < baseStart_588358 := by decide
  rcases family_descends (prefixWord ++ tailWord_588358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588362 : List Nat := [3, 1, 2, 1, 1, 5, 7]
def baseStart_588362 : Nat := 118140960795 + 588362 * 2 ^ 59
def prefixEnd_588362 : Nat := 4983230072969 + 3 ^ 40 * 588362 * 2
def baseEnd_588362 : Nat := 29838272083035285399425

theorem tailTrace_588362 : CollatzResearch.WordTrace tailWord_588362 prefixEnd_588362 29838272083035285399425 := by
  unfold tailWord_588362
  simp only [CollatzResearch.WordTrace]
  refine ⟨5364831273618108268687835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14306216729648288716500893 5364831273618108268687835)
  ·
    refine ⟨8047246910427162403031753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5364831273618108268687835 8047246910427162403031753)
    ·
      refine ⟨6035435182820371802273815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8047246910427162403031753 6035435182820371802273815)
      ·
        refine ⟨9053152774230557703410723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6035435182820371802273815 9053152774230557703410723)
        ·
          refine ⟨13579729161345836555116085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9053152774230557703410723 13579729161345836555116085)
          ·
            refine ⟨1273099608876172177042133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13579729161345836555116085 1273099608876172177042133)
            ·
              refine ⟨29838272083035285399425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1273099608876172177042133 29838272083035285399425)
              ·
                rfl

theorem cell20_588362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 7].length) (baseStart_588362 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_588362 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_588362 prefixEnd_588362 := by exact prefixLift 588362
  have htrace : WordTrace (prefixWord ++ tailWord_588362) baseStart_588362 baseEnd_588362 := by
    simpa [prefixWord, tailWord_588362, baseEnd_588362] using wordTrace_append hprefix tailTrace_588362
  have hstable : (prefixWord ++ tailWord_588362).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588362).length < 2 ^ (prefixWord ++ tailWord_588362).sum := by decide
  have hdescent : baseEnd_588362 < baseStart_588362 := by decide
  rcases family_descends (prefixWord ++ tailWord_588362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588365 : List Nat := [1, 6, 1, 1, 2, 2, 1, 1, 5]
def baseStart_588365 : Nat := 118140960795 + 588365 * 2 ^ 59
def prefixEnd_588365 : Nat := 4983230072969 + 3 ^ 40 * 588365 * 2
def baseEnd_588365 : Nat := 268545818029062891494813

theorem tailTrace_588365 : CollatzResearch.WordTrace tailWord_588365 prefixEnd_588365 268545818029062891494813 := by
  unfold tailWord_588365
  simp only [CollatzResearch.WordTrace]
  refine ⟨21459434513461564587110549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14306289675641043058073699 21459434513461564587110549)
  ·
    refine ⟨1005910992818510840020807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 21459434513461564587110549 1005910992818510840020807)
    ·
      refine ⟨1508866489227766260031211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1005910992818510840020807 1508866489227766260031211)
      ·
        refine ⟨2263299733841649390046817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1508866489227766260031211 2263299733841649390046817)
        ·
          refine ⟨1697474800381237042535113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2263299733841649390046817 1697474800381237042535113)
          ·
            refine ⟨1273106100285927781901335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1697474800381237042535113 1273106100285927781901335)
            ·
              refine ⟨1909659150428891672852003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1273106100285927781901335 1909659150428891672852003)
              ·
                refine ⟨2864488725643337509278005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1909659150428891672852003 2864488725643337509278005)
                ·
                  refine ⟨268545818029062891494813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2864488725643337509278005 268545818029062891494813)
                  ·
                    rfl

theorem cell20_588365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_588365 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_588365 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_588365 prefixEnd_588365 := by exact prefixLift 588365
  have htrace : WordTrace (prefixWord ++ tailWord_588365) baseStart_588365 baseEnd_588365 := by
    simpa [prefixWord, tailWord_588365, baseEnd_588365] using wordTrace_append hprefix tailTrace_588365
  have hstable : (prefixWord ++ tailWord_588365).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588365).length < 2 ^ (prefixWord ++ tailWord_588365).sum := by decide
  have hdescent : baseEnd_588365 < baseStart_588365 := by decide
  rcases family_descends (prefixWord ++ tailWord_588365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588372 : List Nat := [2, 4, 1, 1, 1, 4, 2, 1, 4]
def baseStart_588372 : Nat := 118140960795 + 588372 * 2 ^ 59
def prefixEnd_588372 : Nat := 4983230072969 + 3 ^ 40 * 588372 * 2
def baseEnd_588372 : Nat := 268549013019801978261451

theorem tailTrace_588372 : CollatzResearch.WordTrace tailWord_588372 prefixEnd_588372 268549013019801978261451 := by
  unfold tailWord_588372
  simp only [CollatzResearch.WordTrace]
  refine ⟨10729844912218102391307685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14306459882957469855076913 10729844912218102391307685)
  ·
    refine ⟨2011845921040894198370191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10729844912218102391307685 2011845921040894198370191)
    ·
      refine ⟨3017768881561341297555287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2011845921040894198370191 3017768881561341297555287)
      ·
        refine ⟨4526653322342011946332931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3017768881561341297555287 4526653322342011946332931)
        ·
          refine ⟨6789979983513017919499397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4526653322342011946332931 6789979983513017919499397)
          ·
            refine ⟨1273121246908690859906137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6789979983513017919499397 1273121246908690859906137)
            ·
              refine ⟨954840935181518144929603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1273121246908690859906137 954840935181518144929603)
              ·
                refine ⟨1432261402772277217394405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 954840935181518144929603 1432261402772277217394405)
                ·
                  refine ⟨268549013019801978261451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1432261402772277217394405 268549013019801978261451)
                  ·
                    rfl

theorem cell20_588372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_588372 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_588372 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_588372 prefixEnd_588372 := by exact prefixLift 588372
  have htrace : WordTrace (prefixWord ++ tailWord_588372) baseStart_588372 baseEnd_588372 := by
    simpa [prefixWord, tailWord_588372, baseEnd_588372] using wordTrace_append hprefix tailTrace_588372
  have hstable : (prefixWord ++ tailWord_588372).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588372).length < 2 ^ (prefixWord ++ tailWord_588372).sum := by decide
  have hdescent : baseEnd_588372 < baseStart_588372 := by decide
  rcases family_descends (prefixWord ++ tailWord_588372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588407 : List Nat := [1, 1, 3, 1, 1, 3, 3, 2, 5]
def baseStart_588407 : Nat := 118140960795 + 588407 * 2 ^ 59
def prefixEnd_588407 : Nat := 4983230072969 + 3 ^ 40 * 588407 * 2
def baseEnd_588407 : Nat := 268564987973497412094641

theorem tailTrace_588407 : CollatzResearch.WordTrace tailWord_588407 prefixEnd_588407 268564987973497412094641 := by
  unfold tailWord_588407
  simp only [CollatzResearch.WordTrace]
  refine ⟨21460966379309405760139475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14307310919539603840092983 21460966379309405760139475)
  ·
    refine ⟨32191449568964108640209213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21460966379309405760139475 32191449568964108640209213)
    ·
      refine ⟨12071793588361540740078455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32191449568964108640209213 12071793588361540740078455)
      ·
        refine ⟨18107690382542311110117683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12071793588361540740078455 18107690382542311110117683)
        ·
          refine ⟨27161535573813466665176525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18107690382542311110117683 27161535573813466665176525)
          ·
            refine ⟨10185575840180049999441197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27161535573813466665176525 10185575840180049999441197)
            ·
              refine ⟨3819590940067518749790449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10185575840180049999441197 3819590940067518749790449)
              ·
                refine ⟨2864693205050639062342837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3819590940067518749790449 2864693205050639062342837)
                ·
                  refine ⟨268564987973497412094641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2864693205050639062342837 268564987973497412094641)
                  ·
                    rfl

theorem cell20_588407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 2, 5].length) (baseStart_588407 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_588407 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_588407 prefixEnd_588407 := by exact prefixLift 588407
  have htrace : WordTrace (prefixWord ++ tailWord_588407) baseStart_588407 baseEnd_588407 := by
    simpa [prefixWord, tailWord_588407, baseEnd_588407] using wordTrace_append hprefix tailTrace_588407
  have hstable : (prefixWord ++ tailWord_588407).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588407).length < 2 ^ (prefixWord ++ tailWord_588407).sum := by decide
  have hdescent : baseEnd_588407 < baseStart_588407 := by decide
  rcases family_descends (prefixWord ++ tailWord_588407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588528 : List Nat := [2, 1, 1, 1, 3, 1, 3, 2, 6]
def baseStart_588528 : Nat := 118140960795 + 588528 * 2 ^ 59
def prefixEnd_588528 : Nat := 4983230072969 + 3 ^ 40 * 588528 * 2
def baseEnd_588528 : Nat := 268620215670558769060813

theorem tailTrace_588528 : CollatzResearch.WordTrace tailWord_588528 prefixEnd_588528 268620215670558769060813 := by
  unfold tailWord_588528
  simp only [CollatzResearch.WordTrace]
  refine ⟨10732689805935521712647119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14310253074580695616862825 10732689805935521712647119)
  ·
    refine ⟨16099034708903282568970679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10732689805935521712647119 16099034708903282568970679)
    ·
      refine ⟨24148552063354923853456019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16099034708903282568970679 24148552063354923853456019)
      ·
        refine ⟨36222828095032385780184029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24148552063354923853456019 36222828095032385780184029)
        ·
          refine ⟨13583560535637144667569011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36222828095032385780184029 13583560535637144667569011)
          ·
            refine ⟨20375340803455717001353517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13583560535637144667569011 20375340803455717001353517)
            ·
              refine ⟨7640752801295893875507569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20375340803455717001353517 7640752801295893875507569)
              ·
                refine ⟨5730564600971920406630677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7640752801295893875507569 5730564600971920406630677)
                ·
                  refine ⟨268620215670558769060813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5730564600971920406630677 268620215670558769060813)
                  ·
                    rfl

theorem cell20_588528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 2, 6].length) (baseStart_588528 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_588528 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_588528 prefixEnd_588528 := by exact prefixLift 588528
  have htrace : WordTrace (prefixWord ++ tailWord_588528) baseStart_588528 baseEnd_588528 := by
    simpa [prefixWord, tailWord_588528, baseEnd_588528] using wordTrace_append hprefix tailTrace_588528
  have hstable : (prefixWord ++ tailWord_588528).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588528).length < 2 ^ (prefixWord ++ tailWord_588528).sum := by decide
  have hdescent : baseEnd_588528 < baseStart_588528 := by decide
  rcases family_descends (prefixWord ++ tailWord_588528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588538 : List Nat := [3, 1, 1, 1, 1, 3, 5, 2, 3]
def baseStart_588538 : Nat := 118140960795 + 588538 * 2 ^ 59
def prefixEnd_588538 : Nat := 4983230072969 + 3 ^ 40 * 588538 * 2
def baseEnd_588538 : Nat := 268624779943043178727439

theorem tailTrace_588538 : CollatzResearch.WordTrace tailWord_588538 prefixEnd_588538 268624779943043178727439 := by
  unfold tailWord_588538
  simp only [CollatzResearch.WordTrace]
  refine ⟨5366436085458703783289567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14310496227889876755438845 5366436085458703783289567)
  ·
    refine ⟨8049654128188055674934351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5366436085458703783289567 8049654128188055674934351)
    ·
      refine ⟨12074481192282083512401527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8049654128188055674934351 12074481192282083512401527)
      ·
        refine ⟨18111721788423125268602291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12074481192282083512401527 18111721788423125268602291)
        ·
          refine ⟨27167582682634687902903437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18111721788423125268602291 27167582682634687902903437)
          ·
            refine ⟨10187843505988007963588789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27167582682634687902903437 10187843505988007963588789)
            ·
              refine ⟨955110328686375746586449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10187843505988007963588789 955110328686375746586449)
              ·
                refine ⟨716332746514781809939837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 955110328686375746586449 716332746514781809939837)
                ·
                  refine ⟨268624779943043178727439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 716332746514781809939837 268624779943043178727439)
                  ·
                    rfl

theorem cell20_588538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5, 2, 3].length) (baseStart_588538 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_588538 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_588538 prefixEnd_588538 := by exact prefixLift 588538
  have htrace : WordTrace (prefixWord ++ tailWord_588538) baseStart_588538 baseEnd_588538 := by
    simpa [prefixWord, tailWord_588538, baseEnd_588538] using wordTrace_append hprefix tailTrace_588538
  have hstable : (prefixWord ++ tailWord_588538).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588538).length < 2 ^ (prefixWord ++ tailWord_588538).sum := by decide
  have hdescent : baseEnd_588538 < baseStart_588538 := by decide
  rcases family_descends (prefixWord ++ tailWord_588538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588586 : List Nat := [3, 1, 4, 3, 1, 2, 6]
def baseStart_588586 : Nat := 118140960795 + 588586 * 2 ^ 59
def prefixEnd_588586 : Nat := 4983230072969 + 3 ^ 40 * 588586 * 2
def baseEnd_588586 : Nat := 29849632050107593903027

theorem tailTrace_588586 : CollatzResearch.WordTrace tailWord_588586 prefixEnd_588586 29849632050107593903027 := by
  unfold tailWord_588586
  simp only [CollatzResearch.WordTrace]
  refine ⟨5366873761415229832726403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14311663363773946220603741 5366873761415229832726403)
  ·
    refine ⟨8050310642122844749089605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5366873761415229832726403 8050310642122844749089605)
    ·
      refine ⟨1509433245398033390454301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8050310642122844749089605 1509433245398033390454301)
      ·
        refine ⟨566037467024262521420363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1509433245398033390454301 566037467024262521420363)
        ·
          refine ⟨849056200536393782130545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 566037467024262521420363 849056200536393782130545)
          ·
            refine ⟨636792150402295336597909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 849056200536393782130545 636792150402295336597909)
            ·
              refine ⟨29849632050107593903027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 636792150402295336597909 29849632050107593903027)
              ·
                rfl

theorem cell20_588586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 6].length) (baseStart_588586 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_588586 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_588586 prefixEnd_588586 := by exact prefixLift 588586
  have htrace : WordTrace (prefixWord ++ tailWord_588586) baseStart_588586 baseEnd_588586 := by
    simpa [prefixWord, tailWord_588586, baseEnd_588586] using wordTrace_append hprefix tailTrace_588586
  have hstable : (prefixWord ++ tailWord_588586).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588586).length < 2 ^ (prefixWord ++ tailWord_588586).sum := by decide
  have hdescent : baseEnd_588586 < baseStart_588586 := by decide
  rcases family_descends (prefixWord ++ tailWord_588586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588596 : List Nat := [2, 5, 1, 1, 4, 1, 1, 1, 4]
def baseStart_588596 : Nat := 118140960795 + 588596 * 2 ^ 59
def prefixEnd_588596 : Nat := 4983230072969 + 3 ^ 40 * 588596 * 2
def baseEnd_588596 : Nat := 268651252723452754793869

theorem tailTrace_588596 : CollatzResearch.WordTrace tailWord_588596 prefixEnd_588596 268651252723452754793869 := by
  unfold tailWord_588596
  simp only [CollatzResearch.WordTrace]
  refine ⟨10733929887812345519384821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14311906517083127359179761 10733929887812345519384821)
  ·
    refine ⟨1006305926982407392442327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10733929887812345519384821 1006305926982407392442327)
    ·
      refine ⟨1509458890473611088663491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1006305926982407392442327 1509458890473611088663491)
      ·
        refine ⟨2264188335710416632995237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1509458890473611088663491 2264188335710416632995237)
        ·
          refine ⟨424535312945703118686607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2264188335710416632995237 424535312945703118686607)
          ·
            refine ⟨636802969418554678029911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 424535312945703118686607 636802969418554678029911)
            ·
              refine ⟨955204454127832017044867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 636802969418554678029911 955204454127832017044867)
              ·
                refine ⟨1432806681191748025567301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 955204454127832017044867 1432806681191748025567301)
                ·
                  refine ⟨268651252723452754793869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1432806681191748025567301 268651252723452754793869)
                  ·
                    rfl

theorem cell20_588596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 1, 1, 4].length) (baseStart_588596 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_588596 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_588596 prefixEnd_588596 := by exact prefixLift 588596
  have htrace : WordTrace (prefixWord ++ tailWord_588596) baseStart_588596 baseEnd_588596 := by
    simpa [prefixWord, tailWord_588596, baseEnd_588596] using wordTrace_append hprefix tailTrace_588596
  have hstable : (prefixWord ++ tailWord_588596).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588596).length < 2 ^ (prefixWord ++ tailWord_588596).sum := by decide
  have hdescent : baseEnd_588596 < baseStart_588596 := by decide
  rcases family_descends (prefixWord ++ tailWord_588596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588652 : List Nat := [2, 2, 1, 1, 4, 1, 4, 2, 3]
def baseStart_588652 : Nat := 118140960795 + 588652 * 2 ^ 59
def prefixEnd_588652 : Nat := 4983230072969 + 3 ^ 40 * 588652 * 2
def baseEnd_588652 : Nat := 268676812649365448926973

theorem tailTrace_588652 : CollatzResearch.WordTrace tailWord_588652 prefixEnd_588652 268676812649365448926973 := by
  unfold tailWord_588652
  simp only [CollatzResearch.WordTrace]
  refine ⟨10734951131710906301404105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14313268175614541735205473 10734951131710906301404105)
  ·
    refine ⟨8051213348783179726053079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10734951131710906301404105 8051213348783179726053079)
    ·
      refine ⟨12076820023174769589079619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8051213348783179726053079 12076820023174769589079619)
      ·
        refine ⟨18115230034762154383619429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12076820023174769589079619 18115230034762154383619429)
        ·
          refine ⟨3396605631517903946928643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18115230034762154383619429 3396605631517903946928643)
          ·
            refine ⟨5094908447276855920392965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3396605631517903946928643 5094908447276855920392965)
            ·
              refine ⟨955295333864410485073681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5094908447276855920392965 955295333864410485073681)
              ·
                refine ⟨716471500398307863805261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 955295333864410485073681 716471500398307863805261)
                ·
                  refine ⟨268676812649365448926973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 716471500398307863805261 268676812649365448926973)
                  ·
                    rfl

theorem cell20_588652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 3].length) (baseStart_588652 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_588652 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_588652 prefixEnd_588652 := by exact prefixLift 588652
  have htrace : WordTrace (prefixWord ++ tailWord_588652) baseStart_588652 baseEnd_588652 := by
    simpa [prefixWord, tailWord_588652, baseEnd_588652] using wordTrace_append hprefix tailTrace_588652
  have hstable : (prefixWord ++ tailWord_588652).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588652).length < 2 ^ (prefixWord ++ tailWord_588652).sum := by decide
  have hdescent : baseEnd_588652 < baseStart_588652 := by decide
  rcases family_descends (prefixWord ++ tailWord_588652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588662 : List Nat := [5, 1, 1, 3, 1, 3, 1, 5]
def baseStart_588662 : Nat := 118140960795 + 588662 * 2 ^ 59
def prefixEnd_588662 : Nat := 4983230072969 + 3 ^ 40 * 588662 * 2
def baseEnd_588662 : Nat := 89560458973949952864533

theorem tailTrace_588662 : CollatzResearch.WordTrace tailWord_588662 prefixEnd_588662 89560458973949952864533 := by
  unfold tailWord_588662
  simp only [CollatzResearch.WordTrace]
  refine ⟨1341891687086599019417015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14313511328923722873781493 1341891687086599019417015)
  ·
    refine ⟨2012837530629898529125523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1341891687086599019417015 2012837530629898529125523)
    ·
      refine ⟨3019256295944847793688285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2012837530629898529125523 3019256295944847793688285)
      ·
        refine ⟨1132221110979317922633107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3019256295944847793688285 1132221110979317922633107)
        ·
          refine ⟨1698331666468976883949661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1132221110979317922633107 1698331666468976883949661)
          ·
            refine ⟨636874374925866331481123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1698331666468976883949661 636874374925866331481123)
            ·
              refine ⟨955311562388799497221685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 636874374925866331481123 955311562388799497221685)
              ·
                refine ⟨89560458973949952864533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 955311562388799497221685 89560458973949952864533)
                ·
                  rfl

theorem cell20_588662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 1, 5].length) (baseStart_588662 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_588662 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_588662 prefixEnd_588662 := by exact prefixLift 588662
  have htrace : WordTrace (prefixWord ++ tailWord_588662) baseStart_588662 baseEnd_588662 := by
    simpa [prefixWord, tailWord_588662, baseEnd_588662] using wordTrace_append hprefix tailTrace_588662
  have hstable : (prefixWord ++ tailWord_588662).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588662).length < 2 ^ (prefixWord ++ tailWord_588662).sum := by decide
  have hdescent : baseEnd_588662 < baseStart_588662 := by decide
  rcases family_descends (prefixWord ++ tailWord_588662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588783 : List Nat := [1, 1, 2, 1, 4, 5, 2, 1, 3]
def baseStart_588783 : Nat := 118140960795 + 588783 * 2 ^ 59
def prefixEnd_588783 : Nat := 4983230072969 + 3 ^ 40 * 588783 * 2
def baseEnd_588783 : Nat := 268736604618911215559771

theorem tailTrace_588783 : CollatzResearch.WordTrace tailWord_588783 prefixEnd_588783 268736604618911215559771 := by
  unfold tailWord_588783
  simp only [CollatzResearch.WordTrace]
  refine ⟨21474680225947221975827003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14316453483964814650551335 21474680225947221975827003)
  ·
    refine ⟨32212020338920832963740505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21474680225947221975827003 32212020338920832963740505)
    ·
      refine ⟨24159015254190624722805379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32212020338920832963740505 24159015254190624722805379)
      ·
        refine ⟨36238522881285937084208069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24159015254190624722805379 36238522881285937084208069)
        ·
          refine ⟨6794723040241113203289013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36238522881285937084208069 6794723040241113203289013)
          ·
            refine ⟨637005285022604362808345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6794723040241113203289013 637005285022604362808345)
            ·
              refine ⟨477753963766953272106259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 637005285022604362808345 477753963766953272106259)
              ·
                refine ⟨716630945650429908159389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 477753963766953272106259 716630945650429908159389)
                ·
                  refine ⟨268736604618911215559771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 716630945650429908159389 268736604618911215559771)
                  ·
                    rfl

theorem cell20_588783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 2, 1, 3].length) (baseStart_588783 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_588783 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_588783 prefixEnd_588783 := by exact prefixLift 588783
  have htrace : WordTrace (prefixWord ++ tailWord_588783) baseStart_588783 baseEnd_588783 := by
    simpa [prefixWord, tailWord_588783, baseEnd_588783] using wordTrace_append hprefix tailTrace_588783
  have hstable : (prefixWord ++ tailWord_588783).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588783).length < 2 ^ (prefixWord ++ tailWord_588783).sum := by decide
  have hdescent : baseEnd_588783 < baseStart_588783 := by decide
  rcases family_descends (prefixWord ++ tailWord_588783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588794 : List Nat := [3, 1, 1, 1, 1, 2, 1, 6, 4]
def baseStart_588794 : Nat := 118140960795 + 588794 * 2 ^ 59
def prefixEnd_588794 : Nat := 4983230072969 + 3 ^ 40 * 588794 * 2
def baseEnd_588794 : Nat := 268741625318644066193059

theorem tailTrace_588794 : CollatzResearch.WordTrace tailWord_588794 prefixEnd_588794 268741625318644066193059 := by
  unfold tailWord_588794
  simp only [CollatzResearch.WordTrace]
  refine ⟨5368770357226842713619359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14316720952604913902984957 5368770357226842713619359)
  ·
    refine ⟨8053155535840264070429039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5368770357226842713619359 8053155535840264070429039)
    ·
      refine ⟨12079733303760396105643559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8053155535840264070429039 12079733303760396105643559)
      ·
        refine ⟨18119599955640594158465339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12079733303760396105643559 18119599955640594158465339)
        ·
          refine ⟨27179399933460891237698009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18119599955640594158465339 27179399933460891237698009)
          ·
            refine ⟨20384549950095668428273507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27179399933460891237698009 20384549950095668428273507)
            ·
              refine ⟨30576824925143502642410261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20384549950095668428273507 30576824925143502642410261)
              ·
                refine ⟨1433288668366101686362981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 30576824925143502642410261 1433288668366101686362981)
                ·
                  refine ⟨268741625318644066193059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1433288668366101686362981 268741625318644066193059)
                  ·
                    rfl

theorem cell20_588794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 6, 4].length) (baseStart_588794 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_588794 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_588794 prefixEnd_588794 := by exact prefixLift 588794
  have htrace : WordTrace (prefixWord ++ tailWord_588794) baseStart_588794 baseEnd_588794 := by
    simpa [prefixWord, tailWord_588794, baseEnd_588794] using wordTrace_append hprefix tailTrace_588794
  have hstable : (prefixWord ++ tailWord_588794).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588794).length < 2 ^ (prefixWord ++ tailWord_588794).sum := by decide
  have hdescent : baseEnd_588794 < baseStart_588794 := by decide
  rcases family_descends (prefixWord ++ tailWord_588794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588825 : List Nat := [1, 2, 1, 2, 1, 1, 5, 4, 3]
def baseStart_588825 : Nat := 118140960795 + 588825 * 2 ^ 59
def prefixEnd_588825 : Nat := 4983230072969 + 3 ^ 40 * 588825 * 2
def baseEnd_588825 : Nat := 268755774563345736159599

theorem tailTrace_588825 : CollatzResearch.WordTrace tailWord_588825 prefixEnd_588825 268755774563345736159599 := by
  unfold tailWord_588825
  simp only [CollatzResearch.WordTrace]
  refine ⟨21476212091795063148855929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14317474727863375432570619 21476212091795063148855929)
  ·
    refine ⟨16107159068846297361641947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21476212091795063148855929 16107159068846297361641947)
    ·
      refine ⟨24160738603269446042462921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16107159068846297361641947 24160738603269446042462921)
      ·
        refine ⟨18120553952452084531847191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24160738603269446042462921 18120553952452084531847191)
        ·
          refine ⟨27180830928678126797770787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18120553952452084531847191 27180830928678126797770787)
          ·
            refine ⟨40771246393017190196656181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27180830928678126797770787 40771246393017190196656181)
            ·
              refine ⟨3822304349345361580936517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40771246393017190196656181 3822304349345361580936517)
              ·
                refine ⟨716682065502255296425597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3822304349345361580936517 716682065502255296425597)
                ·
                  refine ⟨268755774563345736159599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 716682065502255296425597 268755774563345736159599)
                  ·
                    rfl

theorem cell20_588825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 4, 3].length) (baseStart_588825 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_588825 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_588825 prefixEnd_588825 := by exact prefixLift 588825
  have htrace : WordTrace (prefixWord ++ tailWord_588825) baseStart_588825 baseEnd_588825 := by
    simpa [prefixWord, tailWord_588825, baseEnd_588825] using wordTrace_append hprefix tailTrace_588825
  have hstable : (prefixWord ++ tailWord_588825).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588825).length < 2 ^ (prefixWord ++ tailWord_588825).sum := by decide
  have hdescent : baseEnd_588825 < baseStart_588825 := by decide
  rcases family_descends (prefixWord ++ tailWord_588825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588852 : List Nat := [2, 5, 1, 2, 1, 2, 3, 4]
def baseStart_588852 : Nat := 118140960795 + 588852 * 2 ^ 59
def prefixEnd_588852 : Nat := 4983230072969 + 3 ^ 40 * 588852 * 2
def baseEnd_588852 : Nat := 89589366033017880753163

theorem tailTrace_588852 : CollatzResearch.WordTrace tailWord_588852 prefixEnd_588852 89589366033017880753163 := by
  unfold tailWord_588852
  simp only [CollatzResearch.WordTrace]
  refine ⟨10738598431348623380044405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14318131241798164506725873 10738598431348623380044405)
  ·
    refine ⟨1006743602938933441879163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10738598431348623380044405 1006743602938933441879163)
    ·
      refine ⟨1510115404408400162818745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1006743602938933441879163 1510115404408400162818745)
      ·
        refine ⟨1132586553306300122114059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1510115404408400162818745 1132586553306300122114059)
        ·
          refine ⟨1698879829959450183171089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1132586553306300122114059 1698879829959450183171089)
          ·
            refine ⟨1274159872469587637378317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1698879829959450183171089 1274159872469587637378317)
            ·
              refine ⟨477809952176095364016869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1274159872469587637378317 477809952176095364016869)
              ·
                refine ⟨89589366033017880753163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 477809952176095364016869 89589366033017880753163)
                ·
                  rfl

theorem cell20_588852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 3, 4].length) (baseStart_588852 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_588852 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_588852 prefixEnd_588852 := by exact prefixLift 588852
  have htrace : WordTrace (prefixWord ++ tailWord_588852) baseStart_588852 baseEnd_588852 := by
    simpa [prefixWord, tailWord_588852, baseEnd_588852] using wordTrace_append hprefix tailTrace_588852
  have hstable : (prefixWord ++ tailWord_588852).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588852).length < 2 ^ (prefixWord ++ tailWord_588852).sum := by decide
  have hdescent : baseEnd_588852 < baseStart_588852 := by decide
  rcases family_descends (prefixWord ++ tailWord_588852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588908 : List Nat := [2, 2, 1, 1, 3, 2, 1, 4, 4]
def baseStart_588908 : Nat := 118140960795 + 588908 * 2 ^ 59
def prefixEnd_588908 : Nat := 4983230072969 + 3 ^ 40 * 588908 * 2
def baseEnd_588908 : Nat := 268793658024966336392593

theorem tailTrace_588908 : CollatzResearch.WordTrace tailWord_588908 prefixEnd_588908 268793658024966336392593 := by
  unfold tailWord_588908
  simp only [CollatzResearch.WordTrace]
  refine ⟨10739619675247184162063689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14319492900329578882751585 10739619675247184162063689)
  ·
    refine ⟨8054714756435388121547767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10739619675247184162063689 8054714756435388121547767)
    ·
      refine ⟨12082072134653082182321651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8054714756435388121547767 12082072134653082182321651)
      ·
        refine ⟨18123108201979623273482477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12082072134653082182321651 18123108201979623273482477)
        ·
          refine ⟨6796165575742358727555929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18123108201979623273482477 6796165575742358727555929)
          ·
            refine ⟨5097124181806769045666947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6796165575742358727555929 5097124181806769045666947)
            ·
              refine ⟨7645686272710153568500421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5097124181806769045666947 7645686272710153568500421)
              ·
                refine ⟨1433566176133153794093829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7645686272710153568500421 1433566176133153794093829)
                ·
                  refine ⟨268793658024966336392593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1433566176133153794093829 268793658024966336392593)
                  ·
                    rfl

theorem cell20_588908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 4].length) (baseStart_588908 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_588908 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_588908 prefixEnd_588908 := by exact prefixLift 588908
  have htrace : WordTrace (prefixWord ++ tailWord_588908) baseStart_588908 baseEnd_588908 := by
    simpa [prefixWord, tailWord_588908, baseEnd_588908] using wordTrace_append hprefix tailTrace_588908
  have hstable : (prefixWord ++ tailWord_588908).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588908).length < 2 ^ (prefixWord ++ tailWord_588908).sum := by decide
  have hdescent : baseEnd_588908 < baseStart_588908 := by decide
  rcases family_descends (prefixWord ++ tailWord_588908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588917 : List Nat := [1, 3, 4, 3, 2, 1, 1, 3, 2]
def baseStart_588917 : Nat := 118140960795 + 588917 * 2 ^ 59
def prefixEnd_588917 : Nat := 4983230072969 + 3 ^ 40 * 588917 * 2
def baseEnd_588917 : Nat := 268797765870202305092557

theorem tailTrace_588917 : CollatzResearch.WordTrace tailWord_588917 prefixEnd_588917 268797765870202305092557 := by
  unfold tailWord_588917
  simp only [CollatzResearch.WordTrace]
  refine ⟨21479567607461762861205005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14319711738307841907470003 21479567607461762861205005)
  ·
    refine ⟨8054837852798161072951877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21479567607461762861205005 8054837852798161072951877)
    ·
      refine ⟨1510282097399655201178477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8054837852798161072951877 1510282097399655201178477)
      ·
        refine ⟨566355786524870700441929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1510282097399655201178477 566355786524870700441929)
        ·
          refine ⟨424766839893653025331447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 566355786524870700441929 424766839893653025331447)
          ·
            refine ⟨637150259840479537997171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 424766839893653025331447 637150259840479537997171)
            ·
              refine ⟨955725389760719306995757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 637150259840479537997171 955725389760719306995757)
              ·
                refine ⟨358397021160269740123409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 955725389760719306995757 358397021160269740123409)
                ·
                  refine ⟨268797765870202305092557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 358397021160269740123409 268797765870202305092557)
                  ·
                    rfl

theorem cell20_588917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 1, 3, 2].length) (baseStart_588917 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_588917 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_588917 prefixEnd_588917 := by exact prefixLift 588917
  have htrace : WordTrace (prefixWord ++ tailWord_588917) baseStart_588917 baseEnd_588917 := by
    simpa [prefixWord, tailWord_588917, baseEnd_588917] using wordTrace_append hprefix tailTrace_588917
  have hstable : (prefixWord ++ tailWord_588917).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588917).length < 2 ^ (prefixWord ++ tailWord_588917).sum := by decide
  have hdescent : baseEnd_588917 < baseStart_588917 := by decide
  rcases family_descends (prefixWord ++ tailWord_588917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588921 : List Nat := [1, 2, 1, 3, 5, 2, 1, 3, 2]
def baseStart_588921 : Nat := 118140960795 + 588921 * 2 ^ 59
def prefixEnd_588921 : Nat := 4983230072969 + 3 ^ 40 * 588921 * 2
def baseEnd_588921 : Nat := 268799591579196068959207

theorem tailTrace_588921 : CollatzResearch.WordTrace tailWord_588921 prefixEnd_588921 268799591579196068959207 := by
  unfold tailWord_588921
  simp only [CollatzResearch.WordTrace]
  refine ⟨21479713499447271544350617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14319808999631514362900411 21479713499447271544350617)
  ·
    refine ⟨16109785124585453658262963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21479713499447271544350617 16109785124585453658262963)
    ·
      refine ⟨24164677686878180487394445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16109785124585453658262963 24164677686878180487394445)
      ·
        refine ⟨9061754132579317682772917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24164677686878180487394445 9061754132579317682772917)
        ·
          refine ⟨849539449929311032759961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9061754132579317682772917 849539449929311032759961)
          ·
            refine ⟨637154587446983274569971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 849539449929311032759961 637154587446983274569971)
            ·
              refine ⟨955731881170474911854957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 637154587446983274569971 955731881170474911854957)
              ·
                refine ⟨358399455438928091945609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 955731881170474911854957 358399455438928091945609)
                ·
                  refine ⟨268799591579196068959207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 358399455438928091945609 268799591579196068959207)
                  ·
                    rfl

theorem cell20_588921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 1, 3, 2].length) (baseStart_588921 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_588921 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_588921 prefixEnd_588921 := by exact prefixLift 588921
  have htrace : WordTrace (prefixWord ++ tailWord_588921) baseStart_588921 baseEnd_588921 := by
    simpa [prefixWord, tailWord_588921, baseEnd_588921] using wordTrace_append hprefix tailTrace_588921
  have hstable : (prefixWord ++ tailWord_588921).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588921).length < 2 ^ (prefixWord ++ tailWord_588921).sum := by decide
  have hdescent : baseEnd_588921 < baseStart_588921 := by decide
  rcases family_descends (prefixWord ++ tailWord_588921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588932 : List Nat := [2, 3, 2, 1, 2, 4, 6]
def baseStart_588932 : Nat := 118140960795 + 588932 * 2 ^ 59
def prefixEnd_588932 : Nat := 4983230072969 + 3 ^ 40 * 588932 * 2
def baseEnd_588932 : Nat := 29867179142103213288055

theorem tailTrace_588932 : CollatzResearch.WordTrace tailWord_588932 prefixEnd_588932 29867179142103213288055 := by
  unfold tailWord_588932
  simp only [CollatzResearch.WordTrace]
  refine ⟨10740057351203710211500525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14320076468271613615334033 10740057351203710211500525)
  ·
    refine ⟨4027521506701391329312697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10740057351203710211500525 4027521506701391329312697)
    ·
      refine ⟨3020641130026043496984523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4027521506701391329312697 3020641130026043496984523)
      ·
        refine ⟨4530961695039065245476785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3020641130026043496984523 4530961695039065245476785)
        ·
          refine ⟨3398221271279298934107589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4530961695039065245476785 3398221271279298934107589)
          ·
            refine ⟨637166488364868550145173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3398221271279298934107589 637166488364868550145173)
            ·
              refine ⟨29867179142103213288055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 637166488364868550145173 29867179142103213288055)
              ·
                rfl

theorem cell20_588932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 6].length) (baseStart_588932 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_588932 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_588932 prefixEnd_588932 := by exact prefixLift 588932
  have htrace : WordTrace (prefixWord ++ tailWord_588932) baseStart_588932 baseEnd_588932 := by
    simpa [prefixWord, tailWord_588932, baseEnd_588932] using wordTrace_append hprefix tailTrace_588932
  have hstable : (prefixWord ++ tailWord_588932).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588932).length < 2 ^ (prefixWord ++ tailWord_588932).sum := by decide
  have hdescent : baseEnd_588932 < baseStart_588932 := by decide
  rcases family_descends (prefixWord ++ tailWord_588932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
