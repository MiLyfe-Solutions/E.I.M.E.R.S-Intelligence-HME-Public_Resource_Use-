import V185TrunkScan22Chunk236

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2113209 : List Nat := [1, 2, 1, 4, 1, 1, 4, 2, 1, 5]
def baseStart_2113209 : Nat := 118140960795 + 2113209 * 2 ^ 59
def prefixEnd_2113209 : Nat := 4983230072969 + 3 ^ 40 * 2113209 * 2
def baseEnd_2113209 : Nat := 723394626938085195846023

theorem tailTrace_2113209 : CollatzResearch.WordTrace tailWord_2113209 prefixEnd_2113209 723394626938085195846023 := by
  unfold tailWord_2113209
  simp only [CollatzResearch.WordTrace]
  refine ⟨77075064201212175209006681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51383376134141450139337787 77075064201212175209006681)
  ·
    refine ⟨57806298150909131406755011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77075064201212175209006681 57806298150909131406755011)
    ·
      refine ⟨86709447226363697110132517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57806298150909131406755011 86709447226363697110132517)
      ·
        refine ⟨16258021354943193208149847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 86709447226363697110132517 16258021354943193208149847)
        ·
          refine ⟨24387032032414789812224771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16258021354943193208149847 24387032032414789812224771)
          ·
            refine ⟨36580548048622184718337157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24387032032414789812224771 36580548048622184718337157)
            ·
              refine ⟨6858852759116659634688217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36580548048622184718337157 6858852759116659634688217)
              ·
                refine ⟨5144139569337494726016163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6858852759116659634688217 5144139569337494726016163)
                ·
                  refine ⟨7716209354006242089024245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5144139569337494726016163 7716209354006242089024245)
                  ·
                    refine ⟨723394626938085195846023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7716209354006242089024245 723394626938085195846023)
                    ·
                      rfl

theorem cell22_2113209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 2, 1, 5].length) (baseStart_2113209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2113209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2113209 prefixEnd_2113209 := by exact prefixLift 2113209
  have htrace : WordTrace (prefixWord ++ tailWord_2113209) baseStart_2113209 baseEnd_2113209 := by
    simpa [prefixWord, tailWord_2113209, baseEnd_2113209] using wordTrace_append hprefix tailTrace_2113209
  have hstable : (prefixWord ++ tailWord_2113209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2113209).length < 2 ^ (prefixWord ++ tailWord_2113209).sum := by decide
  have hdescent : baseEnd_2113209 < baseStart_2113209 := by decide
  rcases family_descends (prefixWord ++ tailWord_2113209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2113224 : List Nat := [2, 1, 3, 1, 2, 2, 2, 1, 4, 4]
def baseStart_2113224 : Nat := 118140960795 + 2113224 * 2 ^ 59
def prefixEnd_2113224 : Nat := 4983230072969 + 3 ^ 40 * 2113224 * 2
def baseEnd_2113224 : Nat := 723399761744630156720977

theorem tailTrace_2113224 : CollatzResearch.WordTrace tailWord_2113224 prefixEnd_2113224 723399761744630156720977 := by
  unfold tailWord_2113224
  simp only [CollatzResearch.WordTrace]
  refine ⟨38537805648078916385401363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51383740864105221847201817 38537805648078916385401363)
  ·
    refine ⟨57806708472118374578102045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38537805648078916385401363 57806708472118374578102045)
    ·
      refine ⟨21677515677044390466788267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57806708472118374578102045 21677515677044390466788267)
      ·
        refine ⟨32516273515566585700182401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21677515677044390466788267 32516273515566585700182401)
        ·
          refine ⟨24387205136674939275136801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32516273515566585700182401 24387205136674939275136801)
          ·
            refine ⟨18290403852506204456352601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24387205136674939275136801 18290403852506204456352601)
            ·
              refine ⟨13717802889379653342264451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18290403852506204456352601 13717802889379653342264451)
              ·
                refine ⟨20576704334069480013396677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13717802889379653342264451 20576704334069480013396677)
                ·
                  refine ⟨3858132062638027502511877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20576704334069480013396677 3858132062638027502511877)
                  ·
                    refine ⟨723399761744630156720977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3858132062638027502511877 723399761744630156720977)
                    ·
                      rfl

theorem cell22_2113224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 1, 4, 4].length) (baseStart_2113224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2113224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2113224 prefixEnd_2113224 := by exact prefixLift 2113224
  have htrace : WordTrace (prefixWord ++ tailWord_2113224) baseStart_2113224 baseEnd_2113224 := by
    simpa [prefixWord, tailWord_2113224, baseEnd_2113224] using wordTrace_append hprefix tailTrace_2113224
  have hstable : (prefixWord ++ tailWord_2113224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2113224).length < 2 ^ (prefixWord ++ tailWord_2113224).sum := by decide
  have hdescent : baseEnd_2113224 < baseStart_2113224 := by decide
  rcases family_descends (prefixWord ++ tailWord_2113224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2113256 : List Nat := [2, 1, 4, 1, 3, 1, 4, 6]
def baseStart_2113256 : Nat := 118140960795 + 2113256 * 2 ^ 59
def prefixEnd_2113256 : Nat := 4983230072969 + 3 ^ 40 * 2113256 * 2
def baseEnd_2113256 : Nat := 80378968444288082213431

theorem tailTrace_2113256 : CollatzResearch.WordTrace tailWord_2113256 prefixEnd_2113256 80378968444288082213431 := by
  unfold tailWord_2113256
  simp only [CollatzResearch.WordTrace]
  refine ⟨38538389216020951117983811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51384518954694601490645081 38538389216020951117983811)
  ·
    refine ⟨57807583824031426676975717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38538389216020951117983811 57807583824031426676975717)
    ·
      refine ⟨10838921967005892501932947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57807583824031426676975717 10838921967005892501932947)
      ·
        refine ⟨16258382950508838752899421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10838921967005892501932947 16258382950508838752899421)
        ·
          refine ⟨6096893606440814532337283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16258382950508838752899421 6096893606440814532337283)
          ·
            refine ⟨9145340409661221798505925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6096893606440814532337283 9145340409661221798505925)
            ·
              refine ⟨1714751326811479087219861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9145340409661221798505925 1714751326811479087219861)
              ·
                refine ⟨80378968444288082213431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1714751326811479087219861 80378968444288082213431)
                ·
                  rfl

theorem cell22_2113256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 4, 6].length) (baseStart_2113256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2113256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2113256 prefixEnd_2113256 := by exact prefixLift 2113256
  have htrace : WordTrace (prefixWord ++ tailWord_2113256) baseStart_2113256 baseEnd_2113256 := by
    simpa [prefixWord, tailWord_2113256, baseEnd_2113256] using wordTrace_append hprefix tailTrace_2113256
  have hstable : (prefixWord ++ tailWord_2113256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2113256).length < 2 ^ (prefixWord ++ tailWord_2113256).sum := by decide
  have hdescent : baseEnd_2113256 < baseStart_2113256 := by decide
  rcases family_descends (prefixWord ++ tailWord_2113256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2113301 : List Nat := [1, 3, 2, 1, 2, 4, 1, 3, 5]
def baseStart_2113301 : Nat := 118140960795 + 2113301 * 2 ^ 59
def prefixEnd_2113301 : Nat := 4983230072969 + 3 ^ 40 * 2113301 * 2
def baseEnd_2113301 : Nat := 241142040139409207515247

theorem tailTrace_2113301 : CollatzResearch.WordTrace tailWord_2113301 prefixEnd_2113301 241142040139409207515247 := by
  unfold tailWord_2113301
  simp only [CollatzResearch.WordTrace]
  refine ⟨77078419716878874921355757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51385613144585916614237171 77078419716878874921355757)
  ·
    refine ⟨28904407393829578095508409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77078419716878874921355757 28904407393829578095508409)
    ·
      refine ⟨21678305545372183571631307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28904407393829578095508409 21678305545372183571631307)
      ·
        refine ⟨32517458318058275357446961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21678305545372183571631307 32517458318058275357446961)
        ·
          refine ⟨24388093738543706518085221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32517458318058275357446961 24388093738543706518085221)
          ·
            refine ⟨4572767575976944972140979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24388093738543706518085221 4572767575976944972140979)
            ·
              refine ⟨6859151363965417458211469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4572767575976944972140979 6859151363965417458211469)
              ·
                refine ⟨2572181761487031546829301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6859151363965417458211469 2572181761487031546829301)
                ·
                  refine ⟨241142040139409207515247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2572181761487031546829301 241142040139409207515247)
                  ·
                    rfl

theorem cell22_2113301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 3, 5].length) (baseStart_2113301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2113301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2113301 prefixEnd_2113301 := by exact prefixLift 2113301
  have htrace : WordTrace (prefixWord ++ tailWord_2113301) baseStart_2113301 baseEnd_2113301 := by
    simpa [prefixWord, tailWord_2113301, baseEnd_2113301] using wordTrace_append hprefix tailTrace_2113301
  have hstable : (prefixWord ++ tailWord_2113301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2113301).length < 2 ^ (prefixWord ++ tailWord_2113301).sum := by decide
  have hdescent : baseEnd_2113301 < baseStart_2113301 := by decide
  rcases family_descends (prefixWord ++ tailWord_2113301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2113350 : List Nat := [6, 1, 1, 2, 1, 2, 1, 1, 2, 5]
def baseStart_2113350 : Nat := 118140960795 + 2113350 * 2 ^ 59
def prefixEnd_2113350 : Nat := 4983230072969 + 3 ^ 40 * 2113350 * 2
def baseEnd_2113350 : Nat := 723442894119607828070591

theorem tailTrace_2113350 : CollatzResearch.WordTrace tailWord_2113350 prefixEnd_2113350 723442894119607828070591 := by
  unfold tailWord_2113350
  simp only [CollatzResearch.WordTrace]
  refine ⟨2408756465428167384059047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 51386804595800904193259669 2408756465428167384059047)
  ·
    refine ⟨3613134698142251076088571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2408756465428167384059047 3613134698142251076088571)
    ·
      refine ⟨5419702047213376614132857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3613134698142251076088571 5419702047213376614132857)
      ·
        refine ⟨4064776535410032460599643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5419702047213376614132857 4064776535410032460599643)
        ·
          refine ⟨6097164803115048690899465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4064776535410032460599643 6097164803115048690899465)
          ·
            refine ⟨4572873602336286518174599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6097164803115048690899465 4572873602336286518174599)
            ·
              refine ⟨6859310403504429777261899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4572873602336286518174599 6859310403504429777261899)
              ·
                refine ⟨10288965605256644665892849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6859310403504429777261899 10288965605256644665892849)
                ·
                  refine ⟨7716724203942483499419637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10288965605256644665892849 7716724203942483499419637)
                  ·
                    refine ⟨723442894119607828070591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7716724203942483499419637 723442894119607828070591)
                    ·
                      rfl

theorem cell22_2113350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_2113350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2113350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2113350 prefixEnd_2113350 := by exact prefixLift 2113350
  have htrace : WordTrace (prefixWord ++ tailWord_2113350) baseStart_2113350 baseEnd_2113350 := by
    simpa [prefixWord, tailWord_2113350, baseEnd_2113350] using wordTrace_append hprefix tailTrace_2113350
  have hstable : (prefixWord ++ tailWord_2113350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2113350).length < 2 ^ (prefixWord ++ tailWord_2113350).sum := by decide
  have hdescent : baseEnd_2113350 < baseStart_2113350 := by decide
  rcases family_descends (prefixWord ++ tailWord_2113350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2113361 : List Nat := [1, 2, 2, 1, 5, 1, 1, 3, 1, 5]
def baseStart_2113361 : Nat := 118140960795 + 2113361 * 2 ^ 59
def prefixEnd_2113361 : Nat := 4983230072969 + 3 ^ 40 * 2113361 * 2
def baseEnd_2113361 : Nat := 723446659644407466045557

theorem tailTrace_2113361 : CollatzResearch.WordTrace tailWord_2113361 prefixEnd_2113361 723446659644407466045557 := by
  unfold tailWord_2113361
  simp only [CollatzResearch.WordTrace]
  refine ⟨77080608096661505168539937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51387072064441003445693291 77080608096661505168539937)
  ·
    refine ⟨57810456072496128876404953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77080608096661505168539937 57810456072496128876404953)
    ·
      refine ⟨43357842054372096657303715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57810456072496128876404953 43357842054372096657303715)
      ·
        refine ⟨65036763081558144985955573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43357842054372096657303715 65036763081558144985955573)
        ·
          refine ⟨6097196538896076092433335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 65036763081558144985955573 6097196538896076092433335)
          ·
            refine ⟨9145794808344114138650003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6097196538896076092433335 9145794808344114138650003)
            ·
              refine ⟨13718692212516171207975005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9145794808344114138650003 13718692212516171207975005)
              ·
                refine ⟨5144509579693564202990627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13718692212516171207975005 5144509579693564202990627)
                ·
                  refine ⟨7716764369540346304485941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5144509579693564202990627 7716764369540346304485941)
                  ·
                    refine ⟨723446659644407466045557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7716764369540346304485941 723446659644407466045557)
                    ·
                      rfl

theorem cell22_2113361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 3, 1, 5].length) (baseStart_2113361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2113361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2113361 prefixEnd_2113361 := by exact prefixLift 2113361
  have htrace : WordTrace (prefixWord ++ tailWord_2113361) baseStart_2113361 baseEnd_2113361 := by
    simpa [prefixWord, tailWord_2113361, baseEnd_2113361] using wordTrace_append hprefix tailTrace_2113361
  have hstable : (prefixWord ++ tailWord_2113361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2113361).length < 2 ^ (prefixWord ++ tailWord_2113361).sum := by decide
  have hdescent : baseEnd_2113361 < baseStart_2113361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2113361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2113376 : List Nat := [2, 1, 1, 3, 3, 3, 1, 1, 1, 6]
def baseStart_2113376 : Nat := 118140960795 + 2113376 * 2 ^ 59
def prefixEnd_2113376 : Nat := 4983230072969 + 3 ^ 40 * 2113376 * 2
def baseEnd_2113376 : Nat := 723451794450952426920511

theorem tailTrace_2113376 : CollatzResearch.WordTrace tailWord_2113376 prefixEnd_2113376 723451794450952426920511 := by
  unfold tailWord_2113376
  simp only [CollatzResearch.WordTrace]
  refine ⟨38540577595803581365167991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51387436794404775153557321 38540577595803581365167991)
  ·
    refine ⟨57810866393705372047751987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38540577595803581365167991 57810866393705372047751987)
    ·
      refine ⟨86716299590558058071627981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57810866393705372047751987 86716299590558058071627981)
      ·
        refine ⟨32518612346459271776860493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86716299590558058071627981 32518612346459271776860493)
        ·
          refine ⟨12194479629922226916322685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32518612346459271776860493 12194479629922226916322685)
          ·
            refine ⟨4572929861220835093621007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12194479629922226916322685 4572929861220835093621007)
            ·
              refine ⟨6859394791831252640431511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4572929861220835093621007 6859394791831252640431511)
              ·
                refine ⟨10289092187746878960647267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6859394791831252640431511 10289092187746878960647267)
                ·
                  refine ⟨15433638281620318440970901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10289092187746878960647267 15433638281620318440970901)
                  ·
                    refine ⟨723451794450952426920511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15433638281620318440970901 723451794450952426920511)
                    ·
                      rfl

theorem cell22_2113376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 1, 1, 6].length) (baseStart_2113376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2113376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2113376 prefixEnd_2113376 := by exact prefixLift 2113376
  have htrace : WordTrace (prefixWord ++ tailWord_2113376) baseStart_2113376 baseEnd_2113376 := by
    simpa [prefixWord, tailWord_2113376, baseEnd_2113376] using wordTrace_append hprefix tailTrace_2113376
  have hstable : (prefixWord ++ tailWord_2113376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2113376).length < 2 ^ (prefixWord ++ tailWord_2113376).sum := by decide
  have hdescent : baseEnd_2113376 < baseStart_2113376 := by decide
  rcases family_descends (prefixWord ++ tailWord_2113376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2113378 : List Nat := [3, 3, 2, 1, 2, 1, 2, 2, 1, 5]
def baseStart_2113378 : Nat := 118140960795 + 2113378 * 2 ^ 59
def prefixEnd_2113378 : Nat := 4983230072969 + 3 ^ 40 * 2113378 * 2
def baseEnd_2113378 : Nat := 723452479091825088370505

theorem tailTrace_2113378 : CollatzResearch.WordTrace tailWord_2113378 prefixEnd_2113378 723452479091825088370505 := by
  unfold tailWord_2113378
  simp only [CollatzResearch.WordTrace]
  refine ⟨19270307034399979267977197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51387485425066611381272525 19270307034399979267977197)
  ·
    refine ⟨7226365137899992225491449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19270307034399979267977197 7226365137899992225491449)
    ·
      refine ⟨5419773853424994169118587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7226365137899992225491449 5419773853424994169118587)
      ·
        refine ⟨8129660780137491253677881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5419773853424994169118587 8129660780137491253677881)
        ·
          refine ⟨6097245585103118440258411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8129660780137491253677881 6097245585103118440258411)
          ·
            refine ⟨9145868377654677660387617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6097245585103118440258411 9145868377654677660387617)
            ·
              refine ⟨6859401283241008245290713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9145868377654677660387617 6859401283241008245290713)
              ·
                refine ⟨5144550962430756183968035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6859401283241008245290713 5144550962430756183968035)
                ·
                  refine ⟨7716826443646134275952053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5144550962430756183968035 7716826443646134275952053)
                  ·
                    refine ⟨723452479091825088370505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7716826443646134275952053 723452479091825088370505)
                    ·
                      rfl

theorem cell22_2113378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_2113378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2113378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2113378 prefixEnd_2113378 := by exact prefixLift 2113378
  have htrace : WordTrace (prefixWord ++ tailWord_2113378) baseStart_2113378 baseEnd_2113378 := by
    simpa [prefixWord, tailWord_2113378, baseEnd_2113378] using wordTrace_append hprefix tailTrace_2113378
  have hstable : (prefixWord ++ tailWord_2113378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2113378).length < 2 ^ (prefixWord ++ tailWord_2113378).sum := by decide
  have hdescent : baseEnd_2113378 < baseStart_2113378 := by decide
  rcases family_descends (prefixWord ++ tailWord_2113378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2113380 : List Nat := [2, 3, 1, 1, 5, 1, 2, 3, 4]
def baseStart_2113380 : Nat := 118140960795 + 2113380 * 2 ^ 59
def prefixEnd_2113380 : Nat := 4983230072969 + 3 ^ 40 * 2113380 * 2
def baseEnd_2113380 : Nat := 241151054577565916606833

theorem tailTrace_2113380 : CollatzResearch.WordTrace tailWord_2113380 prefixEnd_2113380 241151054577565916606833 := by
  unfold tailWord_2113380
  simp only [CollatzResearch.WordTrace]
  refine ⟨38540650541796335706740797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51387534055728447608987729 38540650541796335706740797)
  ·
    refine ⟨14452743953173625890027799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38540650541796335706740797 14452743953173625890027799)
    ·
      refine ⟨21679115929760438835041699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14452743953173625890027799 21679115929760438835041699)
      ·
        refine ⟨32518673894640658252562549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21679115929760438835041699 32518673894640658252562549)
        ·
          refine ⟨3048625677622561711177739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32518673894640658252562549 3048625677622561711177739)
          ·
            refine ⟨4572938516433842566766609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3048625677622561711177739 4572938516433842566766609)
            ·
              refine ⟨3429703887325381925074957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4572938516433842566766609 3429703887325381925074957)
              ·
                refine ⟨1286138957747018221903109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3429703887325381925074957 1286138957747018221903109)
                ·
                  refine ⟨241151054577565916606833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1286138957747018221903109 241151054577565916606833)
                  ·
                    rfl

theorem cell22_2113380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 2, 3, 4].length) (baseStart_2113380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2113380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2113380 prefixEnd_2113380 := by exact prefixLift 2113380
  have htrace : WordTrace (prefixWord ++ tailWord_2113380) baseStart_2113380 baseEnd_2113380 := by
    simpa [prefixWord, tailWord_2113380, baseEnd_2113380] using wordTrace_append hprefix tailTrace_2113380
  have hstable : (prefixWord ++ tailWord_2113380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2113380).length < 2 ^ (prefixWord ++ tailWord_2113380).sum := by decide
  have hdescent : baseEnd_2113380 < baseStart_2113380 := by decide
  rcases family_descends (prefixWord ++ tailWord_2113380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2113470 : List Nat := [4, 2, 1, 1, 1, 3, 4, 1, 5]
def baseStart_2113470 : Nat := 118140960795 + 2113470 * 2 ^ 59
def prefixEnd_2113470 : Nat := 4983230072969 + 3 ^ 40 * 2113470 * 2
def baseEnd_2113470 : Nat := 241161324190655838356741

theorem tailTrace_2113470 : CollatzResearch.WordTrace tailWord_2113470 prefixEnd_2113470 241161324190655838356741 := by
  unfold tailWord_2113470
  simp only [CollatzResearch.WordTrace]
  refine ⟨9635572956658327098032233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51389722435511077856171909 9635572956658327098032233)
  ·
    refine ⟨7226679717493745323524175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9635572956658327098032233 7226679717493745323524175)
    ·
      refine ⟨10840019576240617985286263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7226679717493745323524175 10840019576240617985286263)
      ·
        refine ⟨16260029364360926977929395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10840019576240617985286263 16260029364360926977929395)
        ·
          refine ⟨24390044046541390466894093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16260029364360926977929395 24390044046541390466894093)
          ·
            refine ⟨9146266517453021425085285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24390044046541390466894093 9146266517453021425085285)
            ·
              refine ⟨1714924972022441517203491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9146266517453021425085285 1714924972022441517203491)
              ·
                refine ⟨2572387458033662275805237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1714924972022441517203491 2572387458033662275805237)
                ·
                  refine ⟨241161324190655838356741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2572387458033662275805237 241161324190655838356741)
                  ·
                    rfl

theorem cell22_2113470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 4, 1, 5].length) (baseStart_2113470 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2113470 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2113470 prefixEnd_2113470 := by exact prefixLift 2113470
  have htrace : WordTrace (prefixWord ++ tailWord_2113470) baseStart_2113470 baseEnd_2113470 := by
    simpa [prefixWord, tailWord_2113470, baseEnd_2113470] using wordTrace_append hprefix tailTrace_2113470
  have hstable : (prefixWord ++ tailWord_2113470).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2113470).length < 2 ^ (prefixWord ++ tailWord_2113470).sum := by decide
  have hdescent : baseEnd_2113470 < baseStart_2113470 := by decide
  rcases family_descends (prefixWord ++ tailWord_2113470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2113622 : List Nat := [5, 2, 2, 1, 1, 1, 2, 1, 7]
def baseStart_2113622 : Nat := 118140960795 + 2113622 * 2 ^ 59
def prefixEnd_2113622 : Nat := 4983230072969 + 3 ^ 40 * 2113622 * 2
def baseEnd_2113622 : Nat := 241178668426096595089919

theorem tailTrace_2113622 : CollatzResearch.WordTrace tailWord_2113622 prefixEnd_2113622 241178668426096595089919 := by
  unfold tailWord_2113622
  simp only [CollatzResearch.WordTrace]
  refine ⟨4818132971794746671486945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 51393418365810631162527413 4818132971794746671486945)
  ·
    refine ⟨3613599728846060003615209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4818132971794746671486945 3613599728846060003615209)
    ·
      refine ⟨2710199796634545002711407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3613599728846060003615209 2710199796634545002711407)
      ·
        refine ⟨4065299694951817504067111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2710199796634545002711407 4065299694951817504067111)
        ·
          refine ⟨6097949542427726256100667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4065299694951817504067111 6097949542427726256100667)
          ·
            refine ⟨9146924313641589384151001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6097949542427726256100667 9146924313641589384151001)
            ·
              refine ⟨6860193235231192038113251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9146924313641589384151001 6860193235231192038113251)
              ·
                refine ⟨10290289852846788057169877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6860193235231192038113251 10290289852846788057169877)
                ·
                  refine ⟨241178668426096595089919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10290289852846788057169877 241178668426096595089919)
                  ·
                    rfl

theorem cell22_2113622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_2113622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2113622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2113622 prefixEnd_2113622 := by exact prefixLift 2113622
  have htrace : WordTrace (prefixWord ++ tailWord_2113622) baseStart_2113622 baseEnd_2113622 := by
    simpa [prefixWord, tailWord_2113622, baseEnd_2113622] using wordTrace_append hprefix tailTrace_2113622
  have hstable : (prefixWord ++ tailWord_2113622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2113622).length < 2 ^ (prefixWord ++ tailWord_2113622).sum := by decide
  have hdescent : baseEnd_2113622 < baseStart_2113622 := by decide
  rcases family_descends (prefixWord ++ tailWord_2113622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2113678 : List Nat := [4, 1, 1, 3, 13]
def baseStart_2113678 : Nat := 118140960795 + 2113678 * 2 ^ 59
def prefixEnd_2113678 : Nat := 4983230072969 + 3 ^ 40 * 2113678 * 2
def baseEnd_2113678 : Nat := 2977593313673762575595

theorem tailTrace_2113678 : CollatzResearch.WordTrace tailWord_2113678 prefixEnd_2113678 2977593313673762575595 := by
  unfold tailWord_2113678
  simp only [CollatzResearch.WordTrace]
  refine ⟨9636521254564133538478711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51394780024342045538553125 9636521254564133538478711)
  ·
    refine ⟨14454781881846200307718067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9636521254564133538478711 14454781881846200307718067)
    ·
      refine ⟨21682172822769300461577101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14454781881846200307718067 21682172822769300461577101)
      ·
        refine ⟨8130814808538487673091413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21682172822769300461577101 8130814808538487673091413)
        ·
          refine ⟨2977593313673762575595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 8130814808538487673091413 2977593313673762575595)
          ·
            rfl

theorem cell22_2113678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 13].length) (baseStart_2113678 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2113678 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2113678 prefixEnd_2113678 := by exact prefixLift 2113678
  have htrace : WordTrace (prefixWord ++ tailWord_2113678) baseStart_2113678 baseEnd_2113678 := by
    simpa [prefixWord, tailWord_2113678, baseEnd_2113678] using wordTrace_append hprefix tailTrace_2113678
  have hstable : (prefixWord ++ tailWord_2113678).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2113678).length < 2 ^ (prefixWord ++ tailWord_2113678).sum := by decide
  have hdescent : baseEnd_2113678 < baseStart_2113678 := by decide
  rcases family_descends (prefixWord ++ tailWord_2113678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2113695 : List Nat := [1, 1, 2, 6, 1, 1, 3, 7]
def baseStart_2113695 : Nat := 118140960795 + 2113695 * 2 ^ 59
def prefixEnd_2113695 : Nat := 4983230072969 + 3 ^ 40 * 2113695 * 2
def baseEnd_2113695 : Nat := 80395666074460214243837

theorem tailTrace_2113695 : CollatzResearch.WordTrace tailWord_2113695 prefixEnd_2113695 80395666074460214243837 := by
  unfold tailWord_2113695
  simp only [CollatzResearch.WordTrace]
  refine ⟨77092790077451480211198539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51395193384967653474132359 77092790077451480211198539)
  ·
    refine ⟨115639185116177220316797809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77092790077451480211198539 115639185116177220316797809)
    ·
      refine ⟨86729388837132915237598357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115639185116177220316797809 86729388837132915237598357)
      ·
        refine ⟨4065440101740605401762423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 86729388837132915237598357 4065440101740605401762423)
        ·
          refine ⟨6098160152610908102643635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4065440101740605401762423 6098160152610908102643635)
          ·
            refine ⟨9147240228916362153965453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6098160152610908102643635 9147240228916362153965453)
            ·
              refine ⟨3430215085843635807737045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9147240228916362153965453 3430215085843635807737045)
              ·
                refine ⟨80395666074460214243837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3430215085843635807737045 80395666074460214243837)
                ·
                  rfl

theorem cell22_2113695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3, 7].length) (baseStart_2113695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2113695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2113695 prefixEnd_2113695 := by exact prefixLift 2113695
  have htrace : WordTrace (prefixWord ++ tailWord_2113695) baseStart_2113695 baseEnd_2113695 := by
    simpa [prefixWord, tailWord_2113695, baseEnd_2113695] using wordTrace_append hprefix tailTrace_2113695
  have hstable : (prefixWord ++ tailWord_2113695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2113695).length < 2 ^ (prefixWord ++ tailWord_2113695).sum := by decide
  have hdescent : baseEnd_2113695 < baseStart_2113695 := by decide
  rcases family_descends (prefixWord ++ tailWord_2113695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2113723 : List Nat := [1, 1, 1, 1, 1, 2, 6, 2, 7]
def baseStart_2113723 : Nat := 118140960795 + 2113723 * 2 ^ 59
def prefixEnd_2113723 : Nat := 4983230072969 + 3 ^ 40 * 2113723 * 2
def baseEnd_2113723 : Nat := 241190193214119729498149

theorem tailTrace_2113723 : CollatzResearch.WordTrace tailWord_2113723 prefixEnd_2113723 241190193214119729498149 := by
  unfold tailWord_2113723
  simp only [CollatzResearch.WordTrace]
  refine ⟨77093811321350040993217823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51395874214233360662145215 77093811321350040993217823)
  ·
    refine ⟨115640716982025061489826735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77093811321350040993217823 115640716982025061489826735)
    ·
      refine ⟨173461075473037592234740103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115640716982025061489826735 173461075473037592234740103)
      ·
        refine ⟨260191613209556388352110155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173461075473037592234740103 260191613209556388352110155)
        ·
          refine ⟨390287419814334582528165233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 260191613209556388352110155 390287419814334582528165233)
          ·
            refine ⟨292715564860750936896123925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 390287419814334582528165233 292715564860750936896123925)
            ·
              refine ⟨13721042102847700167005809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 292715564860750936896123925 13721042102847700167005809)
              ·
                refine ⟨10290781577135775125254357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13721042102847700167005809 10290781577135775125254357)
                ·
                  refine ⟨241190193214119729498149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10290781577135775125254357 241190193214119729498149)
                  ·
                    rfl

theorem cell22_2113723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 2, 7].length) (baseStart_2113723 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2113723 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2113723 prefixEnd_2113723 := by exact prefixLift 2113723
  have htrace : WordTrace (prefixWord ++ tailWord_2113723) baseStart_2113723 baseEnd_2113723 := by
    simpa [prefixWord, tailWord_2113723, baseEnd_2113723] using wordTrace_append hprefix tailTrace_2113723
  have hstable : (prefixWord ++ tailWord_2113723).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2113723).length < 2 ^ (prefixWord ++ tailWord_2113723).sum := by decide
  have hdescent : baseEnd_2113723 < baseStart_2113723 := by decide
  rcases family_descends (prefixWord ++ tailWord_2113723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2113802 : List Nat := [3, 1, 2, 2, 1, 1, 2, 6, 4]
def baseStart_2113802 : Nat := 118140960795 + 2113802 * 2 ^ 59
def prefixEnd_2113802 : Nat := 4983230072969 + 3 ^ 40 * 2113802 * 2
def baseEnd_2113802 : Nat := 241199207652276438589735

theorem tailTrace_2113802 : CollatzResearch.WordTrace tailWord_2113802 prefixEnd_2113802 241199207652276438589735 := by
  unfold tailWord_2113802
  simp only [CollatzResearch.WordTrace]
  refine ⟨19274173172015959371335915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51397795125375891656895773 19274173172015959371335915)
  ·
    refine ⟨28911259758023939057003873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19274173172015959371335915 28911259758023939057003873)
    ·
      refine ⟨21683444818517954292752905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28911259758023939057003873 21683444818517954292752905)
      ·
        refine ⟨16262583613888465719564679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21683444818517954292752905 16262583613888465719564679)
        ·
          refine ⟨24393875420832698579347019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16262583613888465719564679 24393875420832698579347019)
          ·
            refine ⟨36590813131249047869020529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24393875420832698579347019 36590813131249047869020529)
            ·
              refine ⟨27443109848436785901765397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36590813131249047869020529 27443109848436785901765397)
              ·
                refine ⟨1286395774145474339145253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 27443109848436785901765397 1286395774145474339145253)
                ·
                  refine ⟨241199207652276438589735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1286395774145474339145253 241199207652276438589735)
                  ·
                    rfl

theorem cell22_2113802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 6, 4].length) (baseStart_2113802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2113802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2113802 prefixEnd_2113802 := by exact prefixLift 2113802
  have htrace : WordTrace (prefixWord ++ tailWord_2113802) baseStart_2113802 baseEnd_2113802 := by
    simpa [prefixWord, tailWord_2113802, baseEnd_2113802] using wordTrace_append hprefix tailTrace_2113802
  have hstable : (prefixWord ++ tailWord_2113802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2113802).length < 2 ^ (prefixWord ++ tailWord_2113802).sum := by decide
  have hdescent : baseEnd_2113802 < baseStart_2113802 := by decide
  rcases family_descends (prefixWord ++ tailWord_2113802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2113821 : List Nat := [1, 4, 2, 3, 2, 2, 1, 2, 1, 4]
def baseStart_2113821 : Nat := 118140960795 + 2113821 * 2 ^ 59
def prefixEnd_2113821 : Nat := 4983230072969 + 3 ^ 40 * 2113821 * 2
def baseEnd_2113821 : Nat := 723604127045119599544147

theorem tailTrace_2113821 : CollatzResearch.WordTrace tailWord_2113821 prefixEnd_2113821 723604127045119599544147 := by
  unfold tailWord_2113821
  simp only [CollatzResearch.WordTrace]
  refine ⟨77097385674995003730285317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51398257116663335820190211 77097385674995003730285317)
  ·
    refine ⟨14455759814061563199428497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77097385674995003730285317 14455759814061563199428497)
    ·
      refine ⟨10841819860546172399571373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14455759814061563199428497 10841819860546172399571373)
      ·
        refine ⟨4065682447704814649839265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10841819860546172399571373 4065682447704814649839265)
        ·
          refine ⟨3049261835778610987379449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4065682447704814649839265 3049261835778610987379449)
          ·
            refine ⟨2286946376833958240534587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3049261835778610987379449 2286946376833958240534587)
            ·
              refine ⟨3430419565250937360801881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2286946376833958240534587 3430419565250937360801881)
              ·
                refine ⟨2572814673938203020601411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3430419565250937360801881 2572814673938203020601411)
                ·
                  refine ⟨3859222010907304530902117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2572814673938203020601411 3859222010907304530902117)
                  ·
                    refine ⟨723604127045119599544147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3859222010907304530902117 723604127045119599544147)
                    ·
                      rfl

theorem cell22_2113821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 1, 2, 1, 4].length) (baseStart_2113821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2113821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2113821 prefixEnd_2113821 := by exact prefixLift 2113821
  have htrace : WordTrace (prefixWord ++ tailWord_2113821) baseStart_2113821 baseEnd_2113821 := by
    simpa [prefixWord, tailWord_2113821, baseEnd_2113821] using wordTrace_append hprefix tailTrace_2113821
  have hstable : (prefixWord ++ tailWord_2113821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2113821).length < 2 ^ (prefixWord ++ tailWord_2113821).sum := by decide
  have hdescent : baseEnd_2113821 < baseStart_2113821 := by decide
  rcases family_descends (prefixWord ++ tailWord_2113821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2113834 : List Nat := [3, 1, 4, 2, 2, 1, 1, 2, 1, 5]
def baseStart_2113834 : Nat := 118140960795 + 2113834 * 2 ^ 59
def prefixEnd_2113834 : Nat := 4983230072969 + 3 ^ 40 * 2113834 * 2
def baseEnd_2113834 : Nat := 723608577210791898969107

theorem tailTrace_2113834 : CollatzResearch.WordTrace tailWord_2113834 prefixEnd_2113834 723608577210791898969107 := by
  unfold tailWord_2113834
  simp only [CollatzResearch.WordTrace]
  refine ⟨19274464955986976737627139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51398573215965271300339037 19274464955986976737627139)
  ·
    refine ⟨28911697433980465106440709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19274464955986976737627139 28911697433980465106440709)
    ·
      refine ⟨5420943268871337207457633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28911697433980465106440709 5420943268871337207457633)
      ·
        refine ⟨4065707451653502905593225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5420943268871337207457633 4065707451653502905593225)
        ·
          refine ⟨3049280588740127179194919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4065707451653502905593225 3049280588740127179194919)
          ·
            refine ⟨4573920883110190768792379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3049280588740127179194919 4573920883110190768792379)
            ·
              refine ⟨6860881324665286153188569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4573920883110190768792379 6860881324665286153188569)
              ·
                refine ⟨5145660993498964614891427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6860881324665286153188569 5145660993498964614891427)
                ·
                  refine ⟨7718491490248446922337141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5145660993498964614891427 7718491490248446922337141)
                  ·
                    refine ⟨723608577210791898969107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7718491490248446922337141 723608577210791898969107)
                    ·
                      rfl

theorem cell22_2113834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_2113834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2113834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2113834 prefixEnd_2113834 := by exact prefixLift 2113834
  have htrace : WordTrace (prefixWord ++ tailWord_2113834) baseStart_2113834 baseEnd_2113834 := by
    simpa [prefixWord, tailWord_2113834, baseEnd_2113834] using wordTrace_append hprefix tailTrace_2113834
  have hstable : (prefixWord ++ tailWord_2113834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2113834).length < 2 ^ (prefixWord ++ tailWord_2113834).sum := by decide
  have hdescent : baseEnd_2113834 < baseStart_2113834 := by decide
  rcases family_descends (prefixWord ++ tailWord_2113834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2113838 : List Nat := [4, 1, 3, 3, 1, 1, 3, 1, 1, 4]
def baseStart_2113838 : Nat := 118140960795 + 2113838 * 2 ^ 59
def prefixEnd_2113838 : Nat := 4983230072969 + 3 ^ 40 * 2113838 * 2
def baseEnd_2113838 : Nat := 723609946492537221869095

theorem tailTrace_2113838 : CollatzResearch.WordTrace tailWord_2113838 prefixEnd_2113838 723609946492537221869095 := by
  unfold tailWord_2113838
  simp only [CollatzResearch.WordTrace]
  refine ⟨9637250714491676954206771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51398670477288943755769445 9637250714491676954206771)
  ·
    refine ⟨14455876071737515431310157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9637250714491676954206771 14455876071737515431310157)
    ·
      refine ⟨5420953526901568286741309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14455876071737515431310157 5420953526901568286741309)
      ·
        refine ⟨2032857572588088107527991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5420953526901568286741309 2032857572588088107527991)
        ·
          refine ⟨3049286358882132161291987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2032857572588088107527991 3049286358882132161291987)
          ·
            refine ⟨4573929538323198241937981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3049286358882132161291987 4573929538323198241937981)
            ·
              refine ⟨1715223576871199340726743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4573929538323198241937981 1715223576871199340726743)
              ·
                refine ⟨2572835365306799011090115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1715223576871199340726743 2572835365306799011090115)
                ·
                  refine ⟨3859253047960198516635173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2572835365306799011090115 3859253047960198516635173)
                  ·
                    refine ⟨723609946492537221869095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3859253047960198516635173 723609946492537221869095)
                    ·
                      rfl

theorem cell22_2113838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 3, 1, 1, 4].length) (baseStart_2113838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2113838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2113838 prefixEnd_2113838 := by exact prefixLift 2113838
  have htrace : WordTrace (prefixWord ++ tailWord_2113838) baseStart_2113838 baseEnd_2113838 := by
    simpa [prefixWord, tailWord_2113838, baseEnd_2113838] using wordTrace_append hprefix tailTrace_2113838
  have hstable : (prefixWord ++ tailWord_2113838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2113838).length < 2 ^ (prefixWord ++ tailWord_2113838).sum := by decide
  have hdescent : baseEnd_2113838 < baseStart_2113838 := by decide
  rcases family_descends (prefixWord ++ tailWord_2113838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2113896 : List Nat := [2, 1, 4, 2, 2, 1, 1, 5, 1, 3]
def baseStart_2113896 : Nat := 118140960795 + 2113896 * 2 ^ 59
def prefixEnd_2113896 : Nat := 4983230072969 + 3 ^ 40 * 2113896 * 2
def baseEnd_2113896 : Nat := 723629801077844403918917

theorem tailTrace_2113896 : CollatzResearch.WordTrace tailWord_2113896 prefixEnd_2113896 723629801077844403918917 := by
  unfold tailWord_2113896
  simp only [CollatzResearch.WordTrace]
  refine ⟨38550060574861645769632771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51400080766482194359510361 38550060574861645769632771)
  ·
    refine ⟨57825090862292468654449157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38550060574861645769632771 57825090862292468654449157)
    ·
      refine ⟨10842204536679837872709217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57825090862292468654449157 10842204536679837872709217)
      ·
        refine ⟨8131653402509878404531913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10842204536679837872709217 8131653402509878404531913)
        ·
          refine ⟨6098740051882408803398935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8131653402509878404531913 6098740051882408803398935)
          ·
            refine ⟨9148110077823613205098403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6098740051882408803398935 9148110077823613205098403)
            ·
              refine ⟨13722165116735419807647605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9148110077823613205098403 13722165116735419807647605)
              ·
                refine ⟨1286452979693945606966963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13722165116735419807647605 1286452979693945606966963)
                ·
                  refine ⟨1929679469540918410450445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1286452979693945606966963 1929679469540918410450445)
                  ·
                    refine ⟨723629801077844403918917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1929679469540918410450445 723629801077844403918917)
                    ·
                      rfl

theorem cell22_2113896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 5, 1, 3].length) (baseStart_2113896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2113896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2113896 prefixEnd_2113896 := by exact prefixLift 2113896
  have htrace : WordTrace (prefixWord ++ tailWord_2113896) baseStart_2113896 baseEnd_2113896 := by
    simpa [prefixWord, tailWord_2113896, baseEnd_2113896] using wordTrace_append hprefix tailTrace_2113896
  have hstable : (prefixWord ++ tailWord_2113896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2113896).length < 2 ^ (prefixWord ++ tailWord_2113896).sum := by decide
  have hdescent : baseEnd_2113896 < baseStart_2113896 := by decide
  rcases family_descends (prefixWord ++ tailWord_2113896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2113909 : List Nat := [1, 3, 4, 1, 2, 1, 3, 2, 5]
def baseStart_2113909 : Nat := 118140960795 + 2113909 * 2 ^ 59
def prefixEnd_2113909 : Nat := 4983230072969 + 3 ^ 40 * 2113909 * 2
def baseEnd_2113909 : Nat := 241211417081172234447959

theorem tailTrace_2113909 : CollatzResearch.WordTrace tailWord_2113909 prefixEnd_2113909 241211417081172234447959 := by
  unfold tailWord_2113909
  simp only [CollatzResearch.WordTrace]
  refine ⟨77100595298676194759488781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51400396865784129839659187 77100595298676194759488781)
  ·
    refine ⟨28912723237003573034808293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77100595298676194759488781 28912723237003573034808293)
    ·
      refine ⟨5421135606938169944026555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28912723237003573034808293 5421135606938169944026555)
      ·
        refine ⟨8131703410407254916039833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5421135606938169944026555 8131703410407254916039833)
        ·
          refine ⟨6098777557805441187029875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8131703410407254916039833 6098777557805441187029875)
          ·
            refine ⟨9148166336708161780544813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6098777557805441187029875 9148166336708161780544813)
            ·
              refine ⟨3430562376265560667704305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9148166336708161780544813 3430562376265560667704305)
              ·
                refine ⟨2572921782199170500778229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3430562376265560667704305 2572921782199170500778229)
                ·
                  refine ⟨241211417081172234447959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2572921782199170500778229 241211417081172234447959)
                  ·
                    rfl

theorem cell22_2113909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3, 2, 5].length) (baseStart_2113909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2113909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2113909 prefixEnd_2113909 := by exact prefixLift 2113909
  have htrace : WordTrace (prefixWord ++ tailWord_2113909) baseStart_2113909 baseEnd_2113909 := by
    simpa [prefixWord, tailWord_2113909, baseEnd_2113909] using wordTrace_append hprefix tailTrace_2113909
  have hstable : (prefixWord ++ tailWord_2113909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2113909).length < 2 ^ (prefixWord ++ tailWord_2113909).sum := by decide
  have hdescent : baseEnd_2113909 < baseStart_2113909 := by decide
  rcases family_descends (prefixWord ++ tailWord_2113909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2113969 : List Nat := [1, 2, 2, 4, 1, 2, 2, 1, 4, 3]
def baseStart_2113969 : Nat := 118140960795 + 2113969 * 2 ^ 59
def prefixEnd_2113969 : Nat := 4983230072969 + 3 ^ 40 * 2113969 * 2
def baseEnd_2113969 : Nat := 723654790469696546843693

theorem tailTrace_2113969 : CollatzResearch.WordTrace tailWord_2113969 prefixEnd_2113969 723654790469696546843693 := by
  unfold tailWord_2113969
  simp only [CollatzResearch.WordTrace]
  refine ⟨77102783678458825006672961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51401855785639216671115307 77102783678458825006672961)
  ·
    refine ⟨57827087758844118755004721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77102783678458825006672961 57827087758844118755004721)
    ·
      refine ⟨43370315819133089066253541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57827087758844118755004721 43370315819133089066253541)
      ·
        refine ⟨8131934216087454199922539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43370315819133089066253541 8131934216087454199922539)
        ·
          refine ⟨12197901324131181299883809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8131934216087454199922539 12197901324131181299883809)
          ·
            refine ⟨9148425993098385974912857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12197901324131181299883809 9148425993098385974912857)
            ·
              refine ⟨6861319494823789481184643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9148425993098385974912857 6861319494823789481184643)
              ·
                refine ⟨10291979242235684221776965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6861319494823789481184643 10291979242235684221776965)
                ·
                  refine ⟨1929746107919190791583181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10291979242235684221776965 1929746107919190791583181)
                  ·
                    refine ⟨723654790469696546843693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1929746107919190791583181 723654790469696546843693)
                    ·
                      rfl

theorem cell22_2113969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 1, 4, 3].length) (baseStart_2113969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2113969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2113969 prefixEnd_2113969 := by exact prefixLift 2113969
  have htrace : WordTrace (prefixWord ++ tailWord_2113969) baseStart_2113969 baseEnd_2113969 := by
    simpa [prefixWord, tailWord_2113969, baseEnd_2113969] using wordTrace_append hprefix tailTrace_2113969
  have hstable : (prefixWord ++ tailWord_2113969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2113969).length < 2 ^ (prefixWord ++ tailWord_2113969).sum := by decide
  have hdescent : baseEnd_2113969 < baseStart_2113969 := by decide
  rcases family_descends (prefixWord ++ tailWord_2113969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2113982 : List Nat := [4, 2, 1, 1, 1, 1, 3, 9]
def baseStart_2113982 : Nat := 118140960795 + 2113982 * 2 ^ 59
def prefixEnd_2113982 : Nat := 4983230072969 + 3 ^ 40 * 2113982 * 2
def baseEnd_2113982 : Nat := 80406582292818760696517

theorem tailTrace_2113982 : CollatzResearch.WordTrace tailWord_2113982 prefixEnd_2113982 80406582292818760696517 := by
  unfold tailWord_2113982
  simp only [CollatzResearch.WordTrace]
  refine ⟨9637907228426466028362025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51402171884941152151264133 9637907228426466028362025)
  ·
    refine ⟨7228430421319849521271519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9637907228426466028362025 7228430421319849521271519)
    ·
      refine ⟨10842645631979774281907279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7228430421319849521271519 10842645631979774281907279)
      ·
        refine ⟨16263968447969661422860919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10842645631979774281907279 16263968447969661422860919)
        ·
          refine ⟨24395952671954492134291379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16263968447969661422860919 24395952671954492134291379)
          ·
            refine ⟨36593929007931738201437069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24395952671954492134291379 36593929007931738201437069)
            ·
              refine ⟨13722723377974401825538901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36593929007931738201437069 13722723377974401825538901)
              ·
                refine ⟨80406582292818760696517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13722723377974401825538901 80406582292818760696517)
                ·
                  rfl

theorem cell22_2113982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 9].length) (baseStart_2113982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2113982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2113982 prefixEnd_2113982 := by exact prefixLift 2113982
  have htrace : WordTrace (prefixWord ++ tailWord_2113982) baseStart_2113982 baseEnd_2113982 := by
    simpa [prefixWord, tailWord_2113982, baseEnd_2113982] using wordTrace_append hprefix tailTrace_2113982
  have hstable : (prefixWord ++ tailWord_2113982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2113982).length < 2 ^ (prefixWord ++ tailWord_2113982).sum := by decide
  have hdescent : baseEnd_2113982 < baseStart_2113982 := by decide
  rcases family_descends (prefixWord ++ tailWord_2113982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2114029 : List Nat := [1, 5, 1, 3, 1, 1, 1, 1, 2, 6]
def baseStart_2114029 : Nat := 118140960795 + 2114029 * 2 ^ 59
def prefixEnd_2114029 : Nat := 4983230072969 + 3 ^ 40 * 2114029 * 2
def baseEnd_2114029 : Nat := 723675329695876390343509

theorem tailTrace_2114029 : CollatzResearch.WordTrace tailWord_2114029 prefixEnd_2114029 723675329695876390343509 := by
  unfold tailWord_2114029
  simp only [CollatzResearch.WordTrace]
  refine ⟨77104972058241455253857141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51403314705494303502571427 77104972058241455253857141)
  ·
    refine ⟨7228591130460136430049107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 77104972058241455253857141 7228591130460136430049107)
    ·
      refine ⟨10842886695690204645073661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7228591130460136430049107 10842886695690204645073661)
      ·
        refine ⟨4066082510883826741902623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10842886695690204645073661 4066082510883826741902623)
        ·
          refine ⟨6099123766325740112853935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4066082510883826741902623 6099123766325740112853935)
          ·
            refine ⟨9148685649488610169280903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6099123766325740112853935 9148685649488610169280903)
            ·
              refine ⟨13723028474232915253921355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9148685649488610169280903 13723028474232915253921355)
              ·
                refine ⟨20584542711349372880882033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13723028474232915253921355 20584542711349372880882033)
                ·
                  refine ⟨15438407033512029660661525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20584542711349372880882033 15438407033512029660661525)
                  ·
                    refine ⟨723675329695876390343509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15438407033512029660661525 723675329695876390343509)
                    ·
                      rfl

theorem cell22_2114029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 1, 2, 6].length) (baseStart_2114029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2114029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2114029 prefixEnd_2114029 := by exact prefixLift 2114029
  have htrace : WordTrace (prefixWord ++ tailWord_2114029) baseStart_2114029 baseEnd_2114029 := by
    simpa [prefixWord, tailWord_2114029, baseEnd_2114029] using wordTrace_append hprefix tailTrace_2114029
  have hstable : (prefixWord ++ tailWord_2114029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2114029).length < 2 ^ (prefixWord ++ tailWord_2114029).sum := by decide
  have hdescent : baseEnd_2114029 < baseStart_2114029 := by decide
  rcases family_descends (prefixWord ++ tailWord_2114029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2114116 : List Nat := [2, 3, 5, 1, 2, 1, 1, 3, 1, 3]
def baseStart_2114116 : Nat := 118140960795 + 2114116 * 2 ^ 59
def prefixEnd_2114116 : Nat := 4983230072969 + 3 ^ 40 * 2114116 * 2
def baseEnd_2114116 : Nat := 723705111573837163418243

theorem tailTrace_2114116 : CollatzResearch.WordTrace tailWord_2114116 prefixEnd_2114116 723705111573837163418243 := by
  unfold tailWord_2114116
  simp only [CollatzResearch.WordTrace]
  refine ⟨38554072604463134556137101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51405430139284179408182801 38554072604463134556137101)
  ·
    refine ⟨14457777226673675458551413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38554072604463134556137101 14457777226673675458551413)
    ·
      refine ⟨1355416615000657074239195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14457777226673675458551413 1355416615000657074239195)
      ·
        refine ⟨2033124922500985611358793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1355416615000657074239195 2033124922500985611358793)
        ·
          refine ⟨1524843691875739208519095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2033124922500985611358793 1524843691875739208519095)
          ·
            refine ⟨2287265537813608812778643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1524843691875739208519095 2287265537813608812778643)
            ·
              refine ⟨3430898306720413219167965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2287265537813608812778643 3430898306720413219167965)
              ·
                refine ⟨1286586865020154957187987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3430898306720413219167965 1286586865020154957187987)
                ·
                  refine ⟨1929880297530232435781981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1286586865020154957187987 1929880297530232435781981)
                  ·
                    refine ⟨723705111573837163418243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1929880297530232435781981 723705111573837163418243)
                    ·
                      rfl

theorem cell22_2114116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_2114116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2114116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2114116 prefixEnd_2114116 := by exact prefixLift 2114116
  have htrace : WordTrace (prefixWord ++ tailWord_2114116) baseStart_2114116 baseEnd_2114116 := by
    simpa [prefixWord, tailWord_2114116, baseEnd_2114116] using wordTrace_append hprefix tailTrace_2114116
  have hstable : (prefixWord ++ tailWord_2114116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2114116).length < 2 ^ (prefixWord ++ tailWord_2114116).sum := by decide
  have hdescent : baseEnd_2114116 < baseStart_2114116 := by decide
  rcases family_descends (prefixWord ++ tailWord_2114116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2114119 : List Nat := [1, 1, 4, 1, 4, 1, 2, 1, 1, 6]
def baseStart_2114119 : Nat := 118140960795 + 2114119 * 2 ^ 59
def prefixEnd_2114119 : Nat := 4983230072969 + 3 ^ 40 * 2114119 * 2
def baseEnd_2114119 : Nat := 723706138535146155593233

theorem tailTrace_2114119 : CollatzResearch.WordTrace tailWord_2114119 prefixEnd_2114119 723706138535146155593233 := by
  unfold tailWord_2114119
  simp only [CollatzResearch.WordTrace]
  refine ⟨77108254627915400624633411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51405503085276933749755607 77108254627915400624633411)
  ·
    refine ⟨115662381941873100936950117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77108254627915400624633411 115662381941873100936950117)
    ·
      refine ⟨21686696614101206425678147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 115662381941873100936950117 21686696614101206425678147)
      ·
        refine ⟨32530044921151809638517221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21686696614101206425678147 32530044921151809638517221)
        ·
          refine ⟨6099383422715964307221979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32530044921151809638517221 6099383422715964307221979)
          ·
            refine ⟨9149075134073946460832969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6099383422715964307221979 9149075134073946460832969)
            ·
              refine ⟨6861806350555459845624727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9149075134073946460832969 6861806350555459845624727)
              ·
                refine ⟨10292709525833189768437091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6861806350555459845624727 10292709525833189768437091)
                ·
                  refine ⟨15439064288749784652655637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10292709525833189768437091 15439064288749784652655637)
                  ·
                    refine ⟨723706138535146155593233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15439064288749784652655637 723706138535146155593233)
                    ·
                      rfl

theorem cell22_2114119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 1, 1, 6].length) (baseStart_2114119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2114119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2114119 prefixEnd_2114119 := by exact prefixLift 2114119
  have htrace : WordTrace (prefixWord ++ tailWord_2114119) baseStart_2114119 baseEnd_2114119 := by
    simpa [prefixWord, tailWord_2114119, baseEnd_2114119] using wordTrace_append hprefix tailTrace_2114119
  have hstable : (prefixWord ++ tailWord_2114119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2114119).length < 2 ^ (prefixWord ++ tailWord_2114119).sum := by decide
  have hdescent : baseEnd_2114119 < baseStart_2114119 := by decide
  rcases family_descends (prefixWord ++ tailWord_2114119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2114140 : List Nat := [2, 2, 4, 1, 3, 1, 3, 2, 4]
def baseStart_2114140 : Nat := 118140960795 + 2114140 * 2 ^ 59
def prefixEnd_2114140 : Nat := 4983230072969 + 3 ^ 40 * 2114140 * 2
def baseEnd_2114140 : Nat := 241237775754769700272723

theorem tailTrace_2114140 : CollatzResearch.WordTrace tailWord_2114140 prefixEnd_2114140 241237775754769700272723 := by
  unfold tailWord_2114140
  simp only [CollatzResearch.WordTrace]
  refine ⟨38554510280419660605573937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51406013707226214140765249 38554510280419660605573937)
  ·
    refine ⟨28915882710314745454180453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38554510280419660605573937 28915882710314745454180453)
    ·
      refine ⟨5421728008184014772658835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28915882710314745454180453 5421728008184014772658835)
      ·
        refine ⟨8132592012276022158988253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5421728008184014772658835 8132592012276022158988253)
        ·
          refine ⟨3049722004603508309620595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8132592012276022158988253 3049722004603508309620595)
          ·
            refine ⟨4574583006905262464430893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3049722004603508309620595 4574583006905262464430893)
            ·
              refine ⟨1715468627589473424161585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4574583006905262464430893 1715468627589473424161585)
              ·
                refine ⟨1286601470692105068121189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1715468627589473424161585 1286601470692105068121189)
                ·
                  refine ⟨241237775754769700272723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1286601470692105068121189 241237775754769700272723)
                  ·
                    rfl

theorem cell22_2114140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 3, 2, 4].length) (baseStart_2114140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2114140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2114140 prefixEnd_2114140 := by exact prefixLift 2114140
  have htrace : WordTrace (prefixWord ++ tailWord_2114140) baseStart_2114140 baseEnd_2114140 := by
    simpa [prefixWord, tailWord_2114140, baseEnd_2114140] using wordTrace_append hprefix tailTrace_2114140
  have hstable : (prefixWord ++ tailWord_2114140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2114140).length < 2 ^ (prefixWord ++ tailWord_2114140).sum := by decide
  have hdescent : baseEnd_2114140 < baseStart_2114140 := by decide
  rcases family_descends (prefixWord ++ tailWord_2114140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2114183 : List Nat := [1, 1, 4, 2, 1, 2, 2, 5, 1, 3]
def baseStart_2114183 : Nat := 118140960795 + 2114183 * 2 ^ 59
def prefixEnd_2114183 : Nat := 4983230072969 + 3 ^ 40 * 2114183 * 2
def baseEnd_2114183 : Nat := 723728047043071321993037

theorem tailTrace_2114183 : CollatzResearch.WordTrace tailWord_2114183 prefixEnd_2114183 723728047043071321993037 := by
  unfold tailWord_2114183
  simp only [CollatzResearch.WordTrace]
  refine ⟨77110588899683539554963203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51407059266455693036642135 77110588899683539554963203)
  ·
    refine ⟨115665883349525309332444805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77110588899683539554963203 115665883349525309332444805)
    ·
      refine ⟨21687353128035995499833401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 115665883349525309332444805 21687353128035995499833401)
      ·
        refine ⟨16265514846026996624875051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21687353128035995499833401 16265514846026996624875051)
        ·
          refine ⟨24398272269040494937312577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16265514846026996624875051 24398272269040494937312577)
          ·
            refine ⟨18298704201780371202984433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24398272269040494937312577 18298704201780371202984433)
            ·
              refine ⟨13724028151335278402238325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18298704201780371202984433 13724028151335278402238325)
              ·
                refine ⟨1286627639187682350209843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13724028151335278402238325 1286627639187682350209843)
                ·
                  refine ⟨1929941458781523525314765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1286627639187682350209843 1929941458781523525314765)
                  ·
                    refine ⟨723728047043071321993037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1929941458781523525314765 723728047043071321993037)
                    ·
                      rfl

theorem cell22_2114183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 5, 1, 3].length) (baseStart_2114183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2114183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2114183 prefixEnd_2114183 := by exact prefixLift 2114183
  have htrace : WordTrace (prefixWord ++ tailWord_2114183) baseStart_2114183 baseEnd_2114183 := by
    simpa [prefixWord, tailWord_2114183, baseEnd_2114183] using wordTrace_append hprefix tailTrace_2114183
  have hstable : (prefixWord ++ tailWord_2114183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2114183).length < 2 ^ (prefixWord ++ tailWord_2114183).sum := by decide
  have hdescent : baseEnd_2114183 < baseStart_2114183 := by decide
  rcases family_descends (prefixWord ++ tailWord_2114183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2114226 : List Nat := [3, 2, 1, 1, 1, 2, 1, 6, 1, 4]
def baseStart_2114226 : Nat := 118140960795 + 2114226 * 2 ^ 59
def prefixEnd_2114226 : Nat := 4983230072969 + 3 ^ 40 * 2114226 * 2
def baseEnd_2114226 : Nat := 723742766821833543167905

theorem tailTrace_2114226 : CollatzResearch.WordTrace tailWord_2114226 prefixEnd_2114226 723742766821833543167905 := by
  unfold tailWord_2114226
  simp only [CollatzResearch.WordTrace]
  refine ⟨19278039309631939474694633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51408104825685171932519021 19278039309631939474694633)
  ·
    refine ⟨14458529482223954606020975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19278039309631939474694633 14458529482223954606020975)
    ·
      refine ⟨21687794223335931909031463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14458529482223954606020975 21687794223335931909031463)
      ·
        refine ⟨32531691335003897863547195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21687794223335931909031463 32531691335003897863547195)
        ·
          refine ⟨48797537002505846795320793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32531691335003897863547195 48797537002505846795320793)
          ·
            refine ⟨36598152751879385096490595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48797537002505846795320793 36598152751879385096490595)
            ·
              refine ⟨54897229127819077644735893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36598152751879385096490595 54897229127819077644735893)
              ·
                refine ⟨2573307615366519264596995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 54897229127819077644735893 2573307615366519264596995)
                ·
                  refine ⟨3859961423049778896895493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2573307615366519264596995 3859961423049778896895493)
                  ·
                    refine ⟨723742766821833543167905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3859961423049778896895493 723742766821833543167905)
                    ·
                      rfl

theorem cell22_2114226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 6, 1, 4].length) (baseStart_2114226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2114226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2114226 prefixEnd_2114226 := by exact prefixLift 2114226
  have htrace : WordTrace (prefixWord ++ tailWord_2114226) baseStart_2114226 baseEnd_2114226 := by
    simpa [prefixWord, tailWord_2114226, baseEnd_2114226] using wordTrace_append hprefix tailTrace_2114226
  have hstable : (prefixWord ++ tailWord_2114226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2114226).length < 2 ^ (prefixWord ++ tailWord_2114226).sum := by decide
  have hdescent : baseEnd_2114226 < baseStart_2114226 := by decide
  rcases family_descends (prefixWord ++ tailWord_2114226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2114258 : List Nat := [3, 2, 2, 2, 3, 1, 2, 1, 6]
def baseStart_2114258 : Nat := 118140960795 + 2114258 * 2 ^ 59
def prefixEnd_2114258 : Nat := 4983230072969 + 3 ^ 40 * 2114258 * 2
def baseEnd_2114258 : Nat := 241251240358598708789269

theorem tailTrace_2114258 : CollatzResearch.WordTrace tailWord_2114258 prefixEnd_2114258 241251240358598708789269 := by
  unfold tailWord_2114258
  simp only [CollatzResearch.WordTrace]
  refine ⟨19278331093602956840985857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51408882916274551575962285 19278331093602956840985857)
  ·
    refine ⟨14458748320202217630739393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19278331093602956840985857 14458748320202217630739393)
    ·
      refine ⟨10844061240151663223054545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14458748320202217630739393 10844061240151663223054545)
      ·
        refine ⟨8133045930113747417290909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10844061240151663223054545 8133045930113747417290909)
        ·
          refine ⟨3049892223792655281484091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8133045930113747417290909 3049892223792655281484091)
          ·
            refine ⟨4574838335688982922226137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3049892223792655281484091 4574838335688982922226137)
            ·
              refine ⟨3431128751766737191669603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4574838335688982922226137 3431128751766737191669603)
              ·
                refine ⟨5146693127650105787504405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3431128751766737191669603 5146693127650105787504405)
                ·
                  refine ⟨241251240358598708789269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5146693127650105787504405 241251240358598708789269)
                  ·
                    rfl

theorem cell22_2114258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 2, 1, 6].length) (baseStart_2114258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2114258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2114258 prefixEnd_2114258 := by exact prefixLift 2114258
  have htrace : WordTrace (prefixWord ++ tailWord_2114258) baseStart_2114258 baseEnd_2114258 := by
    simpa [prefixWord, tailWord_2114258, baseEnd_2114258] using wordTrace_append hprefix tailTrace_2114258
  have hstable : (prefixWord ++ tailWord_2114258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2114258).length < 2 ^ (prefixWord ++ tailWord_2114258).sum := by decide
  have hdescent : baseEnd_2114258 < baseStart_2114258 := by decide
  rcases family_descends (prefixWord ++ tailWord_2114258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2114273 : List Nat := [1, 2, 3, 1, 4, 3, 1, 1, 1, 5]
def baseStart_2114273 : Nat := 118140960795 + 2114273 * 2 ^ 59
def prefixEnd_2114273 : Nat := 4983230072969 + 3 ^ 40 * 2114273 * 2
def baseEnd_2114273 : Nat := 723758855882341087242761

theorem tailTrace_2114273 : CollatzResearch.WordTrace tailWord_2114273 prefixEnd_2114273 723758855882341087242761 := by
  unfold tailWord_2114273
  simp only [CollatzResearch.WordTrace]
  refine ⟨77113871469357484925739473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51409247646238323283826315 77113871469357484925739473)
  ·
    refine ⟨57835403602018113694304605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77113871469357484925739473 57835403602018113694304605)
    ·
      refine ⟨21688276350756792635364227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57835403602018113694304605 21688276350756792635364227)
      ·
        refine ⟨32532414526135188953046341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21688276350756792635364227 32532414526135188953046341)
        ·
          refine ⟨6099827723650347928696189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32532414526135188953046341 6099827723650347928696189)
          ·
            refine ⟨2287435396368880473261071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6099827723650347928696189 2287435396368880473261071)
            ·
              refine ⟨3431153094553320709891607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2287435396368880473261071 3431153094553320709891607)
              ·
                refine ⟨5146729641829981064837411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3431153094553320709891607 5146729641829981064837411)
                ·
                  refine ⟨7720094462744971597256117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5146729641829981064837411 7720094462744971597256117)
                  ·
                    refine ⟨723758855882341087242761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7720094462744971597256117 723758855882341087242761)
                    ·
                      rfl

theorem cell22_2114273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 1, 1, 1, 5].length) (baseStart_2114273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2114273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2114273 prefixEnd_2114273 := by exact prefixLift 2114273
  have htrace : WordTrace (prefixWord ++ tailWord_2114273) baseStart_2114273 baseEnd_2114273 := by
    simpa [prefixWord, tailWord_2114273, baseEnd_2114273] using wordTrace_append hprefix tailTrace_2114273
  have hstable : (prefixWord ++ tailWord_2114273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2114273).length < 2 ^ (prefixWord ++ tailWord_2114273).sum := by decide
  have hdescent : baseEnd_2114273 < baseStart_2114273 := by decide
  rcases family_descends (prefixWord ++ tailWord_2114273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2114284 : List Nat := [2, 2, 1, 1, 2, 2, 1, 1, 1, 9]
def baseStart_2114284 : Nat := 118140960795 + 2114284 * 2 ^ 59
def prefixEnd_2114284 : Nat := 4983230072969 + 3 ^ 40 * 2114284 * 2
def baseEnd_2114284 : Nat := 723762621407140725217727

theorem tailTrace_2114284 : CollatzResearch.WordTrace tailWord_2114284 prefixEnd_2114284 723762621407140725217727 := by
  unfold tailWord_2114284
  simp only [CollatzResearch.WordTrace]
  refine ⟨38557136336158816902194953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51409515114878422536259937 38557136336158816902194953)
  ·
    refine ⟨28917852252119112676646215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38557136336158816902194953 28917852252119112676646215)
    ·
      refine ⟨43376778378178669014969323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28917852252119112676646215 43376778378178669014969323)
      ·
        refine ⟨65065167567268003522453985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43376778378178669014969323 65065167567268003522453985)
        ·
          refine ⟨48798875675451002641840489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65065167567268003522453985 48798875675451002641840489)
          ·
            refine ⟨36599156756588251981380367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48798875675451002641840489 36599156756588251981380367)
            ·
              refine ⟨54898735134882377972070551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36599156756588251981380367 54898735134882377972070551)
              ·
                refine ⟨82348102702323566958105827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54898735134882377972070551 82348102702323566958105827)
                ·
                  refine ⟨123522154053485350437158741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 82348102702323566958105827 123522154053485350437158741)
                  ·
                    refine ⟨723762621407140725217727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 123522154053485350437158741 723762621407140725217727)
                    ·
                      rfl

theorem cell22_2114284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 9].length) (baseStart_2114284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2114284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2114284 prefixEnd_2114284 := by exact prefixLift 2114284
  have htrace : WordTrace (prefixWord ++ tailWord_2114284) baseStart_2114284 baseEnd_2114284 := by
    simpa [prefixWord, tailWord_2114284, baseEnd_2114284] using wordTrace_append hprefix tailTrace_2114284
  have hstable : (prefixWord ++ tailWord_2114284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2114284).length < 2 ^ (prefixWord ++ tailWord_2114284).sum := by decide
  have hdescent : baseEnd_2114284 < baseStart_2114284 := by decide
  rcases family_descends (prefixWord ++ tailWord_2114284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2114286 : List Nat := [4, 1, 2, 1, 1, 4, 1, 8]
def baseStart_2114286 : Nat := 118140960795 + 2114286 * 2 ^ 59
def prefixEnd_2114286 : Nat := 4983230072969 + 3 ^ 40 * 2114286 * 2
def baseEnd_2114286 : Nat := 80418145116445931851969

theorem tailTrace_2114286 : CollatzResearch.WordTrace tailWord_2114286 prefixEnd_2114286 80418145116445931851969 := by
  unfold tailWord_2114286
  simp only [CollatzResearch.WordTrace]
  refine ⟨9639293202288798518245339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51409563745540258763975141 9639293202288798518245339)
  ·
    refine ⟨14458939803433197777368009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9639293202288798518245339 14458939803433197777368009)
    ·
      refine ⟨10844204852574898333026007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14458939803433197777368009 10844204852574898333026007)
      ·
        refine ⟨16266307278862347499539011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10844204852574898333026007 16266307278862347499539011)
        ·
          refine ⟨24399460918293521249308517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16266307278862347499539011 24399460918293521249308517)
          ·
            refine ⟨4574898922180035234245347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24399460918293521249308517 4574898922180035234245347)
            ·
              refine ⟨6862348383270052851368021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4574898922180035234245347 6862348383270052851368021)
              ·
                refine ⟨80418145116445931851969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6862348383270052851368021 80418145116445931851969)
                ·
                  rfl

theorem cell22_2114286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 8].length) (baseStart_2114286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2114286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2114286 prefixEnd_2114286 := by exact prefixLift 2114286
  have htrace : WordTrace (prefixWord ++ tailWord_2114286) baseStart_2114286 baseEnd_2114286 := by
    simpa [prefixWord, tailWord_2114286, baseEnd_2114286] using wordTrace_append hprefix tailTrace_2114286
  have hstable : (prefixWord ++ tailWord_2114286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2114286).length < 2 ^ (prefixWord ++ tailWord_2114286).sum := by decide
  have hdescent : baseEnd_2114286 < baseStart_2114286 := by decide
  rcases family_descends (prefixWord ++ tailWord_2114286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2114365 : List Nat := [1, 4, 1, 4, 2, 1, 2, 2, 5]
def baseStart_2114365 : Nat := 118140960795 + 2114365 * 2 ^ 59
def prefixEnd_2114365 : Nat := 4983230072969 + 3 ^ 40 * 2114365 * 2
def baseEnd_2114365 : Nat := 241263449787494504647493

theorem tailTrace_2114365 : CollatzResearch.WordTrace tailWord_2114365 prefixEnd_2114365 241263449787494504647493 := by
  unfold tailWord_2114365
  simp only [CollatzResearch.WordTrace]
  refine ⟨77117226985024184638088549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51411484656682789758725699 77117226985024184638088549)
  ·
    refine ⟨14459480059692034619641603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77117226985024184638088549 14459480059692034619641603)
    ·
      refine ⟨21689220089538051929462405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14459480059692034619641603 21689220089538051929462405)
      ·
        refine ⟨4066728766788384736774201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21689220089538051929462405 4066728766788384736774201)
        ·
          refine ⟨3050046575091288552580651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4066728766788384736774201 3050046575091288552580651)
          ·
            refine ⟨4575069862636932828870977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3050046575091288552580651 4575069862636932828870977)
            ·
              refine ⟨3431302396977699621653233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4575069862636932828870977 3431302396977699621653233)
              ·
                refine ⟨2573476797733274716239925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3431302396977699621653233 2573476797733274716239925)
                ·
                  refine ⟨241263449787494504647493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2573476797733274716239925 241263449787494504647493)
                  ·
                    rfl

theorem cell22_2114365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 2, 2, 5].length) (baseStart_2114365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2114365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2114365 prefixEnd_2114365 := by exact prefixLift 2114365
  have htrace : WordTrace (prefixWord ++ tailWord_2114365) baseStart_2114365 baseEnd_2114365 := by
    simpa [prefixWord, tailWord_2114365, baseEnd_2114365] using wordTrace_append hprefix tailTrace_2114365
  have hstable : (prefixWord ++ tailWord_2114365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2114365).length < 2 ^ (prefixWord ++ tailWord_2114365).sum := by decide
  have hdescent : baseEnd_2114365 < baseStart_2114365 := by decide
  rcases family_descends (prefixWord ++ tailWord_2114365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2114369 : List Nat := [1, 2, 5, 3, 1, 1, 1, 4, 1, 3]
def baseStart_2114369 : Nat := 118140960795 + 2114369 * 2 ^ 59
def prefixEnd_2114369 : Nat := 4983230072969 + 3 ^ 40 * 2114369 * 2
def baseEnd_2114369 : Nat := 723791718644228836842467

theorem tailTrace_2114369 : CollatzResearch.WordTrace tailWord_2114369 prefixEnd_2114369 723791718644228836842467 := by
  unfold tailWord_2114369
  simp only [CollatzResearch.WordTrace]
  refine ⟨77117372877009693321234161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51411581918006462214156107 77117372877009693321234161)
  ·
    refine ⟨57838029657757269990925621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77117372877009693321234161 57838029657757269990925621)
    ·
      refine ⟨5422315280414744061649277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 57838029657757269990925621 5422315280414744061649277)
      ·
        refine ⟨2033368230155529023118479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5422315280414744061649277 2033368230155529023118479)
        ·
          refine ⟨3050052345233293534677719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2033368230155529023118479 3050052345233293534677719)
          ·
            refine ⟨4575078517849940302016579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3050052345233293534677719 4575078517849940302016579)
            ·
              refine ⟨6862617776774910453024869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4575078517849940302016579 6862617776774910453024869)
              ·
                refine ⟨1286740833145295709942163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6862617776774910453024869 1286740833145295709942163)
                ·
                  refine ⟨1930111249717943564913245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1286740833145295709942163 1930111249717943564913245)
                  ·
                    refine ⟨723791718644228836842467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1930111249717943564913245 723791718644228836842467)
                    ·
                      rfl

theorem cell22_2114369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 4, 1, 3].length) (baseStart_2114369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2114369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2114369 prefixEnd_2114369 := by exact prefixLift 2114369
  have htrace : WordTrace (prefixWord ++ tailWord_2114369) baseStart_2114369 baseEnd_2114369 := by
    simpa [prefixWord, tailWord_2114369, baseEnd_2114369] using wordTrace_append hprefix tailTrace_2114369
  have hstable : (prefixWord ++ tailWord_2114369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2114369).length < 2 ^ (prefixWord ++ tailWord_2114369).sum := by decide
  have hdescent : baseEnd_2114369 < baseStart_2114369 := by decide
  rcases family_descends (prefixWord ++ tailWord_2114369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2114376 : List Nat := [2, 1, 3, 1, 1, 3, 2, 3, 6]
def baseStart_2114376 : Nat := 118140960795 + 2114376 * 2 ^ 59
def prefixEnd_2114376 : Nat := 4983230072969 + 3 ^ 40 * 2114376 * 2
def baseEnd_2114376 : Nat := 241264704962427717305815

theorem tailTrace_2114376 : CollatzResearch.WordTrace tailWord_2114376 prefixEnd_2114376 241264704962427717305815 := by
  unfold tailWord_2114376
  simp only [CollatzResearch.WordTrace]
  refine ⟨38558814093992166758369491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51411752125322889011159321 38558814093992166758369491)
  ·
    refine ⟨57838221140988250137554237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38558814093992166758369491 57838221140988250137554237)
    ·
      refine ⟨21689332927870593801582839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57838221140988250137554237 21689332927870593801582839)
      ·
        refine ⟨32533999391805890702374259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21689332927870593801582839 32533999391805890702374259)
        ·
          refine ⟨48800999087708836053561389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32533999391805890702374259 48800999087708836053561389)
          ·
            refine ⟨18300374657890813520085521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48800999087708836053561389 18300374657890813520085521)
            ·
              refine ⟨13725280993418110140064141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18300374657890813520085521 13725280993418110140064141)
              ·
                refine ⟨5146980372531791302524053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13725280993418110140064141 5146980372531791302524053)
                ·
                  refine ⟨241264704962427717305815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5146980372531791302524053 241264704962427717305815)
                  ·
                    rfl

theorem cell22_2114376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 3, 6].length) (baseStart_2114376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2114376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2114376 prefixEnd_2114376 := by exact prefixLift 2114376
  have htrace : WordTrace (prefixWord ++ tailWord_2114376) baseStart_2114376 baseEnd_2114376 := by
    simpa [prefixWord, tailWord_2114376, baseEnd_2114376] using wordTrace_append hprefix tailTrace_2114376
  have hstable : (prefixWord ++ tailWord_2114376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2114376).length < 2 ^ (prefixWord ++ tailWord_2114376).sum := by decide
  have hdescent : baseEnd_2114376 < baseStart_2114376 := by decide
  rcases family_descends (prefixWord ++ tailWord_2114376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2114408 : List Nat := [2, 1, 4, 2, 1, 2, 2, 2, 1, 5]
def baseStart_2114408 : Nat := 118140960795 + 2114408 * 2 ^ 59
def prefixEnd_2114408 : Nat := 4983230072969 + 3 ^ 40 * 2114408 * 2
def baseEnd_2114408 : Nat := 723805069141245735117347

theorem tailTrace_2114408 : CollatzResearch.WordTrace tailWord_2114408 prefixEnd_2114408 723805069141245735117347 := by
  unfold tailWord_2114408
  simp only [CollatzResearch.WordTrace]
  refine ⟨38559397661934201490951939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51412530215912268654602585 38559397661934201490951939)
  ·
    refine ⟨57839096492901302236427909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38559397661934201490951939 57839096492901302236427909)
    ·
      refine ⟨10844830592418994169330233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57839096492901302236427909 10844830592418994169330233)
      ·
        refine ⟨8133622944314245626997675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10844830592418994169330233 8133622944314245626997675)
        ·
          refine ⟨12200434416471368440496513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8133622944314245626997675 12200434416471368440496513)
          ·
            refine ⟨9150325812353526330372385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12200434416471368440496513 9150325812353526330372385)
            ·
              refine ⟨6862744359265144747779289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9150325812353526330372385 6862744359265144747779289)
              ·
                refine ⟨5147058269448858560834467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6862744359265144747779289 5147058269448858560834467)
                ·
                  refine ⟨7720587404173287841251701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5147058269448858560834467 7720587404173287841251701)
                  ·
                    refine ⟨723805069141245735117347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7720587404173287841251701 723805069141245735117347)
                    ·
                      rfl

theorem cell22_2114408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 2, 1, 5].length) (baseStart_2114408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2114408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2114408 prefixEnd_2114408 := by exact prefixLift 2114408
  have htrace : WordTrace (prefixWord ++ tailWord_2114408) baseStart_2114408 baseEnd_2114408 := by
    simpa [prefixWord, tailWord_2114408, baseEnd_2114408] using wordTrace_append hprefix tailTrace_2114408
  have hstable : (prefixWord ++ tailWord_2114408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2114408).length < 2 ^ (prefixWord ++ tailWord_2114408).sum := by decide
  have hdescent : baseEnd_2114408 < baseStart_2114408 := by decide
  rcases family_descends (prefixWord ++ tailWord_2114408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2114425 : List Nat := [1, 2, 1, 3, 2, 3, 3, 2, 2, 3]
def baseStart_2114425 : Nat := 118140960795 + 2114425 * 2 ^ 59
def prefixEnd_2114425 : Nat := 4983230072969 + 3 ^ 40 * 2114425 * 2
def baseEnd_2114425 : Nat := 723810888588663357442295

theorem tailTrace_2114425 : CollatzResearch.WordTrace tailWord_2114425 prefixEnd_2114425 723810888588663357442295 := by
  unfold tailWord_2114425
  simp only [CollatzResearch.WordTrace]
  refine ⟨77119415364806814885272729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51412943576537876590181819 77119415364806814885272729)
  ·
    refine ⟨57839561523605111163954547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77119415364806814885272729 57839561523605111163954547)
    ·
      refine ⟨86759342285407666745931821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57839561523605111163954547 86759342285407666745931821)
      ·
        refine ⟨32534753357027875029724433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86759342285407666745931821 32534753357027875029724433)
        ·
          refine ⟨24401065017770906272293325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32534753357027875029724433 24401065017770906272293325)
          ·
            refine ⟨9150399381664089852109997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24401065017770906272293325 9150399381664089852109997)
            ·
              refine ⟨3431399768124033694541249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9150399381664089852109997 3431399768124033694541249)
              ·
                refine ⟨2573549826093025270905937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3431399768124033694541249 2573549826093025270905937)
                ·
                  refine ⟨1930162369569768953179453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2573549826093025270905937 1930162369569768953179453)
                  ·
                    refine ⟨723810888588663357442295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1930162369569768953179453 723810888588663357442295)
                    ·
                      rfl

theorem cell22_2114425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3, 2, 2, 3].length) (baseStart_2114425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2114425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2114425 prefixEnd_2114425 := by exact prefixLift 2114425
  have htrace : WordTrace (prefixWord ++ tailWord_2114425) baseStart_2114425 baseEnd_2114425 := by
    simpa [prefixWord, tailWord_2114425, baseEnd_2114425] using wordTrace_append hprefix tailTrace_2114425
  have hstable : (prefixWord ++ tailWord_2114425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2114425).length < 2 ^ (prefixWord ++ tailWord_2114425).sum := by decide
  have hdescent : baseEnd_2114425 < baseStart_2114425 := by decide
  rcases family_descends (prefixWord ++ tailWord_2114425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2114513 : List Nat := [1, 2, 2, 1, 2, 1, 5, 1, 3, 4]
def baseStart_2114513 : Nat := 118140960795 + 2114513 * 2 ^ 59
def prefixEnd_2114513 : Nat := 4983230072969 + 3 ^ 40 * 2114513 * 2
def baseEnd_2114513 : Nat := 723841012787060461242025

theorem tailTrace_2114513 : CollatzResearch.WordTrace tailWord_2114513 prefixEnd_2114513 723841012787060461242025 := by
  unfold tailWord_2114513
  simp only [CollatzResearch.WordTrace]
  refine ⟨77122624988488005914476193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51415083325658670609650795 77122624988488005914476193)
  ·
    refine ⟨57841968741366004435857145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77122624988488005914476193 57841968741366004435857145)
    ·
      refine ⟨43381476556024503326892859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57841968741366004435857145 43381476556024503326892859)
      ·
        refine ⟨65072214834036754990339289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43381476556024503326892859 65072214834036754990339289)
        ·
          refine ⟨48804161125527566242754467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65072214834036754990339289 48804161125527566242754467)
          ·
            refine ⟨73206241688291349364131701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48804161125527566242754467 73206241688291349364131701)
            ·
              refine ⟨6863085158277314002887347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 73206241688291349364131701 6863085158277314002887347)
              ·
                refine ⟨10294627737415971004331021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6863085158277314002887347 10294627737415971004331021)
                ·
                  refine ⟨3860485401530989126624133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10294627737415971004331021 3860485401530989126624133)
                  ·
                    refine ⟨723841012787060461242025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3860485401530989126624133 723841012787060461242025)
                    ·
                      rfl

theorem cell22_2114513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 1, 3, 4].length) (baseStart_2114513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2114513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2114513 prefixEnd_2114513 := by exact prefixLift 2114513
  have htrace : WordTrace (prefixWord ++ tailWord_2114513) baseStart_2114513 baseEnd_2114513 := by
    simpa [prefixWord, tailWord_2114513, baseEnd_2114513] using wordTrace_append hprefix tailTrace_2114513
  have hstable : (prefixWord ++ tailWord_2114513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2114513).length < 2 ^ (prefixWord ++ tailWord_2114513).sum := by decide
  have hdescent : baseEnd_2114513 < baseStart_2114513 := by decide
  rcases family_descends (prefixWord ++ tailWord_2114513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2114594 : List Nat := [3, 3, 1, 1, 1, 5, 1, 2, 2, 3]
def baseStart_2114594 : Nat := 118140960795 + 2114594 * 2 ^ 59
def prefixEnd_2114594 : Nat := 4983230072969 + 3 ^ 40 * 2114594 * 2
def baseEnd_2114594 : Nat := 723868740742403249966777

theorem tailTrace_2114594 : CollatzResearch.WordTrace tailWord_2114594 prefixEnd_2114594 723868740742403249966777 := by
  unfold tailWord_2114594
  simp only [CollatzResearch.WordTrace]
  refine ⟨19281394825298639187043709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51417052867463037832116557 19281394825298639187043709)
  ·
    refine ⟨7230523059486989695141391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19281394825298639187043709 7230523059486989695141391)
    ·
      refine ⟨10845784589230484542712087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7230523059486989695141391 10845784589230484542712087)
      ·
        refine ⟨16268676883845726814068131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10845784589230484542712087 16268676883845726814068131)
        ·
          refine ⟨24403015325768590221102197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16268676883845726814068131 24403015325768590221102197)
          ·
            refine ⟨2287782686790805333228331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24403015325768590221102197 2287782686790805333228331)
            ·
              refine ⟨3431674030186207999842497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2287782686790805333228331 3431674030186207999842497)
              ·
                refine ⟨2573755522639655999881873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3431674030186207999842497 2573755522639655999881873)
                ·
                  refine ⟨1930316641979741999911405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2573755522639655999881873 1930316641979741999911405)
                  ·
                    refine ⟨723868740742403249966777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1930316641979741999911405 723868740742403249966777)
                    ·
                      rfl

theorem cell22_2114594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 1, 2, 2, 3].length) (baseStart_2114594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2114594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2114594 prefixEnd_2114594 := by exact prefixLift 2114594
  have htrace : WordTrace (prefixWord ++ tailWord_2114594) baseStart_2114594 baseEnd_2114594 := by
    simpa [prefixWord, tailWord_2114594, baseEnd_2114594] using wordTrace_append hprefix tailTrace_2114594
  have hstable : (prefixWord ++ tailWord_2114594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2114594).length < 2 ^ (prefixWord ++ tailWord_2114594).sum := by decide
  have hdescent : baseEnd_2114594 < baseStart_2114594 := by decide
  rcases family_descends (prefixWord ++ tailWord_2114594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2114633 : List Nat := [1, 2, 1, 1, 2, 2, 2, 2, 4, 5]
def baseStart_2114633 : Nat := 118140960795 + 2114633 * 2 ^ 59
def prefixEnd_2114633 : Nat := 4983230072969 + 3 ^ 40 * 2114633 * 2
def baseEnd_2114633 : Nat := 723882091239420148241657

theorem tailTrace_2114633 : CollatzResearch.WordTrace tailWord_2114633 prefixEnd_2114633 723882091239420148241657 := by
  unfold tailWord_2114633
  simp only [CollatzResearch.WordTrace]
  refine ⟨77127001748053266408844553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51418001165368844272563035 77127001748053266408844553)
  ·
    refine ⟨57845251311039949806633415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77127001748053266408844553 57845251311039949806633415)
    ·
      refine ⟨86767876966559924709950123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57845251311039949806633415 86767876966559924709950123)
      ·
        refine ⟨130151815449839887064925185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86767876966559924709950123 130151815449839887064925185)
        ·
          refine ⟨97613861587379915298693889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130151815449839887064925185 97613861587379915298693889)
          ·
            refine ⟨73210396190534936474020417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97613861587379915298693889 73210396190534936474020417)
            ·
              refine ⟨54907797142901202355515313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73210396190534936474020417 54907797142901202355515313)
              ·
                refine ⟨41180847857175901766636485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54907797142901202355515313 41180847857175901766636485)
                ·
                  refine ⟨7721408973220481581244341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41180847857175901766636485 7721408973220481581244341)
                  ·
                    refine ⟨723882091239420148241657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7721408973220481581244341 723882091239420148241657)
                    ·
                      rfl

theorem cell22_2114633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 4, 5].length) (baseStart_2114633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2114633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2114633 prefixEnd_2114633 := by exact prefixLift 2114633
  have htrace : WordTrace (prefixWord ++ tailWord_2114633) baseStart_2114633 baseEnd_2114633 := by
    simpa [prefixWord, tailWord_2114633, baseEnd_2114633] using wordTrace_append hprefix tailTrace_2114633
  have hstable : (prefixWord ++ tailWord_2114633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2114633).length < 2 ^ (prefixWord ++ tailWord_2114633).sum := by decide
  have hdescent : baseEnd_2114633 < baseStart_2114633 := by decide
  rcases family_descends (prefixWord ++ tailWord_2114633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2114669 : List Nat := [1, 5, 1, 1, 2, 4, 2, 1, 5]
def baseStart_2114669 : Nat := 118140960795 + 2114669 * 2 ^ 59
def prefixEnd_2114669 : Nat := 4983230072969 + 3 ^ 40 * 2114669 * 2
def baseEnd_2114669 : Nat := 241298138258376018113849

theorem tailTrace_2114669 : CollatzResearch.WordTrace tailWord_2114669 prefixEnd_2114669 241298138258376018113849 := by
  unfold tailWord_2114669
  simp only [CollatzResearch.WordTrace]
  refine ⟨77128314775922844557155061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51418876517281896371436707 77128314775922844557155061)
  ·
    refine ⟨7230779510242766677233287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 77128314775922844557155061 7230779510242766677233287)
    ·
      refine ⟨10846169265364150015849931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7230779510242766677233287 10846169265364150015849931)
      ·
        refine ⟨16269253898046225023774897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10846169265364150015849931 16269253898046225023774897)
        ·
          refine ⟨12201940423534668767831173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16269253898046225023774897 12201940423534668767831173)
          ·
            refine ⟨2287863829412750393968345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12201940423534668767831173 2287863829412750393968345)
            ·
              refine ⟨1715897872059562795476259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2287863829412750393968345 1715897872059562795476259)
              ·
                refine ⟨2573846808089344193214389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1715897872059562795476259 2573846808089344193214389)
                ·
                  refine ⟨241298138258376018113849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2573846808089344193214389 241298138258376018113849)
                  ·
                    rfl

theorem cell22_2114669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 2, 1, 5].length) (baseStart_2114669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2114669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2114669 prefixEnd_2114669 := by exact prefixLift 2114669
  have htrace : WordTrace (prefixWord ++ tailWord_2114669) baseStart_2114669 baseEnd_2114669 := by
    simpa [prefixWord, tailWord_2114669, baseEnd_2114669] using wordTrace_append hprefix tailTrace_2114669
  have hstable : (prefixWord ++ tailWord_2114669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2114669).length < 2 ^ (prefixWord ++ tailWord_2114669).sum := by decide
  have hdescent : baseEnd_2114669 < baseStart_2114669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2114669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2114714 : List Nat := [3, 1, 1, 5, 1, 2, 1, 4, 4]
def baseStart_2114714 : Nat := 118140960795 + 2114714 * 2 ^ 59
def prefixEnd_2114714 : Nat := 4983230072969 + 3 ^ 40 * 2114714 * 2
def baseEnd_2114714 : Nat := 241303273064920978988803

theorem tailTrace_2114714 : CollatzResearch.WordTrace tailWord_2114714 prefixEnd_2114714 241303273064920978988803 := by
  unfold tailWord_2114714
  simp only [CollatzResearch.WordTrace]
  refine ⟨19282489015189954310635799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51419970707173211495028797 19282489015189954310635799)
  ·
    refine ⟨28923733522784931465953699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19282489015189954310635799 28923733522784931465953699)
    ·
      refine ⟨43385600284177397198930549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28923733522784931465953699 43385600284177397198930549)
      ·
        refine ⟨4067400026641630987399739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 43385600284177397198930549 4067400026641630987399739)
        ·
          refine ⟨6101100039962446481099609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4067400026641630987399739 6101100039962446481099609)
          ·
            refine ⟨4575825029971834860824707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6101100039962446481099609 4575825029971834860824707)
            ·
              refine ⟨6863737544957752291237061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4575825029971834860824707 6863737544957752291237061)
              ·
                refine ⟨1286950789679578554606949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6863737544957752291237061 1286950789679578554606949)
                ·
                  refine ⟨241303273064920978988803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1286950789679578554606949 241303273064920978988803)
                  ·
                    rfl

theorem cell22_2114714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 4, 4].length) (baseStart_2114714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2114714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2114714 prefixEnd_2114714 := by exact prefixLift 2114714
  have htrace : WordTrace (prefixWord ++ tailWord_2114714) baseStart_2114714 baseEnd_2114714 := by
    simpa [prefixWord, tailWord_2114714, baseEnd_2114714] using wordTrace_append hprefix tailTrace_2114714
  have hstable : (prefixWord ++ tailWord_2114714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2114714).length < 2 ^ (prefixWord ++ tailWord_2114714).sum := by decide
  have hdescent : baseEnd_2114714 < baseStart_2114714 := by decide
  rcases family_descends (prefixWord ++ tailWord_2114714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2114725 : List Nat := [1, 3, 1, 2, 1, 4, 3, 7]
def baseStart_2114725 : Nat := 118140960795 + 2114725 * 2 ^ 59
def prefixEnd_2114725 : Nat := 4983230072969 + 3 ^ 40 * 2114725 * 2
def baseEnd_2114725 : Nat := 80434842746618063882375

theorem tailTrace_2114725 : CollatzResearch.WordTrace tailWord_2114725 prefixEnd_2114725 80434842746618063882375 := by
  unfold tailWord_2114725
  simp only [CollatzResearch.WordTrace]
  refine ⟨77130357263719966121193629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51420238175813310747462419 77130357263719966121193629)
  ·
    refine ⟨28923883973894987295447611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77130357263719966121193629 28923883973894987295447611)
    ·
      refine ⟨43385825960842480943171417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28923883973894987295447611 43385825960842480943171417)
      ·
        refine ⟨32539369470631860707378563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43385825960842480943171417 32539369470631860707378563)
        ·
          refine ⟨48809054205947791061067845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32539369470631860707378563 48809054205947791061067845)
          ·
            refine ⟨9151697663615210823950221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48809054205947791061067845 9151697663615210823950221)
            ·
              refine ⟨3431886623855704058981333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9151697663615210823950221 3431886623855704058981333)
              ·
                refine ⟨80434842746618063882375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3431886623855704058981333 80434842746618063882375)
                ·
                  rfl

theorem cell22_2114725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3, 7].length) (baseStart_2114725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2114725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2114725 prefixEnd_2114725 := by exact prefixLift 2114725
  have htrace : WordTrace (prefixWord ++ tailWord_2114725) baseStart_2114725 baseEnd_2114725 := by
    simpa [prefixWord, tailWord_2114725, baseEnd_2114725] using wordTrace_append hprefix tailTrace_2114725
  have hstable : (prefixWord ++ tailWord_2114725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2114725).length < 2 ^ (prefixWord ++ tailWord_2114725).sum := by decide
  have hdescent : baseEnd_2114725 < baseStart_2114725 := by decide
  rcases family_descends (prefixWord ++ tailWord_2114725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2114875 : List Nat := [1, 1, 1, 1, 1, 2, 1, 1, 6, 7]
def baseStart_2114875 : Nat := 118140960795 + 2114875 * 2 ^ 59
def prefixEnd_2114875 : Nat := 4983230072969 + 3 ^ 40 * 2114875 * 2
def baseEnd_2114875 : Nat := 723964932785012183690915

theorem tailTrace_2114875 : CollatzResearch.WordTrace tailWord_2114875 prefixEnd_2114875 723964932785012183690915 := by
  unfold tailWord_2114875
  simp only [CollatzResearch.WordTrace]
  refine ⟨77135828213176541739154079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51423885475451027826102719 77135828213176541739154079)
  ·
    refine ⟨115703742319764812608731119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77135828213176541739154079 115703742319764812608731119)
    ·
      refine ⟨173555613479647218913096679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115703742319764812608731119 173555613479647218913096679)
      ·
        refine ⟨260333420219470828369645019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173555613479647218913096679 260333420219470828369645019)
        ·
          refine ⟨390500130329206242554467529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 260333420219470828369645019 390500130329206242554467529)
          ·
            refine ⟨292875097746904681915850647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 390500130329206242554467529 292875097746904681915850647)
            ·
              refine ⟨439312646620357022873775971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 292875097746904681915850647 439312646620357022873775971)
              ·
                refine ⟨658968969930535534310663957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 439312646620357022873775971 658968969930535534310663957)
                ·
                  refine ⟨30889170465493853170812373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 658968969930535534310663957 30889170465493853170812373)
                  ·
                    refine ⟨723964932785012183690915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30889170465493853170812373 723964932785012183690915)
                    ·
                      rfl

theorem cell22_2114875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 6, 7].length) (baseStart_2114875 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2114875 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2114875 prefixEnd_2114875 := by exact prefixLift 2114875
  have htrace : WordTrace (prefixWord ++ tailWord_2114875) baseStart_2114875 baseEnd_2114875 := by
    simpa [prefixWord, tailWord_2114875, baseEnd_2114875] using wordTrace_append hprefix tailTrace_2114875
  have hstable : (prefixWord ++ tailWord_2114875).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2114875).length < 2 ^ (prefixWord ++ tailWord_2114875).sum := by decide
  have hdescent : baseEnd_2114875 < baseStart_2114875 := by decide
  rcases family_descends (prefixWord ++ tailWord_2114875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2114877 : List Nat := [1, 4, 1, 5, 11]
def baseStart_2114877 : Nat := 118140960795 + 2114877 * 2 ^ 59
def prefixEnd_2114877 : Nat := 4983230072969 + 3 ^ 40 * 2114877 * 2
def baseEnd_2114877 : Nat := 2979282376238209239263

theorem tailTrace_2114877 : CollatzResearch.WordTrace tailWord_2114877 prefixEnd_2114877 2979282376238209239263 := by
  unfold tailWord_2114877
  simp only [CollatzResearch.WordTrace]
  refine ⟨77135901159169296080726885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51423934106112864053817923 77135901159169296080726885)
  ·
    refine ⟨14462981467344243015136291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77135901159169296080726885 14462981467344243015136291)
    ·
      refine ⟨21694472201016364522704437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14462981467344243015136291 21694472201016364522704437)
      ·
        refine ⟨2033856768845284174003541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21694472201016364522704437 2033856768845284174003541)
        ·
          refine ⟨2979282376238209239263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 2033856768845284174003541 2979282376238209239263)
          ·
            rfl

theorem cell22_2114877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 11].length) (baseStart_2114877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2114877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2114877 prefixEnd_2114877 := by exact prefixLift 2114877
  have htrace : WordTrace (prefixWord ++ tailWord_2114877) baseStart_2114877 baseEnd_2114877 := by
    simpa [prefixWord, tailWord_2114877, baseEnd_2114877] using wordTrace_append hprefix tailTrace_2114877
  have hstable : (prefixWord ++ tailWord_2114877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2114877).length < 2 ^ (prefixWord ++ tailWord_2114877).sum := by decide
  have hdescent : baseEnd_2114877 < baseStart_2114877 := by decide
  rcases family_descends (prefixWord ++ tailWord_2114877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2114881 : List Nat := [1, 2, 5, 2, 1, 1, 1, 4, 2, 3]
def baseStart_2114881 : Nat := 118140960795 + 2114881 * 2 ^ 59
def prefixEnd_2114881 : Nat := 4983230072969 + 3 ^ 40 * 2114881 * 2
def baseEnd_2114881 : Nat := 723966986707630168040897

theorem tailTrace_2114881 : CollatzResearch.WordTrace tailWord_2114881 prefixEnd_2114881 723966986707630168040897 := by
  unfold tailWord_2114881
  simp only [CollatzResearch.WordTrace]
  refine ⟨77136047051154804763872497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51424031367436536509248331 77136047051154804763872497)
  ·
    refine ⟨57852035288366103572904373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77136047051154804763872497 57852035288366103572904373)
    ·
      refine ⟨5423628308284322209959785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 57852035288366103572904373 5423628308284322209959785)
      ·
        refine ⟨4067721231213241657469839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5423628308284322209959785 4067721231213241657469839)
        ·
          refine ⟨6101581846819862486204759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4067721231213241657469839 6101581846819862486204759)
          ·
            refine ⟨9152372770229793729307139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6101581846819862486204759 9152372770229793729307139)
            ·
              refine ⟨13728559155344690593960709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9152372770229793729307139 13728559155344690593960709)
              ·
                refine ⟨2574104841627129486367633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13728559155344690593960709 2574104841627129486367633)
                ·
                  refine ⟨1930578631220347114775725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2574104841627129486367633 1930578631220347114775725)
                  ·
                    refine ⟨723966986707630168040897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1930578631220347114775725 723966986707630168040897)
                    ·
                      rfl

theorem cell22_2114881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 4, 2, 3].length) (baseStart_2114881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2114881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2114881 prefixEnd_2114881 := by exact prefixLift 2114881
  have htrace : WordTrace (prefixWord ++ tailWord_2114881) baseStart_2114881 baseEnd_2114881 := by
    simpa [prefixWord, tailWord_2114881, baseEnd_2114881] using wordTrace_append hprefix tailTrace_2114881
  have hstable : (prefixWord ++ tailWord_2114881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2114881).length < 2 ^ (prefixWord ++ tailWord_2114881).sum := by decide
  have hdescent : baseEnd_2114881 < baseStart_2114881 := by decide
  rcases family_descends (prefixWord ++ tailWord_2114881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2114937 : List Nat := [1, 2, 1, 3, 2, 1, 3, 2, 2, 5]
def baseStart_2114937 : Nat := 118140960795 + 2114937 * 2 ^ 59
def prefixEnd_2114937 : Nat := 4983230072969 + 3 ^ 40 * 2114937 * 2
def baseEnd_2114937 : Nat := 723986156652064688640725

theorem tailTrace_2114937 : CollatzResearch.WordTrace tailWord_2114937 prefixEnd_2114937 723986156652064688640725 := by
  unfold tailWord_2114937
  simp only [CollatzResearch.WordTrace]
  refine ⟨77138089538951926327911065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51425393025967950885274043 77138089538951926327911065)
  ·
    refine ⟨57853567154213944745933299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77138089538951926327911065 57853567154213944745933299)
    ·
      refine ⟨86780350731320917118899949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57853567154213944745933299 86780350731320917118899949)
      ·
        refine ⟨32542631524245343919587481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86780350731320917118899949 32542631524245343919587481)
        ·
          refine ⟨24406973643184007939690611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32542631524245343919587481 24406973643184007939690611)
          ·
            refine ⟨36610460464776011909535917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24406973643184007939690611 36610460464776011909535917)
            ·
              refine ⟨13728922674291004466075969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36610460464776011909535917 13728922674291004466075969)
              ·
                refine ⟨10296692005718253349556977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13728922674291004466075969 10296692005718253349556977)
                ·
                  refine ⟨7722519004288690012167733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10296692005718253349556977 7722519004288690012167733)
                  ·
                    refine ⟨723986156652064688640725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7722519004288690012167733 723986156652064688640725)
                    ·
                      rfl

theorem cell22_2114937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 2, 2, 5].length) (baseStart_2114937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2114937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2114937 prefixEnd_2114937 := by exact prefixLift 2114937
  have htrace : WordTrace (prefixWord ++ tailWord_2114937) baseStart_2114937 baseEnd_2114937 := by
    simpa [prefixWord, tailWord_2114937, baseEnd_2114937] using wordTrace_append hprefix tailTrace_2114937
  have hstable : (prefixWord ++ tailWord_2114937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2114937).length < 2 ^ (prefixWord ++ tailWord_2114937).sum := by decide
  have hdescent : baseEnd_2114937 < baseStart_2114937 := by decide
  rcases family_descends (prefixWord ++ tailWord_2114937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2114969 : List Nat := [1, 2, 1, 2, 1, 5, 1, 4, 1, 4]
def baseStart_2114969 : Nat := 118140960795 + 2114969 * 2 ^ 59
def prefixEnd_2114969 : Nat := 4983230072969 + 3 ^ 40 * 2114969 * 2
def baseEnd_2114969 : Nat := 723997110906027271840627

theorem tailTrace_2114969 : CollatzResearch.WordTrace tailWord_2114969 prefixEnd_2114969 723997110906027271840627 := by
  unfold tailWord_2114969
  simp only [CollatzResearch.WordTrace]
  refine ⟨77139256674835995793075961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51426171116557330528717307 77139256674835995793075961)
  ·
    refine ⟨57854442506126996844806971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77139256674835995793075961 57854442506126996844806971)
    ·
      refine ⟨86781663759190495267210457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57854442506126996844806971 86781663759190495267210457)
      ·
        refine ⟨65086247819392871450407843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86781663759190495267210457 65086247819392871450407843)
        ·
          refine ⟨97629371729089307175611765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65086247819392871450407843 97629371729089307175611765)
          ·
            refine ⟨9152753599602122547713603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 97629371729089307175611765 9152753599602122547713603)
            ·
              refine ⟨13729130399403183821570405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9152753599602122547713603 13729130399403183821570405)
              ·
                refine ⟨2574211949888096966544451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13729130399403183821570405 2574211949888096966544451)
                ·
                  refine ⟨3861317924832145449816677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2574211949888096966544451 3861317924832145449816677)
                  ·
                    refine ⟨723997110906027271840627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3861317924832145449816677 723997110906027271840627)
                    ·
                      rfl

theorem cell22_2114969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 4, 1, 4].length) (baseStart_2114969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2114969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2114969 prefixEnd_2114969 := by exact prefixLift 2114969
  have htrace : WordTrace (prefixWord ++ tailWord_2114969) baseStart_2114969 baseEnd_2114969 := by
    simpa [prefixWord, tailWord_2114969, baseEnd_2114969] using wordTrace_append hprefix tailTrace_2114969
  have hstable : (prefixWord ++ tailWord_2114969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2114969).length < 2 ^ (prefixWord ++ tailWord_2114969).sum := by decide
  have hdescent : baseEnd_2114969 < baseStart_2114969 := by decide
  rcases family_descends (prefixWord ++ tailWord_2114969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2114999 : List Nat := [1, 1, 3, 1, 3, 2, 1, 3, 4, 3]
def baseStart_2114999 : Nat := 118140960795 + 2114999 * 2 ^ 59
def prefixEnd_2114999 : Nat := 4983230072969 + 3 ^ 40 * 2114999 * 2
def baseEnd_2114999 : Nat := 724007380519117193590535

theorem tailTrace_2114999 : CollatzResearch.WordTrace tailWord_2114999 prefixEnd_2114999 724007380519117193590535 := by
  unfold tailWord_2114999
  simp only [CollatzResearch.WordTrace]
  refine ⟨77140350864727310916668051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51426900576484873944445367 77140350864727310916668051)
  ·
    refine ⟨115710526297090966375002077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77140350864727310916668051 115710526297090966375002077)
    ·
      refine ⟨43391447361409112390625779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115710526297090966375002077 43391447361409112390625779)
      ·
        refine ⟨65087171042113668585938669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43391447361409112390625779 65087171042113668585938669)
        ·
          refine ⟨24407689140792625719727001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65087171042113668585938669 24407689140792625719727001)
          ·
            refine ⟨18305766855594469289795251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24407689140792625719727001 18305766855594469289795251)
            ·
              refine ⟨27458650283391703934692877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18305766855594469289795251 27458650283391703934692877)
              ·
                refine ⟨10296993856271888975509829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27458650283391703934692877 10296993856271888975509829)
                ·
                  refine ⟨1930686348050979182908093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10296993856271888975509829 1930686348050979182908093)
                  ·
                    refine ⟨724007380519117193590535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1930686348050979182908093 724007380519117193590535)
                    ·
                      rfl

theorem cell22_2114999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 3, 4, 3].length) (baseStart_2114999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2114999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2114999 prefixEnd_2114999 := by exact prefixLift 2114999
  have htrace : WordTrace (prefixWord ++ tailWord_2114999) baseStart_2114999 baseEnd_2114999 := by
    simpa [prefixWord, tailWord_2114999, baseEnd_2114999] using wordTrace_append hprefix tailTrace_2114999
  have hstable : (prefixWord ++ tailWord_2114999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2114999).length < 2 ^ (prefixWord ++ tailWord_2114999).sum := by decide
  have hdescent : baseEnd_2114999 < baseStart_2114999 := by decide
  rcases family_descends (prefixWord ++ tailWord_2114999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2115001 : List Nat := [1, 2, 1, 4, 4, 2, 1, 1, 6]
def baseStart_2115001 : Nat := 118140960795 + 2115001 * 2 ^ 59
def prefixEnd_2115001 : Nat := 4983230072969 + 3 ^ 40 * 2115001 * 2
def baseEnd_2115001 : Nat := 241336021719996618346843

theorem tailTrace_2115001 : CollatzResearch.WordTrace tailWord_2115001 prefixEnd_2115001 241336021719996618346843 := by
  unfold tailWord_2115001
  simp only [CollatzResearch.WordTrace]
  refine ⟨77140423810720065258240857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51426949207146710172160571 77140423810720065258240857)
  ·
    refine ⟨57855317858040048943680643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77140423810720065258240857 57855317858040048943680643)
    ·
      refine ⟨86782976787060073415520965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57855317858040048943680643 86782976787060073415520965)
      ·
        refine ⟨16271808147573763765410181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 86782976787060073415520965 16271808147573763765410181)
        ·
          refine ⟨3050964027670080706014409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16271808147573763765410181 3050964027670080706014409)
          ·
            refine ⟨2288223020752560529510807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3050964027670080706014409 2288223020752560529510807)
            ·
              refine ⟨3432334531128840794266211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2288223020752560529510807 3432334531128840794266211)
              ·
                refine ⟨5148501796693261191399317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3432334531128840794266211 5148501796693261191399317)
                ·
                  refine ⟨241336021719996618346843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5148501796693261191399317 241336021719996618346843)
                  ·
                    rfl

theorem cell22_2115001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 1, 1, 6].length) (baseStart_2115001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2115001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2115001 prefixEnd_2115001 := by exact prefixLift 2115001
  have htrace : WordTrace (prefixWord ++ tailWord_2115001) baseStart_2115001 baseEnd_2115001 := by
    simpa [prefixWord, tailWord_2115001, baseEnd_2115001] using wordTrace_append hprefix tailTrace_2115001
  have hstable : (prefixWord ++ tailWord_2115001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2115001).length < 2 ^ (prefixWord ++ tailWord_2115001).sum := by decide
  have hdescent : baseEnd_2115001 < baseStart_2115001 := by decide
  rcases family_descends (prefixWord ++ tailWord_2115001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2115016 : List Nat := [2, 1, 3, 1, 3, 1, 3, 3, 2, 3]
def baseStart_2115016 : Nat := 118140960795 + 2115016 * 2 ^ 59
def prefixEnd_2115016 : Nat := 4983230072969 + 3 ^ 40 * 2115016 * 2
def baseEnd_2115016 : Nat := 724013199966534815915483

theorem tailTrace_2115016 : CollatzResearch.WordTrace tailWord_2115016 prefixEnd_2115016 724013199966534815915483 := by
  unfold tailWord_2115016
  simp only [CollatzResearch.WordTrace]
  refine ⟨38570485452832861410018451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51427313937110481880024601 38570485452832861410018451)
  ·
    refine ⟨57855728179249292115027677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38570485452832861410018451 57855728179249292115027677)
    ·
      refine ⟨21695898067218484543135379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57855728179249292115027677 21695898067218484543135379)
      ·
        refine ⟨32543847100827726814703069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21695898067218484543135379 32543847100827726814703069)
        ·
          refine ⟨12203942662810397555513651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32543847100827726814703069 12203942662810397555513651)
          ·
            refine ⟨18305913994215596333270477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12203942662810397555513651 18305913994215596333270477)
            ·
              refine ⟨6864717747830848624976429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18305913994215596333270477 6864717747830848624976429)
              ·
                refine ⟨2574269155436568234366161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6864717747830848624976429 2574269155436568234366161)
                ·
                  refine ⟨1930701866577426175774621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2574269155436568234366161 1930701866577426175774621)
                  ·
                    refine ⟨724013199966534815915483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1930701866577426175774621 724013199966534815915483)
                    ·
                      rfl

theorem cell22_2115016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 3, 2, 3].length) (baseStart_2115016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2115016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2115016 prefixEnd_2115016 := by exact prefixLift 2115016
  have htrace : WordTrace (prefixWord ++ tailWord_2115016) baseStart_2115016 baseEnd_2115016 := by
    simpa [prefixWord, tailWord_2115016, baseEnd_2115016] using wordTrace_append hprefix tailTrace_2115016
  have hstable : (prefixWord ++ tailWord_2115016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2115016).length < 2 ^ (prefixWord ++ tailWord_2115016).sum := by decide
  have hdescent : baseEnd_2115016 < baseStart_2115016 := by decide
  rcases family_descends (prefixWord ++ tailWord_2115016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2115194 : List Nat := [3, 1, 1, 1, 1, 1, 1, 3, 4, 6]
def baseStart_2115194 : Nat := 118140960795 + 2115194 * 2 ^ 59
def prefixEnd_2115194 : Nat := 4983230072969 + 3 ^ 40 * 2115194 * 2
def baseEnd_2115194 : Nat := 724074133004201684964937

theorem tailTrace_2115194 : CollatzResearch.WordTrace tailWord_2115194 prefixEnd_2115194 724074133004201684964937 := by
  unfold tailWord_2115194
  simp only [CollatzResearch.WordTrace]
  refine ⟨19286865774755214805004159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51431642066013906146677757 19286865774755214805004159)
  ·
    refine ⟨28930298662132822207506239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19286865774755214805004159 28930298662132822207506239)
    ·
      refine ⟨43395447993199233311259359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28930298662132822207506239 43395447993199233311259359)
      ·
        refine ⟨65093171989798849966889039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43395447993199233311259359 65093171989798849966889039)
        ·
          refine ⟨97639757984698274950333559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65093171989798849966889039 97639757984698274950333559)
          ·
            refine ⟨146459636977047412425500339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97639757984698274950333559 146459636977047412425500339)
            ·
              refine ⟨219689455465571118638250509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 146459636977047412425500339 219689455465571118638250509)
              ·
                refine ⟨82383545799589169489343941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 219689455465571118638250509 82383545799589169489343941)
                ·
                  refine ⟨15446914837422969279251989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 82383545799589169489343941 15446914837422969279251989)
                  ·
                    refine ⟨724074133004201684964937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15446914837422969279251989 724074133004201684964937)
                    ·
                      rfl

theorem cell22_2115194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 4, 6].length) (baseStart_2115194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2115194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2115194 prefixEnd_2115194 := by exact prefixLift 2115194
  have htrace : WordTrace (prefixWord ++ tailWord_2115194) baseStart_2115194 baseEnd_2115194 := by
    simpa [prefixWord, tailWord_2115194, baseEnd_2115194] using wordTrace_append hprefix tailTrace_2115194
  have hstable : (prefixWord ++ tailWord_2115194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2115194).length < 2 ^ (prefixWord ++ tailWord_2115194).sum := by decide
  have hdescent : baseEnd_2115194 < baseStart_2115194 := by decide
  rcases family_descends (prefixWord ++ tailWord_2115194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2115196 : List Nat := [2, 2, 2, 1, 1, 2, 1, 3, 5, 3]
def baseStart_2115196 : Nat := 118140960795 + 2115196 * 2 ^ 59
def prefixEnd_2115196 : Nat := 4983230072969 + 3 ^ 40 * 2115196 * 2
def baseEnd_2115196 : Nat := 724074817645074346414931

theorem tailTrace_2115196 : CollatzResearch.WordTrace tailWord_2115196 prefixEnd_2115196 724074817645074346414931 := by
  unfold tailWord_2115196
  simp only [CollatzResearch.WordTrace]
  refine ⟨38573768022506806780794721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51431690696675742374392961 38573768022506806780794721)
  ·
    refine ⟨28930326016880105085596041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38573768022506806780794721 28930326016880105085596041)
    ·
      refine ⟨21697744512660078814197031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28930326016880105085596041 21697744512660078814197031)
      ·
        refine ⟨32546616768990118221295547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21697744512660078814197031 32546616768990118221295547)
        ·
          refine ⟨48819925153485177331943321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32546616768990118221295547 48819925153485177331943321)
          ·
            refine ⟨36614943865113882998957491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48819925153485177331943321 36614943865113882998957491)
            ·
              refine ⟨54922415797670824498436237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36614943865113882998957491 54922415797670824498436237)
              ·
                refine ⟨20595905924126559186913589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54922415797670824498436237 20595905924126559186913589)
                ·
                  refine ⟨1930866180386864923773149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20595905924126559186913589 1930866180386864923773149)
                  ·
                    refine ⟨724074817645074346414931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1930866180386864923773149 724074817645074346414931)
                    ·
                      rfl

theorem cell22_2115196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 3, 5, 3].length) (baseStart_2115196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2115196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2115196 prefixEnd_2115196 := by exact prefixLift 2115196
  have htrace : WordTrace (prefixWord ++ tailWord_2115196) baseStart_2115196 baseEnd_2115196 := by
    simpa [prefixWord, tailWord_2115196, baseEnd_2115196] using wordTrace_append hprefix tailTrace_2115196
  have hstable : (prefixWord ++ tailWord_2115196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2115196).length < 2 ^ (prefixWord ++ tailWord_2115196).sum := by decide
  have hdescent : baseEnd_2115196 < baseStart_2115196 := by decide
  rcases family_descends (prefixWord ++ tailWord_2115196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2115209 : List Nat := [1, 2, 1, 1, 4, 1, 2, 1, 9]
def baseStart_2115209 : Nat := 118140960795 + 2115209 * 2 ^ 59
def prefixEnd_2115209 : Nat := 4983230072969 + 3 ^ 40 * 2115209 * 2
def baseEnd_2115209 : Nat := 241359755936915548613297

theorem tailTrace_2115209 : CollatzResearch.WordTrace tailWord_2115209 prefixEnd_2115209 241359755936915548613297 := by
  unfold tailWord_2115209
  simp only [CollatzResearch.WordTrace]
  refine ⟨77148010193966516781812681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51432006795977677854541787 77148010193966516781812681)
  ·
    refine ⟨57861007645474887586359511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77148010193966516781812681 57861007645474887586359511)
    ·
      refine ⟨86791511468212331379539267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57861007645474887586359511 86791511468212331379539267)
      ·
        refine ⟨130187267202318497069308901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86791511468212331379539267 130187267202318497069308901)
        ·
          refine ⟨24410112600434718200495419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 130187267202318497069308901 24410112600434718200495419)
          ·
            refine ⟨36615168900652077300743129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24410112600434718200495419 36615168900652077300743129)
            ·
              refine ⟨27461376675489057975557347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36615168900652077300743129 27461376675489057975557347)
              ·
                refine ⟨41192065013233586963336021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27461376675489057975557347 41192065013233586963336021)
                ·
                  refine ⟨241359755936915548613297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 41192065013233586963336021 241359755936915548613297)
                  ·
                    rfl

theorem cell22_2115209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 9].length) (baseStart_2115209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2115209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2115209 prefixEnd_2115209 := by exact prefixLift 2115209
  have htrace : WordTrace (prefixWord ++ tailWord_2115209) baseStart_2115209 baseEnd_2115209 := by
    simpa [prefixWord, tailWord_2115209, baseEnd_2115209] using wordTrace_append hprefix tailTrace_2115209
  have hstable : (prefixWord ++ tailWord_2115209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2115209).length < 2 ^ (prefixWord ++ tailWord_2115209).sum := by decide
  have hdescent : baseEnd_2115209 < baseStart_2115209 := by decide
  rcases family_descends (prefixWord ++ tailWord_2115209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2115277 : List Nat := [1, 6, 2, 1, 1, 3, 1, 2, 5]
def baseStart_2115277 : Nat := 118140960795 + 2115277 * 2 ^ 59
def prefixEnd_2115277 : Nat := 4983230072969 + 3 ^ 40 * 2115277 * 2
def baseEnd_2115277 : Nat := 241367515200139045046561

theorem tailTrace_2115277 : CollatzResearch.WordTrace tailWord_2115277 prefixEnd_2115277 241367515200139045046561 := by
  unfold tailWord_2115277
  simp only [CollatzResearch.WordTrace]
  refine ⟨77150490357720164395288085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51433660238480109596858723 77150490357720164395288085)
  ·
    refine ⟨3616429235518132706029129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 77150490357720164395288085 3616429235518132706029129)
    ·
      refine ⟨2712321926638599529521847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3616429235518132706029129 2712321926638599529521847)
      ·
        refine ⟨4068482889957899294282771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2712321926638599529521847 4068482889957899294282771)
        ·
          refine ⟨6102724334936848941424157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4068482889957899294282771 6102724334936848941424157)
          ·
            refine ⟨2288521625601318353034059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6102724334936848941424157 2288521625601318353034059)
            ·
              refine ⟨3432782438401977529551089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2288521625601318353034059 3432782438401977529551089)
              ·
                refine ⟨2574586828801483147163317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3432782438401977529551089 2574586828801483147163317)
                ·
                  refine ⟨241367515200139045046561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2574586828801483147163317 241367515200139045046561)
                  ·
                    rfl

theorem cell22_2115277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 1, 2, 5].length) (baseStart_2115277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2115277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2115277 prefixEnd_2115277 := by exact prefixLift 2115277
  have htrace : WordTrace (prefixWord ++ tailWord_2115277) baseStart_2115277 baseEnd_2115277 := by
    simpa [prefixWord, tailWord_2115277, baseEnd_2115277] using wordTrace_append hprefix tailTrace_2115277
  have hstable : (prefixWord ++ tailWord_2115277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2115277).length < 2 ^ (prefixWord ++ tailWord_2115277).sum := by decide
  have hdescent : baseEnd_2115277 < baseStart_2115277 := by decide
  rcases family_descends (prefixWord ++ tailWord_2115277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2115288 : List Nat := [2, 1, 2, 2, 3, 1, 1, 6, 4]
def baseStart_2115288 : Nat := 118140960795 + 2115288 * 2 ^ 59
def prefixEnd_2115288 : Nat := 4983230072969 + 3 ^ 40 * 2115288 * 2
def baseEnd_2115288 : Nat := 241368770375072257704883

theorem tailTrace_2115288 : CollatzResearch.WordTrace tailWord_2115288 prefixEnd_2115288 241368770375072257704883 := by
  unfold tailWord_2115288
  simp only [CollatzResearch.WordTrace]
  refine ⟨38575445780340156636969259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51433927707120208849292345 38575445780340156636969259)
  ·
    refine ⟨57863168670510234955453889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38575445780340156636969259 57863168670510234955453889)
    ·
      refine ⟨43397376502882676216590417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57863168670510234955453889 43397376502882676216590417)
      ·
        refine ⟨32548032377162007162442813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43397376502882676216590417 32548032377162007162442813)
        ·
          refine ⟨12205512141435752685916055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32548032377162007162442813 12205512141435752685916055)
          ·
            refine ⟨18308268212153629028874083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12205512141435752685916055 18308268212153629028874083)
            ·
              refine ⟨27462402318230443543311125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18308268212153629028874083 27462402318230443543311125)
              ·
                refine ⟨1287300108667052041092709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 27462402318230443543311125 1287300108667052041092709)
                ·
                  refine ⟨241368770375072257704883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1287300108667052041092709 241368770375072257704883)
                  ·
                    rfl

theorem cell22_2115288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 6, 4].length) (baseStart_2115288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2115288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2115288 prefixEnd_2115288 := by exact prefixLift 2115288
  have htrace : WordTrace (prefixWord ++ tailWord_2115288) baseStart_2115288 baseEnd_2115288 := by
    simpa [prefixWord, tailWord_2115288, baseEnd_2115288] using wordTrace_append hprefix tailTrace_2115288
  have hstable : (prefixWord ++ tailWord_2115288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2115288).length < 2 ^ (prefixWord ++ tailWord_2115288).sum := by decide
  have hdescent : baseEnd_2115288 < baseStart_2115288 := by decide
  rcases family_descends (prefixWord ++ tailWord_2115288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2115301 : List Nat := [1, 3, 1, 4, 1, 1, 1, 1, 3, 6]
def baseStart_2115301 : Nat := 118140960795 + 2115301 * 2 ^ 59
def prefixEnd_2115301 : Nat := 4983230072969 + 3 ^ 40 * 2115301 * 2
def baseEnd_2115301 : Nat := 724110761290889072539609

theorem tailTrace_2115301 : CollatzResearch.WordTrace tailWord_2115301 prefixEnd_2115301 724110761290889072539609 := by
  unfold tailWord_2115301
  simp only [CollatzResearch.WordTrace]
  refine ⟨77151365709633216494161757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51434243806422144329441171 77151365709633216494161757)
  ·
    refine ⟨28931762141112456185310659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77151365709633216494161757 28931762141112456185310659)
    ·
      refine ⟨43397643211668684277965989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28931762141112456185310659 43397643211668684277965989)
      ·
        refine ⟨8137058102187878302118623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43397643211668684277965989 8137058102187878302118623)
        ·
          refine ⟨12205587153281817453177935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8137058102187878302118623 12205587153281817453177935)
          ·
            refine ⟨18308380729922726179766903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12205587153281817453177935 18308380729922726179766903)
            ·
              refine ⟨27462571094884089269650355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18308380729922726179766903 27462571094884089269650355)
              ·
                refine ⟨41193856642326133904475533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27462571094884089269650355 41193856642326133904475533)
                ·
                  refine ⟨15447696240872300214178325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41193856642326133904475533 15447696240872300214178325)
                  ·
                    refine ⟨724110761290889072539609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15447696240872300214178325 724110761290889072539609)
                    ·
                      rfl

theorem cell22_2115301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 3, 6].length) (baseStart_2115301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2115301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2115301 prefixEnd_2115301 := by exact prefixLift 2115301
  have htrace : WordTrace (prefixWord ++ tailWord_2115301) baseStart_2115301 baseEnd_2115301 := by
    simpa [prefixWord, tailWord_2115301, baseEnd_2115301] using wordTrace_append hprefix tailTrace_2115301
  have hstable : (prefixWord ++ tailWord_2115301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2115301).length < 2 ^ (prefixWord ++ tailWord_2115301).sum := by decide
  have hdescent : baseEnd_2115301 < baseStart_2115301 := by decide
  rcases family_descends (prefixWord ++ tailWord_2115301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2115318 : List Nat := [5, 1, 1, 1, 1, 3, 2, 1, 1, 6]
def baseStart_2115318 : Nat := 118140960795 + 2115318 * 2 ^ 59
def prefixEnd_2115318 : Nat := 4983230072969 + 3 ^ 40 * 2115318 * 2
def baseEnd_2115318 : Nat := 724116580738306694864557

theorem tailTrace_2115318 : CollatzResearch.WordTrace tailWord_2115318 prefixEnd_2115318 724116580738306694864557 := by
  unfold tailWord_2115318
  simp only [CollatzResearch.WordTrace]
  refine ⟨4821999109410726774845663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 51434657167047752265020405 4821999109410726774845663)
  ·
    refine ⟨7232998664116090162268495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4821999109410726774845663 7232998664116090162268495)
    ·
      refine ⟨10849497996174135243402743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7232998664116090162268495 10849497996174135243402743)
      ·
        refine ⟨16274246994261202865104115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10849497996174135243402743 16274246994261202865104115)
        ·
          refine ⟨24411370491391804297656173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16274246994261202865104115 24411370491391804297656173)
          ·
            refine ⟨9154263934271926611621065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24411370491391804297656173 9154263934271926611621065)
            ·
              refine ⟨6865697950703944958715799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9154263934271926611621065 6865697950703944958715799)
              ·
                refine ⟨10298546926055917438073699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6865697950703944958715799 10298546926055917438073699)
                ·
                  refine ⟨15447820389083876157110549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10298546926055917438073699 15447820389083876157110549)
                  ·
                    refine ⟨724116580738306694864557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15447820389083876157110549 724116580738306694864557)
                    ·
                      rfl

theorem cell22_2115318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 1, 1, 6].length) (baseStart_2115318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2115318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2115318 prefixEnd_2115318 := by exact prefixLift 2115318
  have htrace : WordTrace (prefixWord ++ tailWord_2115318) baseStart_2115318 baseEnd_2115318 := by
    simpa [prefixWord, tailWord_2115318, baseEnd_2115318] using wordTrace_append hprefix tailTrace_2115318
  have hstable : (prefixWord ++ tailWord_2115318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2115318).length < 2 ^ (prefixWord ++ tailWord_2115318).sum := by decide
  have hdescent : baseEnd_2115318 < baseStart_2115318 := by decide
  rcases family_descends (prefixWord ++ tailWord_2115318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2115335 : List Nat := [1, 1, 4, 4, 2, 1, 1, 2, 2, 4]
def baseStart_2115335 : Nat := 118140960795 + 2115335 * 2 ^ 59
def prefixEnd_2115335 : Nat := 4983230072969 + 3 ^ 40 * 2115335 * 2
def baseEnd_2115335 : Nat := 724122400185724317189505

theorem tailTrace_2115335 : CollatzResearch.WordTrace tailWord_2115335 prefixEnd_2115335 724122400185724317189505 := by
  unfold tailWord_2115335
  simp only [CollatzResearch.WordTrace]
  refine ⟨77152605791510040300899459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51435070527673360200599639 77152605791510040300899459)
  ·
    refine ⟨115728908687265060451349189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77152605791510040300899459 115728908687265060451349189)
    ·
      refine ⟨21699170378862198834627973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 115728908687265060451349189 21699170378862198834627973)
      ·
        refine ⟨4068594446036662281492745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21699170378862198834627973 4068594446036662281492745)
        ·
          refine ⟨3051445834527496711119559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4068594446036662281492745 3051445834527496711119559)
          ·
            refine ⟨4577168751791245066679339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3051445834527496711119559 4577168751791245066679339)
            ·
              refine ⟨6865753127686867600019009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4577168751791245066679339 6865753127686867600019009)
              ·
                refine ⟨5149314845765150700014257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6865753127686867600019009 5149314845765150700014257)
                ·
                  refine ⟨3861986134323863025010693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5149314845765150700014257 3861986134323863025010693)
                  ·
                    refine ⟨724122400185724317189505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3861986134323863025010693 724122400185724317189505)
                    ·
                      rfl

theorem cell22_2115335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 2, 2, 4].length) (baseStart_2115335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2115335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2115335 prefixEnd_2115335 := by exact prefixLift 2115335
  have htrace : WordTrace (prefixWord ++ tailWord_2115335) baseStart_2115335 baseEnd_2115335 := by
    simpa [prefixWord, tailWord_2115335, baseEnd_2115335] using wordTrace_append hprefix tailTrace_2115335
  have hstable : (prefixWord ++ tailWord_2115335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2115335).length < 2 ^ (prefixWord ++ tailWord_2115335).sum := by decide
  have hdescent : baseEnd_2115335 < baseStart_2115335 := by decide
  rcases family_descends (prefixWord ++ tailWord_2115335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2115376 : List Nat := [2, 1, 1, 1, 2, 2, 1, 1, 6, 5]
def baseStart_2115376 : Nat := 118140960795 + 2115376 * 2 ^ 59
def prefixEnd_2115376 : Nat := 4983230072969 + 3 ^ 40 * 2115376 * 2
def baseEnd_2115376 : Nat := 724136435323613876914379

theorem tailTrace_2115376 : CollatzResearch.WordTrace tailWord_2115376 prefixEnd_2115376 724136435323613876914379 := by
  unfold tailWord_2115376
  simp only [CollatzResearch.WordTrace]
  refine ⟨38577050592180752151570991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51436067456241002868761321 38577050592180752151570991)
  ·
    refine ⟨57865575888271128227356487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38577050592180752151570991 57865575888271128227356487)
    ·
      refine ⟨86798363832406692341034731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57865575888271128227356487 86798363832406692341034731)
      ·
        refine ⟨130197545748610038511552097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86798363832406692341034731 130197545748610038511552097)
        ·
          refine ⟨97648159311457528883664073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130197545748610038511552097 97648159311457528883664073)
          ·
            refine ⟨73236119483593146662748055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97648159311457528883664073 73236119483593146662748055)
            ·
              refine ⟨109854179225389719994122083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73236119483593146662748055 109854179225389719994122083)
              ·
                refine ⟨164781268838084579991183125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109854179225389719994122083 164781268838084579991183125)
                ·
                  refine ⟨7724121976785214687086709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 164781268838084579991183125 7724121976785214687086709)
                  ·
                    refine ⟨724136435323613876914379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7724121976785214687086709 724136435323613876914379)
                    ·
                      rfl

theorem cell22_2115376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 6, 5].length) (baseStart_2115376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2115376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2115376 prefixEnd_2115376 := by exact prefixLift 2115376
  have htrace : WordTrace (prefixWord ++ tailWord_2115376) baseStart_2115376 baseEnd_2115376 := by
    simpa [prefixWord, tailWord_2115376, baseEnd_2115376] using wordTrace_append hprefix tailTrace_2115376
  have hstable : (prefixWord ++ tailWord_2115376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2115376).length < 2 ^ (prefixWord ++ tailWord_2115376).sum := by decide
  have hdescent : baseEnd_2115376 < baseStart_2115376 := by decide
  rcases family_descends (prefixWord ++ tailWord_2115376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2115423 : List Nat := [1, 1, 2, 3, 1, 5, 1, 2, 6]
def baseStart_2115423 : Nat := 118140960795 + 2115423 * 2 ^ 59
def prefixEnd_2115423 : Nat := 4983230072969 + 3 ^ 40 * 2115423 * 2
def baseEnd_2115423 : Nat := 241384174794707140329745

theorem tailTrace_2115423 : CollatzResearch.WordTrace tailWord_2115423 prefixEnd_2115423 241384174794707140329745 := by
  unfold tailWord_2115423
  simp only [CollatzResearch.WordTrace]
  refine ⟨77155815415191231330102923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51437210276794154220068615 77155815415191231330102923)
  ·
    refine ⟨115733723122786846995154385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77155815415191231330102923 115733723122786846995154385)
    ·
      refine ⟨86800292342090135246365789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115733723122786846995154385 86800292342090135246365789)
      ·
        refine ⟨32550109628283800717387171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86800292342090135246365789 32550109628283800717387171)
        ·
          refine ⟨48825164442425701076080757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32550109628283800717387171 48825164442425701076080757)
          ·
            refine ⟨4577359166477409475882571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 48825164442425701076080757 4577359166477409475882571)
            ·
              refine ⟨6866038749716114213823857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4577359166477409475882571 6866038749716114213823857)
              ·
                refine ⟨5149529062287085660367893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6866038749716114213823857 5149529062287085660367893)
                ·
                  refine ⟨241384174794707140329745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5149529062287085660367893 241384174794707140329745)
                  ·
                    rfl

theorem cell22_2115423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 2, 6].length) (baseStart_2115423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2115423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2115423 prefixEnd_2115423 := by exact prefixLift 2115423
  have htrace : WordTrace (prefixWord ++ tailWord_2115423) baseStart_2115423 baseEnd_2115423 := by
    simpa [prefixWord, tailWord_2115423, baseEnd_2115423] using wordTrace_append hprefix tailTrace_2115423
  have hstable : (prefixWord ++ tailWord_2115423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2115423).length < 2 ^ (prefixWord ++ tailWord_2115423).sum := by decide
  have hdescent : baseEnd_2115423 < baseStart_2115423 := by decide
  rcases family_descends (prefixWord ++ tailWord_2115423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2115453 : List Nat := [1, 4, 1, 1, 2, 1, 1, 3, 4, 4]
def baseStart_2115453 : Nat := 118140960795 + 2115453 * 2 ^ 59
def prefixEnd_2115453 : Nat := 4983230072969 + 3 ^ 40 * 2115453 * 2
def baseEnd_2115453 : Nat := 724162793997211342739143

theorem tailTrace_2115453 : CollatzResearch.WordTrace tailWord_2115453 prefixEnd_2115453 724162793997211342739143 := by
  unfold tailWord_2115453
  simp only [CollatzResearch.WordTrace]
  refine ⟨77156909605082546453695013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51437939736721697635796675 77156909605082546453695013)
  ·
    refine ⟨14466920550952977460067815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77156909605082546453695013 14466920550952977460067815)
    ·
      refine ⟨21700380826429466190101723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14466920550952977460067815 21700380826429466190101723)
      ·
        refine ⟨32550571239644199285152585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21700380826429466190101723 32550571239644199285152585)
        ·
          refine ⟨24412928429733149463864439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32550571239644199285152585 24412928429733149463864439)
          ·
            refine ⟨36619392644599724195796659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24412928429733149463864439 36619392644599724195796659)
            ·
              refine ⟨54929088966899586293694989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36619392644599724195796659 54929088966899586293694989)
              ·
                refine ⟨20598408362587344860135621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54929088966899586293694989 20598408362587344860135621)
                ·
                  refine ⟨3862201567985127161275429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20598408362587344860135621 3862201567985127161275429)
                  ·
                    refine ⟨724162793997211342739143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3862201567985127161275429 724162793997211342739143)
                    ·
                      rfl

theorem cell22_2115453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 3, 4, 4].length) (baseStart_2115453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2115453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2115453 prefixEnd_2115453 := by exact prefixLift 2115453
  have htrace : WordTrace (prefixWord ++ tailWord_2115453) baseStart_2115453 baseEnd_2115453 := by
    simpa [prefixWord, tailWord_2115453, baseEnd_2115453] using wordTrace_append hprefix tailTrace_2115453
  have hstable : (prefixWord ++ tailWord_2115453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2115453).length < 2 ^ (prefixWord ++ tailWord_2115453).sum := by decide
  have hdescent : baseEnd_2115453 < baseStart_2115453 := by decide
  rcases family_descends (prefixWord ++ tailWord_2115453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2115457 : List Nat := [1, 2, 4, 4, 1, 1, 2, 1, 6]
def baseStart_2115457 : Nat := 118140960795 + 2115457 * 2 ^ 59
def prefixEnd_2115457 : Nat := 4983230072969 + 3 ^ 40 * 2115457 * 2
def baseEnd_2115457 : Nat := 241388054426318888546377

theorem tailTrace_2115457 : CollatzResearch.WordTrace tailWord_2115457 prefixEnd_2115457 241388054426318888546377 := by
  unfold tailWord_2115457
  simp only [CollatzResearch.WordTrace]
  refine ⟨77157055497068055136840625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51438036998045370091227083 77157055497068055136840625)
  ·
    refine ⟨57867791622801041352630469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77157055497068055136840625 57867791622801041352630469)
    ·
      refine ⟨10850210929275195253618213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57867791622801041352630469 10850210929275195253618213)
      ·
        refine ⟨2034414549239099110053415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10850210929275195253618213 2034414549239099110053415)
        ·
          refine ⟨3051621823858648665080123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2034414549239099110053415 3051621823858648665080123)
          ·
            refine ⟨4577432735787972997620185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3051621823858648665080123 4577432735787972997620185)
            ·
              refine ⟨3433074551840979748215139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4577432735787972997620185 3433074551840979748215139)
              ·
                refine ⟨5149611827761469622322709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3433074551840979748215139 5149611827761469622322709)
                ·
                  refine ⟨241388054426318888546377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5149611827761469622322709 241388054426318888546377)
                  ·
                    rfl

theorem cell22_2115457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 2, 1, 6].length) (baseStart_2115457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2115457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2115457 prefixEnd_2115457 := by exact prefixLift 2115457
  have htrace : WordTrace (prefixWord ++ tailWord_2115457) baseStart_2115457 baseEnd_2115457 := by
    simpa [prefixWord, tailWord_2115457, baseEnd_2115457] using wordTrace_append hprefix tailTrace_2115457
  have hstable : (prefixWord ++ tailWord_2115457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2115457).length < 2 ^ (prefixWord ++ tailWord_2115457).sum := by decide
  have hdescent : baseEnd_2115457 < baseStart_2115457 := by decide
  rcases family_descends (prefixWord ++ tailWord_2115457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2115485 : List Nat := [1, 4, 2, 1, 2, 2, 4, 6]
def baseStart_2115485 : Nat := 118140960795 + 2115485 * 2 ^ 59
def prefixEnd_2115485 : Nat := 4983230072969 + 3 ^ 40 * 2115485 * 2
def baseEnd_2115485 : Nat := 80463749805685991771005

theorem tailTrace_2115485 : CollatzResearch.WordTrace tailWord_2115485 prefixEnd_2115485 80463749805685991771005 := by
  unfold tailWord_2115485
  simp only [CollatzResearch.WordTrace]
  refine ⟨77158076740966615918859909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51438717827311077279239939 77158076740966615918859909)
  ·
    refine ⟨14467139388931240484786233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77158076740966615918859909 14467139388931240484786233)
    ·
      refine ⟨10850354541698430363589675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14467139388931240484786233 10850354541698430363589675)
      ·
        refine ⟨16275531812547645545384513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10850354541698430363589675 16275531812547645545384513)
        ·
          refine ⟨12206648859410734159038385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16275531812547645545384513 12206648859410734159038385)
          ·
            refine ⟨9154986644558050619278789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12206648859410734159038385 9154986644558050619278789)
            ·
              refine ⟨1716559995854634491114773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9154986644558050619278789 1716559995854634491114773)
              ·
                refine ⟨80463749805685991771005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1716559995854634491114773 80463749805685991771005)
                ·
                  rfl

theorem cell22_2115485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 4, 6].length) (baseStart_2115485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2115485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2115485 prefixEnd_2115485 := by exact prefixLift 2115485
  have htrace : WordTrace (prefixWord ++ tailWord_2115485) baseStart_2115485 baseEnd_2115485 := by
    simpa [prefixWord, tailWord_2115485, baseEnd_2115485] using wordTrace_append hprefix tailTrace_2115485
  have hstable : (prefixWord ++ tailWord_2115485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2115485).length < 2 ^ (prefixWord ++ tailWord_2115485).sum := by decide
  have hdescent : baseEnd_2115485 < baseStart_2115485 := by decide
  rcases family_descends (prefixWord ++ tailWord_2115485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2115513 : List Nat := [1, 2, 1, 4, 2, 1, 1, 3, 7]
def baseStart_2115513 : Nat := 118140960795 + 2115513 * 2 ^ 59
def prefixEnd_2115513 : Nat := 4983230072969 + 3 ^ 40 * 2115513 * 2
def baseEnd_2115513 : Nat := 241394444407797062079653

theorem tailTrace_2115513 : CollatzResearch.WordTrace tailWord_2115513 prefixEnd_2115513 241394444407797062079653 := by
  unfold tailWord_2115513
  simp only [CollatzResearch.WordTrace]
  refine ⟨77159097984865176700879193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51439398656576784467252795 77159097984865176700879193)
  ·
    refine ⟨57869323488648882525659395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77159097984865176700879193 57869323488648882525659395)
    ·
      refine ⟨86803985232973323788489093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57869323488648882525659395 86803985232973323788489093)
      ·
        refine ⟨16275747231182498210341705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 86803985232973323788489093 16275747231182498210341705)
        ·
          refine ⟨12206810423386873657756279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16275747231182498210341705 12206810423386873657756279)
          ·
            refine ⟨18310215635080310486634419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12206810423386873657756279 18310215635080310486634419)
            ·
              refine ⟨27465323452620465729951629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18310215635080310486634419 27465323452620465729951629)
              ·
                refine ⟨10299496294732674648731861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27465323452620465729951629 10299496294732674648731861)
                ·
                  refine ⟨241394444407797062079653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10299496294732674648731861 241394444407797062079653)
                  ·
                    rfl

theorem cell22_2115513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 3, 7].length) (baseStart_2115513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2115513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2115513 prefixEnd_2115513 := by exact prefixLift 2115513
  have htrace : WordTrace (prefixWord ++ tailWord_2115513) baseStart_2115513 baseEnd_2115513 := by
    simpa [prefixWord, tailWord_2115513, baseEnd_2115513] using wordTrace_append hprefix tailTrace_2115513
  have hstable : (prefixWord ++ tailWord_2115513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2115513).length < 2 ^ (prefixWord ++ tailWord_2115513).sum := by decide
  have hdescent : baseEnd_2115513 < baseStart_2115513 := by decide
  rcases family_descends (prefixWord ++ tailWord_2115513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2115517 : List Nat := [1, 4, 1, 2, 3, 1, 3, 1, 3, 3]
def baseStart_2115517 : Nat := 118140960795 + 2115517 * 2 ^ 59
def prefixEnd_2115517 : Nat := 4983230072969 + 3 ^ 40 * 2115517 * 2
def baseEnd_2115517 : Nat := 724184702505136509138947

theorem tailTrace_2115517 : CollatzResearch.WordTrace tailWord_2115517 prefixEnd_2115517 724184702505136509138947 := by
  unfold tailWord_2115517
  simp only [CollatzResearch.WordTrace]
  refine ⟨77159243876850685384024805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51439495917900456922683203 77159243876850685384024805)
  ·
    refine ⟨14467358226909503509504651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77159243876850685384024805 14467358226909503509504651)
    ·
      refine ⟨21701037340364255264256977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14467358226909503509504651 21701037340364255264256977)
      ·
        refine ⟨16275778005273191448192733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21701037340364255264256977 16275778005273191448192733)
        ·
          refine ⟨6103416751977446793072275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16275778005273191448192733 6103416751977446793072275)
          ·
            refine ⟨9155125127966170189608413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6103416751977446793072275 9155125127966170189608413)
            ·
              refine ⟨3433171922987313821103155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9155125127966170189608413 3433171922987313821103155)
              ·
                refine ⟨5149757884480970731654733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3433171922987313821103155 5149757884480970731654733)
                ·
                  refine ⟨1931159206680364024370525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5149757884480970731654733 1931159206680364024370525)
                  ·
                    refine ⟨724184702505136509138947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1931159206680364024370525 724184702505136509138947)
                    ·
                      rfl

theorem cell22_2115517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3, 1, 3, 3].length) (baseStart_2115517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2115517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2115517 prefixEnd_2115517 := by exact prefixLift 2115517
  have htrace : WordTrace (prefixWord ++ tailWord_2115517) baseStart_2115517 baseEnd_2115517 := by
    simpa [prefixWord, tailWord_2115517, baseEnd_2115517] using wordTrace_append hprefix tailTrace_2115517
  have hstable : (prefixWord ++ tailWord_2115517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2115517).length < 2 ^ (prefixWord ++ tailWord_2115517).sum := by decide
  have hdescent : baseEnd_2115517 < baseStart_2115517 := by decide
  rcases family_descends (prefixWord ++ tailWord_2115517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2115603 : List Nat := [1, 1, 1, 2, 1, 4, 2, 10]
def baseStart_2115603 : Nat := 118140960795 + 2115603 * 2 ^ 59
def prefixEnd_2115603 : Nat := 4983230072969 + 3 ^ 40 * 2115603 * 2
def baseEnd_2115603 : Nat := 80468238006962327943187

theorem tailTrace_2115603 : CollatzResearch.WordTrace tailWord_2115603 prefixEnd_2115603 80468238006962327943187 := by
  unfold tailWord_2115603
  simp only [CollatzResearch.WordTrace]
  refine ⟨77162380554539122071655463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51441587036359414714436975 77162380554539122071655463)
  ·
    refine ⟨115743570831808683107483195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77162380554539122071655463 115743570831808683107483195)
    ·
      refine ⟨173615356247713024661224793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115743570831808683107483195 173615356247713024661224793)
      ·
        refine ⟨130211517185784768495918595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 173615356247713024661224793 130211517185784768495918595)
        ·
          refine ⟨195317275778677152743877893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130211517185784768495918595 195317275778677152743877893)
          ·
            refine ⟨36621989208501966139477105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 195317275778677152743877893 36621989208501966139477105)
            ·
              refine ⟨27466491906376474604607829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36621989208501966139477105 27466491906376474604607829)
              ·
                refine ⟨80468238006962327943187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 27466491906376474604607829 80468238006962327943187)
                ·
                  rfl

theorem cell22_2115603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 10].length) (baseStart_2115603 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2115603 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2115603 prefixEnd_2115603 := by exact prefixLift 2115603
  have htrace : WordTrace (prefixWord ++ tailWord_2115603) baseStart_2115603 baseEnd_2115603 := by
    simpa [prefixWord, tailWord_2115603, baseEnd_2115603] using wordTrace_append hprefix tailTrace_2115603
  have hstable : (prefixWord ++ tailWord_2115603).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2115603).length < 2 ^ (prefixWord ++ tailWord_2115603).sum := by decide
  have hdescent : baseEnd_2115603 < baseStart_2115603 := by decide
  rcases family_descends (prefixWord ++ tailWord_2115603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2115641 : List Nat := [1, 2, 1, 5, 3, 1, 3, 1, 2, 3]
def baseStart_2115641 : Nat := 118140960795 + 2115641 * 2 ^ 59
def prefixEnd_2115641 : Nat := 4983230072969 + 3 ^ 40 * 2115641 * 2
def baseEnd_2115641 : Nat := 724227150239241519038567

theorem tailTrace_2115641 : CollatzResearch.WordTrace tailWord_2115641 prefixEnd_2115641 724227150239241519038567 := by
  unfold tailWord_2115641
  simp only [CollatzResearch.WordTrace]
  refine ⟨77163766528401454561538777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51442511018934303041025851 77163766528401454561538777)
  ·
    refine ⟨57872824896301090921154083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77163766528401454561538777 57872824896301090921154083)
    ·
      refine ⟨86809237344451636381731125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57872824896301090921154083 86809237344451636381731125)
      ·
        refine ⟨8138366001042340910787293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 86809237344451636381731125 8138366001042340910787293)
        ·
          refine ⟨3051887250390877841545235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8138366001042340910787293 3051887250390877841545235)
          ·
            refine ⟨4577830875586316762317853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3051887250390877841545235 4577830875586316762317853)
            ·
              refine ⟨1716686578344868785869195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4577830875586316762317853 1716686578344868785869195)
              ·
                refine ⟨2575029867517303178803793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1716686578344868785869195 2575029867517303178803793)
                ·
                  refine ⟨1931272400637977384102845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2575029867517303178803793 1931272400637977384102845)
                  ·
                    refine ⟨724227150239241519038567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1931272400637977384102845 724227150239241519038567)
                    ·
                      rfl

theorem cell22_2115641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 3, 1, 2, 3].length) (baseStart_2115641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2115641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2115641 prefixEnd_2115641 := by exact prefixLift 2115641
  have htrace : WordTrace (prefixWord ++ tailWord_2115641) baseStart_2115641 baseEnd_2115641 := by
    simpa [prefixWord, tailWord_2115641, baseEnd_2115641] using wordTrace_append hprefix tailTrace_2115641
  have hstable : (prefixWord ++ tailWord_2115641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2115641).length < 2 ^ (prefixWord ++ tailWord_2115641).sum := by decide
  have hdescent : baseEnd_2115641 < baseStart_2115641 := by decide
  rcases family_descends (prefixWord ++ tailWord_2115641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2115744 : List Nat := [2, 1, 1, 4, 2, 3, 1, 4, 4]
def baseStart_2115744 : Nat := 118140960795 + 2115744 * 2 ^ 59
def prefixEnd_2115744 : Nat := 4983230072969 + 3 ^ 40 * 2115744 * 2
def baseEnd_2115744 : Nat := 241420803081394527904417

theorem tailTrace_2115744 : CollatzResearch.WordTrace tailWord_2115744 prefixEnd_2115744 241420803081394527904417 := by
  unfold tailWord_2115744
  simp only [CollatzResearch.WordTrace]
  refine ⟨38583761623514151576269143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51445015498018868768358857 38583761623514151576269143)
  ·
    refine ⟨57875642435271227364403715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38583761623514151576269143 57875642435271227364403715)
    ·
      refine ⟨86813463652906841046605573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57875642435271227364403715 86813463652906841046605573)
      ·
        refine ⟨16277524434920032696238545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 86813463652906841046605573 16277524434920032696238545)
        ·
          refine ⟨12208143326190024522178909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16277524434920032696238545 12208143326190024522178909)
          ·
            refine ⟨4578053747321259195817091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12208143326190024522178909 4578053747321259195817091)
            ·
              refine ⟨6867080620981888793725637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4578053747321259195817091 6867080620981888793725637)
              ·
                refine ⟨1287577616434104148823557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6867080620981888793725637 1287577616434104148823557)
                ·
                  refine ⟨241420803081394527904417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1287577616434104148823557 241420803081394527904417)
                  ·
                    rfl

theorem cell22_2115744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 4, 4].length) (baseStart_2115744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2115744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2115744 prefixEnd_2115744 := by exact prefixLift 2115744
  have htrace : WordTrace (prefixWord ++ tailWord_2115744) baseStart_2115744 baseEnd_2115744 := by
    simpa [prefixWord, tailWord_2115744, baseEnd_2115744] using wordTrace_append hprefix tailTrace_2115744
  have hstable : (prefixWord ++ tailWord_2115744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2115744).length < 2 ^ (prefixWord ++ tailWord_2115744).sum := by decide
  have hdescent : baseEnd_2115744 < baseStart_2115744 := by decide
  rcases family_descends (prefixWord ++ tailWord_2115744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2115774 : List Nat := [4, 2, 1, 1, 4, 1, 1, 1, 1, 6]
def baseStart_2115774 : Nat := 118140960795 + 2115774 * 2 ^ 59
def prefixEnd_2115774 : Nat := 4983230072969 + 3 ^ 40 * 2115774 * 2
def baseEnd_2115774 : Nat := 724272678857273505463159

theorem tailTrace_2115774 : CollatzResearch.WordTrace tailWord_2115774 prefixEnd_2115774 724272678857273505463159 := by
  unfold tailWord_2115774
  simp only [CollatzResearch.WordTrace]
  refine ⟨9646077179614952284516297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51445744957946412184086917 9646077179614952284516297)
  ·
    refine ⟨7234557884711214213387223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9646077179614952284516297 7234557884711214213387223)
    ·
      refine ⟨10851836827066821320080835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7234557884711214213387223 10851836827066821320080835)
      ·
        refine ⟨16277755240600231980121253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10851836827066821320080835 16277755240600231980121253)
        ·
          refine ⟨3052079107612543496272735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16277755240600231980121253 3052079107612543496272735)
          ·
            refine ⟨4578118661418815244409103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3052079107612543496272735 4578118661418815244409103)
            ·
              refine ⟨6867177992128222866613655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4578118661418815244409103 6867177992128222866613655)
              ·
                refine ⟨10300766988192334299920483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6867177992128222866613655 10300766988192334299920483)
                ·
                  refine ⟨15451150482288501449880725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10300766988192334299920483 15451150482288501449880725)
                  ·
                    refine ⟨724272678857273505463159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15451150482288501449880725 724272678857273505463159)
                    ·
                      rfl

theorem cell22_2115774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 1, 1, 6].length) (baseStart_2115774 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2115774 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2115774 prefixEnd_2115774 := by exact prefixLift 2115774
  have htrace : WordTrace (prefixWord ++ tailWord_2115774) baseStart_2115774 baseEnd_2115774 := by
    simpa [prefixWord, tailWord_2115774, baseEnd_2115774] using wordTrace_append hprefix tailTrace_2115774
  have hstable : (prefixWord ++ tailWord_2115774).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2115774).length < 2 ^ (prefixWord ++ tailWord_2115774).sum := by decide
  have hdescent : baseEnd_2115774 < baseStart_2115774 := by decide
  rcases family_descends (prefixWord ++ tailWord_2115774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2115778 : List Nat := [3, 5, 1, 1, 1, 1, 1, 5, 4]
def baseStart_2115778 : Nat := 118140960795 + 2115778 * 2 ^ 59
def prefixEnd_2115778 : Nat := 4983230072969 + 3 ^ 40 * 2115778 * 2
def baseEnd_2115778 : Nat := 241424682713006276121049

theorem tailTrace_2115778 : CollatzResearch.WordTrace tailWord_2115778 prefixEnd_2115778 241424682713006276121049 := by
  unfold tailWord_2115778
  simp only [CollatzResearch.WordTrace]
  refine ⟨19292190832226281739818997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51445842219270084639517325 19292190832226281739818997)
  ·
    refine ⟨1808642890521213913108031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19292190832226281739818997 1808642890521213913108031)
    ·
      refine ⟨2712964335781820869662047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1808642890521213913108031 2712964335781820869662047)
      ·
        refine ⟨4069446503672731304493071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2712964335781820869662047 4069446503672731304493071)
        ·
          refine ⟨6104169755509096956739607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4069446503672731304493071 6104169755509096956739607)
          ·
            refine ⟨9156254633263645435109411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6104169755509096956739607 9156254633263645435109411)
            ·
              refine ⟨13734381949895468152664117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9156254633263645435109411 13734381949895468152664117)
              ·
                refine ⟨1287598307802700139312261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13734381949895468152664117 1287598307802700139312261)
                ·
                  refine ⟨241424682713006276121049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1287598307802700139312261 241424682713006276121049)
                  ·
                    rfl

theorem cell22_2115778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_2115778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2115778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2115778 prefixEnd_2115778 := by exact prefixLift 2115778
  have htrace : WordTrace (prefixWord ++ tailWord_2115778) baseStart_2115778 baseEnd_2115778 := by
    simpa [prefixWord, tailWord_2115778, baseEnd_2115778] using wordTrace_append hprefix tailTrace_2115778
  have hstable : (prefixWord ++ tailWord_2115778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2115778).length < 2 ^ (prefixWord ++ tailWord_2115778).sum := by decide
  have hdescent : baseEnd_2115778 < baseStart_2115778 := by decide
  rcases family_descends (prefixWord ++ tailWord_2115778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2115785 : List Nat := [1, 2, 1, 1, 2, 1, 1, 4, 1, 8]
def baseStart_2115785 : Nat := 118140960795 + 2115785 * 2 ^ 59
def prefixEnd_2115785 : Nat := 4983230072969 + 3 ^ 40 * 2115785 * 2
def baseEnd_2115785 : Nat := 724276444382073143438125

theorem tailTrace_2115785 : CollatzResearch.WordTrace tailWord_2115785 prefixEnd_2115785 724276444382073143438125 := by
  unfold tailWord_2115785
  simp only [CollatzResearch.WordTrace]
  refine ⟨77169018639879767154780809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51446012426586511436520539 77169018639879767154780809)
  ·
    refine ⟨57876763979909825366085607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77169018639879767154780809 57876763979909825366085607)
    ·
      refine ⟨86815145969864738049128411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57876763979909825366085607 86815145969864738049128411)
      ·
        refine ⟨130222718954797107073692617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86815145969864738049128411 130222718954797107073692617)
        ·
          refine ⟨97667039216097830305269463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130222718954797107073692617 97667039216097830305269463)
          ·
            refine ⟨146500558824146745457904195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97667039216097830305269463 146500558824146745457904195)
            ·
              refine ⟨219750838236220118186856293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 146500558824146745457904195 219750838236220118186856293)
              ·
                refine ⟨41203282169291272160035555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 219750838236220118186856293 41203282169291272160035555)
                ·
                  refine ⟨61804923253936908240053333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41203282169291272160035555 61804923253936908240053333)
                  ·
                    refine ⟨724276444382073143438125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 61804923253936908240053333 724276444382073143438125)
                    ·
                      rfl

theorem cell22_2115785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 8].length) (baseStart_2115785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2115785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2115785 prefixEnd_2115785 := by exact prefixLift 2115785
  have htrace : WordTrace (prefixWord ++ tailWord_2115785) baseStart_2115785 baseEnd_2115785 := by
    simpa [prefixWord, tailWord_2115785, baseEnd_2115785] using wordTrace_append hprefix tailTrace_2115785
  have hstable : (prefixWord ++ tailWord_2115785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2115785).length < 2 ^ (prefixWord ++ tailWord_2115785).sum := by decide
  have hdescent : baseEnd_2115785 < baseStart_2115785 := by decide
  rcases family_descends (prefixWord ++ tailWord_2115785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2115787 : List Nat := [1, 1, 1, 1, 3, 2, 3, 2, 5, 3]
def baseStart_2115787 : Nat := 118140960795 + 2115787 * 2 ^ 59
def prefixEnd_2115787 : Nat := 4983230072969 + 3 ^ 40 * 2115787 * 2
def baseEnd_2115787 : Nat := 724277129022945804888119

theorem tailTrace_2115787 : CollatzResearch.WordTrace tailWord_2115787 prefixEnd_2115787 724277129022945804888119 := by
  unfold tailWord_2115787
  simp only [CollatzResearch.WordTrace]
  refine ⟨77169091585872521496353615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51446061057248347664235743 77169091585872521496353615)
  ·
    refine ⟨115753637378808782244530423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77169091585872521496353615 115753637378808782244530423)
    ·
      refine ⟨173630456068213173366795635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115753637378808782244530423 173630456068213173366795635)
      ·
        refine ⟨260445684102319760050193453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173630456068213173366795635 260445684102319760050193453)
        ·
          refine ⟨97667131538369910018822545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 260445684102319760050193453 97667131538369910018822545)
          ·
            refine ⟨73250348653777432514116909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97667131538369910018822545 73250348653777432514116909)
            ·
              refine ⟨27468880745166537192793841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73250348653777432514116909 27468880745166537192793841)
              ·
                refine ⟨20601660558874902894595381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27468880745166537192793841 20601660558874902894595381)
                ·
                  refine ⟨1931405677394522146368317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20601660558874902894595381 1931405677394522146368317)
                  ·
                    refine ⟨724277129022945804888119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1931405677394522146368317 724277129022945804888119)
                    ·
                      rfl

theorem cell22_2115787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 2, 5, 3].length) (baseStart_2115787 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2115787 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2115787 prefixEnd_2115787 := by exact prefixLift 2115787
  have htrace : WordTrace (prefixWord ++ tailWord_2115787) baseStart_2115787 baseEnd_2115787 := by
    simpa [prefixWord, tailWord_2115787, baseEnd_2115787] using wordTrace_append hprefix tailTrace_2115787
  have hstable : (prefixWord ++ tailWord_2115787).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2115787).length < 2 ^ (prefixWord ++ tailWord_2115787).sum := by decide
  have hdescent : baseEnd_2115787 < baseStart_2115787 := by decide
  rcases family_descends (prefixWord ++ tailWord_2115787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2115810 : List Nat := [3, 3, 4, 1, 1, 2, 1, 1, 1, 5]
def baseStart_2115810 : Nat := 118140960795 + 2115810 * 2 ^ 59
def prefixEnd_2115810 : Nat := 4983230072969 + 3 ^ 40 * 2115810 * 2
def baseEnd_2115810 : Nat := 724285002392981411563049

theorem tailTrace_2115810 : CollatzResearch.WordTrace tailWord_2115810 prefixEnd_2115810 724285002392981411563049 := by
  unfold tailWord_2115810
  simp only [CollatzResearch.WordTrace]
  refine ⟨19292482616197299106110221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51446620309859464282960589 19292482616197299106110221)
  ·
    refine ⟨7234680981073987164791333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19292482616197299106110221 7234680981073987164791333)
    ·
      refine ⟨1356502683951372593398375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7234680981073987164791333 1356502683951372593398375)
      ·
        refine ⟨2034754025927058890097563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1356502683951372593398375 2034754025927058890097563)
        ·
          refine ⟨3052131038890588335146345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2034754025927058890097563 3052131038890588335146345)
          ·
            refine ⟨2289098279167941251359759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3052131038890588335146345 2289098279167941251359759)
            ·
              refine ⟨3433647418751911877039639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2289098279167941251359759 3433647418751911877039639)
              ·
                refine ⟨5150471128127867815559459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3433647418751911877039639 5150471128127867815559459)
                ·
                  refine ⟨7725706692191801723339189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5150471128127867815559459 7725706692191801723339189)
                  ·
                    refine ⟨724285002392981411563049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7725706692191801723339189 724285002392981411563049)
                    ·
                      rfl

theorem cell22_2115810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_2115810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2115810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2115810 prefixEnd_2115810 := by exact prefixLift 2115810
  have htrace : WordTrace (prefixWord ++ tailWord_2115810) baseStart_2115810 baseEnd_2115810 := by
    simpa [prefixWord, tailWord_2115810, baseEnd_2115810] using wordTrace_append hprefix tailTrace_2115810
  have hstable : (prefixWord ++ tailWord_2115810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2115810).length < 2 ^ (prefixWord ++ tailWord_2115810).sum := by decide
  have hdescent : baseEnd_2115810 < baseStart_2115810 := by decide
  rcases family_descends (prefixWord ++ tailWord_2115810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2115911 : List Nat := [1, 1, 4, 1, 2, 2, 4, 2, 2, 3]
def baseStart_2115911 : Nat := 118140960795 + 2115911 * 2 ^ 59
def prefixEnd_2115911 : Nat := 4983230072969 + 3 ^ 40 * 2115911 * 2
def baseEnd_2115911 : Nat := 724319576757050814787739

theorem tailTrace_2115911 : CollatzResearch.WordTrace tailWord_2115911 prefixEnd_2115911 724319576757050814787739 := by
  unfold tailWord_2115911
  simp only [CollatzResearch.WordTrace]
  refine ⟨77173614237423290673867587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51449076158282193782578391 77173614237423290673867587)
  ·
    refine ⟨115760421356134936010801381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77173614237423290673867587 115760421356134936010801381)
    ·
      refine ⟨21705079004275300502025259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 115760421356134936010801381 21705079004275300502025259)
      ·
        refine ⟨32557618506412950753037889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21705079004275300502025259 32557618506412950753037889)
        ·
          refine ⟨24418213879809713064778417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32557618506412950753037889 24418213879809713064778417)
          ·
            refine ⟨18313660409857284798583813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24418213879809713064778417 18313660409857284798583813)
            ·
              refine ⟨3433811326848240899734465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18313660409857284798583813 3433811326848240899734465)
              ·
                refine ⟨2575358495136180674800849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3433811326848240899734465 2575358495136180674800849)
                ·
                  refine ⟨1931518871352135506100637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2575358495136180674800849 1931518871352135506100637)
                  ·
                    refine ⟨724319576757050814787739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1931518871352135506100637 724319576757050814787739)
                    ·
                      rfl

theorem cell22_2115911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4, 2, 2, 3].length) (baseStart_2115911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2115911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2115911 prefixEnd_2115911 := by exact prefixLift 2115911
  have htrace : WordTrace (prefixWord ++ tailWord_2115911) baseStart_2115911 baseEnd_2115911 := by
    simpa [prefixWord, tailWord_2115911, baseEnd_2115911] using wordTrace_append hprefix tailTrace_2115911
  have hstable : (prefixWord ++ tailWord_2115911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2115911).length < 2 ^ (prefixWord ++ tailWord_2115911).sum := by decide
  have hdescent : baseEnd_2115911 < baseStart_2115911 := by decide
  rcases family_descends (prefixWord ++ tailWord_2115911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2115924 : List Nat := [2, 4, 1, 1, 2, 2, 3, 7]
def baseStart_2115924 : Nat := 118140960795 + 2115924 * 2 ^ 59
def prefixEnd_2115924 : Nat := 4983230072969 + 3 ^ 40 * 2115924 * 2
def baseEnd_2115924 : Nat := 80480447435858123801411

theorem tailTrace_2115924 : CollatzResearch.WordTrace tailWord_2115924 prefixEnd_2115924 80480447435858123801411 := by
  unfold tailWord_2115924
  simp only [CollatzResearch.WordTrace]
  refine ⟨38587044193188096947045413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51449392257584129262727217 38587044193188096947045413)
  ·
    refine ⟨7235070786222768177571015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38587044193188096947045413 7235070786222768177571015)
    ·
      refine ⟨10852606179334152266356523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7235070786222768177571015 10852606179334152266356523)
      ·
        refine ⟨16278909269001228399534785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10852606179334152266356523 16278909269001228399534785)
        ·
          refine ⟨12209181951750921299651089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16278909269001228399534785 12209181951750921299651089)
          ·
            refine ⟨9156886463813190974738317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12209181951750921299651089 9156886463813190974738317)
            ·
              refine ⟨3433832423929946615526869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9156886463813190974738317 3433832423929946615526869)
              ·
                refine ⟨80480447435858123801411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3433832423929946615526869 80480447435858123801411)
                ·
                  rfl

theorem cell22_2115924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3, 7].length) (baseStart_2115924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2115924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2115924 prefixEnd_2115924 := by exact prefixLift 2115924
  have htrace : WordTrace (prefixWord ++ tailWord_2115924) baseStart_2115924 baseEnd_2115924 := by
    simpa [prefixWord, tailWord_2115924, baseEnd_2115924] using wordTrace_append hprefix tailTrace_2115924
  have hstable : (prefixWord ++ tailWord_2115924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2115924).length < 2 ^ (prefixWord ++ tailWord_2115924).sum := by decide
  have hdescent : baseEnd_2115924 < baseStart_2115924 := by decide
  rcases family_descends (prefixWord ++ tailWord_2115924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2115967 : List Nat := [1, 1, 2, 2, 1, 1, 2, 2, 3, 7]
def baseStart_2115967 : Nat := 118140960795 + 2115967 * 2 ^ 59
def prefixEnd_2115967 : Nat := 4983230072969 + 3 ^ 40 * 2115967 * 2
def baseEnd_2115967 : Nat := 724338746701485335387567

theorem tailTrace_2115967 : CollatzResearch.WordTrace tailWord_2115967 prefixEnd_2115967 724338746701485335387567 := by
  unfold tailWord_2115967
  simp only [CollatzResearch.WordTrace]
  refine ⟨77175656725220412237906155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51450437816813608158604103 77175656725220412237906155)
  ·
    refine ⟨115763485087830618356859233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77175656725220412237906155 115763485087830618356859233)
    ·
      refine ⟨86822613815872963767644425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115763485087830618356859233 86822613815872963767644425)
      ·
        refine ⟨65116960361904722825733319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86822613815872963767644425 65116960361904722825733319)
        ·
          refine ⟨97675440542857084238599979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65116960361904722825733319 97675440542857084238599979)
          ·
            refine ⟨146513160814285626357899969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97675440542857084238599979 146513160814285626357899969)
            ·
              refine ⟨109884870610714219768424977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 146513160814285626357899969 109884870610714219768424977)
              ·
                refine ⟨82413652958035664826318733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 109884870610714219768424977 82413652958035664826318733)
                ·
                  refine ⟨30905119859263374309869525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 82413652958035664826318733 30905119859263374309869525)
                  ·
                    refine ⟨724338746701485335387567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30905119859263374309869525 724338746701485335387567)
                    ·
                      rfl

theorem cell22_2115967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 3, 7].length) (baseStart_2115967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2115967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2115967 prefixEnd_2115967 := by exact prefixLift 2115967
  have htrace : WordTrace (prefixWord ++ tailWord_2115967) baseStart_2115967 baseEnd_2115967 := by
    simpa [prefixWord, tailWord_2115967, baseEnd_2115967] using wordTrace_append hprefix tailTrace_2115967
  have hstable : (prefixWord ++ tailWord_2115967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2115967).length < 2 ^ (prefixWord ++ tailWord_2115967).sum := by decide
  have hdescent : baseEnd_2115967 < baseStart_2115967 := by decide
  rcases family_descends (prefixWord ++ tailWord_2115967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2116082 : List Nat := [3, 2, 1, 4, 2, 2, 2, 2, 4]
def baseStart_2116082 : Nat := 118140960795 + 2116082 * 2 ^ 59
def prefixEnd_2116082 : Nat := 4983230072969 + 3 ^ 40 * 2116082 * 2
def baseEnd_2116082 : Nat := 241459371183887789587405

theorem tailTrace_2116082 : CollatzResearch.WordTrace tailWord_2116082 prefixEnd_2116082 241459371183887789587405 := by
  unfold tailWord_2116082
  simp only [CollatzResearch.WordTrace]
  refine ⟨19294962779950946719585625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51453234079869191252228333 19294962779950946719585625)
  ·
    refine ⟨14471222084963210039689219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19294962779950946719585625 14471222084963210039689219)
    ·
      refine ⟨21706833127444815059533829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14471222084963210039689219 21706833127444815059533829)
      ·
        refine ⟨4070031211395902823662593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21706833127444815059533829 4070031211395902823662593)
        ·
          refine ⟨3052523408546927117746945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4070031211395902823662593 3052523408546927117746945)
          ·
            refine ⟨2289392556410195338310209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3052523408546927117746945 2289392556410195338310209)
            ·
              refine ⟨1717044417307646503732657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2289392556410195338310209 1717044417307646503732657)
              ·
                refine ⟨1287783312980734877799493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1717044417307646503732657 1287783312980734877799493)
                ·
                  refine ⟨241459371183887789587405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1287783312980734877799493 241459371183887789587405)
                  ·
                    rfl

theorem cell22_2116082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 2, 2, 4].length) (baseStart_2116082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2116082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2116082 prefixEnd_2116082 := by exact prefixLift 2116082
  have htrace : WordTrace (prefixWord ++ tailWord_2116082) baseStart_2116082 baseEnd_2116082 := by
    simpa [prefixWord, tailWord_2116082, baseEnd_2116082] using wordTrace_append hprefix tailTrace_2116082
  have hstable : (prefixWord ++ tailWord_2116082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2116082).length < 2 ^ (prefixWord ++ tailWord_2116082).sum := by decide
  have hdescent : baseEnd_2116082 < baseStart_2116082 := by decide
  rcases family_descends (prefixWord ++ tailWord_2116082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2116089 : List Nat := [1, 2, 1, 3, 1, 2, 3, 1, 2, 6]
def baseStart_2116089 : Nat := 118140960795 + 2116089 * 2 ^ 59
def prefixEnd_2116089 : Nat := 4983230072969 + 3 ^ 40 * 2116089 * 2
def baseEnd_2116089 : Nat := 724380509794717683837193

theorem tailTrace_2116089 : CollatzResearch.WordTrace tailWord_2116089 prefixEnd_2116089 724380509794717683837193 := by
  unfold tailWord_2116089
  simp only [CollatzResearch.WordTrace]
  refine ⟨77180106430778427073847321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51453404287185618049231547 77180106430778427073847321)
  ·
    refine ⟨57885079823083820305385491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77180106430778427073847321 57885079823083820305385491)
    ·
      refine ⟨86827619734625730458078237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57885079823083820305385491 86827619734625730458078237)
      ·
        refine ⟨32560357400484648921779339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86827619734625730458078237 32560357400484648921779339)
        ·
          refine ⟨48840536100726973382669009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32560357400484648921779339 48840536100726973382669009)
          ·
            refine ⟨36630402075545230037001757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48840536100726973382669009 36630402075545230037001757)
            ·
              refine ⟨13736400778329461263875659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36630402075545230037001757 13736400778329461263875659)
              ·
                refine ⟨20604601167494191895813489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13736400778329461263875659 20604601167494191895813489)
                ·
                  refine ⟨15453450875620643921860117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20604601167494191895813489 15453450875620643921860117)
                  ·
                    refine ⟨724380509794717683837193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15453450875620643921860117 724380509794717683837193)
                    ·
                      rfl

theorem cell22_2116089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 1, 2, 6].length) (baseStart_2116089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2116089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2116089 prefixEnd_2116089 := by exact prefixLift 2116089
  have htrace : WordTrace (prefixWord ++ tailWord_2116089) baseStart_2116089 baseEnd_2116089 := by
    simpa [prefixWord, tailWord_2116089, baseEnd_2116089] using wordTrace_append hprefix tailTrace_2116089
  have hstable : (prefixWord ++ tailWord_2116089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2116089).length < 2 ^ (prefixWord ++ tailWord_2116089).sum := by decide
  have hdescent : baseEnd_2116089 < baseStart_2116089 := by decide
  rcases family_descends (prefixWord ++ tailWord_2116089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2116104 : List Nat := [2, 1, 3, 2, 1, 1, 1, 2, 9]
def baseStart_2116104 : Nat := 118140960795 + 2116104 * 2 ^ 59
def prefixEnd_2116104 : Nat := 4983230072969 + 3 ^ 40 * 2116104 * 2
def baseEnd_2116104 : Nat := 241461881533754214904049

theorem tailTrace_2116104 : CollatzResearch.WordTrace tailWord_2116104 prefixEnd_2116104 241461881533754214904049 := by
  unfold tailWord_2116104
  simp only [CollatzResearch.WordTrace]
  refine ⟨38590326762862042317821683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51453769017149389757095577 38590326762862042317821683)
  ·
    refine ⟨57885490144293063476732525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38590326762862042317821683 57885490144293063476732525)
    ·
      refine ⟨21707058804109898803774697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57885490144293063476732525 21707058804109898803774697)
      ·
        refine ⟨16280294103082424102831023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21707058804109898803774697 16280294103082424102831023)
        ·
          refine ⟨24420441154623636154246535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16280294103082424102831023 24420441154623636154246535)
          ·
            refine ⟨36630661731935454231369803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24420441154623636154246535 36630661731935454231369803)
            ·
              refine ⟨54945992597903181347054705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36630661731935454231369803 54945992597903181347054705)
              ·
                refine ⟨41209494448427386010291029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54945992597903181347054705 41209494448427386010291029)
                ·
                  refine ⟨241461881533754214904049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 41209494448427386010291029 241461881533754214904049)
                  ·
                    rfl

theorem cell22_2116104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 9].length) (baseStart_2116104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2116104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2116104 prefixEnd_2116104 := by exact prefixLift 2116104
  have htrace : WordTrace (prefixWord ++ tailWord_2116104) baseStart_2116104 baseEnd_2116104 := by
    simpa [prefixWord, tailWord_2116104, baseEnd_2116104] using wordTrace_append hprefix tailTrace_2116104
  have hstable : (prefixWord ++ tailWord_2116104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2116104).length < 2 ^ (prefixWord ++ tailWord_2116104).sum := by decide
  have hdescent : baseEnd_2116104 < baseStart_2116104 := by decide
  rcases family_descends (prefixWord ++ tailWord_2116104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2116108 : List Nat := [2, 2, 1, 2, 4, 2, 1, 2, 3, 3]
def baseStart_2116108 : Nat := 118140960795 + 2116108 * 2 ^ 59
def prefixEnd_2116108 : Nat := 4983230072969 + 3 ^ 40 * 2116108 * 2
def baseEnd_2116108 : Nat := 724387013883007967612135

theorem tailTrace_2116108 : CollatzResearch.WordTrace tailWord_2116108 prefixEnd_2116108 724387013883007967612135 := by
  unfold tailWord_2116108
  simp only [CollatzResearch.WordTrace]
  refine ⟨38590399708854796659394489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51453866278473062212525985 38590399708854796659394489)
  ·
    refine ⟨28942799781641097494545867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38590399708854796659394489 28942799781641097494545867)
    ·
      refine ⟨43414199672461646241818801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28942799781641097494545867 43414199672461646241818801)
      ·
        refine ⟨32560649754346234681364101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43414199672461646241818801 32560649754346234681364101)
        ·
          refine ⟨6105121828939919002755769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32560649754346234681364101 6105121828939919002755769)
          ·
            refine ⟨4578841371704939252066827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6105121828939919002755769 4578841371704939252066827)
            ·
              refine ⟨6868262057557408878100241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4578841371704939252066827 6868262057557408878100241)
              ·
                refine ⟨5151196543168056658575181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6868262057557408878100241 5151196543168056658575181)
                ·
                  refine ⟨1931698703688021246965693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5151196543168056658575181 1931698703688021246965693)
                  ·
                    refine ⟨724387013883007967612135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1931698703688021246965693 724387013883007967612135)
                    ·
                      rfl

theorem cell22_2116108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 2, 3, 3].length) (baseStart_2116108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2116108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2116108 prefixEnd_2116108 := by exact prefixLift 2116108
  have htrace : WordTrace (prefixWord ++ tailWord_2116108) baseStart_2116108 baseEnd_2116108 := by
    simpa [prefixWord, tailWord_2116108, baseEnd_2116108] using wordTrace_append hprefix tailTrace_2116108
  have hstable : (prefixWord ++ tailWord_2116108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2116108).length < 2 ^ (prefixWord ++ tailWord_2116108).sum := by decide
  have hdescent : baseEnd_2116108 < baseStart_2116108 := by decide
  rcases family_descends (prefixWord ++ tailWord_2116108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2116125 : List Nat := [1, 4, 2, 2, 1, 2, 1, 5, 1, 3]
def baseStart_2116125 : Nat := 118140960795 + 2116125 * 2 ^ 59
def prefixEnd_2116125 : Nat := 4983230072969 + 3 ^ 40 * 2116125 * 2
def baseEnd_2116125 : Nat := 724392833330425589937083

theorem tailTrace_2116125 : CollatzResearch.WordTrace tailWord_2116125 prefixEnd_2116125 724392833330425589937083 := by
  unfold tailWord_2116125
  simp only [CollatzResearch.WordTrace]
  refine ⟨77181419458648005222157829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51454279639098670148105219 77181419458648005222157829)
  ·
    refine ⟨14471516148496500979154593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77181419458648005222157829 14471516148496500979154593)
    ·
      refine ⟨10853637111372375734365945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14471516148496500979154593 10853637111372375734365945)
      ·
        refine ⟨8140227833529281800774459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10853637111372375734365945 8140227833529281800774459)
        ·
          refine ⟨12210341750293922701161689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8140227833529281800774459 12210341750293922701161689)
          ·
            refine ⟨9157756312720442025871267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12210341750293922701161689 9157756312720442025871267)
            ·
              refine ⟨13736634469080663038806901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9157756312720442025871267 13736634469080663038806901)
              ·
                refine ⟨1287809481476312159888147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13736634469080663038806901 1287809481476312159888147)
                ·
                  refine ⟨1931714222214468239832221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1287809481476312159888147 1931714222214468239832221)
                  ·
                    refine ⟨724392833330425589937083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1931714222214468239832221 724392833330425589937083)
                    ·
                      rfl

theorem cell22_2116125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 5, 1, 3].length) (baseStart_2116125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2116125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2116125 prefixEnd_2116125 := by exact prefixLift 2116125
  have htrace : WordTrace (prefixWord ++ tailWord_2116125) baseStart_2116125 baseEnd_2116125 := by
    simpa [prefixWord, tailWord_2116125, baseEnd_2116125] using wordTrace_append hprefix tailTrace_2116125
  have hstable : (prefixWord ++ tailWord_2116125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2116125).length < 2 ^ (prefixWord ++ tailWord_2116125).sum := by decide
  have hdescent : baseEnd_2116125 < baseStart_2116125 := by decide
  rcases family_descends (prefixWord ++ tailWord_2116125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2116138 : List Nat := [3, 1, 4, 1, 1, 2, 3, 2, 5]
def baseStart_2116138 : Nat := 118140960795 + 2116138 * 2 ^ 59
def prefixEnd_2116138 : Nat := 4983230072969 + 3 ^ 40 * 2116138 * 2
def baseEnd_2116138 : Nat := 241465761165365963120681

theorem tailTrace_2116138 : CollatzResearch.WordTrace tailWord_2116138 prefixEnd_2116138 241465761165365963120681 := by
  unfold tailWord_2116138
  simp only [CollatzResearch.WordTrace]
  refine ⟨19295473401900227110595267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51454595738400605628254045 19295473401900227110595267)
  ·
    refine ⟨28943210102850340665892901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19295473401900227110595267 28943210102850340665892901)
    ·
      refine ⟨5426851894284438874854919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28943210102850340665892901 5426851894284438874854919)
      ·
        refine ⟨8140277841426658312282379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5426851894284438874854919 8140277841426658312282379)
        ·
          refine ⟨12210416762139987468423569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8140277841426658312282379 12210416762139987468423569)
          ·
            refine ⟨9157812571604990601317677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12210416762139987468423569 9157812571604990601317677)
            ·
              refine ⟨3434179714351871475494129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9157812571604990601317677 3434179714351871475494129)
              ·
                refine ⟨2575634785763903606620597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3434179714351871475494129 2575634785763903606620597)
                ·
                  refine ⟨241465761165365963120681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2575634785763903606620597 241465761165365963120681)
                  ·
                    rfl

theorem cell22_2116138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3, 2, 5].length) (baseStart_2116138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2116138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2116138 prefixEnd_2116138 := by exact prefixLift 2116138
  have htrace : WordTrace (prefixWord ++ tailWord_2116138) baseStart_2116138 baseEnd_2116138 := by
    simpa [prefixWord, tailWord_2116138, baseEnd_2116138] using wordTrace_append hprefix tailTrace_2116138
  have hstable : (prefixWord ++ tailWord_2116138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2116138).length < 2 ^ (prefixWord ++ tailWord_2116138).sum := by decide
  have hdescent : baseEnd_2116138 < baseStart_2116138 := by decide
  rcases family_descends (prefixWord ++ tailWord_2116138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2116181 : List Nat := [1, 3, 2, 2, 1, 1, 2, 4, 1, 5]
def baseStart_2116181 : Nat := 118140960795 + 2116181 * 2 ^ 59
def prefixEnd_2116181 : Nat := 4983230072969 + 3 ^ 40 * 2116181 * 2
def baseEnd_2116181 : Nat := 724412003274860110536911

theorem tailTrace_2116181 : CollatzResearch.WordTrace tailWord_2116181 prefixEnd_2116181 724412003274860110536911 := by
  unfold tailWord_2116181
  simp only [CollatzResearch.WordTrace]
  refine ⟨77183461946445126786196397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51455641297630084524130931 77183461946445126786196397)
  ·
    refine ⟨28943798229916922544823649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77183461946445126786196397 28943798229916922544823649)
    ·
      refine ⟨21707848672437691908617737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28943798229916922544823649 21707848672437691908617737)
      ·
        refine ⟨16280886504328268931463303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21707848672437691908617737 16280886504328268931463303)
        ·
          refine ⟨24421329756492403397194955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16280886504328268931463303 24421329756492403397194955)
          ·
            refine ⟨36631994634738605095792433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24421329756492403397194955 36631994634738605095792433)
            ·
              refine ⟨27473995976053953821844325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36631994634738605095792433 27473995976053953821844325)
              ·
                refine ⟨5151374245510116341595811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27473995976053953821844325 5151374245510116341595811)
                ·
                  refine ⟨7727061368265174512393717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5151374245510116341595811 7727061368265174512393717)
                  ·
                    refine ⟨724412003274860110536911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7727061368265174512393717 724412003274860110536911)
                    ·
                      rfl

theorem cell22_2116181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 4, 1, 5].length) (baseStart_2116181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2116181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2116181 prefixEnd_2116181 := by exact prefixLift 2116181
  have htrace : WordTrace (prefixWord ++ tailWord_2116181) baseStart_2116181 baseEnd_2116181 := by
    simpa [prefixWord, tailWord_2116181, baseEnd_2116181] using wordTrace_append hprefix tailTrace_2116181
  have hstable : (prefixWord ++ tailWord_2116181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2116181).length < 2 ^ (prefixWord ++ tailWord_2116181).sum := by decide
  have hdescent : baseEnd_2116181 < baseStart_2116181 := by decide
  rcases family_descends (prefixWord ++ tailWord_2116181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2116200 : List Nat := [2, 1, 4, 3, 2, 2, 1, 1, 6]
def baseStart_2116200 : Nat := 118140960795 + 2116200 * 2 ^ 59
def prefixEnd_2116200 : Nat := 4983230072969 + 3 ^ 40 * 2116200 * 2
def baseEnd_2116200 : Nat := 241472835787716798103951

theorem tailTrace_2116200 : CollatzResearch.WordTrace tailWord_2116200 prefixEnd_2116200 241472835787716798103951 := by
  unfold tailWord_2116200
  simp only [CollatzResearch.WordTrace]
  refine ⟨38592077466688146515569027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51456103288917528687425369 38592077466688146515569027)
  ·
    refine ⟨57888116200032219773353541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38592077466688146515569027 57888116200032219773353541)
    ·
      refine ⟨10854021787506041207503789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57888116200032219773353541 10854021787506041207503789)
      ·
        refine ⟨4070258170314765452813921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10854021787506041207503789 4070258170314765452813921)
        ·
          refine ⟨3052693627736074089610441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4070258170314765452813921 3052693627736074089610441)
          ·
            refine ⟨2289520220802055567207831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3052693627736074089610441 2289520220802055567207831)
            ·
              refine ⟨3434280331203083350811747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2289520220802055567207831 3434280331203083350811747)
              ·
                refine ⟨5151420496804625026217621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3434280331203083350811747 5151420496804625026217621)
                ·
                  refine ⟨241472835787716798103951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5151420496804625026217621 241472835787716798103951)
                  ·
                    rfl

theorem cell22_2116200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 1, 1, 6].length) (baseStart_2116200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2116200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2116200 prefixEnd_2116200 := by exact prefixLift 2116200
  have htrace : WordTrace (prefixWord ++ tailWord_2116200) baseStart_2116200 baseEnd_2116200 := by
    simpa [prefixWord, tailWord_2116200, baseEnd_2116200] using wordTrace_append hprefix tailTrace_2116200
  have hstable : (prefixWord ++ tailWord_2116200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2116200).length < 2 ^ (prefixWord ++ tailWord_2116200).sum := by decide
  have hdescent : baseEnd_2116200 < baseStart_2116200 := by decide
  rcases family_descends (prefixWord ++ tailWord_2116200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2116215 : List Nat := [1, 1, 3, 1, 1, 3, 6, 1, 2, 3]
def baseStart_2116215 : Nat := 118140960795 + 2116215 * 2 ^ 59
def prefixEnd_2116215 : Nat := 4983230072969 + 3 ^ 40 * 2116215 * 2
def baseEnd_2116215 : Nat := 724423642169695355186807

theorem tailTrace_2116215 : CollatzResearch.WordTrace tailWord_2116215 prefixEnd_2116215 724423642169695355186807 := by
  unfold tailWord_2116215
  simp only [CollatzResearch.WordTrace]
  refine ⟨77184702028321950592934099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51456468018881300395289399 77184702028321950592934099)
  ·
    refine ⟨115777053042482925889401149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77184702028321950592934099 115777053042482925889401149)
    ·
      refine ⟨43416394890931097208525431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115777053042482925889401149 43416394890931097208525431)
      ·
        refine ⟨65124592336396645812788147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43416394890931097208525431 65124592336396645812788147)
        ·
          refine ⟨97686888504594968719182221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65124592336396645812788147 97686888504594968719182221)
          ·
            refine ⟨36632583189223113269693333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 97686888504594968719182221 36632583189223113269693333)
            ·
              refine ⟨1717152336994833434516875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 36632583189223113269693333 1717152336994833434516875)
              ·
                refine ⟨2575728505492250151775313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1717152336994833434516875 2575728505492250151775313)
                ·
                  refine ⟨1931796379119187613831485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2575728505492250151775313 1931796379119187613831485)
                  ·
                    refine ⟨724423642169695355186807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1931796379119187613831485 724423642169695355186807)
                    ·
                      rfl

theorem cell22_2116215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 6, 1, 2, 3].length) (baseStart_2116215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2116215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2116215 prefixEnd_2116215 := by exact prefixLift 2116215
  have htrace : WordTrace (prefixWord ++ tailWord_2116215) baseStart_2116215 baseEnd_2116215 := by
    simpa [prefixWord, tailWord_2116215, baseEnd_2116215] using wordTrace_append hprefix tailTrace_2116215
  have hstable : (prefixWord ++ tailWord_2116215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2116215).length < 2 ^ (prefixWord ++ tailWord_2116215).sum := by decide
  have hdescent : baseEnd_2116215 < baseStart_2116215 := by decide
  rcases family_descends (prefixWord ++ tailWord_2116215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2116271 : List Nat := [1, 1, 2, 1, 2, 5, 1, 1, 1, 7]
def baseStart_2116271 : Nat := 118140960795 + 2116271 * 2 ^ 59
def prefixEnd_2116271 : Nat := 4983230072969 + 3 ^ 40 * 2116271 * 2
def baseEnd_2116271 : Nat := 724442812114129875786635

theorem tailTrace_2116271 : CollatzResearch.WordTrace tailWord_2116271 prefixEnd_2116271 724442812114129875786635 := by
  unfold tailWord_2116271
  simp only [CollatzResearch.WordTrace]
  refine ⟨77186744516119072156972667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51457829677412714771315111 77186744516119072156972667)
  ·
    refine ⟨115780116774178608235459001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77186744516119072156972667 115780116774178608235459001)
    ·
      refine ⟨86835087580633956176594251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115780116774178608235459001 86835087580633956176594251)
      ·
        refine ⟨130252631370950934264891377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86835087580633956176594251 130252631370950934264891377)
        ·
          refine ⟨97689473528213200698668533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130252631370950934264891377 97689473528213200698668533)
          ·
            refine ⟨9158388143269987565500175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 97689473528213200698668533 9158388143269987565500175)
            ·
              refine ⟨13737582214904981348250263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9158388143269987565500175 13737582214904981348250263)
              ·
                refine ⟨20606373322357472022375395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13737582214904981348250263 20606373322357472022375395)
                ·
                  refine ⟨30909559983536208033563093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20606373322357472022375395 30909559983536208033563093)
                  ·
                    refine ⟨724442812114129875786635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30909559983536208033563093 724442812114129875786635)
                    ·
                      rfl

theorem cell22_2116271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 1, 1, 7].length) (baseStart_2116271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2116271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2116271 prefixEnd_2116271 := by exact prefixLift 2116271
  have htrace : WordTrace (prefixWord ++ tailWord_2116271) baseStart_2116271 baseEnd_2116271 := by
    simpa [prefixWord, tailWord_2116271, baseEnd_2116271] using wordTrace_append hprefix tailTrace_2116271
  have hstable : (prefixWord ++ tailWord_2116271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2116271).length < 2 ^ (prefixWord ++ tailWord_2116271).sum := by decide
  have hdescent : baseEnd_2116271 < baseStart_2116271 := by decide
  rcases family_descends (prefixWord ++ tailWord_2116271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2116348 : List Nat := [2, 2, 2, 1, 3, 2, 2, 1, 1, 6]
def baseStart_2116348 : Nat := 118140960795 + 2116348 * 2 ^ 59
def prefixEnd_2116348 : Nat := 4983230072969 + 3 ^ 40 * 2116348 * 2
def baseEnd_2116348 : Nat := 724469170787727341611399

theorem tailTrace_2116348 : CollatzResearch.WordTrace tailWord_2116348 prefixEnd_2116348 724469170787727341611399 := by
  unfold tailWord_2116348
  simp only [CollatzResearch.WordTrace]
  refine ⟨38594776468420057153762849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51459701957893409538350465 38594776468420057153762849)
  ·
    refine ⟨28946082351315042865322137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38594776468420057153762849 28946082351315042865322137)
    ·
      refine ⟨21709561763486282148991603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28946082351315042865322137 21709561763486282148991603)
      ·
        refine ⟨32564342645229423223487405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21709561763486282148991603 32564342645229423223487405)
        ·
          refine ⟨12211628491961033708807777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32564342645229423223487405 12211628491961033708807777)
          ·
            refine ⟨9158721368970775281605833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12211628491961033708807777 9158721368970775281605833)
            ·
              refine ⟨6869041026728081461204375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9158721368970775281605833 6869041026728081461204375)
              ·
                refine ⟨10303561540092122191806563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6869041026728081461204375 10303561540092122191806563)
                ·
                  refine ⟨15455342310138183287709845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10303561540092122191806563 15455342310138183287709845)
                  ·
                    refine ⟨724469170787727341611399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15455342310138183287709845 724469170787727341611399)
                    ·
                      rfl

theorem cell22_2116348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 1, 1, 6].length) (baseStart_2116348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2116348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2116348 prefixEnd_2116348 := by exact prefixLift 2116348
  have htrace : WordTrace (prefixWord ++ tailWord_2116348) baseStart_2116348 baseEnd_2116348 := by
    simpa [prefixWord, tailWord_2116348, baseEnd_2116348] using wordTrace_append hprefix tailTrace_2116348
  have hstable : (prefixWord ++ tailWord_2116348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2116348).length < 2 ^ (prefixWord ++ tailWord_2116348).sum := by decide
  have hdescent : baseEnd_2116348 < baseStart_2116348 := by decide
  rcases family_descends (prefixWord ++ tailWord_2116348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2116384 : List Nat := [2, 1, 1, 5, 1, 4, 2, 1, 2, 3]
def baseStart_2116384 : Nat := 118140960795 + 2116384 * 2 ^ 59
def prefixEnd_2116384 : Nat := 4983230072969 + 3 ^ 40 * 2116384 * 2
def baseEnd_2116384 : Nat := 724481494323435247711289

theorem tailTrace_2116384 : CollatzResearch.WordTrace tailWord_2116384 prefixEnd_2116384 724481494323435247711289 := by
  unfold tailWord_2116384
  simp only [CollatzResearch.WordTrace]
  refine ⟨38595432982354846227918103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51460577309806461637224137 38595432982354846227918103)
  ·
    refine ⟨57893149473532269341877155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38595432982354846227918103 57893149473532269341877155)
    ·
      refine ⟨86839724210298404012815733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57893149473532269341877155 86839724210298404012815733)
      ·
        refine ⟨8141224144715475376201475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 86839724210298404012815733 8141224144715475376201475)
        ·
          refine ⟨12211836217073213064302213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8141224144715475376201475 12211836217073213064302213)
          ·
            refine ⟨2289719290701227449556665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12211836217073213064302213 2289719290701227449556665)
            ·
              refine ⟨1717289468025920587167499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2289719290701227449556665 1717289468025920587167499)
              ·
                refine ⟨2575934202038880880751249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1717289468025920587167499 2575934202038880880751249)
                ·
                  refine ⟨1931950651529160660563437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2575934202038880880751249 1931950651529160660563437)
                  ·
                    refine ⟨724481494323435247711289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1931950651529160660563437 724481494323435247711289)
                    ·
                      rfl

theorem cell22_2116384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 2, 1, 2, 3].length) (baseStart_2116384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2116384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2116384 prefixEnd_2116384 := by exact prefixLift 2116384
  have htrace : WordTrace (prefixWord ++ tailWord_2116384) baseStart_2116384 baseEnd_2116384 := by
    simpa [prefixWord, tailWord_2116384, baseEnd_2116384] using wordTrace_append hprefix tailTrace_2116384
  have hstable : (prefixWord ++ tailWord_2116384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2116384).length < 2 ^ (prefixWord ++ tailWord_2116384).sum := by decide
  have hdescent : baseEnd_2116384 < baseStart_2116384 := by decide
  rcases family_descends (prefixWord ++ tailWord_2116384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2116412 : List Nat := [2, 2, 2, 2, 1, 1, 1, 7, 1, 3]
def baseStart_2116412 : Nat := 118140960795 + 2116412 * 2 ^ 59
def prefixEnd_2116412 : Nat := 4983230072969 + 3 ^ 40 * 2116412 * 2
def baseEnd_2116412 : Nat := 724491079295652508011203

theorem tailTrace_2116412 : CollatzResearch.WordTrace tailWord_2116412 prefixEnd_2116412 724491079295652508011203 := by
  unfold tailWord_2116412
  simp only [CollatzResearch.WordTrace]
  refine ⟨38595943604304126618927745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51461258139072168825236993 38595943604304126618927745)
  ·
    refine ⟨28946957703228094964195809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38595943604304126618927745 28946957703228094964195809)
    ·
      refine ⟨21710218277421071223146857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28946957703228094964195809 21710218277421071223146857)
      ·
        refine ⟨16282663708065803417360143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21710218277421071223146857 16282663708065803417360143)
        ·
          refine ⟨24423995562098705126040215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16282663708065803417360143 24423995562098705126040215)
          ·
            refine ⟨36635993343148057689060323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24423995562098705126040215 36635993343148057689060323)
            ·
              refine ⟨54953990014722086533590485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36635993343148057689060323 54953990014722086533590485)
              ·
                refine ⟨1287984140970048903131027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 54953990014722086533590485 1287984140970048903131027)
                ·
                  refine ⟨1931976211455073354696541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1287984140970048903131027 1931976211455073354696541)
                  ·
                    refine ⟨724491079295652508011203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1931976211455073354696541 724491079295652508011203)
                    ·
                      rfl

theorem cell22_2116412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 7, 1, 3].length) (baseStart_2116412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2116412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2116412 prefixEnd_2116412 := by exact prefixLift 2116412
  have htrace : WordTrace (prefixWord ++ tailWord_2116412) baseStart_2116412 baseEnd_2116412 := by
    simpa [prefixWord, tailWord_2116412, baseEnd_2116412] using wordTrace_append hprefix tailTrace_2116412
  have hstable : (prefixWord ++ tailWord_2116412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2116412).length < 2 ^ (prefixWord ++ tailWord_2116412).sum := by decide
  have hdescent : baseEnd_2116412 < baseStart_2116412 := by decide
  rcases family_descends (prefixWord ++ tailWord_2116412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2116423 : List Nat := [1, 1, 4, 1, 2, 1, 1, 4, 2, 5]
def baseStart_2116423 : Nat := 118140960795 + 2116423 * 2 ^ 59
def prefixEnd_2116423 : Nat := 4983230072969 + 3 ^ 40 * 2116423 * 2
def baseEnd_2116423 : Nat := 724494844820452145986169

theorem tailTrace_2116423 : CollatzResearch.WordTrace tailWord_2116423 prefixEnd_2116423 724494844820452145986169 := by
  unfold tailWord_2116423
  simp only [CollatzResearch.WordTrace]
  refine ⟨77192288411568402116505923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51461525607712268077670615 77192288411568402116505923)
  ·
    refine ⟨115788432617352603174758885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77192288411568402116505923 115788432617352603174758885)
    ·
      refine ⟨21710331115753613095267291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 115788432617352603174758885 21710331115753613095267291)
      ·
        refine ⟨32565496673630419642900937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21710331115753613095267291 32565496673630419642900937)
        ·
          refine ⟨24424122505222814732175703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32565496673630419642900937 24424122505222814732175703)
          ·
            refine ⟨36636183757834222098263555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24424122505222814732175703 36636183757834222098263555)
            ·
              refine ⟨54954275636751333147395333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36636183757834222098263555 54954275636751333147395333)
              ·
                refine ⟨10303926681890874965136625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54954275636751333147395333 10303926681890874965136625)
                ·
                  refine ⟨7727945011418156223852469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10303926681890874965136625 7727945011418156223852469)
                  ·
                    refine ⟨724494844820452145986169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7727945011418156223852469 724494844820452145986169)
                    ·
                      rfl

theorem cell22_2116423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 4, 2, 5].length) (baseStart_2116423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2116423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2116423 prefixEnd_2116423 := by exact prefixLift 2116423
  have htrace : WordTrace (prefixWord ++ tailWord_2116423) baseStart_2116423 baseEnd_2116423 := by
    simpa [prefixWord, tailWord_2116423, baseEnd_2116423] using wordTrace_append hprefix tailTrace_2116423
  have hstable : (prefixWord ++ tailWord_2116423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2116423).length < 2 ^ (prefixWord ++ tailWord_2116423).sum := by decide
  have hdescent : baseEnd_2116423 < baseStart_2116423 := by decide
  rcases family_descends (prefixWord ++ tailWord_2116423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2116425 : List Nat := [1, 2, 1, 1, 2, 6, 2, 2, 5]
def baseStart_2116425 : Nat := 118140960795 + 2116425 * 2 ^ 59
def prefixEnd_2116425 : Nat := 4983230072969 + 3 ^ 40 * 2116425 * 2
def baseEnd_2116425 : Nat := 241498509820441602478721

theorem tailTrace_2116425 : CollatzResearch.WordTrace tailWord_2116425 prefixEnd_2116425 241498509820441602478721 := by
  unfold tailWord_2116425
  simp only [CollatzResearch.WordTrace]
  refine ⟨77192361357561156458078729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51461574238374104305385819 77192361357561156458078729)
  ·
    refine ⟨57894271018170867343559047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77192361357561156458078729 57894271018170867343559047)
    ·
      refine ⟨86841406527256301015338571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57894271018170867343559047 86841406527256301015338571)
      ·
        refine ⟨130262109790884451523007857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86841406527256301015338571 130262109790884451523007857)
        ·
          refine ⟨97696582343163338642255893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130262109790884451523007857 97696582343163338642255893)
          ·
            refine ⟨4579527297335781498855745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 97696582343163338642255893 4579527297335781498855745)
            ·
              refine ⟨3434645473001836124141809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4579527297335781498855745 3434645473001836124141809)
              ·
                refine ⟨2575984104751377093106357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3434645473001836124141809 2575984104751377093106357)
                ·
                  refine ⟨241498509820441602478721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2575984104751377093106357 241498509820441602478721)
                  ·
                    rfl

theorem cell22_2116425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2, 2, 5].length) (baseStart_2116425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2116425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2116425 prefixEnd_2116425 := by exact prefixLift 2116425
  have htrace : WordTrace (prefixWord ++ tailWord_2116425) baseStart_2116425 baseEnd_2116425 := by
    simpa [prefixWord, tailWord_2116425, baseEnd_2116425] using wordTrace_append hprefix tailTrace_2116425
  have hstable : (prefixWord ++ tailWord_2116425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2116425).length < 2 ^ (prefixWord ++ tailWord_2116425).sum := by decide
  have hdescent : baseEnd_2116425 < baseStart_2116425 := by decide
  rcases family_descends (prefixWord ++ tailWord_2116425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2116453 : List Nat := [1, 3, 1, 3, 1, 1, 3, 1, 8]
def baseStart_2116453 : Nat := 118140960795 + 2116453 * 2 ^ 59
def prefixEnd_2116453 : Nat := 4983230072969 + 3 ^ 40 * 2116453 * 2
def baseEnd_2116453 : Nat := 241501704811180689245359

theorem tailTrace_2116453 : CollatzResearch.WordTrace tailWord_2116453 prefixEnd_2116453 241501704811180689245359 := by
  unfold tailWord_2116453
  simp only [CollatzResearch.WordTrace]
  refine ⟨77193382601459717240098013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51462255067639811493398675 77193382601459717240098013)
  ·
    refine ⟨28947518475547393965036755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77193382601459717240098013 28947518475547393965036755)
    ·
      refine ⟨43421277713321090947555133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28947518475547393965036755 43421277713321090947555133)
      ·
        refine ⟨16282979142495409105333175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43421277713321090947555133 16282979142495409105333175)
        ·
          refine ⟨24424468713743113657999763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16282979142495409105333175 24424468713743113657999763)
          ·
            refine ⟨36636703070614670486999645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24424468713743113657999763 36636703070614670486999645)
            ·
              refine ⟨13738763651480501432624867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36636703070614670486999645 13738763651480501432624867)
              ·
                refine ⟨20608145477220752148937301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13738763651480501432624867 20608145477220752148937301)
                ·
                  refine ⟨241501704811180689245359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20608145477220752148937301 241501704811180689245359)
                  ·
                    rfl

theorem cell22_2116453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 1, 8].length) (baseStart_2116453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2116453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2116453 prefixEnd_2116453 := by exact prefixLift 2116453
  have htrace : WordTrace (prefixWord ++ tailWord_2116453) baseStart_2116453 baseEnd_2116453 := by
    simpa [prefixWord, tailWord_2116453, baseEnd_2116453] using wordTrace_append hprefix tailTrace_2116453
  have hstable : (prefixWord ++ tailWord_2116453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2116453).length < 2 ^ (prefixWord ++ tailWord_2116453).sum := by decide
  have hdescent : baseEnd_2116453 < baseStart_2116453 := by decide
  rcases family_descends (prefixWord ++ tailWord_2116453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2116455 : List Nat := [1, 1, 5, 1, 2, 2, 2, 1, 3, 4]
def baseStart_2116455 : Nat := 118140960795 + 2116455 * 2 ^ 59
def prefixEnd_2116455 : Nat := 4983230072969 + 3 ^ 40 * 2116455 * 2
def baseEnd_2116455 : Nat := 724505799074414729186071

theorem tailTrace_2116455 : CollatzResearch.WordTrace tailWord_2116455 prefixEnd_2116455 724505799074414729186071 := by
  unfold tailWord_2116455
  simp only [CollatzResearch.WordTrace]
  refine ⟨77193455547452471581670819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51462303698301647721113879 77193455547452471581670819)
  ·
    refine ⟨115790183321178707372506229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77193455547452471581670819 115790183321178707372506229)
    ·
      refine ⟨10855329686360503816172459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 115790183321178707372506229 10855329686360503816172459)
      ·
        refine ⟨16282994529540755724258689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10855329686360503816172459 16282994529540755724258689)
        ·
          refine ⟨12212245897155566793194017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16282994529540755724258689 12212245897155566793194017)
          ·
            refine ⟨9159184422866675094895513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12212245897155566793194017 9159184422866675094895513)
            ·
              refine ⟨6869388317150006321171635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9159184422866675094895513 6869388317150006321171635)
              ·
                refine ⟨10304082475725009481757453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6869388317150006321171635 10304082475725009481757453)
                ·
                  refine ⟨3864030928396878555659045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10304082475725009481757453 3864030928396878555659045)
                  ·
                    refine ⟨724505799074414729186071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3864030928396878555659045 724505799074414729186071)
                    ·
                      rfl

theorem cell22_2116455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 1, 3, 4].length) (baseStart_2116455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2116455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2116455 prefixEnd_2116455 := by exact prefixLift 2116455
  have htrace : WordTrace (prefixWord ++ tailWord_2116455) baseStart_2116455 baseEnd_2116455 := by
    simpa [prefixWord, tailWord_2116455, baseEnd_2116455] using wordTrace_append hprefix tailTrace_2116455
  have hstable : (prefixWord ++ tailWord_2116455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2116455).length < 2 ^ (prefixWord ++ tailWord_2116455).sum := by decide
  have hdescent : baseEnd_2116455 < baseStart_2116455 := by decide
  rcases family_descends (prefixWord ++ tailWord_2116455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2116487 : List Nat := [1, 1, 4, 2, 3, 1, 2, 4, 4]
def baseStart_2116487 : Nat := 118140960795 + 2116487 * 2 ^ 59
def prefixEnd_2116487 : Nat := 4983230072969 + 3 ^ 40 * 2116487 * 2
def baseEnd_2116487 : Nat := 241505584442792437461991

theorem tailTrace_2116487 : CollatzResearch.WordTrace tailWord_2116487 prefixEnd_2116487 241505584442792437461991 := by
  unfold tailWord_2116487
  simp only [CollatzResearch.WordTrace]
  refine ⟨77194622683336541046835715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51463081788891027364557143 77194622683336541046835715)
  ·
    refine ⟨115791934025004811570253573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77194622683336541046835715 115791934025004811570253573)
    ·
      refine ⟨21710987629688402169422545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 115791934025004811570253573 21710987629688402169422545)
      ·
        refine ⟨16283240722266301627066909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21710987629688402169422545 16283240722266301627066909)
        ·
          refine ⟨6106215270849863110150091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16283240722266301627066909 6106215270849863110150091)
          ·
            refine ⟨9159322906274794665225137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6106215270849863110150091 9159322906274794665225137)
            ·
              refine ⟨6869492179706095998918853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9159322906274794665225137 6869492179706095998918853)
              ·
                refine ⟨1288029783694892999797285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6869492179706095998918853 1288029783694892999797285)
                ·
                  refine ⟨241505584442792437461991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1288029783694892999797285 241505584442792437461991)
                  ·
                    rfl

theorem cell22_2116487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 4, 4].length) (baseStart_2116487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2116487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2116487 prefixEnd_2116487 := by exact prefixLift 2116487
  have htrace : WordTrace (prefixWord ++ tailWord_2116487) baseStart_2116487 baseEnd_2116487 := by
    simpa [prefixWord, tailWord_2116487, baseEnd_2116487] using wordTrace_append hprefix tailTrace_2116487
  have hstable : (prefixWord ++ tailWord_2116487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2116487).length < 2 ^ (prefixWord ++ tailWord_2116487).sum := by decide
  have hdescent : baseEnd_2116487 < baseStart_2116487 := by decide
  rcases family_descends (prefixWord ++ tailWord_2116487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2116500 : List Nat := [2, 4, 2, 1, 1, 1, 1, 1, 3, 6]
def baseStart_2116500 : Nat := 118140960795 + 2116500 * 2 ^ 59
def prefixEnd_2116500 : Nat := 4983230072969 + 3 ^ 40 * 2116500 * 2
def baseEnd_2116500 : Nat := 724521203494049611810933

theorem tailTrace_2116500 : CollatzResearch.WordTrace tailWord_2116500 prefixEnd_2116500 724521203494049611810933 := by
  unfold tailWord_2116500
  simp only [CollatzResearch.WordTrace]
  refine ⟨38597548416144722133529477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51463397888192962844705969 38597548416144722133529477)
  ·
    refine ⟨7237040328027135400036777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38597548416144722133529477 7237040328027135400036777)
    ·
      refine ⟨5427780246020351550027583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7237040328027135400036777 5427780246020351550027583)
      ·
        refine ⟨8141670369030527325041375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5427780246020351550027583 8141670369030527325041375)
        ·
          refine ⟨12212505553545790987562063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8141670369030527325041375 12212505553545790987562063)
          ·
            refine ⟨18318758330318686481343095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12212505553545790987562063 18318758330318686481343095)
            ·
              refine ⟨27478137495478029722014643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18318758330318686481343095 27478137495478029722014643)
              ·
                refine ⟨41217206243217044583021965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27478137495478029722014643 41217206243217044583021965)
                ·
                  refine ⟨15456452341206391718633237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41217206243217044583021965 15456452341206391718633237)
                  ·
                    refine ⟨724521203494049611810933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15456452341206391718633237 724521203494049611810933)
                    ·
                      rfl

theorem cell22_2116500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_2116500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2116500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2116500 prefixEnd_2116500 := by exact prefixLift 2116500
  have htrace : WordTrace (prefixWord ++ tailWord_2116500) baseStart_2116500 baseEnd_2116500 := by
    simpa [prefixWord, tailWord_2116500, baseEnd_2116500] using wordTrace_append hprefix tailTrace_2116500
  have hstable : (prefixWord ++ tailWord_2116500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2116500).length < 2 ^ (prefixWord ++ tailWord_2116500).sum := by decide
  have hdescent : baseEnd_2116500 < baseStart_2116500 := by decide
  rcases family_descends (prefixWord ++ tailWord_2116500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2116515 : List Nat := [1, 1, 1, 4, 1, 2, 6, 6]
def baseStart_2116515 : Nat := 118140960795 + 2116515 * 2 ^ 59
def prefixEnd_2116515 : Nat := 4983230072969 + 3 ^ 40 * 2116515 * 2
def baseEnd_2116515 : Nat := 80502926477843841409543

theorem tailTrace_2116515 : CollatzResearch.WordTrace tailWord_2116515 prefixEnd_2116515 80502926477843841409543 := by
  unfold tailWord_2116515
  simp only [CollatzResearch.WordTrace]
  refine ⟨77195643927235101828854999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51463762618156734552569999 77195643927235101828854999)
  ·
    refine ⟨115793465890852652743282499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77195643927235101828854999 115793465890852652743282499)
    ·
      refine ⟨173690198836278979114923749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115793465890852652743282499 173690198836278979114923749)
      ·
        refine ⟨32566912281802308584048203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 173690198836278979114923749 32566912281802308584048203)
        ·
          refine ⟨48850368422703462876072305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32566912281802308584048203 48850368422703462876072305)
          ·
            refine ⟨36637776317027597157054229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48850368422703462876072305 36637776317027597157054229)
            ·
              refine ⟨1717395764860668616736917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 36637776317027597157054229 1717395764860668616736917)
              ·
                refine ⟨80502926477843841409543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1717395764860668616736917 80502926477843841409543)
                ·
                  rfl

theorem cell22_2116515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 6, 6].length) (baseStart_2116515 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2116515 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2116515 prefixEnd_2116515 := by exact prefixLift 2116515
  have htrace : WordTrace (prefixWord ++ tailWord_2116515) baseStart_2116515 baseEnd_2116515 := by
    simpa [prefixWord, tailWord_2116515, baseEnd_2116515] using wordTrace_append hprefix tailTrace_2116515
  have hstable : (prefixWord ++ tailWord_2116515).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2116515).length < 2 ^ (prefixWord ++ tailWord_2116515).sum := by decide
  have hdescent : baseEnd_2116515 < baseStart_2116515 := by decide
  rcases family_descends (prefixWord ++ tailWord_2116515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2116532 : List Nat := [2, 5, 2, 1, 1, 1, 10]
def baseStart_2116532 : Nat := 118140960795 + 2116532 * 2 ^ 59
def prefixEnd_2116532 : Nat := 4983230072969 + 3 ^ 40 * 2116532 * 2
def baseEnd_2116532 : Nat := 26834524361037488704105

theorem tailTrace_2116532 : CollatzResearch.WordTrace tailWord_2116532 prefixEnd_2116532 26834524361037488704105 := by
  unfold tailWord_2116532
  simp only [CollatzResearch.WordTrace]
  refine ⟨38598131984086756866111925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51464175978782342488149233 38598131984086756866111925)
  ·
    refine ⟨3618574873508133456197993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38598131984086756866111925 3618574873508133456197993)
    ·
      refine ⟨2713931155131100092148495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3618574873508133456197993 2713931155131100092148495)
      ·
        refine ⟨4070896732696650138222743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2713931155131100092148495 4070896732696650138222743)
        ·
          refine ⟨6106345099044975207334115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4070896732696650138222743 6106345099044975207334115)
          ·
            refine ⟨9159517648567462811001173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6106345099044975207334115 9159517648567462811001173)
            ·
              refine ⟨26834524361037488704105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9159517648567462811001173 26834524361037488704105)
              ·
                rfl

theorem cell22_2116532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 10].length) (baseStart_2116532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2116532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2116532 prefixEnd_2116532 := by exact prefixLift 2116532
  have htrace : WordTrace (prefixWord ++ tailWord_2116532) baseStart_2116532 baseEnd_2116532 := by
    simpa [prefixWord, tailWord_2116532, baseEnd_2116532] using wordTrace_append hprefix tailTrace_2116532
  have hstable : (prefixWord ++ tailWord_2116532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2116532).length < 2 ^ (prefixWord ++ tailWord_2116532).sum := by decide
  have hdescent : baseEnd_2116532 < baseStart_2116532 := by decide
  rcases family_descends (prefixWord ++ tailWord_2116532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2116598 : List Nat := [5, 1, 1, 1, 3, 1, 4, 2, 1, 3]
def baseStart_2116598 : Nat := 118140960795 + 2116598 * 2 ^ 59
def prefixEnd_2116598 : Nat := 4983230072969 + 3 ^ 40 * 2116598 * 2
def baseEnd_2116598 : Nat := 724554750896810022860633

theorem tailTrace_2116598 : CollatzResearch.WordTrace tailWord_2116598 prefixEnd_2116598 724554750896810022860633 := by
  unfold tailWord_2116598
  simp only [CollatzResearch.WordTrace]
  refine ⟨4824916949120900437757903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 51465780790622938002750965 4824916949120900437757903)
  ·
    refine ⟨7237375423681350656636855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4824916949120900437757903 7237375423681350656636855)
    ·
      refine ⟨10856063135522025984955283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7237375423681350656636855 10856063135522025984955283)
      ·
        refine ⟨16284094703283038977432925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10856063135522025984955283 16284094703283038977432925)
        ·
          refine ⟨6106535513731139616537347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16284094703283038977432925 6106535513731139616537347)
          ·
            refine ⟨9159803270596709424806021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6106535513731139616537347 9159803270596709424806021)
            ·
              refine ⟨1717463113236883017151129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9159803270596709424806021 1717463113236883017151129)
              ·
                refine ⟨1288097334927662262863347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1717463113236883017151129 1288097334927662262863347)
                ·
                  refine ⟨1932146002391493394295021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1288097334927662262863347 1932146002391493394295021)
                  ·
                    refine ⟨724554750896810022860633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1932146002391493394295021 724554750896810022860633)
                    ·
                      rfl

theorem cell22_2116598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 4, 2, 1, 3].length) (baseStart_2116598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2116598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2116598 prefixEnd_2116598 := by exact prefixLift 2116598
  have htrace : WordTrace (prefixWord ++ tailWord_2116598) baseStart_2116598 baseEnd_2116598 := by
    simpa [prefixWord, tailWord_2116598, baseEnd_2116598] using wordTrace_append hprefix tailTrace_2116598
  have hstable : (prefixWord ++ tailWord_2116598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2116598).length < 2 ^ (prefixWord ++ tailWord_2116598).sum := by decide
  have hdescent : baseEnd_2116598 < baseStart_2116598 := by decide
  rcases family_descends (prefixWord ++ tailWord_2116598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2116605 : List Nat := [1, 4, 1, 1, 1, 2, 1, 5, 6]
def baseStart_2116605 : Nat := 118140960795 + 2116605 * 2 ^ 59
def prefixEnd_2116605 : Nat := 4983230072969 + 3 ^ 40 * 2116605 * 2
def baseEnd_2116605 : Nat := 241519049046621445978537

theorem tailTrace_2116605 : CollatzResearch.WordTrace tailWord_2116605 prefixEnd_2116605 241519049046621445978537 := by
  unfold tailWord_2116605
  simp only [CollatzResearch.WordTrace]
  refine ⟨77198926496909047199631269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51465950997939364799754179 77198926496909047199631269)
  ·
    refine ⟨14474798718170446349930863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77198926496909047199631269 14474798718170446349930863)
    ·
      refine ⟨21712198077255669524896295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14474798718170446349930863 21712198077255669524896295)
      ·
        refine ⟨32568297115883504287344443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21712198077255669524896295 32568297115883504287344443)
        ·
          refine ⟨48852445673825256431016665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32568297115883504287344443 48852445673825256431016665)
          ·
            refine ⟨36639334255368942323262499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48852445673825256431016665 36639334255368942323262499)
            ·
              refine ⟨54959001383053413484893749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36639334255368942323262499 54959001383053413484893749)
              ·
                refine ⟨5152406379661257514208789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54959001383053413484893749 5152406379661257514208789)
                ·
                  refine ⟨241519049046621445978537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5152406379661257514208789 241519049046621445978537)
                  ·
                    rfl

theorem cell22_2116605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 5, 6].length) (baseStart_2116605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2116605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2116605 prefixEnd_2116605 := by exact prefixLift 2116605
  have htrace : WordTrace (prefixWord ++ tailWord_2116605) baseStart_2116605 baseEnd_2116605 := by
    simpa [prefixWord, tailWord_2116605, baseEnd_2116605] using wordTrace_append hprefix tailTrace_2116605
  have hstable : (prefixWord ++ tailWord_2116605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2116605).length < 2 ^ (prefixWord ++ tailWord_2116605).sum := by decide
  have hdescent : baseEnd_2116605 < baseStart_2116605 := by decide
  rcases family_descends (prefixWord ++ tailWord_2116605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2116622 : List Nat := [4, 1, 1, 2, 2, 3, 1, 2, 6]
def baseStart_2116622 : Nat := 118140960795 + 2116622 * 2 ^ 59
def prefixEnd_2116622 : Nat := 4983230072969 + 3 ^ 40 * 2116622 * 2
def baseEnd_2116622 : Nat := 241520988862427320086853

theorem tailTrace_2116622 : CollatzResearch.WordTrace tailWord_2116622 prefixEnd_2116622 241520988862427320086853 := by
  unfold tailWord_2116622
  simp only [CollatzResearch.WordTrace]
  refine ⟨9649943317230932387875015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51466364358564972735333413 9649943317230932387875015)
  ·
    refine ⟨14474914975846398581812523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9649943317230932387875015 14474914975846398581812523)
    ·
      refine ⟨21712372463769597872718785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14474914975846398581812523 21712372463769597872718785)
      ·
        refine ⟨16284279347827198404539089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21712372463769597872718785 16284279347827198404539089)
        ·
          refine ⟨12213209510870398803404317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16284279347827198404539089 12213209510870398803404317)
          ·
            refine ⟨4579953566576399551276619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12213209510870398803404317 4579953566576399551276619)
            ·
              refine ⟨6869930349864599326914929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4579953566576399551276619 6869930349864599326914929)
              ·
                refine ⟨5152447762398449495186197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6869930349864599326914929 5152447762398449495186197)
                ·
                  refine ⟨241520988862427320086853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5152447762398449495186197 241520988862427320086853)
                  ·
                    rfl

theorem cell22_2116622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 2, 6].length) (baseStart_2116622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2116622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2116622 prefixEnd_2116622 := by exact prefixLift 2116622
  have htrace : WordTrace (prefixWord ++ tailWord_2116622) baseStart_2116622 baseEnd_2116622 := by
    simpa [prefixWord, tailWord_2116622, baseEnd_2116622] using wordTrace_append hprefix tailTrace_2116622
  have hstable : (prefixWord ++ tailWord_2116622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2116622).length < 2 ^ (prefixWord ++ tailWord_2116622).sum := by decide
  have hdescent : baseEnd_2116622 < baseStart_2116622 := by decide
  rcases family_descends (prefixWord ++ tailWord_2116622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2116639 : List Nat := [1, 1, 2, 4, 1, 4, 2, 3, 4]
def baseStart_2116639 : Nat := 118140960795 + 2116639 * 2 ^ 59
def prefixEnd_2116639 : Nat := 4983230072969 + 3 ^ 40 * 2116639 * 2
def baseEnd_2116639 : Nat := 241522928678233194195169

theorem tailTrace_2116639 : CollatzResearch.WordTrace tailWord_2116639 prefixEnd_2116639 241522928678233194195169 := by
  unfold tailWord_2116639
  simp only [CollatzResearch.WordTrace]
  refine ⟨77200166578785871006368971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51466777719190580670912647 77200166578785871006368971)
  ·
    refine ⟨115800249868178806509553457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77200166578785871006368971 115800249868178806509553457)
    ·
      refine ⟨86850187401134104882165093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115800249868178806509553457 86850187401134104882165093)
      ·
        refine ⟨16284410137712644665405955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 86850187401134104882165093 16284410137712644665405955)
        ·
          refine ⟨24426615206568966998108933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16284410137712644665405955 24426615206568966998108933)
          ·
            refine ⟨4579990351231681312145425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24426615206568966998108933 4579990351231681312145425)
            ·
              refine ⟨3434992763423760984109069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4579990351231681312145425 3434992763423760984109069)
              ·
                refine ⟨1288122286283910369040901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3434992763423760984109069 1288122286283910369040901)
                ·
                  refine ⟨241522928678233194195169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1288122286283910369040901 241522928678233194195169)
                  ·
                    rfl

theorem cell22_2116639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2, 3, 4].length) (baseStart_2116639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2116639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2116639 prefixEnd_2116639 := by exact prefixLift 2116639
  have htrace : WordTrace (prefixWord ++ tailWord_2116639) baseStart_2116639 baseEnd_2116639 := by
    simpa [prefixWord, tailWord_2116639, baseEnd_2116639] using wordTrace_append hprefix tailTrace_2116639
  have hstable : (prefixWord ++ tailWord_2116639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2116639).length < 2 ^ (prefixWord ++ tailWord_2116639).sum := by decide
  have hdescent : baseEnd_2116639 < baseStart_2116639 := by decide
  rcases family_descends (prefixWord ++ tailWord_2116639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2116641 : List Nat := [1, 2, 3, 2, 3, 3, 2, 1, 1, 4]
def baseStart_2116641 : Nat := 118140960795 + 2116641 * 2 ^ 59
def prefixEnd_2116641 : Nat := 4983230072969 + 3 ^ 40 * 2116641 * 2
def baseEnd_2116641 : Nat := 724569470675572244035501

theorem tailTrace_2116641 : CollatzResearch.WordTrace tailWord_2116641 prefixEnd_2116641 724569470675572244035501 := by
  unfold tailWord_2116641
  simp only [CollatzResearch.WordTrace]
  refine ⟨77200239524778625347941777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51466826349852416898627851 77200239524778625347941777)
  ·
    refine ⟨57900179643583969010956333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77200239524778625347941777 57900179643583969010956333)
    ·
      refine ⟨21712567366343988379108625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57900179643583969010956333 21712567366343988379108625)
      ·
        refine ⟨16284425524757991284331469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21712567366343988379108625 16284425524757991284331469)
        ·
          refine ⟨6106659571784246731624301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16284425524757991284331469 6106659571784246731624301)
          ·
            refine ⟨2289997339419092524359113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6106659571784246731624301 2289997339419092524359113)
            ·
              refine ⟨1717498004564319393269335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2289997339419092524359113 1717498004564319393269335)
              ·
                refine ⟨2576247006846479089904003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1717498004564319393269335 2576247006846479089904003)
                ·
                  refine ⟨3864370510269718634856005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2576247006846479089904003 3864370510269718634856005)
                  ·
                    refine ⟨724569470675572244035501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3864370510269718634856005 724569470675572244035501)
                    ·
                      rfl

theorem cell22_2116641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 2, 1, 1, 4].length) (baseStart_2116641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2116641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2116641 prefixEnd_2116641 := by exact prefixLift 2116641
  have htrace : WordTrace (prefixWord ++ tailWord_2116641) baseStart_2116641 baseEnd_2116641 := by
    simpa [prefixWord, tailWord_2116641, baseEnd_2116641] using wordTrace_append hprefix tailTrace_2116641
  have hstable : (prefixWord ++ tailWord_2116641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2116641).length < 2 ^ (prefixWord ++ tailWord_2116641).sum := by decide
  have hdescent : baseEnd_2116641 < baseStart_2116641 := by decide
  rcases family_descends (prefixWord ++ tailWord_2116641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2116654 : List Nat := [4, 1, 3, 1, 1, 1, 3, 1, 4, 3]
def baseStart_2116654 : Nat := 118140960795 + 2116654 * 2 ^ 59
def prefixEnd_2116654 : Nat := 4983230072969 + 3 ^ 40 * 2116654 * 2
def baseEnd_2116654 : Nat := 724573920841244543460461

theorem tailTrace_2116654 : CollatzResearch.WordTrace tailWord_2116654 prefixEnd_2116654 724573920841244543460461 := by
  unfold tailWord_2116654
  simp only [CollatzResearch.WordTrace]
  refine ⟨9650089209216441071020627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51467142449154352378776677 9650089209216441071020627)
  ·
    refine ⟨14475133813824661606530941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9650089209216441071020627 14475133813824661606530941)
    ·
      refine ⟨5428175180184248102449103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14475133813824661606530941 5428175180184248102449103)
      ·
        refine ⟨8142262770276372153673655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5428175180184248102449103 8142262770276372153673655)
        ·
          refine ⟨12213394155414558230510483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8142262770276372153673655 12213394155414558230510483)
          ·
            refine ⟨18320091233121837345765725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12213394155414558230510483 18320091233121837345765725)
            ·
              refine ⟨6870034212420689004662147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18320091233121837345765725 6870034212420689004662147)
              ·
                refine ⟨10305051318631033506993221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6870034212420689004662147 10305051318631033506993221)
                ·
                  refine ⟨1932197122243318782561229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10305051318631033506993221 1932197122243318782561229)
                  ·
                    refine ⟨724573920841244543460461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1932197122243318782561229 724573920841244543460461)
                    ·
                      rfl

theorem cell22_2116654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 1, 4, 3].length) (baseStart_2116654 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2116654 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2116654 prefixEnd_2116654 := by exact prefixLift 2116654
  have htrace : WordTrace (prefixWord ++ tailWord_2116654) baseStart_2116654 baseEnd_2116654 := by
    simpa [prefixWord, tailWord_2116654, baseEnd_2116654] using wordTrace_append hprefix tailTrace_2116654
  have hstable : (prefixWord ++ tailWord_2116654).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2116654).length < 2 ^ (prefixWord ++ tailWord_2116654).sum := by decide
  have hdescent : baseEnd_2116654 < baseStart_2116654 := by decide
  rcases family_descends (prefixWord ++ tailWord_2116654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2116701 : List Nat := [1, 4, 4, 1, 3, 1, 8]
def baseStart_2116701 : Nat := 118140960795 + 2116701 * 2 ^ 59
def prefixEnd_2116701 : Nat := 4983230072969 + 3 ^ 40 * 2116701 * 2
def baseEnd_2116701 : Nat := 26836667033398225464271

theorem tailTrace_2116701 : CollatzResearch.WordTrace tailWord_2116701 prefixEnd_2116701 26836667033398225464271 := by
  unfold tailWord_2116701
  simp only [CollatzResearch.WordTrace]
  refine ⟨77202427904561255595125957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51468285269707503730083971 77202427904561255595125957)
  ·
    refine ⟨14475455232105235424086117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77202427904561255595125957 14475455232105235424086117)
    ·
      refine ⟨2714147856019731642016147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14475455232105235424086117 2714147856019731642016147)
      ·
        refine ⟨4071221784029597463024221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2714147856019731642016147 4071221784029597463024221)
        ·
          refine ⟨1526708169011099048634083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4071221784029597463024221 1526708169011099048634083)
          ·
            refine ⟨2290062253516648572951125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1526708169011099048634083 2290062253516648572951125)
            ·
              refine ⟨26836667033398225464271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2290062253516648572951125 26836667033398225464271)
              ·
                rfl

theorem cell22_2116701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 8].length) (baseStart_2116701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2116701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2116701 prefixEnd_2116701 := by exact prefixLift 2116701
  have htrace : WordTrace (prefixWord ++ tailWord_2116701) baseStart_2116701 baseEnd_2116701 := by
    simpa [prefixWord, tailWord_2116701, baseEnd_2116701] using wordTrace_append hprefix tailTrace_2116701
  have hstable : (prefixWord ++ tailWord_2116701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2116701).length < 2 ^ (prefixWord ++ tailWord_2116701).sum := by decide
  have hdescent : baseEnd_2116701 < baseStart_2116701 := by decide
  rcases family_descends (prefixWord ++ tailWord_2116701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2116729 : List Nat := [1, 2, 1, 3, 5, 1, 1, 3, 5]
def baseStart_2116729 : Nat := 118140960795 + 2116729 * 2 ^ 59
def prefixEnd_2116729 : Nat := 4983230072969 + 3 ^ 40 * 2116729 * 2
def baseEnd_2116729 : Nat := 241533198291323115945077

theorem tailTrace_2116729 : CollatzResearch.WordTrace tailWord_2116729 prefixEnd_2116729 241533198291323115945077 := by
  unfold tailWord_2116729
  simp only [CollatzResearch.WordTrace]
  refine ⟨77203449148459816377145241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51468966098973210918096827 77203449148459816377145241)
  ·
    refine ⟨57902586861344862282858931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77203449148459816377145241 57902586861344862282858931)
    ·
      refine ⟨86853880292017293424288397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57902586861344862282858931 86853880292017293424288397)
      ·
        refine ⟨32570205109506485034108149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86853880292017293424288397 32570205109506485034108149)
        ·
          refine ⟨3053456729016232971947639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32570205109506485034108149 3053456729016232971947639)
          ·
            refine ⟨4580185093524349457921459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3053456729016232971947639 4580185093524349457921459)
            ·
              refine ⟨6870277640286524186882189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4580185093524349457921459 6870277640286524186882189)
              ·
                refine ⟨2576354115107446570080821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6870277640286524186882189 2576354115107446570080821)
                ·
                  refine ⟨241533198291323115945077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2576354115107446570080821 241533198291323115945077)
                  ·
                    rfl

theorem cell22_2116729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 3, 5].length) (baseStart_2116729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2116729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2116729 prefixEnd_2116729 := by exact prefixLift 2116729
  have htrace : WordTrace (prefixWord ++ tailWord_2116729) baseStart_2116729 baseEnd_2116729 := by
    simpa [prefixWord, tailWord_2116729, baseEnd_2116729] using wordTrace_append hprefix tailTrace_2116729
  have hstable : (prefixWord ++ tailWord_2116729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2116729).length < 2 ^ (prefixWord ++ tailWord_2116729).sum := by decide
  have hdescent : baseEnd_2116729 < baseStart_2116729 := by decide
  rcases family_descends (prefixWord ++ tailWord_2116729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2116767 : List Nat := [1, 1, 2, 6, 3, 1, 2, 2, 1, 3]
def baseStart_2116767 : Nat := 118140960795 + 2116767 * 2 ^ 59
def prefixEnd_2116767 : Nat := 4983230072969 + 3 ^ 40 * 2116767 * 2
def baseEnd_2116767 : Nat := 724612603050549915385115

theorem tailTrace_2116767 : CollatzResearch.WordTrace tailWord_2116767 prefixEnd_2116767 724612603050549915385115 := by
  unfold tailWord_2116767
  simp only [CollatzResearch.WordTrace]
  refine ⟨77204835122322148867028555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51469890081548099244685703 77204835122322148867028555)
  ·
    refine ⟨115807252683483223300542833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77204835122322148867028555 115807252683483223300542833)
    ·
      refine ⟨86855439512612417475407125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115807252683483223300542833 86855439512612417475407125)
      ·
        refine ⟨4071348727153707069159709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 86855439512612417475407125 4071348727153707069159709)
        ·
          refine ⟨1526755772682640150934891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4071348727153707069159709 1526755772682640150934891)
          ·
            refine ⟨2290133659023960226402337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1526755772682640150934891 2290133659023960226402337)
            ·
              refine ⟨1717600244267970169801753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2290133659023960226402337 1717600244267970169801753)
              ·
                refine ⟨1288200183200977627351315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1717600244267970169801753 1288200183200977627351315)
                ·
                  refine ⟨1932300274801466441026973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1288200183200977627351315 1932300274801466441026973)
                  ·
                    refine ⟨724612603050549915385115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1932300274801466441026973 724612603050549915385115)
                    ·
                      rfl

theorem cell22_2116767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 2, 2, 1, 3].length) (baseStart_2116767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2116767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2116767 prefixEnd_2116767 := by exact prefixLift 2116767
  have htrace : WordTrace (prefixWord ++ tailWord_2116767) baseStart_2116767 baseEnd_2116767 := by
    simpa [prefixWord, tailWord_2116767, baseEnd_2116767] using wordTrace_append hprefix tailTrace_2116767
  have hstable : (prefixWord ++ tailWord_2116767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2116767).length < 2 ^ (prefixWord ++ tailWord_2116767).sum := by decide
  have hdescent : baseEnd_2116767 < baseStart_2116767 := by decide
  rcases family_descends (prefixWord ++ tailWord_2116767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2116787 : List Nat := [1, 1, 1, 2, 3, 2, 2, 2, 4, 4]
def baseStart_2116787 : Nat := 118140960795 + 2116787 * 2 ^ 59
def prefixEnd_2116787 : Nat := 4983230072969 + 3 ^ 40 * 2116787 * 2
def baseEnd_2116787 : Nat := 724619449459276529885053

theorem tailTrace_2116787 : CollatzResearch.WordTrace tailWord_2116787 prefixEnd_2116787 724619449459276529885053 := by
  unfold tailWord_2116787
  simp only [CollatzResearch.WordTrace]
  refine ⟨77205564582249692282756615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51470376388166461521837743 77205564582249692282756615)
  ·
    refine ⟨115808346873374538424134923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77205564582249692282756615 115808346873374538424134923)
    ·
      refine ⟨173712520310061807636202385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115808346873374538424134923 173712520310061807636202385)
      ·
        refine ⟨130284390232546355727151789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 173712520310061807636202385 130284390232546355727151789)
        ·
          refine ⟨48856646337204883397681921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 130284390232546355727151789 48856646337204883397681921)
          ·
            refine ⟨36642484752903662548261441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48856646337204883397681921 36642484752903662548261441)
            ·
              refine ⟨27481863564677746911196081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36642484752903662548261441 27481863564677746911196081)
              ·
                refine ⟨20611397673508310183397061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27481863564677746911196081 20611397673508310183397061)
                ·
                  refine ⟨3864637063782808159386949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20611397673508310183397061 3864637063782808159386949)
                  ·
                    refine ⟨724619449459276529885053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3864637063782808159386949 724619449459276529885053)
                    ·
                      rfl

theorem cell22_2116787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 2, 4, 4].length) (baseStart_2116787 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2116787 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2116787 prefixEnd_2116787 := by exact prefixLift 2116787
  have htrace : WordTrace (prefixWord ++ tailWord_2116787) baseStart_2116787 baseEnd_2116787 := by
    simpa [prefixWord, tailWord_2116787, baseEnd_2116787] using wordTrace_append hprefix tailTrace_2116787
  have hstable : (prefixWord ++ tailWord_2116787).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2116787).length < 2 ^ (prefixWord ++ tailWord_2116787).sum := by decide
  have hdescent : baseEnd_2116787 < baseStart_2116787 := by decide
  rcases family_descends (prefixWord ++ tailWord_2116787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2116924 : List Nat := [2, 2, 2, 2, 1, 3, 1, 1, 3, 5]
def baseStart_2116924 : Nat := 118140960795 + 2116924 * 2 ^ 59
def prefixEnd_2116924 : Nat := 4983230072969 + 3 ^ 40 * 2116924 * 2
def baseEnd_2116924 : Nat := 724666347359053839209633

theorem tailTrace_2116924 : CollatzResearch.WordTrace tailWord_2116924 prefixEnd_2116924 724666347359053839209633 := by
  unfold tailWord_2116924
  simp only [CollatzResearch.WordTrace]
  refine ⟨38605280691376682340246913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51473707588502243120329217 38605280691376682340246913)
  ·
    refine ⟨28953960518532511755185185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38605280691376682340246913 28953960518532511755185185)
    ·
      refine ⟨21715470388899383816388889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28953960518532511755185185 21715470388899383816388889)
      ·
        refine ⟨16286602791674537862291667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21715470388899383816388889 16286602791674537862291667)
        ·
          refine ⟨24429904187511806793437501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16286602791674537862291667 24429904187511806793437501)
          ·
            refine ⟨9161214070316927547539063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24429904187511806793437501 9161214070316927547539063)
            ·
              refine ⟨13741821105475391321308595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9161214070316927547539063 13741821105475391321308595)
              ·
                refine ⟨20612731658213086981962893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13741821105475391321308595 20612731658213086981962893)
                ·
                  refine ⟨7729774371829907618236085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20612731658213086981962893 7729774371829907618236085)
                  ·
                    refine ⟨724666347359053839209633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7729774371829907618236085 724666347359053839209633)
                    ·
                      rfl

theorem cell22_2116924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 1, 3, 5].length) (baseStart_2116924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2116924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2116924 prefixEnd_2116924 := by exact prefixLift 2116924
  have htrace : WordTrace (prefixWord ++ tailWord_2116924) baseStart_2116924 baseEnd_2116924 := by
    simpa [prefixWord, tailWord_2116924, baseEnd_2116924] using wordTrace_append hprefix tailTrace_2116924
  have hstable : (prefixWord ++ tailWord_2116924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2116924).length < 2 ^ (prefixWord ++ tailWord_2116924).sum := by decide
  have hdescent : baseEnd_2116924 < baseStart_2116924 := by decide
  rcases family_descends (prefixWord ++ tailWord_2116924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2116954 : List Nat := [3, 1, 1, 2, 1, 2, 5, 7]
def baseStart_2116954 : Nat := 118140960795 + 2116954 * 2 ^ 59
def prefixEnd_2116954 : Nat := 4983230072969 + 3 ^ 40 * 2116954 * 2
def baseEnd_2116954 : Nat := 80519624108015973439949

theorem tailTrace_2116954 : CollatzResearch.WordTrace tailWord_2116954 prefixEnd_2116954 80519624108015973439949 := by
  unfold tailWord_2116954
  simp only [CollatzResearch.WordTrace]
  refine ⟨19302913893161169951021479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51474437048429786536057277 19302913893161169951021479)
  ·
    refine ⟨28954370839741754926532219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19302913893161169951021479 28954370839741754926532219)
    ·
      refine ⟨43431556259612632389798329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28954370839741754926532219 43431556259612632389798329)
      ·
        refine ⟨32573667194709474292348747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43431556259612632389798329 32573667194709474292348747)
        ·
          refine ⟨48860500792064211438523121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32573667194709474292348747 48860500792064211438523121)
          ·
            refine ⟨36645375594048158578892341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48860500792064211438523121 36645375594048158578892341)
            ·
              refine ⟨3435503961942014866771157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36645375594048158578892341 3435503961942014866771157)
              ·
                refine ⟨80519624108015973439949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3435503961942014866771157 80519624108015973439949)
                ·
                  rfl

theorem cell22_2116954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5, 7].length) (baseStart_2116954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2116954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2116954 prefixEnd_2116954 := by exact prefixLift 2116954
  have htrace : WordTrace (prefixWord ++ tailWord_2116954) baseStart_2116954 baseEnd_2116954 := by
    simpa [prefixWord, tailWord_2116954, baseEnd_2116954] using wordTrace_append hprefix tailTrace_2116954
  have hstable : (prefixWord ++ tailWord_2116954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2116954).length < 2 ^ (prefixWord ++ tailWord_2116954).sum := by decide
  have hdescent : baseEnd_2116954 < baseStart_2116954 := by decide
  rcases family_descends (prefixWord ++ tailWord_2116954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2116973 : List Nat := [1, 5, 1, 1, 1, 5, 1, 1, 2, 4]
def baseStart_2116973 : Nat := 118140960795 + 2116973 * 2 ^ 59
def prefixEnd_2116973 : Nat := 4983230072969 + 3 ^ 40 * 2116973 * 2
def baseEnd_2116973 : Nat := 724683121060434044734483

theorem tailTrace_2116973 : CollatzResearch.WordTrace tailWord_2116973 prefixEnd_2116973 724683121060434044734483 := by
  unfold tailWord_2116973
  simp only [CollatzResearch.WordTrace]
  refine ⟨77212348559575846049027573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51474899039717230699351715 77212348559575846049027573)
  ·
    refine ⟨7238657677460235567096335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 77212348559575846049027573 7238657677460235567096335)
    ·
      refine ⟨10857986516190353350644503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7238657677460235567096335 10857986516190353350644503)
      ·
        refine ⟨16286979774285530025966755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10857986516190353350644503 16286979774285530025966755)
        ·
          refine ⟨24430469661428295038950133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16286979774285530025966755 24430469661428295038950133)
          ·
            refine ⟨2290356530758902659901575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24430469661428295038950133 2290356530758902659901575)
            ·
              refine ⟨3435534796138353989852363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2290356530758902659901575 3435534796138353989852363)
              ·
                refine ⟨5153302194207530984778545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3435534796138353989852363 5153302194207530984778545)
                ·
                  refine ⟨3864976645655648238583909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5153302194207530984778545 3864976645655648238583909)
                  ·
                    refine ⟨724683121060434044734483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3864976645655648238583909 724683121060434044734483)
                    ·
                      rfl

theorem cell22_2116973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 1, 1, 2, 4].length) (baseStart_2116973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2116973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2116973 prefixEnd_2116973 := by exact prefixLift 2116973
  have htrace : WordTrace (prefixWord ++ tailWord_2116973) baseStart_2116973 baseEnd_2116973 := by
    simpa [prefixWord, tailWord_2116973, baseEnd_2116973] using wordTrace_append hprefix tailTrace_2116973
  have hstable : (prefixWord ++ tailWord_2116973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2116973).length < 2 ^ (prefixWord ++ tailWord_2116973).sum := by decide
  have hdescent : baseEnd_2116973 < baseStart_2116973 := by decide
  rcases family_descends (prefixWord ++ tailWord_2116973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2117003 : List Nat := [1, 1, 1, 1, 4, 3, 1, 6, 1, 3]
def baseStart_2117003 : Nat := 118140960795 + 2117003 * 2 ^ 59
def prefixEnd_2117003 : Nat := 4983230072969 + 3 ^ 40 * 2117003 * 2
def baseEnd_2117003 : Nat := 724693390673523966484391

theorem tailTrace_2117003 : CollatzResearch.WordTrace tailWord_2117003 prefixEnd_2117003 724693390673523966484391 := by
  unfold tailWord_2117003
  simp only [CollatzResearch.WordTrace]
  refine ⟨77213442749467161172619663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51475628499644774115079775 77213442749467161172619663)
  ·
    refine ⟨115820164124200741758929495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77213442749467161172619663 115820164124200741758929495)
    ·
      refine ⟨173730246186301112638394243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115820164124200741758929495 173730246186301112638394243)
      ·
        refine ⟨260595369279451668957591365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173730246186301112638394243 260595369279451668957591365)
        ·
          refine ⟨48861631739897187929548381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 260595369279451668957591365 48861631739897187929548381)
          ·
            refine ⟨18323111902461445473580643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48861631739897187929548381 18323111902461445473580643)
            ·
              refine ⟨27484667853692168210370965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18323111902461445473580643 27484667853692168210370965)
              ·
                refine ⟨1288343805641820384861139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 27484667853692168210370965 1288343805641820384861139)
                ·
                  refine ⟨1932515708462730577291709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1288343805641820384861139 1932515708462730577291709)
                  ·
                    refine ⟨724693390673523966484391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1932515708462730577291709 724693390673523966484391)
                    ·
                      rfl

theorem cell22_2117003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 6, 1, 3].length) (baseStart_2117003 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2117003 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2117003 prefixEnd_2117003 := by exact prefixLift 2117003
  have htrace : WordTrace (prefixWord ++ tailWord_2117003) baseStart_2117003 baseEnd_2117003 := by
    simpa [prefixWord, tailWord_2117003, baseEnd_2117003] using wordTrace_append hprefix tailTrace_2117003
  have hstable : (prefixWord ++ tailWord_2117003).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2117003).length < 2 ^ (prefixWord ++ tailWord_2117003).sum := by decide
  have hdescent : baseEnd_2117003 < baseStart_2117003 := by decide
  rcases family_descends (prefixWord ++ tailWord_2117003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2117022 : List Nat := [4, 3, 1, 2, 3, 1, 2, 6]
def baseStart_2117022 : Nat := 118140960795 + 2117022 * 2 ^ 59
def prefixEnd_2117022 : Nat := 4983230072969 + 3 ^ 40 * 2117022 * 2
def baseEnd_2117022 : Nat := 80522210529090472251037

theorem tailTrace_2117022 : CollatzResearch.WordTrace tailWord_2117022 prefixEnd_2117022 80522210529090472251037 := by
  unfold tailWord_2117022
  simp only [CollatzResearch.WordTrace]
  refine ⟨9651766967049790927195165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51476090490932218278374213 9651766967049790927195165)
  ·
    refine ⟨3619412612643671597698187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9651766967049790927195165 3619412612643671597698187)
    ·
      refine ⟨5429118918965507396547281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3619412612643671597698187 5429118918965507396547281)
      ·
        refine ⟨4071839189224130547410461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5429118918965507396547281 4071839189224130547410461)
        ·
          refine ⟨1526939695959048955278923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4071839189224130547410461 1526939695959048955278923)
          ·
            refine ⟨2290409543938573432918385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1526939695959048955278923 2290409543938573432918385)
            ·
              refine ⟨1717807157953930074688789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2290409543938573432918385 1717807157953930074688789)
              ·
                refine ⟨80522210529090472251037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1717807157953930074688789 80522210529090472251037)
                ·
                  rfl

theorem cell22_2117022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 2, 6].length) (baseStart_2117022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2117022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2117022 prefixEnd_2117022 := by exact prefixLift 2117022
  have htrace : WordTrace (prefixWord ++ tailWord_2117022) baseStart_2117022 baseEnd_2117022 := by
    simpa [prefixWord, tailWord_2117022, baseEnd_2117022] using wordTrace_append hprefix tailTrace_2117022
  have hstable : (prefixWord ++ tailWord_2117022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2117022).length < 2 ^ (prefixWord ++ tailWord_2117022).sum := by decide
  have hdescent : baseEnd_2117022 < baseStart_2117022 := by decide
  rcases family_descends (prefixWord ++ tailWord_2117022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2117037 : List Nat := [1, 5, 2, 2, 1, 1, 3, 3, 1, 3]
def baseStart_2117037 : Nat := 118140960795 + 2117037 * 2 ^ 59
def prefixEnd_2117037 : Nat := 4983230072969 + 3 ^ 40 * 2117037 * 2
def baseEnd_2117037 : Nat := 724705029568359211134287

theorem tailTrace_2117037 : CollatzResearch.WordTrace tailWord_2117037 prefixEnd_2117037 724705029568359211134287 := by
  unfold tailWord_2117037
  simp only [CollatzResearch.WordTrace]
  refine ⟨77214682831343984979357365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51476455220895989986238243 77214682831343984979357365)
  ·
    refine ⟨7238876515438498591814753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 77214682831343984979357365 7238876515438498591814753)
    ·
      refine ⟨5429157386578873943861065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7238876515438498591814753 5429157386578873943861065)
      ·
        refine ⟨4071868039934155457895799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5429157386578873943861065 4071868039934155457895799)
        ·
          refine ⟨6107802059901233186843699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4071868039934155457895799 6107802059901233186843699)
          ·
            refine ⟨9161703089851849780265549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6107802059901233186843699 9161703089851849780265549)
            ·
              refine ⟨3435638658694443667599581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9161703089851849780265549 3435638658694443667599581)
              ·
                refine ⟨1288364497010416375349843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3435638658694443667599581 1288364497010416375349843)
                ·
                  refine ⟨1932546745515624563024765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1288364497010416375349843 1932546745515624563024765)
                  ·
                    refine ⟨724705029568359211134287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1932546745515624563024765 724705029568359211134287)
                    ·
                      rfl

theorem cell22_2117037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3, 3, 1, 3].length) (baseStart_2117037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2117037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2117037 prefixEnd_2117037 := by exact prefixLift 2117037
  have htrace : WordTrace (prefixWord ++ tailWord_2117037) baseStart_2117037 baseEnd_2117037 := by
    simpa [prefixWord, tailWord_2117037, baseEnd_2117037] using wordTrace_append hprefix tailTrace_2117037
  have hstable : (prefixWord ++ tailWord_2117037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2117037).length < 2 ^ (prefixWord ++ tailWord_2117037).sum := by decide
  have hdescent : baseEnd_2117037 < baseStart_2117037 := by decide
  rcases family_descends (prefixWord ++ tailWord_2117037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2117093 : List Nat := [1, 3, 1, 5, 1, 2, 1, 2, 1, 5]
def baseStart_2117093 : Nat := 118140960795 + 2117093 * 2 ^ 59
def prefixEnd_2117093 : Nat := 4983230072969 + 3 ^ 40 * 2117093 * 2
def baseEnd_2117093 : Nat := 724724199512793731734115

theorem tailTrace_2117093 : CollatzResearch.WordTrace tailWord_2117093 prefixEnd_2117093 724724199512793731734115 := by
  unfold tailWord_2117093
  simp only [CollatzResearch.WordTrace]
  refine ⟨77216725319141106543395933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51477816879427404362263955 77216725319141106543395933)
  ·
    refine ⟨28956271994677914953773475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77216725319141106543395933 28956271994677914953773475)
    ·
      refine ⟨43434407992016872430660213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28956271994677914953773475 43434407992016872430660213)
      ·
        refine ⟨4071975749251581790374395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 43434407992016872430660213 4071975749251581790374395)
        ·
          refine ⟨6107963623877372685561593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4071975749251581790374395 6107963623877372685561593)
          ·
            refine ⟨4580972717908029514171195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6107963623877372685561593 4580972717908029514171195)
            ·
              refine ⟨6871459076862044271256793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4580972717908029514171195 6871459076862044271256793)
              ·
                refine ⟨5153594307646533203442595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6871459076862044271256793 5153594307646533203442595)
                ·
                  refine ⟨7730391461469799805163893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5153594307646533203442595 7730391461469799805163893)
                  ·
                    refine ⟨724724199512793731734115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7730391461469799805163893 724724199512793731734115)
                    ·
                      rfl

theorem cell22_2117093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 2, 1, 5].length) (baseStart_2117093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2117093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2117093 prefixEnd_2117093 := by exact prefixLift 2117093
  have htrace : WordTrace (prefixWord ++ tailWord_2117093) baseStart_2117093 baseEnd_2117093 := by
    simpa [prefixWord, tailWord_2117093, baseEnd_2117093] using wordTrace_append hprefix tailTrace_2117093
  have hstable : (prefixWord ++ tailWord_2117093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2117093).length < 2 ^ (prefixWord ++ tailWord_2117093).sum := by decide
  have hdescent : baseEnd_2117093 < baseStart_2117093 := by decide
  rcases family_descends (prefixWord ++ tailWord_2117093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2117106 : List Nat := [3, 2, 1, 4, 1, 11]
def baseStart_2117106 : Nat := 118140960795 + 2117106 * 2 ^ 59
def prefixEnd_2117106 : Nat := 4983230072969 + 3 ^ 40 * 2117106 * 2
def baseEnd_2117106 : Nat := 8947267279981062113075

theorem tailTrace_2117106 : CollatzResearch.WordTrace tailWord_2117106 prefixEnd_2117106 8947267279981062113075 := by
  unfold tailWord_2117106
  simp only [CollatzResearch.WordTrace]
  refine ⟨19304299867023502440904793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51478132978729339842412781 19304299867023502440904793)
  ·
    refine ⟨14478224900267626830678595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19304299867023502440904793 14478224900267626830678595)
    ·
      refine ⟨21717337350401440246017893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14478224900267626830678595 21717337350401440246017893)
      ·
        refine ⟨4072000753200270046128355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21717337350401440246017893 4072000753200270046128355)
        ·
          refine ⟨6108001129800405069192533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4072000753200270046128355 6108001129800405069192533)
          ·
            refine ⟨8947267279981062113075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 6108001129800405069192533 8947267279981062113075)
            ·
              rfl

theorem cell22_2117106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 11].length) (baseStart_2117106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2117106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2117106 prefixEnd_2117106 := by exact prefixLift 2117106
  have htrace : WordTrace (prefixWord ++ tailWord_2117106) baseStart_2117106 baseEnd_2117106 := by
    simpa [prefixWord, tailWord_2117106, baseEnd_2117106] using wordTrace_append hprefix tailTrace_2117106
  have hstable : (prefixWord ++ tailWord_2117106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2117106).length < 2 ^ (prefixWord ++ tailWord_2117106).sum := by decide
  have hdescent : baseEnd_2117106 < baseStart_2117106 := by decide
  rcases family_descends (prefixWord ++ tailWord_2117106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2117110 : List Nat := [5, 1, 1, 1, 2, 2, 1, 4, 2, 3]
def baseStart_2117110 : Nat := 118140960795 + 2117110 * 2 ^ 59
def prefixEnd_2117110 : Nat := 4983230072969 + 3 ^ 40 * 2117110 * 2
def baseEnd_2117110 : Nat := 724730018960211354059063

theorem tailTrace_2117110 : CollatzResearch.WordTrace tailWord_2117110 prefixEnd_2117110 724730018960211354059063 := by
  unfold tailWord_2117110
  simp only [CollatzResearch.WordTrace]
  refine ⟨4826084085004969902922799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 51478230240053012297843189 4826084085004969902922799)
  ·
    refine ⟨7239126127507454854384199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4826084085004969902922799 7239126127507454854384199)
    ·
      refine ⟨10858689191261182281576299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7239126127507454854384199 10858689191261182281576299)
      ·
        refine ⟨16288033786891773422364449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10858689191261182281576299 16288033786891773422364449)
        ·
          refine ⟨12216025340168830066773337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16288033786891773422364449 12216025340168830066773337)
          ·
            refine ⟨9162019005126622550080003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12216025340168830066773337 9162019005126622550080003)
            ·
              refine ⟨13743028507689933825120005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9162019005126622550080003 13743028507689933825120005)
              ·
                refine ⟨2576817845191862592210001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13743028507689933825120005 2576817845191862592210001)
                ·
                  refine ⟨1932613383893896944157501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2576817845191862592210001 1932613383893896944157501)
                  ·
                    refine ⟨724730018960211354059063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1932613383893896944157501 724730018960211354059063)
                    ·
                      rfl

theorem cell22_2117110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 4, 2, 3].length) (baseStart_2117110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2117110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2117110 prefixEnd_2117110 := by exact prefixLift 2117110
  have htrace : WordTrace (prefixWord ++ tailWord_2117110) baseStart_2117110 baseEnd_2117110 := by
    simpa [prefixWord, tailWord_2117110, baseEnd_2117110] using wordTrace_append hprefix tailTrace_2117110
  have hstable : (prefixWord ++ tailWord_2117110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2117110).length < 2 ^ (prefixWord ++ tailWord_2117110).sum := by decide
  have hdescent : baseEnd_2117110 < baseStart_2117110 := by decide
  rcases family_descends (prefixWord ++ tailWord_2117110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2117185 : List Nat := [1, 2, 5, 1, 1, 1, 5, 1, 5]
def baseStart_2117185 : Nat := 118140960795 + 2117185 * 2 ^ 59
def prefixEnd_2117185 : Nat := 4983230072969 + 3 ^ 40 * 2117185 * 2
def baseEnd_2117185 : Nat := 241585230997645386144611

theorem tailTrace_2117185 : CollatzResearch.WordTrace tailWord_2117185 prefixEnd_2117185 241585230997645386144611 := by
  unfold tailWord_2117185
  simp only [CollatzResearch.WordTrace]
  refine ⟨77220080834807806255745009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51480053889871870837163339 77220080834807806255745009)
  ·
    refine ⟨57915060626105854691808757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77220080834807806255745009 57915060626105854691808757)
    ·
      refine ⟨5429536933697423877357071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 57915060626105854691808757 5429536933697423877357071)
      ·
        refine ⟨8144305400546135816035607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5429536933697423877357071 8144305400546135816035607)
        ·
          refine ⟨12216458100819203724053411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8144305400546135816035607 12216458100819203724053411)
          ·
            refine ⟨18324687151228805586080117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12216458100819203724053411 18324687151228805586080117)
            ·
              refine ⟨1717939420427700523695011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18324687151228805586080117 1717939420427700523695011)
              ·
                refine ⟨2576909130641550785542517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1717939420427700523695011 2576909130641550785542517)
                ·
                  refine ⟨241585230997645386144611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2576909130641550785542517 241585230997645386144611)
                  ·
                    rfl

theorem cell22_2117185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 5, 1, 5].length) (baseStart_2117185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2117185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2117185 prefixEnd_2117185 := by exact prefixLift 2117185
  have htrace : WordTrace (prefixWord ++ tailWord_2117185) baseStart_2117185 baseEnd_2117185 := by
    simpa [prefixWord, tailWord_2117185, baseEnd_2117185] using wordTrace_append hprefix tailTrace_2117185
  have hstable : (prefixWord ++ tailWord_2117185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2117185).length < 2 ^ (prefixWord ++ tailWord_2117185).sum := by decide
  have hdescent : baseEnd_2117185 < baseStart_2117185 := by decide
  rcases family_descends (prefixWord ++ tailWord_2117185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2117258 : List Nat := [3, 1, 2, 3, 2, 1, 2, 8]
def baseStart_2117258 : Nat := 118140960795 + 2117258 * 2 ^ 59
def prefixEnd_2117258 : Nat := 4983230072969 + 3 ^ 40 * 2117258 * 2
def baseEnd_2117258 : Nat := 80531186931643144595401

theorem tailTrace_2117258 : CollatzResearch.WordTrace tailWord_2117258 prefixEnd_2117258 80531186931643144595401 := by
  unfold tailWord_2117258
  simp only [CollatzResearch.WordTrace]
  refine ⟨19305685840885834930788107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51481828909028893148768285 19305685840885834930788107)
  ·
    refine ⟨28958528761328752396182161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19305685840885834930788107 28958528761328752396182161)
    ·
      refine ⟨21718896570996564297136621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28958528761328752396182161 21718896570996564297136621)
      ·
        refine ⟨8144586214123711611426233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21718896570996564297136621 8144586214123711611426233)
        ·
          refine ⟨6108439660592783708569675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8144586214123711611426233 6108439660592783708569675)
          ·
            refine ⟨9162659490889175562854513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6108439660592783708569675 9162659490889175562854513)
            ·
              refine ⟨6871994618166881672140885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9162659490889175562854513 6871994618166881672140885)
              ·
                refine ⟨80531186931643144595401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6871994618166881672140885 80531186931643144595401)
                ·
                  rfl

theorem cell22_2117258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 8].length) (baseStart_2117258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2117258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2117258 prefixEnd_2117258 := by exact prefixLift 2117258
  have htrace : WordTrace (prefixWord ++ tailWord_2117258) baseStart_2117258 baseEnd_2117258 := by
    simpa [prefixWord, tailWord_2117258, baseEnd_2117258] using wordTrace_append hprefix tailTrace_2117258
  have hstable : (prefixWord ++ tailWord_2117258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2117258).length < 2 ^ (prefixWord ++ tailWord_2117258).sum := by decide
  have hdescent : baseEnd_2117258 < baseStart_2117258 := by decide
  rcases family_descends (prefixWord ++ tailWord_2117258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2117273 : List Nat := [1, 2, 1, 2, 1, 2, 2, 1, 7, 3]
def baseStart_2117273 : Nat := 118140960795 + 2117273 * 2 ^ 59
def prefixEnd_2117273 : Nat := 4983230072969 + 3 ^ 40 * 2117273 * 2
def baseEnd_2117273 : Nat := 724785817191333262233563

theorem tailTrace_2117273 : CollatzResearch.WordTrace tailWord_2117273 prefixEnd_2117273 724785817191333262233563 := by
  unfold tailWord_2117273
  simp only [CollatzResearch.WordTrace]
  refine ⟨77223290458488997284948473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51482193638992664856632315 77223290458488997284948473)
  ·
    refine ⟨57917467843866747963711355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77223290458488997284948473 57917467843866747963711355)
    ·
      refine ⟨86876201765800121945567033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57917467843866747963711355 86876201765800121945567033)
      ·
        refine ⟨65157151324350091459175275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86876201765800121945567033 65157151324350091459175275)
        ·
          refine ⟨97735726986525137188762913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65157151324350091459175275 97735726986525137188762913)
          ·
            refine ⟨73301795239893852891572185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97735726986525137188762913 73301795239893852891572185)
            ·
              refine ⟨54976346429920389668679139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73301795239893852891572185 54976346429920389668679139)
              ·
                refine ⟨82464519644880584503018709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54976346429920389668679139 82464519644880584503018709)
                ·
                  refine ⟨1932762179176888699289501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 82464519644880584503018709 1932762179176888699289501)
                  ·
                    refine ⟨724785817191333262233563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1932762179176888699289501 724785817191333262233563)
                    ·
                      rfl

theorem cell22_2117273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 7, 3].length) (baseStart_2117273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2117273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2117273 prefixEnd_2117273 := by exact prefixLift 2117273
  have htrace : WordTrace (prefixWord ++ tailWord_2117273) baseStart_2117273 baseEnd_2117273 := by
    simpa [prefixWord, tailWord_2117273, baseEnd_2117273] using wordTrace_append hprefix tailTrace_2117273
  have hstable : (prefixWord ++ tailWord_2117273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2117273).length < 2 ^ (prefixWord ++ tailWord_2117273).sum := by decide
  have hdescent : baseEnd_2117273 < baseStart_2117273 := by decide
  rcases family_descends (prefixWord ++ tailWord_2117273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2117279 : List Nat := [1, 1, 2, 7, 1, 1, 2, 2, 2, 3]
def baseStart_2117279 : Nat := 118140960795 + 2117279 * 2 ^ 59
def prefixEnd_2117279 : Nat := 4983230072969 + 3 ^ 40 * 2117279 * 2
def baseEnd_2117279 : Nat := 724787871113951246583545

theorem tailTrace_2117279 : CollatzResearch.WordTrace tailWord_2117279 prefixEnd_2117279 724787871113951246583545 := by
  unfold tailWord_2117279
  simp only [CollatzResearch.WordTrace]
  refine ⟨77223509296467260309666891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51482339530978173539777927 77223509296467260309666891)
  ·
    refine ⟨115835263944700890464500337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77223509296467260309666891 115835263944700890464500337)
    ·
      refine ⟨86876447958525667848375253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115835263944700890464500337 86876447958525667848375253)
      ·
        refine ⟨2036166749027945340196295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 86876447958525667848375253 2036166749027945340196295)
        ·
          refine ⟨3054250123541918010294443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2036166749027945340196295 3054250123541918010294443)
          ·
            refine ⟨4581375185312877015441665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3054250123541918010294443 4581375185312877015441665)
            ·
              refine ⟨3436031388984657761581249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4581375185312877015441665 3436031388984657761581249)
              ·
                refine ⟨2577023541738493321185937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3436031388984657761581249 2577023541738493321185937)
                ·
                  refine ⟨1932767656303869990889453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2577023541738493321185937 1932767656303869990889453)
                  ·
                    refine ⟨724787871113951246583545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1932767656303869990889453 724787871113951246583545)
                    ·
                      rfl

theorem cell22_2117279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 2, 2, 2, 3].length) (baseStart_2117279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2117279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2117279 prefixEnd_2117279 := by exact prefixLift 2117279
  have htrace : WordTrace (prefixWord ++ tailWord_2117279) baseStart_2117279 baseEnd_2117279 := by
    simpa [prefixWord, tailWord_2117279, baseEnd_2117279] using wordTrace_append hprefix tailTrace_2117279
  have hstable : (prefixWord ++ tailWord_2117279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2117279).length < 2 ^ (prefixWord ++ tailWord_2117279).sum := by decide
  have hdescent : baseEnd_2117279 < baseStart_2117279 := by decide
  rcases family_descends (prefixWord ++ tailWord_2117279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2117399 : List Nat := [1, 1, 3, 4, 2, 2, 3, 2, 4]
def baseStart_2117399 : Nat := 118140960795 + 2117399 * 2 ^ 59
def prefixEnd_2117399 : Nat := 4983230072969 + 3 ^ 40 * 2117399 * 2
def baseEnd_2117399 : Nat := 241609649855436977861059

theorem tailTrace_2117399 : CollatzResearch.WordTrace tailWord_2117399 prefixEnd_2117399 241609649855436977861059 := by
  unfold tailWord_2117399
  simp only [CollatzResearch.WordTrace]
  refine ⟨77227886056032520804035251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51485257370688347202690167 77227886056032520804035251)
  ·
    refine ⟨115841829084048781206052877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77227886056032520804035251 115841829084048781206052877)
    ·
      refine ⟨43440685906518292952269829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115841829084048781206052877 43440685906518292952269829)
      ·
        refine ⟨8145128607472179928550593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43440685906518292952269829 8145128607472179928550593)
        ·
          refine ⟨6108846455604134946412945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8145128607472179928550593 6108846455604134946412945)
          ·
            refine ⟨4581634841703101209809709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6108846455604134946412945 4581634841703101209809709)
            ·
              refine ⟨1718113065638662953678641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4581634841703101209809709 1718113065638662953678641)
              ·
                refine ⟨1288584799228997215258981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1718113065638662953678641 1288584799228997215258981)
                ·
                  refine ⟨241609649855436977861059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1288584799228997215258981 241609649855436977861059)
                  ·
                    rfl

theorem cell22_2117399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 3, 2, 4].length) (baseStart_2117399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2117399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2117399 prefixEnd_2117399 := by exact prefixLift 2117399
  have htrace : WordTrace (prefixWord ++ tailWord_2117399) baseStart_2117399 baseEnd_2117399 := by
    simpa [prefixWord, tailWord_2117399, baseEnd_2117399] using wordTrace_append hprefix tailTrace_2117399
  have hstable : (prefixWord ++ tailWord_2117399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2117399).length < 2 ^ (prefixWord ++ tailWord_2117399).sum := by decide
  have hdescent : baseEnd_2117399 < baseStart_2117399 := by decide
  rcases family_descends (prefixWord ++ tailWord_2117399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2117410 : List Nat := [3, 3, 1, 1, 2, 1, 4, 7]
def baseStart_2117410 : Nat := 118140960795 + 2117410 * 2 ^ 59
def prefixEnd_2117410 : Nat := 4983230072969 + 3 ^ 40 * 2117410 * 2
def baseEnd_2117410 : Nat := 80536968343456730173127

theorem tailTrace_2117410 : CollatzResearch.WordTrace tailWord_2117410 prefixEnd_2117410 80536968343456730173127 := by
  unfold tailWord_2117410
  simp only [CollatzResearch.WordTrace]
  refine ⟨19307071814748167420671421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51485524839328446455123789 19307071814748167420671421)
  ·
    refine ⟨7240151930530562782751783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19307071814748167420671421 7240151930530562782751783)
    ·
      refine ⟨10860227895795844174127675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7240151930530562782751783 10860227895795844174127675)
      ·
        refine ⟨16290341843693766261191513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10860227895795844174127675 16290341843693766261191513)
        ·
          refine ⟨12217756382770324695893635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16290341843693766261191513 12217756382770324695893635)
          ·
            refine ⟨18326634574155487043840453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12217756382770324695893635 18326634574155487043840453)
            ·
              refine ⟨3436243982654153820720085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18326634574155487043840453 3436243982654153820720085)
              ·
                refine ⟨80536968343456730173127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3436243982654153820720085 80536968343456730173127)
                ·
                  rfl

theorem cell22_2117410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4, 7].length) (baseStart_2117410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2117410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2117410 prefixEnd_2117410 := by exact prefixLift 2117410
  have htrace : WordTrace (prefixWord ++ tailWord_2117410) baseStart_2117410 baseEnd_2117410 := by
    simpa [prefixWord, tailWord_2117410, baseEnd_2117410] using wordTrace_append hprefix tailTrace_2117410
  have hstable : (prefixWord ++ tailWord_2117410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2117410).length < 2 ^ (prefixWord ++ tailWord_2117410).sum := by decide
  have hdescent : baseEnd_2117410 < baseStart_2117410 := by decide
  rcases family_descends (prefixWord ++ tailWord_2117410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2117423 : List Nat := [1, 1, 2, 1, 2, 1, 2, 4, 2, 6]
def baseStart_2117423 : Nat := 118140960795 + 2117423 * 2 ^ 59
def prefixEnd_2117423 : Nat := 4983230072969 + 3 ^ 40 * 2117423 * 2
def baseEnd_2117423 : Nat := 724837165256782870983103

theorem tailTrace_2117423 : CollatzResearch.WordTrace tailWord_2117423 prefixEnd_2117423 724837165256782870983103 := by
  unfold tailWord_2117423
  simp only [CollatzResearch.WordTrace]
  refine ⟨77228761407945572902908923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51485840938630381935272615 77228761407945572902908923)
  ·
    refine ⟨115843142111918359354363385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77228761407945572902908923 115843142111918359354363385)
    ·
      refine ⟨86882356583938769515772539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115843142111918359354363385 86882356583938769515772539)
      ·
        refine ⟨130323534875908154273658809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86882356583938769515772539 130323534875908154273658809)
        ·
          refine ⟨97742651156931115705244107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130323534875908154273658809 97742651156931115705244107)
          ·
            refine ⟨146613976735396673557866161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97742651156931115705244107 146613976735396673557866161)
            ·
              refine ⟨109960482551547505168399621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 146613976735396673557866161 109960482551547505168399621)
              ·
                refine ⟨20617590478415157219074929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 109960482551547505168399621 20617590478415157219074929)
                ·
                  refine ⟨15463192858811367914306197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20617590478415157219074929 15463192858811367914306197)
                  ·
                    refine ⟨724837165256782870983103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15463192858811367914306197 724837165256782870983103)
                    ·
                      rfl

theorem cell22_2117423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 4, 2, 6].length) (baseStart_2117423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2117423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2117423 prefixEnd_2117423 := by exact prefixLift 2117423
  have htrace : WordTrace (prefixWord ++ tailWord_2117423) baseStart_2117423 baseEnd_2117423 := by
    simpa [prefixWord, tailWord_2117423, baseEnd_2117423] using wordTrace_append hprefix tailTrace_2117423
  have hstable : (prefixWord ++ tailWord_2117423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2117423).length < 2 ^ (prefixWord ++ tailWord_2117423).sum := by decide
  have hdescent : baseEnd_2117423 < baseStart_2117423 := by decide
  rcases family_descends (prefixWord ++ tailWord_2117423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2117575 : List Nat := [1, 1, 4, 1, 1, 2, 1, 3, 2, 6]
def baseStart_2117575 : Nat := 118140960795 + 2117575 * 2 ^ 59
def prefixEnd_2117575 : Nat := 4983230072969 + 3 ^ 40 * 2117575 * 2
def baseEnd_2117575 : Nat := 724889197963105141182637

theorem tailTrace_2117575 : CollatzResearch.WordTrace tailWord_2117575 prefixEnd_2117575 724889197963105141182637 := by
  unfold tailWord_2117575
  simp only [CollatzResearch.WordTrace]
  refine ⟨77234305303394902862442179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51489536868929935241628119 77234305303394902862442179)
  ·
    refine ⟨115851457955092354293663269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77234305303394902862442179 115851457955092354293663269)
    ·
      refine ⟨21722148366579816430061863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 115851457955092354293663269 21722148366579816430061863)
      ·
        refine ⟨32583222549869724645092795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21722148366579816430061863 32583222549869724645092795)
        ·
          refine ⟨48874833824804586967639193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32583222549869724645092795 48874833824804586967639193)
          ·
            refine ⟨36656125368603440225729395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48874833824804586967639193 36656125368603440225729395)
            ·
              refine ⟨54984188052905160338594093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36656125368603440225729395 54984188052905160338594093)
              ·
                refine ⟨20619070519839435126972785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54984188052905160338594093 20619070519839435126972785)
                ·
                  refine ⟨15464302889879576345229589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20619070519839435126972785 15464302889879576345229589)
                  ·
                    refine ⟨724889197963105141182637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15464302889879576345229589 724889197963105141182637)
                    ·
                      rfl

theorem cell22_2117575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 3, 2, 6].length) (baseStart_2117575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2117575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2117575 prefixEnd_2117575 := by exact prefixLift 2117575
  have htrace : WordTrace (prefixWord ++ tailWord_2117575) baseStart_2117575 baseEnd_2117575 := by
    simpa [prefixWord, tailWord_2117575, baseEnd_2117575] using wordTrace_append hprefix tailTrace_2117575
  have hstable : (prefixWord ++ tailWord_2117575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2117575).length < 2 ^ (prefixWord ++ tailWord_2117575).sum := by decide
  have hdescent : baseEnd_2117575 < baseStart_2117575 := by decide
  rcases family_descends (prefixWord ++ tailWord_2117575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2117635 : List Nat := [1, 1, 1, 3, 2, 1, 1, 2, 10]
def baseStart_2117635 : Nat := 118140960795 + 2117635 * 2 ^ 59
def prefixEnd_2117635 : Nat := 4983230072969 + 3 ^ 40 * 2117635 * 2
def baseEnd_2117635 : Nat := 241636579063094994894151

theorem tailTrace_2117635 : CollatzResearch.WordTrace tailWord_2117635 prefixEnd_2117635 241636579063094994894151 := by
  unfold tailWord_2117635
  simp only [CollatzResearch.WordTrace]
  refine ⟨77236493683177533109626359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51490995788785022073084239 77236493683177533109626359)
  ·
    refine ⟨115854740524766299664439539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77236493683177533109626359 115854740524766299664439539)
    ·
      refine ⟨173782110787149449496659309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115854740524766299664439539 173782110787149449496659309)
      ·
        refine ⟨65168291545181043561247241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 173782110787149449496659309 65168291545181043561247241)
        ·
          refine ⟨48876218658885782670935431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65168291545181043561247241 48876218658885782670935431)
          ·
            refine ⟨73314327988328674006403147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48876218658885782670935431 73314327988328674006403147)
            ·
              refine ⟨109971491982493011009604721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73314327988328674006403147 109971491982493011009604721)
              ·
                refine ⟨82478618986869758257203541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 109971491982493011009604721 82478618986869758257203541)
                ·
                  refine ⟨241636579063094994894151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 82478618986869758257203541 241636579063094994894151)
                  ·
                    rfl

theorem cell22_2117635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 10].length) (baseStart_2117635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2117635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2117635 prefixEnd_2117635 := by exact prefixLift 2117635
  have htrace : WordTrace (prefixWord ++ tailWord_2117635) baseStart_2117635 baseEnd_2117635 := by
    simpa [prefixWord, tailWord_2117635, baseEnd_2117635] using wordTrace_append hprefix tailTrace_2117635
  have hstable : (prefixWord ++ tailWord_2117635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2117635).length < 2 ^ (prefixWord ++ tailWord_2117635).sum := by decide
  have hdescent : baseEnd_2117635 < baseStart_2117635 := by decide
  rcases family_descends (prefixWord ++ tailWord_2117635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2117637 : List Nat := [1, 3, 1, 1, 2, 4, 1, 2, 3, 4]
def baseStart_2117637 : Nat := 118140960795 + 2117637 * 2 ^ 59
def prefixEnd_2117637 : Nat := 4983230072969 + 3 ^ 40 * 2117637 * 2
def baseEnd_2117637 : Nat := 724910421830157646132447

theorem tailTrace_2117637 : CollatzResearch.WordTrace tailWord_2117637 prefixEnd_2117637 724910421830157646132447 := by
  unfold tailWord_2117637
  simp only [CollatzResearch.WordTrace]
  refine ⟨77236566629170287451199165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51491044419446858300799443 77236566629170287451199165)
  ·
    refine ⟨28963712485938857794199687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77236566629170287451199165 28963712485938857794199687)
    ·
      refine ⟨43445568728908286691299531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28963712485938857794199687 43445568728908286691299531)
      ·
        refine ⟨65168353093362430036949297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43445568728908286691299531 65168353093362430036949297)
        ·
          refine ⟨48876264820021822527711973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65168353093362430036949297 48876264820021822527711973)
          ·
            refine ⟨9164299653754091723945995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48876264820021822527711973 9164299653754091723945995)
            ·
              refine ⟨13746449480631137585918993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9164299653754091723945995 13746449480631137585918993)
              ·
                refine ⟨10309837110473353189439245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13746449480631137585918993 10309837110473353189439245)
                ·
                  refine ⟨3866188916427507446039717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10309837110473353189439245 3866188916427507446039717)
                  ·
                    refine ⟨724910421830157646132447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3866188916427507446039717 724910421830157646132447)
                    ·
                      rfl

theorem cell22_2117637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 2, 3, 4].length) (baseStart_2117637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2117637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2117637 prefixEnd_2117637 := by exact prefixLift 2117637
  have htrace : WordTrace (prefixWord ++ tailWord_2117637) baseStart_2117637 baseEnd_2117637 := by
    simpa [prefixWord, tailWord_2117637, baseEnd_2117637] using wordTrace_append hprefix tailTrace_2117637
  have hstable : (prefixWord ++ tailWord_2117637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2117637).length < 2 ^ (prefixWord ++ tailWord_2117637).sum := by decide
  have hdescent : baseEnd_2117637 < baseStart_2117637 := by decide
  rcases family_descends (prefixWord ++ tailWord_2117637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2117645 : List Nat := [1, 7, 1, 2, 1, 1, 1, 2, 3, 3]
def baseStart_2117645 : Nat := 118140960795 + 2117645 * 2 ^ 59
def prefixEnd_2117645 : Nat := 4983230072969 + 3 ^ 40 * 2117645 * 2
def baseEnd_2117645 : Nat := 724913160393648291932423

theorem tailTrace_2117645 : CollatzResearch.WordTrace tailWord_2117645 prefixEnd_2117645 724913160393648291932423 := by
  unfold tailWord_2117645
  simp only [CollatzResearch.WordTrace]
  refine ⟨77236858413141304817490389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51491238942094203211660259 77236858413141304817490389)
  ·
    refine ⟨1810238869057999331659931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 77236858413141304817490389 1810238869057999331659931)
    ·
      refine ⟨2715358303586998997489897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1810238869057999331659931 2715358303586998997489897)
      ·
        refine ⟨2036518727690249248117423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2715358303586998997489897 2036518727690249248117423)
        ·
          refine ⟨3054778091535373872176135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2036518727690249248117423 3054778091535373872176135)
          ·
            refine ⟨4582167137303060808264203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3054778091535373872176135 4582167137303060808264203)
            ·
              refine ⟨6873250705954591212396305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4582167137303060808264203 6873250705954591212396305)
              ·
                refine ⟨5154938029465943409297229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6873250705954591212396305 5154938029465943409297229)
                ·
                  refine ⟨1933101761049728778486461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5154938029465943409297229 1933101761049728778486461)
                  ·
                    refine ⟨724913160393648291932423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1933101761049728778486461 724913160393648291932423)
                    ·
                      rfl

theorem cell22_2117645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_2117645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2117645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2117645 prefixEnd_2117645 := by exact prefixLift 2117645
  have htrace : WordTrace (prefixWord ++ tailWord_2117645) baseStart_2117645 baseEnd_2117645 := by
    simpa [prefixWord, tailWord_2117645, baseEnd_2117645] using wordTrace_append hprefix tailTrace_2117645
  have hstable : (prefixWord ++ tailWord_2117645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2117645).length < 2 ^ (prefixWord ++ tailWord_2117645).sum := by decide
  have hdescent : baseEnd_2117645 < baseStart_2117645 := by decide
  rcases family_descends (prefixWord ++ tailWord_2117645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2117667 : List Nat := [1, 1, 1, 4, 3, 1, 1, 4, 1, 5]
def baseStart_2117667 : Nat := 118140960795 + 2117667 * 2 ^ 59
def prefixEnd_2117667 : Nat := 4983230072969 + 3 ^ 40 * 2117667 * 2
def baseEnd_2117667 : Nat := 724920691443247567882355

theorem tailTrace_2117667 : CollatzResearch.WordTrace tailWord_2117667 prefixEnd_2117667 724920691443247567882355 := by
  unfold tailWord_2117667
  simp only [CollatzResearch.WordTrace]
  refine ⟨77237660819061602574791255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51491773879374401716527503 77237660819061602574791255)
  ·
    refine ⟨115856491228592403862186883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77237660819061602574791255 115856491228592403862186883)
    ·
      refine ⟨173784736842888605793280325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115856491228592403862186883 173784736842888605793280325)
      ·
        refine ⟨32584638158041613586240061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 173784736842888605793280325 32584638158041613586240061)
        ·
          refine ⟨12219239309265605094840023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32584638158041613586240061 12219239309265605094840023)
          ·
            refine ⟨18328858963898407642260035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12219239309265605094840023 18328858963898407642260035)
            ·
              refine ⟨27493288445847611463390053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18328858963898407642260035 27493288445847611463390053)
              ·
                refine ⟨5154991583596427149385635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27493288445847611463390053 5154991583596427149385635)
                ·
                  refine ⟨7732487375394640724078453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5154991583596427149385635 7732487375394640724078453)
                  ·
                    refine ⟨724920691443247567882355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7732487375394640724078453 724920691443247567882355)
                    ·
                      rfl

theorem cell22_2117667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 4, 1, 5].length) (baseStart_2117667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2117667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2117667 prefixEnd_2117667 := by exact prefixLift 2117667
  have htrace : WordTrace (prefixWord ++ tailWord_2117667) baseStart_2117667 baseEnd_2117667 := by
    simpa [prefixWord, tailWord_2117667, baseEnd_2117667] using wordTrace_append hprefix tailTrace_2117667
  have hstable : (prefixWord ++ tailWord_2117667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2117667).length < 2 ^ (prefixWord ++ tailWord_2117667).sum := by decide
  have hdescent : baseEnd_2117667 < baseStart_2117667 := by decide
  rcases family_descends (prefixWord ++ tailWord_2117667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2117669 : List Nat := [1, 3, 1, 2, 2, 3, 1, 5, 4]
def baseStart_2117669 : Nat := 118140960795 + 2117669 * 2 ^ 59
def prefixEnd_2117669 : Nat := 4983230072969 + 3 ^ 40 * 2117669 * 2
def baseEnd_2117669 : Nat := 241640458694706743110783

theorem tailTrace_2117669 : CollatzResearch.WordTrace tailWord_2117669 prefixEnd_2117669 241640458694706743110783 := by
  unfold tailWord_2117669
  simp only [CollatzResearch.WordTrace]
  refine ⟨77237733765054356916364061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51491822510036237944242707 77237733765054356916364061)
  ·
    refine ⟨28964150161895383843636523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77237733765054356916364061 28964150161895383843636523)
    ·
      refine ⟨43446225242843075765454785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28964150161895383843636523 43446225242843075765454785)
      ·
        refine ⟨32584668932132306824091089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43446225242843075765454785 32584668932132306824091089)
        ·
          refine ⟨24438501699099230118068317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32584668932132306824091089 24438501699099230118068317)
          ·
            refine ⟨9164438137162211294275619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24438501699099230118068317 9164438137162211294275619)
            ·
              refine ⟨13746657205743316941413429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9164438137162211294275619 13746657205743316941413429)
              ·
                refine ⟨1288749113038435963257509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13746657205743316941413429 1288749113038435963257509)
                ·
                  refine ⟨241640458694706743110783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1288749113038435963257509 241640458694706743110783)
                  ·
                    rfl

theorem cell22_2117669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 5, 4].length) (baseStart_2117669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2117669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2117669 prefixEnd_2117669 := by exact prefixLift 2117669
  have htrace : WordTrace (prefixWord ++ tailWord_2117669) baseStart_2117669 baseEnd_2117669 := by
    simpa [prefixWord, tailWord_2117669, baseEnd_2117669] using wordTrace_append hprefix tailTrace_2117669
  have hstable : (prefixWord ++ tailWord_2117669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2117669).length < 2 ^ (prefixWord ++ tailWord_2117669).sum := by decide
  have hdescent : baseEnd_2117669 < baseStart_2117669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2117669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2117686 : List Nat := [5, 1, 2, 1, 1, 1, 1, 6, 4]
def baseStart_2117686 : Nat := 118140960795 + 2117686 * 2 ^ 59
def prefixEnd_2117686 : Nat := 4983230072969 + 3 ^ 40 * 2117686 * 2
def baseEnd_2117686 : Nat := 241642398510512617219099

theorem tailTrace_2117686 : CollatzResearch.WordTrace tailWord_2117686 prefixEnd_2117686 241642398510512617219099 := by
  unfold tailWord_2117686
  simp only [CollatzResearch.WordTrace]
  refine ⟨4827397112874548051233307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 51492235870661845879821941 4827397112874548051233307)
  ·
    refine ⟨7241095669311822076849961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4827397112874548051233307 7241095669311822076849961)
    ·
      refine ⟨5430821751983866557637471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7241095669311822076849961 5430821751983866557637471)
      ·
        refine ⟨8146232627975799836456207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5430821751983866557637471 8146232627975799836456207)
        ·
          refine ⟨12219348941963699754684311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8146232627975799836456207 12219348941963699754684311)
          ·
            refine ⟨18329023412945549632026467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12219348941963699754684311 18329023412945549632026467)
            ·
              refine ⟨27493535119418324448039701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18329023412945549632026467 27493535119418324448039701)
              ·
                refine ⟨1288759458722733958501861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 27493535119418324448039701 1288759458722733958501861)
                ·
                  refine ⟨241642398510512617219099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1288759458722733958501861 241642398510512617219099)
                  ·
                    rfl

theorem cell22_2117686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 6, 4].length) (baseStart_2117686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2117686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2117686 prefixEnd_2117686 := by exact prefixLift 2117686
  have htrace : WordTrace (prefixWord ++ tailWord_2117686) baseStart_2117686 baseEnd_2117686 := by
    simpa [prefixWord, tailWord_2117686, baseEnd_2117686] using wordTrace_append hprefix tailTrace_2117686
  have hstable : (prefixWord ++ tailWord_2117686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2117686).length < 2 ^ (prefixWord ++ tailWord_2117686).sum := by decide
  have hdescent : baseEnd_2117686 < baseStart_2117686 := by decide
  rcases family_descends (prefixWord ++ tailWord_2117686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2117714 : List Nat := [3, 2, 2, 1, 4, 1, 1, 8]
def baseStart_2117714 : Nat := 118140960795 + 2117714 * 2 ^ 59
def prefixEnd_2117714 : Nat := 4983230072969 + 3 ^ 40 * 2117714 * 2
def baseEnd_2117714 : Nat := 80548531167083901328579

theorem tailTrace_2117714 : CollatzResearch.WordTrace tailWord_2117714 prefixEnd_2117714 80548531167083901328579 := by
  unfold tailWord_2117714
  simp only [CollatzResearch.WordTrace]
  refine ⟨19309843762472832400438049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51492916699927553067834797 19309843762472832400438049)
  ·
    refine ⟨14482382821854624300328537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19309843762472832400438049 14482382821854624300328537)
    ·
      refine ⟨10861787116390968225246403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14482382821854624300328537 10861787116390968225246403)
      ·
        refine ⟨16292680674586452337869605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10861787116390968225246403 16292680674586452337869605)
        ·
          refine ⟨3054877626484959813350551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16292680674586452337869605 3054877626484959813350551)
          ·
            refine ⟨4582316439727439720025827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3054877626484959813350551 4582316439727439720025827)
            ·
              refine ⟨6873474659591159580038741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4582316439727439720025827 6873474659591159580038741)
              ·
                refine ⟨80548531167083901328579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6873474659591159580038741 80548531167083901328579)
                ·
                  rfl

theorem cell22_2117714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 8].length) (baseStart_2117714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2117714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2117714 prefixEnd_2117714 := by exact prefixLift 2117714
  have htrace : WordTrace (prefixWord ++ tailWord_2117714) baseStart_2117714 baseEnd_2117714 := by
    simpa [prefixWord, tailWord_2117714, baseEnd_2117714] using wordTrace_append hprefix tailTrace_2117714
  have hstable : (prefixWord ++ tailWord_2117714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2117714).length < 2 ^ (prefixWord ++ tailWord_2117714).sum := by decide
  have hdescent : baseEnd_2117714 < baseStart_2117714 := by decide
  rcases family_descends (prefixWord ++ tailWord_2117714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2117718 : List Nat := [5, 2, 2, 1, 1, 1, 1, 2, 4, 3]
def baseStart_2117718 : Nat := 118140960795 + 2117718 * 2 ^ 59
def prefixEnd_2117718 : Nat := 4983230072969 + 3 ^ 40 * 2117718 * 2
def baseEnd_2117718 : Nat := 724938149785500434857199

theorem tailTrace_2117718 : CollatzResearch.WordTrace tailWord_2117718 prefixEnd_2117718 724938149785500434857199 := by
  unfold tailWord_2117718
  simp only [CollatzResearch.WordTrace]
  refine ⟨4827470058867302392806113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 51493013961251225523265205 4827470058867302392806113)
  ·
    refine ⟨3620602544150476794604585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4827470058867302392806113 3620602544150476794604585)
    ·
      refine ⟨2715451908112857595953439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3620602544150476794604585 2715451908112857595953439)
      ·
        refine ⟨4073177862169286393930159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2715451908112857595953439 4073177862169286393930159)
        ·
          refine ⟨6109766793253929590895239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4073177862169286393930159 6109766793253929590895239)
          ·
            refine ⟨9164650189880894386342859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6109766793253929590895239 9164650189880894386342859)
            ·
              refine ⟨13746975284821341579514289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9164650189880894386342859 13746975284821341579514289)
              ·
                refine ⟨10310231463616006184635717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13746975284821341579514289 10310231463616006184635717)
                ·
                  refine ⟨1933168399428001159619197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10310231463616006184635717 1933168399428001159619197)
                  ·
                    refine ⟨724938149785500434857199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1933168399428001159619197 724938149785500434857199)
                    ·
                      rfl

theorem cell22_2117718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_2117718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2117718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2117718 prefixEnd_2117718 := by exact prefixLift 2117718
  have htrace : WordTrace (prefixWord ++ tailWord_2117718) baseStart_2117718 baseEnd_2117718 := by
    simpa [prefixWord, tailWord_2117718, baseEnd_2117718] using wordTrace_append hprefix tailTrace_2117718
  have hstable : (prefixWord ++ tailWord_2117718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2117718).length < 2 ^ (prefixWord ++ tailWord_2117718).sum := by decide
  have hdescent : baseEnd_2117718 < baseStart_2117718 := by decide
  rcases family_descends (prefixWord ++ tailWord_2117718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2117746 : List Nat := [3, 2, 1, 2, 2, 2, 3, 1, 3, 3]
def baseStart_2117746 : Nat := 118140960795 + 2117746 * 2 ^ 59
def prefixEnd_2117746 : Nat := 4983230072969 + 3 ^ 40 * 2117746 * 2
def baseEnd_2117746 : Nat := 724947734757717695157113

theorem tailTrace_2117746 : CollatzResearch.WordTrace tailWord_2117746 prefixEnd_2117746 724947734757717695157113 := by
  unfold tailWord_2117746
  simp only [CollatzResearch.WordTrace]
  refine ⟨19310135546443849766729273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51493694790516932711278061 19310135546443849766729273)
  ·
    refine ⟨14482601659832887325046955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19310135546443849766729273 14482601659832887325046955)
    ·
      refine ⟨21723902489749330987570433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14482601659832887325046955 21723902489749330987570433)
      ·
        refine ⟨16292926867311998240677825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21723902489749330987570433 16292926867311998240677825)
        ·
          refine ⟨12219695150483998680508369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16292926867311998240677825 12219695150483998680508369)
          ·
            refine ⟨9164771362862999010381277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12219695150483998680508369 9164771362862999010381277)
            ·
              refine ⟨3436789261073624628892979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9164771362862999010381277 3436789261073624628892979)
              ·
                refine ⟨5155183891610436943339469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3436789261073624628892979 5155183891610436943339469)
                ·
                  refine ⟨1933193959353913853752301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5155183891610436943339469 1933193959353913853752301)
                  ·
                    refine ⟨724947734757717695157113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1933193959353913853752301 724947734757717695157113)
                    ·
                      rfl

theorem cell22_2117746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3, 1, 3, 3].length) (baseStart_2117746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2117746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2117746 prefixEnd_2117746 := by exact prefixLift 2117746
  have htrace : WordTrace (prefixWord ++ tailWord_2117746) baseStart_2117746 baseEnd_2117746 := by
    simpa [prefixWord, tailWord_2117746, baseEnd_2117746] using wordTrace_append hprefix tailTrace_2117746
  have hstable : (prefixWord ++ tailWord_2117746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2117746).length < 2 ^ (prefixWord ++ tailWord_2117746).sum := by decide
  have hdescent : baseEnd_2117746 < baseStart_2117746 := by decide
  rcases family_descends (prefixWord ++ tailWord_2117746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2117819 : List Nat := [1, 1, 1, 1, 1, 2, 8, 1, 1, 5]
def baseStart_2117819 : Nat := 118140960795 + 2117819 * 2 ^ 59
def prefixEnd_2117819 : Nat := 4983230072969 + 3 ^ 40 * 2117819 * 2
def baseEnd_2117819 : Nat := 724972724149569838081889

theorem tailTrace_2117819 : CollatzResearch.WordTrace tailWord_2117819 prefixEnd_2117819 724972724149569838081889 := by
  unfold tailWord_2117819
  simp only [CollatzResearch.WordTrace]
  refine ⟨77243204714510932534324511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51495469809673955022883007 77243204714510932534324511)
  ·
    refine ⟨115864807071766398801486767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77243204714510932534324511 115864807071766398801486767)
    ·
      refine ⟨173797210607649598202230151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115864807071766398801486767 173797210607649598202230151)
      ·
        refine ⟨260695815911474397303345227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173797210607649598202230151 260695815911474397303345227)
        ·
          refine ⟨391043723867211595955017841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 260695815911474397303345227 391043723867211595955017841)
          ·
            refine ⟨293282792900408696966263381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 391043723867211595955017841 293282792900408696966263381)
            ·
              refine ⟨3436907729301664417573399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 293282792900408696966263381 3436907729301664417573399)
              ·
                refine ⟨5155361593952496626360099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3436907729301664417573399 5155361593952496626360099)
                ·
                  refine ⟨7733042390928744939540149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5155361593952496626360099 7733042390928744939540149)
                  ·
                    refine ⟨724972724149569838081889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7733042390928744939540149 724972724149569838081889)
                    ·
                      rfl

theorem cell22_2117819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8, 1, 1, 5].length) (baseStart_2117819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2117819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2117819 prefixEnd_2117819 := by exact prefixLift 2117819
  have htrace : WordTrace (prefixWord ++ tailWord_2117819) baseStart_2117819 baseEnd_2117819 := by
    simpa [prefixWord, tailWord_2117819, baseEnd_2117819] using wordTrace_append hprefix tailTrace_2117819
  have hstable : (prefixWord ++ tailWord_2117819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2117819).length < 2 ^ (prefixWord ++ tailWord_2117819).sum := by decide
  have hdescent : baseEnd_2117819 < baseStart_2117819 := by decide
  rcases family_descends (prefixWord ++ tailWord_2117819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2117834 : List Nat := [3, 1, 2, 1, 3, 1, 3, 1, 1, 6]
def baseStart_2117834 : Nat := 118140960795 + 2117834 * 2 ^ 59
def prefixEnd_2117834 : Nat := 4983230072969 + 3 ^ 40 * 2117834 * 2
def baseEnd_2117834 : Nat := 724977858956114798956843

theorem tailTrace_2117834 : CollatzResearch.WordTrace tailWord_2117834 prefixEnd_2117834 724977858956114798956843 := by
  unfold tailWord_2117834
  simp only [CollatzResearch.WordTrace]
  refine ⟨19310937952364147524030139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51495834539637726730747037 19310937952364147524030139)
  ·
    refine ⟨28966406928546221286045209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19310937952364147524030139 28966406928546221286045209)
    ·
      refine ⟨21724805196409665964533907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28966406928546221286045209 21724805196409665964533907)
      ·
        refine ⟨32587207794614498946800861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21724805196409665964533907 32587207794614498946800861)
        ·
          refine ⟨12220202922980437105050323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32587207794614498946800861 12220202922980437105050323)
          ·
            refine ⟨18330304384470655657575485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12220202922980437105050323 18330304384470655657575485)
            ·
              refine ⟨6873864144176495871590807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18330304384470655657575485 6873864144176495871590807)
              ·
                refine ⟨10310796216264743807386211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6873864144176495871590807 10310796216264743807386211)
                ·
                  refine ⟨15466194324397115711079317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10310796216264743807386211 15466194324397115711079317)
                  ·
                    refine ⟨724977858956114798956843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15466194324397115711079317 724977858956114798956843)
                    ·
                      rfl

theorem cell22_2117834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 1, 1, 6].length) (baseStart_2117834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2117834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2117834 prefixEnd_2117834 := by exact prefixLift 2117834
  have htrace : WordTrace (prefixWord ++ tailWord_2117834) baseStart_2117834 baseEnd_2117834 := by
    simpa [prefixWord, tailWord_2117834, baseEnd_2117834] using wordTrace_append hprefix tailTrace_2117834
  have hstable : (prefixWord ++ tailWord_2117834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2117834).length < 2 ^ (prefixWord ++ tailWord_2117834).sum := by decide
  have hdescent : baseEnd_2117834 < baseStart_2117834 := by decide
  rcases family_descends (prefixWord ++ tailWord_2117834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2117838 : List Nat := [4, 1, 1, 1, 4, 2, 2, 3, 4]
def baseStart_2117838 : Nat := 118140960795 + 2117838 * 2 ^ 59
def prefixEnd_2117838 : Nat := 4983230072969 + 3 ^ 40 * 2117838 * 2
def baseEnd_2117838 : Nat := 241659742745953373952277

theorem tailTrace_2117838 : CollatzResearch.WordTrace tailWord_2117838 prefixEnd_2117838 241659742745953373952277 := by
  unfold tailWord_2117838
  simp only [CollatzResearch.WordTrace]
  refine ⟨9655487212680262347408271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51495931800961399186177445 9655487212680262347408271)
  ·
    refine ⟨14483230819020393521112407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9655487212680262347408271 14483230819020393521112407)
    ·
      refine ⟨21724846228530590281668611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14483230819020393521112407 21724846228530590281668611)
      ·
        refine ⟨32587269342795885422502917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21724846228530590281668611 32587269342795885422502917)
        ·
          refine ⟨6110113001774228516719297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32587269342795885422502917 6110113001774228516719297)
          ·
            refine ⟨4582584751330671387539473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6110113001774228516719297 4582584751330671387539473)
            ·
              refine ⟨3436938563498003540654605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4582584751330671387539473 3436938563498003540654605)
              ·
                refine ⟨1288851961311751327745477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3436938563498003540654605 1288851961311751327745477)
                ·
                  refine ⟨241659742745953373952277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1288851961311751327745477 241659742745953373952277)
                  ·
                    rfl

theorem cell22_2117838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2, 3, 4].length) (baseStart_2117838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2117838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2117838 prefixEnd_2117838 := by exact prefixLift 2117838
  have htrace : WordTrace (prefixWord ++ tailWord_2117838) baseStart_2117838 baseEnd_2117838 := by
    simpa [prefixWord, tailWord_2117838, baseEnd_2117838] using wordTrace_append hprefix tailTrace_2117838
  have hstable : (prefixWord ++ tailWord_2117838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2117838).length < 2 ^ (prefixWord ++ tailWord_2117838).sum := by decide
  have hdescent : baseEnd_2117838 < baseStart_2117838 := by decide
  rcases family_descends (prefixWord ++ tailWord_2117838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2117853 : List Nat := [1, 4, 3, 2, 1, 2, 1, 1, 4, 3]
def baseStart_2117853 : Nat := 118140960795 + 2117853 * 2 ^ 59
def prefixEnd_2117853 : Nat := 4983230072969 + 3 ^ 40 * 2117853 * 2
def baseEnd_2117853 : Nat := 724984363044405082731785

theorem tailTrace_2117853 : CollatzResearch.WordTrace tailWord_2117853 prefixEnd_2117853 724984363044405082731785 := by
  unfold tailWord_2117853
  simp only [CollatzResearch.WordTrace]
  refine ⟨77244444796387756341062213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51496296530925170894041475 77244444796387756341062213)
  ·
    refine ⟨14483333399322704313949165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77244444796387756341062213 14483333399322704313949165)
    ·
      refine ⟨5431250024746014117730937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14483333399322704313949165 5431250024746014117730937)
      ·
        refine ⟨4073437518559510588298203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5431250024746014117730937 4073437518559510588298203)
        ·
          refine ⟨6110156277839265882447305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4073437518559510588298203 6110156277839265882447305)
          ·
            refine ⟨4582617208379449411835479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6110156277839265882447305 4582617208379449411835479)
            ·
              refine ⟨6873925812569174117753219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4582617208379449411835479 6873925812569174117753219)
              ·
                refine ⟨10310888718853761176629829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6873925812569174117753219 10310888718853761176629829)
                ·
                  refine ⟨1933291634785080220618093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10310888718853761176629829 1933291634785080220618093)
                  ·
                    refine ⟨724984363044405082731785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1933291634785080220618093 724984363044405082731785)
                    ·
                      rfl

theorem cell22_2117853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 1, 4, 3].length) (baseStart_2117853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2117853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2117853 prefixEnd_2117853 := by exact prefixLift 2117853
  have htrace : WordTrace (prefixWord ++ tailWord_2117853) baseStart_2117853 baseEnd_2117853 := by
    simpa [prefixWord, tailWord_2117853, baseEnd_2117853] using wordTrace_append hprefix tailTrace_2117853
  have hstable : (prefixWord ++ tailWord_2117853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2117853).length < 2 ^ (prefixWord ++ tailWord_2117853).sum := by decide
  have hdescent : baseEnd_2117853 < baseStart_2117853 := by decide
  rcases family_descends (prefixWord ++ tailWord_2117853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2117909 : List Nat := [1, 3, 2, 1, 2, 1, 2, 1, 4, 5]
def baseStart_2117909 : Nat := 118140960795 + 2117909 * 2 ^ 59
def prefixEnd_2117909 : Nat := 4983230072969 + 3 ^ 40 * 2117909 * 2
def baseEnd_2117909 : Nat := 725003532988839603331613

theorem tailTrace_2117909 : CollatzResearch.WordTrace tailWord_2117909 prefixEnd_2117909 725003532988839603331613 := by
  unfold tailWord_2117909
  simp only [CollatzResearch.WordTrace]
  refine ⟨77246487284184877905100781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51497658189456585270067187 77246487284184877905100781)
  ·
    refine ⟨28967432731569329214412793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77246487284184877905100781 28967432731569329214412793)
    ·
      refine ⟨21725574548676996910809595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28967432731569329214412793 21725574548676996910809595)
      ·
        refine ⟨32588361823015495366214393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21725574548676996910809595 32588361823015495366214393)
        ·
          refine ⟨24441271367261621524660795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32588361823015495366214393 24441271367261621524660795)
          ·
            refine ⟨36661907050892432286991193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24441271367261621524660795 36661907050892432286991193)
            ·
              refine ⟨27496430288169324215243395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36661907050892432286991193 27496430288169324215243395)
              ·
                refine ⟨41244645432253986322865093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27496430288169324215243395 41244645432253986322865093)
                ·
                  refine ⟨7733371018547622435537205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41244645432253986322865093 7733371018547622435537205)
                  ·
                    refine ⟨725003532988839603331613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7733371018547622435537205 725003532988839603331613)
                    ·
                      rfl

theorem cell22_2117909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 4, 5].length) (baseStart_2117909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2117909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2117909 prefixEnd_2117909 := by exact prefixLift 2117909
  have htrace : WordTrace (prefixWord ++ tailWord_2117909) baseStart_2117909 baseEnd_2117909 := by
    simpa [prefixWord, tailWord_2117909, baseEnd_2117909] using wordTrace_append hprefix tailTrace_2117909
  have hstable : (prefixWord ++ tailWord_2117909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2117909).length < 2 ^ (prefixWord ++ tailWord_2117909).sum := by decide
  have hdescent : baseEnd_2117909 < baseStart_2117909 := by decide
  rcases family_descends (prefixWord ++ tailWord_2117909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2117928 : List Nat := [2, 1, 5, 1, 3, 1, 1, 3, 5]
def baseStart_2117928 : Nat := 118140960795 + 2117928 * 2 ^ 59
def prefixEnd_2117928 : Nat := 4983230072969 + 3 ^ 40 * 2117928 * 2
def baseEnd_2117928 : Nat := 241670012359043295702185

theorem tailTrace_2117928 : CollatzResearch.WordTrace tailWord_2117928 prefixEnd_2117928 241670012359043295702185 := by
  unfold tailWord_2117928
  simp only [CollatzResearch.WordTrace]
  refine ⟨38623590135558022075021219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51498120180744029433361625 38623590135558022075021219)
  ·
    refine ⟨57935385203337033112531829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38623590135558022075021219 57935385203337033112531829)
    ·
      refine ⟨5431442362812846854299859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 57935385203337033112531829 5431442362812846854299859)
      ·
        refine ⟨8147163544219270281449789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5431442362812846854299859 8147163544219270281449789)
        ·
          refine ⟨3055186329082226355543671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8147163544219270281449789 3055186329082226355543671)
          ·
            refine ⟨4582779493623339533315507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3055186329082226355543671 4582779493623339533315507)
            ·
              refine ⟨6874169240435009299973261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4582779493623339533315507 6874169240435009299973261)
              ·
                refine ⟨2577813465163128487489973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6874169240435009299973261 2577813465163128487489973)
                ·
                  refine ⟨241670012359043295702185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2577813465163128487489973 241670012359043295702185)
                  ·
                    rfl

theorem cell22_2117928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 3, 5].length) (baseStart_2117928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2117928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2117928 prefixEnd_2117928 := by exact prefixLift 2117928
  have htrace : WordTrace (prefixWord ++ tailWord_2117928) baseStart_2117928 baseEnd_2117928 := by
    simpa [prefixWord, tailWord_2117928, baseEnd_2117928] using wordTrace_append hprefix tailTrace_2117928
  have hstable : (prefixWord ++ tailWord_2117928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2117928).length < 2 ^ (prefixWord ++ tailWord_2117928).sum := by decide
  have hdescent : baseEnd_2117928 < baseStart_2117928 := by decide
  rcases family_descends (prefixWord ++ tailWord_2117928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2117939 : List Nat := [1, 1, 1, 2, 5, 1, 2, 1, 8]
def baseStart_2117939 : Nat := 118140960795 + 2117939 * 2 ^ 59
def prefixEnd_2117939 : Nat := 4983230072969 + 3 ^ 40 * 2117939 * 2
def baseEnd_2117939 : Nat := 241671267533976508360507

theorem tailTrace_2117939 : CollatzResearch.WordTrace tailWord_2117939 prefixEnd_2117939 241671267533976508360507 := by
  unfold tailWord_2117939
  simp only [CollatzResearch.WordTrace]
  refine ⟨77247581474076193028692871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51498387649384128685795247 77247581474076193028692871)
  ·
    refine ⟨115871372211114289543039307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77247581474076193028692871 115871372211114289543039307)
    ·
      refine ⟨173807058316671434314558961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115871372211114289543039307 173807058316671434314558961)
      ·
        refine ⟨130355293737503575735919221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 173807058316671434314558961 130355293737503575735919221)
        ·
          refine ⟨12220808787890960225242427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 130355293737503575735919221 12220808787890960225242427)
          ·
            refine ⟨18331213181836440337863641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12220808787890960225242427 18331213181836440337863641)
            ·
              refine ⟨13748409886377330253397731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18331213181836440337863641 13748409886377330253397731)
              ·
                refine ⟨20622614829565995380096597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13748409886377330253397731 20622614829565995380096597)
                ·
                  refine ⟨241671267533976508360507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20622614829565995380096597 241671267533976508360507)
                  ·
                    rfl

theorem cell22_2117939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 1, 8].length) (baseStart_2117939 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2117939 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2117939 prefixEnd_2117939 := by exact prefixLift 2117939
  have htrace : WordTrace (prefixWord ++ tailWord_2117939) baseStart_2117939 baseEnd_2117939 := by
    simpa [prefixWord, tailWord_2117939, baseEnd_2117939] using wordTrace_append hprefix tailTrace_2117939
  have hstable : (prefixWord ++ tailWord_2117939).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2117939).length < 2 ^ (prefixWord ++ tailWord_2117939).sum := by decide
  have hdescent : baseEnd_2117939 < baseStart_2117939 := by decide
  rcases family_descends (prefixWord ++ tailWord_2117939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2117941 : List Nat := [1, 3, 3, 1, 2, 1, 3, 1, 3, 4]
def baseStart_2117941 : Nat := 118140960795 + 2117941 * 2 ^ 59
def prefixEnd_2117941 : Nat := 4983230072969 + 3 ^ 40 * 2117941 * 2
def baseEnd_2117941 : Nat := 725014487242802186531515

theorem tailTrace_2117941 : CollatzResearch.WordTrace tailWord_2117941 prefixEnd_2117941 725014487242802186531515 := by
  unfold tailWord_2117941
  simp only [CollatzResearch.WordTrace]
  refine ⟨77247654420068947370265677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51498436280045964913510451 77247654420068947370265677)
  ·
    refine ⟨28967870407525855263849629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77247654420068947370265677 28967870407525855263849629)
    ·
      refine ⟨10862951402822195723943611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28967870407525855263849629 10862951402822195723943611)
      ·
        refine ⟨16294427104233293585915417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10862951402822195723943611 16294427104233293585915417)
        ·
          refine ⟨12220820328174970189436563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16294427104233293585915417 12220820328174970189436563)
          ·
            refine ⟨18331230492262455284154845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12220820328174970189436563 18331230492262455284154845)
            ·
              refine ⟨6874211434598420731558067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18331230492262455284154845 6874211434598420731558067)
              ·
                refine ⟨10311317151897631097337101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6874211434598420731558067 10311317151897631097337101)
                ·
                  refine ⟨3866743931961611661501413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10311317151897631097337101 3866743931961611661501413)
                  ·
                    refine ⟨725014487242802186531515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3866743931961611661501413 725014487242802186531515)
                    ·
                      rfl

theorem cell22_2117941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 1, 3, 4].length) (baseStart_2117941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2117941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2117941 prefixEnd_2117941 := by exact prefixLift 2117941
  have htrace : WordTrace (prefixWord ++ tailWord_2117941) baseStart_2117941 baseEnd_2117941 := by
    simpa [prefixWord, tailWord_2117941, baseEnd_2117941] using wordTrace_append hprefix tailTrace_2117941
  have hstable : (prefixWord ++ tailWord_2117941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2117941).length < 2 ^ (prefixWord ++ tailWord_2117941).sum := by decide
  have hdescent : baseEnd_2117941 < baseStart_2117941 := by decide
  rcases family_descends (prefixWord ++ tailWord_2117941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2117988 : List Nat := [2, 3, 1, 1, 3, 1, 1, 5, 2, 3]
def baseStart_2117988 : Nat := 118140960795 + 2117988 * 2 ^ 59
def prefixEnd_2117988 : Nat := 4983230072969 + 3 ^ 40 * 2117988 * 2
def baseEnd_2117988 : Nat := 725030576303309730606371

theorem tailTrace_2117988 : CollatzResearch.WordTrace tailWord_2117988 prefixEnd_2117988 725030576303309730606371 := by
  unfold tailWord_2117988
  simp only [CollatzResearch.WordTrace]
  refine ⟨38624684325449337198613309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51499579100599116264817745 38624684325449337198613309)
  ·
    refine ⟨14484256622043501449479991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38624684325449337198613309 14484256622043501449479991)
    ·
      refine ⟨21726384933065252174219987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14484256622043501449479991 21726384933065252174219987)
      ·
        refine ⟨32589577399597878261329981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21726384933065252174219987 32589577399597878261329981)
        ·
          refine ⟨12221091524849204347998743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32589577399597878261329981 12221091524849204347998743)
          ·
            refine ⟨18331637287273806521998115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12221091524849204347998743 18331637287273806521998115)
            ·
              refine ⟨27497455930910709782997173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18331637287273806521998115 27497455930910709782997173)
              ·
                refine ⟨2577886493522879042155985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27497455930910709782997173 2577886493522879042155985)
                ·
                  refine ⟨1933414870142159281616989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2577886493522879042155985 1933414870142159281616989)
                  ·
                    refine ⟨725030576303309730606371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1933414870142159281616989 725030576303309730606371)
                    ·
                      rfl

theorem cell22_2117988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 5, 2, 3].length) (baseStart_2117988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2117988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2117988 prefixEnd_2117988 := by exact prefixLift 2117988
  have htrace : WordTrace (prefixWord ++ tailWord_2117988) baseStart_2117988 baseEnd_2117988 := by
    simpa [prefixWord, tailWord_2117988, baseEnd_2117988] using wordTrace_append hprefix tailTrace_2117988
  have hstable : (prefixWord ++ tailWord_2117988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2117988).length < 2 ^ (prefixWord ++ tailWord_2117988).sum := by decide
  have hdescent : baseEnd_2117988 < baseStart_2117988 := by decide
  rcases family_descends (prefixWord ++ tailWord_2117988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2117999 : List Nat := [1, 1, 2, 1, 3, 1, 2, 1, 1, 9]
def baseStart_2117999 : Nat := 118140960795 + 2117999 * 2 ^ 59
def prefixEnd_2117999 : Nat := 4983230072969 + 3 ^ 40 * 2117999 * 2
def baseEnd_2117999 : Nat := 725034341828109368581337

theorem tailTrace_2117999 : CollatzResearch.WordTrace tailWord_2117999 prefixEnd_2117999 725034341828109368581337 := by
  unfold tailWord_2117999
  simp only [CollatzResearch.WordTrace]
  refine ⟨77249769853858823275877051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51499846569239215517251367 77249769853858823275877051)
  ·
    refine ⟨115874654780788234913815577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77249769853858823275877051 115874654780788234913815577)
    ·
      refine ⟨86905991085591176185361683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115874654780788234913815577 86905991085591176185361683)
      ·
        refine ⟨130358986628386764278042525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86905991085591176185361683 130358986628386764278042525)
        ·
          refine ⟨48884619985645036604265947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 130358986628386764278042525 48884619985645036604265947)
          ·
            refine ⟨73326929978467554906398921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48884619985645036604265947 73326929978467554906398921)
            ·
              refine ⟨54995197483850666179799191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73326929978467554906398921 54995197483850666179799191)
              ·
                refine ⟨82492796225775999269698787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54995197483850666179799191 82492796225775999269698787)
                ·
                  refine ⟨123739194338663998904548181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 82492796225775999269698787 123739194338663998904548181)
                  ·
                    refine ⟨725034341828109368581337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 123739194338663998904548181 725034341828109368581337)
                    ·
                      rfl

theorem cell22_2117999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 9].length) (baseStart_2117999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2117999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2117999 prefixEnd_2117999 := by exact prefixLift 2117999
  have htrace : WordTrace (prefixWord ++ tailWord_2117999) baseStart_2117999 baseEnd_2117999 := by
    simpa [prefixWord, tailWord_2117999, baseEnd_2117999] using wordTrace_append hprefix tailTrace_2117999
  have hstable : (prefixWord ++ tailWord_2117999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2117999).length < 2 ^ (prefixWord ++ tailWord_2117999).sum := by decide
  have hdescent : baseEnd_2117999 < baseStart_2117999 := by decide
  rcases family_descends (prefixWord ++ tailWord_2117999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2118084 : List Nat := [2, 3, 3, 2, 3, 1, 1, 1, 3, 3]
def baseStart_2118084 : Nat := 118140960795 + 2118084 * 2 ^ 59
def prefixEnd_2118084 : Nat := 4983230072969 + 3 ^ 40 * 2118084 * 2
def baseEnd_2118084 : Nat := 725063439065197480206077

theorem tailTrace_2118084 : CollatzResearch.WordTrace tailWord_2118084 prefixEnd_2118084 725063439065197480206077 := by
  unfold tailWord_2118084
  simp only [CollatzResearch.WordTrace]
  refine ⟨38626435029275441396360653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51501913372367255195147537 38626435029275441396360653)
  ·
    refine ⟨14484913135978290523635245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38626435029275441396360653 14484913135978290523635245)
    ·
      refine ⟨5431842425991858946363217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14484913135978290523635245 5431842425991858946363217)
      ·
        refine ⟨4073881819493894209772413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5431842425991858946363217 4073881819493894209772413)
        ·
          refine ⟨1527705682310210328664655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4073881819493894209772413 1527705682310210328664655)
          ·
            refine ⟨2291558523465315492996983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1527705682310210328664655 2291558523465315492996983)
            ·
              refine ⟨3437337785197973239495475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2291558523465315492996983 3437337785197973239495475)
              ·
                refine ⟨5156006677796959859243213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3437337785197973239495475 5156006677796959859243213)
                ·
                  refine ⟨1933502504173859947216205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5156006677796959859243213 1933502504173859947216205)
                  ·
                    refine ⟨725063439065197480206077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1933502504173859947216205 725063439065197480206077)
                    ·
                      rfl

theorem cell22_2118084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 1, 1, 3, 3].length) (baseStart_2118084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2118084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2118084 prefixEnd_2118084 := by exact prefixLift 2118084
  have htrace : WordTrace (prefixWord ++ tailWord_2118084) baseStart_2118084 baseEnd_2118084 := by
    simpa [prefixWord, tailWord_2118084, baseEnd_2118084] using wordTrace_append hprefix tailTrace_2118084
  have hstable : (prefixWord ++ tailWord_2118084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2118084).length < 2 ^ (prefixWord ++ tailWord_2118084).sum := by decide
  have hdescent : baseEnd_2118084 < baseStart_2118084 := by decide
  rcases family_descends (prefixWord ++ tailWord_2118084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2118157 : List Nat := [1, 7, 1, 1, 1, 1, 1, 3, 1, 5]
def baseStart_2118157 : Nat := 118140960795 + 2118157 * 2 ^ 59
def prefixEnd_2118157 : Nat := 4983230072969 + 3 ^ 40 * 2118157 * 2
def baseEnd_2118157 : Nat := 725088428457049623130853

theorem tailTrace_2118157 : CollatzResearch.WordTrace tailWord_2118157 prefixEnd_2118157 725088428457049623130853 := by
  unfold tailWord_2118157
  simp only [CollatzResearch.WordTrace]
  refine ⟨77255532587286416260128725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51503688391524277506752483 77255532587286416260128725)
  ·
    refine ⟨1810676545014525381096767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 77255532587286416260128725 1810676545014525381096767)
    ·
      refine ⟨2716014817521788071645151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1810676545014525381096767 2716014817521788071645151)
      ·
        refine ⟨4074022226282682107467727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2716014817521788071645151 4074022226282682107467727)
        ·
          refine ⟨6111033339424023161201591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4074022226282682107467727 6111033339424023161201591)
          ·
            refine ⟨9166550009136034741802387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6111033339424023161201591 9166550009136034741802387)
            ·
              refine ⟨13749825013704052112703581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9166550009136034741802387 13749825013704052112703581)
              ·
                refine ⟨5156184380139019542263843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13749825013704052112703581 5156184380139019542263843)
                ·
                  refine ⟨7734276570208529313395765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5156184380139019542263843 7734276570208529313395765)
                  ·
                    refine ⟨725088428457049623130853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7734276570208529313395765 725088428457049623130853)
                    ·
                      rfl

theorem cell22_2118157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_2118157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2118157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2118157 prefixEnd_2118157 := by exact prefixLift 2118157
  have htrace : WordTrace (prefixWord ++ tailWord_2118157) baseStart_2118157 baseEnd_2118157 := by
    simpa [prefixWord, tailWord_2118157, baseEnd_2118157] using wordTrace_append hprefix tailTrace_2118157
  have hstable : (prefixWord ++ tailWord_2118157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2118157).length < 2 ^ (prefixWord ++ tailWord_2118157).sum := by decide
  have hdescent : baseEnd_2118157 < baseStart_2118157 := by decide
  rcases family_descends (prefixWord ++ tailWord_2118157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2118202 : List Nat := [3, 1, 1, 1, 3, 3, 2, 4, 1, 3]
def baseStart_2118202 : Nat := 118140960795 + 2118202 * 2 ^ 59
def prefixEnd_2118202 : Nat := 4983230072969 + 3 ^ 40 * 2118202 * 2
def baseEnd_2118202 : Nat := 725103832876684505755715

theorem tailTrace_2118202 : CollatzResearch.WordTrace tailWord_2118202 prefixEnd_2118202 725103832876684505755715 := by
  unfold tailWord_2118202
  simp only [CollatzResearch.WordTrace]
  refine ⟨19314293468030847236379215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51504782581415592630344573 19314293468030847236379215)
  ·
    refine ⟨28971440202046270854568823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19314293468030847236379215 28971440202046270854568823)
    ·
      refine ⟨43457160303069406281853235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28971440202046270854568823 43457160303069406281853235)
      ·
        refine ⟨65185740454604109422779853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43457160303069406281853235 65185740454604109422779853)
        ·
          refine ⟨24444652670476541033542445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65185740454604109422779853 24444652670476541033542445)
          ·
            refine ⟨9166744751428702887578417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24444652670476541033542445 9166744751428702887578417)
            ·
              refine ⟨6875058563571527165683813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9166744751428702887578417 6875058563571527165683813)
              ·
                refine ⟨1289073480669661343565715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6875058563571527165683813 1289073480669661343565715)
                ·
                  refine ⟨1933610221004492015348573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1289073480669661343565715 1933610221004492015348573)
                  ·
                    refine ⟨725103832876684505755715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1933610221004492015348573 725103832876684505755715)
                    ·
                      rfl

theorem cell22_2118202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 4, 1, 3].length) (baseStart_2118202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2118202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2118202 prefixEnd_2118202 := by exact prefixLift 2118202
  have htrace : WordTrace (prefixWord ++ tailWord_2118202) baseStart_2118202 baseEnd_2118202 := by
    simpa [prefixWord, tailWord_2118202, baseEnd_2118202] using wordTrace_append hprefix tailTrace_2118202
  have hstable : (prefixWord ++ tailWord_2118202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2118202).length < 2 ^ (prefixWord ++ tailWord_2118202).sum := by decide
  have hdescent : baseEnd_2118202 < baseStart_2118202 := by decide
  rcases family_descends (prefixWord ++ tailWord_2118202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2118213 : List Nat := [1, 3, 1, 1, 1, 5, 2, 1, 2, 5]
def baseStart_2118213 : Nat := 118140960795 + 2118213 * 2 ^ 59
def prefixEnd_2118213 : Nat := 4983230072969 + 3 ^ 40 * 2118213 * 2
def baseEnd_2118213 : Nat := 725107598401484143730681

theorem tailTrace_2118213 : CollatzResearch.WordTrace tailWord_2118213 prefixEnd_2118213 725107598401484143730681 := by
  unfold tailWord_2118213
  simp only [CollatzResearch.WordTrace]
  refine ⟨77257575075083537824167293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51505050050055691882778195 77257575075083537824167293)
  ·
    refine ⟨28971590653156326684062735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77257575075083537824167293 28971590653156326684062735)
    ·
      refine ⟨43457385979734490026094103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28971590653156326684062735 43457385979734490026094103)
      ·
        refine ⟨65186078969601735039141155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43457385979734490026094103 65186078969601735039141155)
        ·
          refine ⟨97779118454402602558711733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65186078969601735039141155 97779118454402602558711733)
          ·
            refine ⟨9166792355100243989879225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 97779118454402602558711733 9166792355100243989879225)
            ·
              refine ⟨6875094266325182992409419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9166792355100243989879225 6875094266325182992409419)
              ·
                refine ⟨10312641399487774488614129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6875094266325182992409419 10312641399487774488614129)
                ·
                  refine ⟨7734481049615830866460597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10312641399487774488614129 7734481049615830866460597)
                  ·
                    refine ⟨725107598401484143730681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7734481049615830866460597 725107598401484143730681)
                    ·
                      rfl

theorem cell22_2118213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 1, 2, 5].length) (baseStart_2118213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2118213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2118213 prefixEnd_2118213 := by exact prefixLift 2118213
  have htrace : WordTrace (prefixWord ++ tailWord_2118213) baseStart_2118213 baseEnd_2118213 := by
    simpa [prefixWord, tailWord_2118213, baseEnd_2118213] using wordTrace_append hprefix tailTrace_2118213
  have hstable : (prefixWord ++ tailWord_2118213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2118213).length < 2 ^ (prefixWord ++ tailWord_2118213).sum := by decide
  have hdescent : baseEnd_2118213 < baseStart_2118213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2118213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2118236 : List Nat := [2, 2, 4, 1, 3, 2, 1, 3, 1, 3]
def baseStart_2118236 : Nat := 118140960795 + 2118236 * 2 ^ 59
def prefixEnd_2118236 : Nat := 4983230072969 + 3 ^ 40 * 2118236 * 2
def baseEnd_2118236 : Nat := 725115471771519750405611

theorem tailTrace_2118236 : CollatzResearch.WordTrace tailWord_2118236 prefixEnd_2118236 725115471771519750405611 := by
  unfold tailWord_2118236
  simp only [CollatzResearch.WordTrace]
  refine ⟨38629206977000106376127281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51505609302666808501503041 38629206977000106376127281)
  ·
    refine ⟨28971905232750079782095461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38629206977000106376127281 28971905232750079782095461)
    ·
      refine ⟨5432232231140639959142899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28971905232750079782095461 5432232231140639959142899)
      ·
        refine ⟨8148348346710959938714349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5432232231140639959142899 8148348346710959938714349)
        ·
          refine ⟨3055630630016609977017881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8148348346710959938714349 3055630630016609977017881)
          ·
            refine ⟨2291722972512457482763411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3055630630016609977017881 2291722972512457482763411)
            ·
              refine ⟨3437584458768686224145117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2291722972512457482763411 3437584458768686224145117)
              ·
                refine ⟨1289094172038257334054419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3437584458768686224145117 1289094172038257334054419)
                ·
                  refine ⟨1933641258057386001081629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1289094172038257334054419 1933641258057386001081629)
                  ·
                    refine ⟨725115471771519750405611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1933641258057386001081629 725115471771519750405611)
                    ·
                      rfl

theorem cell22_2118236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 1, 3, 1, 3].length) (baseStart_2118236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2118236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2118236 prefixEnd_2118236 := by exact prefixLift 2118236
  have htrace : WordTrace (prefixWord ++ tailWord_2118236) baseStart_2118236 baseEnd_2118236 := by
    simpa [prefixWord, tailWord_2118236, baseEnd_2118236] using wordTrace_append hprefix tailTrace_2118236
  have hstable : (prefixWord ++ tailWord_2118236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2118236).length < 2 ^ (prefixWord ++ tailWord_2118236).sum := by decide
  have hdescent : baseEnd_2118236 < baseStart_2118236 := by decide
  rcases family_descends (prefixWord ++ tailWord_2118236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2118292 : List Nat := [2, 4, 2, 2, 1, 2, 1, 2, 1, 5]
def baseStart_2118292 : Nat := 118140960795 + 2118292 * 2 ^ 59
def prefixEnd_2118292 : Nat := 4983230072969 + 3 ^ 40 * 2118292 * 2
def baseEnd_2118292 : Nat := 725134641715954271005439

theorem tailTrace_2118292 : CollatzResearch.WordTrace tailWord_2118292 prefixEnd_2118292 725134641715954271005439 := by
  unfold tailWord_2118292
  simp only [CollatzResearch.WordTrace]
  refine ⟨38630228220898667158146565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51506970961198222877528753 38630228220898667158146565)
  ·
    refine ⟨7243167791418500092152481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38630228220898667158146565 7243167791418500092152481)
    ·
      refine ⟨5432375843563875069114361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7243167791418500092152481 5432375843563875069114361)
      ·
        refine ⟨4074281882672906301835771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5432375843563875069114361 4074281882672906301835771)
        ·
          refine ⟨6111422824009359452753657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4074281882672906301835771 6111422824009359452753657)
          ·
            refine ⟨4583567118007019589565243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6111422824009359452753657 4583567118007019589565243)
            ·
              refine ⟨6875350677010529384347865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4583567118007019589565243 6875350677010529384347865)
              ·
                refine ⟨5156513007757897038260899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6875350677010529384347865 5156513007757897038260899)
                ·
                  refine ⟨7734769511636845557391349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5156513007757897038260899 7734769511636845557391349)
                  ·
                    refine ⟨725134641715954271005439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7734769511636845557391349 725134641715954271005439)
                    ·
                      rfl

theorem cell22_2118292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_2118292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2118292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2118292 prefixEnd_2118292 := by exact prefixLift 2118292
  have htrace : WordTrace (prefixWord ++ tailWord_2118292) baseStart_2118292 baseEnd_2118292 := by
    simpa [prefixWord, tailWord_2118292, baseEnd_2118292] using wordTrace_append hprefix tailTrace_2118292
  have hstable : (prefixWord ++ tailWord_2118292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2118292).length < 2 ^ (prefixWord ++ tailWord_2118292).sum := by decide
  have hdescent : baseEnd_2118292 < baseStart_2118292 := by decide
  rcases family_descends (prefixWord ++ tailWord_2118292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2118305 : List Nat := [1, 2, 3, 3, 4, 9]
def baseStart_2118305 : Nat := 118140960795 + 2118305 * 2 ^ 59
def prefixEnd_2118305 : Nat := 4983230072969 + 3 ^ 40 * 2118305 * 2
def baseEnd_2118305 : Nat := 8952334467674402104079

theorem tailTrace_2118305 : CollatzResearch.WordTrace tailWord_2118305 prefixEnd_2118305 8952334467674402104079 := by
  unfold tailWord_2118305
  simp only [CollatzResearch.WordTrace]
  refine ⟨77260930590750237536516369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51507287060500158357677579 77260930590750237536516369)
  ·
    refine ⟨57945697943062678152387277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77260930590750237536516369 57945697943062678152387277)
    ·
      refine ⟨21729636728648504307145229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57945697943062678152387277 21729636728648504307145229)
      ·
        refine ⟨8148613773243189115179461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21729636728648504307145229 8148613773243189115179461)
        ·
          refine ⟨1527865082483097959096149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8148613773243189115179461 1527865082483097959096149)
          ·
            refine ⟨8952334467674402104079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1527865082483097959096149 8952334467674402104079)
            ·
              rfl

theorem cell22_2118305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 9].length) (baseStart_2118305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2118305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2118305 prefixEnd_2118305 := by exact prefixLift 2118305
  have htrace : WordTrace (prefixWord ++ tailWord_2118305) baseStart_2118305 baseEnd_2118305 := by
    simpa [prefixWord, tailWord_2118305, baseEnd_2118305] using wordTrace_append hprefix tailTrace_2118305
  have hstable : (prefixWord ++ tailWord_2118305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2118305).length < 2 ^ (prefixWord ++ tailWord_2118305).sum := by decide
  have hdescent : baseEnd_2118305 < baseStart_2118305 := by decide
  rcases family_descends (prefixWord ++ tailWord_2118305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2118320 : List Nat := [2, 1, 1, 1, 2, 1, 3, 5, 3, 3]
def baseStart_2118320 : Nat := 118140960795 + 2118320 * 2 ^ 59
def prefixEnd_2118320 : Nat := 4983230072969 + 3 ^ 40 * 2118320 * 2
def baseEnd_2118320 : Nat := 725144226688171531305353

theorem tailTrace_2118320 : CollatzResearch.WordTrace tailWord_2118320 prefixEnd_2118320 725144226688171531305353 := by
  unfold tailWord_2118320
  simp only [CollatzResearch.WordTrace]
  refine ⟨38630738842847947549156207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51507651790463930065541609 38630738842847947549156207)
  ·
    refine ⟨57946108264271921323734311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38630738842847947549156207 57946108264271921323734311)
    ·
      refine ⟨86919162396407881985601467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57946108264271921323734311 86919162396407881985601467)
      ·
        refine ⟨130378743594611822978402201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86919162396407881985601467 130378743594611822978402201)
        ·
          refine ⟨97784057695958867233801651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130378743594611822978402201 97784057695958867233801651)
          ·
            refine ⟨146676086543938300850702477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97784057695958867233801651 146676086543938300850702477)
            ·
              refine ⟨55003532453976862819013429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 146676086543938300850702477 55003532453976862819013429)
              ·
                refine ⟨5156581167560330889282509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 55003532453976862819013429 5156581167560330889282509)
                ·
                  refine ⟨1933717937835124083480941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5156581167560330889282509 1933717937835124083480941)
                  ·
                    refine ⟨725144226688171531305353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1933717937835124083480941 725144226688171531305353)
                    ·
                      rfl

theorem cell22_2118320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 5, 3, 3].length) (baseStart_2118320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2118320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2118320 prefixEnd_2118320 := by exact prefixLift 2118320
  have htrace : WordTrace (prefixWord ++ tailWord_2118320) baseStart_2118320 baseEnd_2118320 := by
    simpa [prefixWord, tailWord_2118320, baseEnd_2118320] using wordTrace_append hprefix tailTrace_2118320
  have hstable : (prefixWord ++ tailWord_2118320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2118320).length < 2 ^ (prefixWord ++ tailWord_2118320).sum := by decide
  have hdescent : baseEnd_2118320 < baseStart_2118320 := by decide
  rcases family_descends (prefixWord ++ tailWord_2118320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2118367 : List Nat := [1, 1, 2, 3, 2, 5, 1, 2, 5]
def baseStart_2118367 : Nat := 118140960795 + 2118367 * 2 ^ 59
def prefixEnd_2118367 : Nat := 4983230072969 + 3 ^ 40 * 2118367 * 2
def baseEnd_2118367 : Nat := 241720105249559691793403

theorem tailTrace_2118367 : CollatzResearch.WordTrace tailWord_2118367 prefixEnd_2118367 241720105249559691793403 := by
  unfold tailWord_2118367
  simp only [CollatzResearch.WordTrace]
  refine ⟨77263191916525622125273355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51508794611017081416848903 77263191916525622125273355)
  ·
    refine ⟨115894787874788433187910033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77263191916525622125273355 115894787874788433187910033)
    ·
      refine ⟨86921090906091324890932525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115894787874788433187910033 86921090906091324890932525)
      ·
        refine ⟨32595409089784246834099697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86921090906091324890932525 32595409089784246834099697)
        ·
          refine ⟨24446556817338185125574773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32595409089784246834099697 24446556817338185125574773)
          ·
            refine ⟨2291864701625454855522635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24446556817338185125574773 2291864701625454855522635)
            ·
              refine ⟨3437797052438182283283953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2291864701625454855522635 3437797052438182283283953)
              ·
                refine ⟨2578347789328636712462965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3437797052438182283283953 2578347789328636712462965)
                ·
                  refine ⟨241720105249559691793403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2578347789328636712462965 241720105249559691793403)
                  ·
                    rfl

theorem cell22_2118367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 1, 2, 5].length) (baseStart_2118367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2118367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2118367 prefixEnd_2118367 := by exact prefixLift 2118367
  have htrace : WordTrace (prefixWord ++ tailWord_2118367) baseStart_2118367 baseEnd_2118367 := by
    simpa [prefixWord, tailWord_2118367, baseEnd_2118367] using wordTrace_append hprefix tailTrace_2118367
  have hstable : (prefixWord ++ tailWord_2118367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2118367).length < 2 ^ (prefixWord ++ tailWord_2118367).sum := by decide
  have hdescent : baseEnd_2118367 < baseStart_2118367 := by decide
  rcases family_descends (prefixWord ++ tailWord_2118367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2118397 : List Nat := [1, 4, 1, 1, 1, 1, 6, 2, 1, 4]
def baseStart_2118397 : Nat := 118140960795 + 2118397 * 2 ^ 59
def prefixEnd_2118397 : Nat := 4983230072969 + 3 ^ 40 * 2118397 * 2
def baseEnd_2118397 : Nat := 725170585361768997130117

theorem tailTrace_2118397 : CollatzResearch.WordTrace tailWord_2118397 prefixEnd_2118397 725170585361768997130117 := by
  unfold tailWord_2118397
  simp only [CollatzResearch.WordTrace]
  refine ⟨77264286106416937248865445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51509524070944624832576963 77264286106416937248865445)
  ·
    refine ⟨14487053644953175734162271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77264286106416937248865445 14487053644953175734162271)
    ·
      refine ⟨21730580467429763601243407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14487053644953175734162271 21730580467429763601243407)
      ·
        refine ⟨32595870701144645401865111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21730580467429763601243407 32595870701144645401865111)
        ·
          refine ⟨48893806051716968102797667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32595870701144645401865111 48893806051716968102797667)
          ·
            refine ⟨73340709077575452154196501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48893806051716968102797667 73340709077575452154196501)
            ·
              refine ⟨3437845738011349319727961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 73340709077575452154196501 3437845738011349319727961)
              ·
                refine ⟨2578384303508511989795971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3437845738011349319727961 2578384303508511989795971)
                ·
                  refine ⟨3867576455262767984693957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2578384303508511989795971 3867576455262767984693957)
                  ·
                    refine ⟨725170585361768997130117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3867576455262767984693957 725170585361768997130117)
                    ·
                      rfl

theorem cell22_2118397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6, 2, 1, 4].length) (baseStart_2118397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2118397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2118397 prefixEnd_2118397 := by exact prefixLift 2118397
  have htrace : WordTrace (prefixWord ++ tailWord_2118397) baseStart_2118397 baseEnd_2118397 := by
    simpa [prefixWord, tailWord_2118397, baseEnd_2118397] using wordTrace_append hprefix tailTrace_2118397
  have hstable : (prefixWord ++ tailWord_2118397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2118397).length < 2 ^ (prefixWord ++ tailWord_2118397).sum := by decide
  have hdescent : baseEnd_2118397 < baseStart_2118397 := by decide
  rcases family_descends (prefixWord ++ tailWord_2118397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2118410 : List Nat := [3, 1, 2, 2, 1, 2, 2, 1, 3, 5]
def baseStart_2118410 : Nat := 118140960795 + 2118410 * 2 ^ 59
def prefixEnd_2118410 : Nat := 4983230072969 + 3 ^ 40 * 2118410 * 2
def baseEnd_2118410 : Nat := 725175035527441296555077

theorem tailTrace_2118410 : CollatzResearch.WordTrace tailWord_2118410 prefixEnd_2118410 725175035527441296555077 := by
  unfold tailWord_2118410
  simp only [CollatzResearch.WordTrace]
  refine ⟨19316190063842460117272171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51509840170246560312725789 19316190063842460117272171)
  ·
    refine ⟨28974285095763690175908257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19316190063842460117272171 28974285095763690175908257)
    ·
      refine ⟨21730713821822767631931193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28974285095763690175908257 21730713821822767631931193)
      ·
        refine ⟨16298035366367075723948395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21730713821822767631931193 16298035366367075723948395)
        ·
          refine ⟨24447053049550613585922593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16298035366367075723948395 24447053049550613585922593)
          ·
            refine ⟨18335289787162960189441945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24447053049550613585922593 18335289787162960189441945)
            ·
              refine ⟨13751467340372220142081459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18335289787162960189441945 13751467340372220142081459)
              ·
                refine ⟨20627201010558330213122189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13751467340372220142081459 20627201010558330213122189)
                ·
                  refine ⟨7735200378959373829920821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20627201010558330213122189 7735200378959373829920821)
                  ·
                    refine ⟨725175035527441296555077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7735200378959373829920821 725175035527441296555077)
                    ·
                      rfl

theorem cell22_2118410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 1, 3, 5].length) (baseStart_2118410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2118410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2118410 prefixEnd_2118410 := by exact prefixLift 2118410
  have htrace : WordTrace (prefixWord ++ tailWord_2118410) baseStart_2118410 baseEnd_2118410 := by
    simpa [prefixWord, tailWord_2118410, baseEnd_2118410] using wordTrace_append hprefix tailTrace_2118410
  have hstable : (prefixWord ++ tailWord_2118410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2118410).length < 2 ^ (prefixWord ++ tailWord_2118410).sum := by decide
  have hdescent : baseEnd_2118410 < baseStart_2118410 := by decide
  rcases family_descends (prefixWord ++ tailWord_2118410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2118592 : List Nat := [2, 1, 1, 2, 3, 5, 8]
def baseStart_2118592 : Nat := 118140960795 + 2118592 * 2 ^ 59
def prefixEnd_2118592 : Nat := 4983230072969 + 3 ^ 40 * 2118592 * 2
def baseEnd_2118592 : Nat := 26860642142476055129797

theorem tailTrace_2118592 : CollatzResearch.WordTrace tailWord_2118592 prefixEnd_2118592 26860642142476055129797 := by
  unfold tailWord_2118592
  simp only [CollatzResearch.WordTrace]
  refine ⟨38635699170355242776107015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51514265560473657034809353 38635699170355242776107015)
  ·
    refine ⟨57953548755532864164160523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38635699170355242776107015 57953548755532864164160523)
    ·
      refine ⟨86930323133299296246240785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57953548755532864164160523 86930323133299296246240785)
      ·
        refine ⟨65197742349974472184680589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86930323133299296246240785 65197742349974472184680589)
        ·
          refine ⟨24449153381240427069255221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65197742349974472184680589 24449153381240427069255221)
          ·
            refine ⟨2292108129491290037742677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24449153381240427069255221 2292108129491290037742677)
            ·
              refine ⟨26860642142476055129797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2292108129491290037742677 26860642142476055129797)
              ·
                rfl

theorem cell22_2118592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 8].length) (baseStart_2118592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2118592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2118592 prefixEnd_2118592 := by exact prefixLift 2118592
  have htrace : WordTrace (prefixWord ++ tailWord_2118592) baseStart_2118592 baseEnd_2118592 := by
    simpa [prefixWord, tailWord_2118592, baseEnd_2118592] using wordTrace_append hprefix tailTrace_2118592
  have hstable : (prefixWord ++ tailWord_2118592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2118592).length < 2 ^ (prefixWord ++ tailWord_2118592).sum := by decide
  have hdescent : baseEnd_2118592 < baseStart_2118592 := by decide
  rcases family_descends (prefixWord ++ tailWord_2118592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2118716 : List Nat := [2, 2, 2, 2, 2, 2, 2, 4, 4]
def baseStart_2118716 : Nat := 118140960795 + 2118716 * 2 ^ 59
def prefixEnd_2118716 : Nat := 4983230072969 + 3 ^ 40 * 2118716 * 2
def baseEnd_2118716 : Nat := 241759928526986166134713

theorem tailTrace_2118716 : CollatzResearch.WordTrace tailWord_2118716 prefixEnd_2118716 241759928526986166134713 := by
  unfold tailWord_2118716
  simp only [CollatzResearch.WordTrace]
  refine ⟨38637960496130627364864001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51517280661507503153152001 38637960496130627364864001)
  ·
    refine ⟨28978470372097970523648001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38637960496130627364864001 28978470372097970523648001)
    ·
      refine ⟨21733852779073477892736001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28978470372097970523648001 21733852779073477892736001)
      ·
        refine ⟨16300389584305108419552001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21733852779073477892736001 16300389584305108419552001)
        ·
          refine ⟨12225292188228831314664001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16300389584305108419552001 12225292188228831314664001)
          ·
            refine ⟨9168969141171623485998001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12225292188228831314664001 9168969141171623485998001)
            ·
              refine ⟨6876726855878717614498501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9168969141171623485998001 6876726855878717614498501)
              ·
                refine ⟨1289386285477259552718469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6876726855878717614498501 1289386285477259552718469)
                ·
                  refine ⟨241759928526986166134713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1289386285477259552718469 241759928526986166134713)
                  ·
                    rfl

theorem cell22_2118716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 4, 4].length) (baseStart_2118716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2118716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2118716 prefixEnd_2118716 := by exact prefixLift 2118716
  have htrace : WordTrace (prefixWord ++ tailWord_2118716) baseStart_2118716 baseEnd_2118716 := by
    simpa [prefixWord, tailWord_2118716, baseEnd_2118716] using wordTrace_append hprefix tailTrace_2118716
  have hstable : (prefixWord ++ tailWord_2118716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2118716).length < 2 ^ (prefixWord ++ tailWord_2118716).sum := by decide
  have hdescent : baseEnd_2118716 < baseStart_2118716 := by decide
  rcases family_descends (prefixWord ++ tailWord_2118716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2118776 : List Nat := [2, 1, 2, 1, 1, 1, 7, 1, 3, 3]
def baseStart_2118776 : Nat := 118140960795 + 2118776 * 2 ^ 59
def prefixEnd_2118776 : Nat := 4983230072969 + 3 ^ 40 * 2118776 * 2
def baseEnd_2118776 : Nat := 725300324807138341903955

theorem tailTrace_2118776 : CollatzResearch.WordTrace tailWord_2118776 prefixEnd_2118776 725300324807138341903955 := by
  unfold tailWord_2118776
  simp only [CollatzResearch.WordTrace]
  refine ⟨38639054686021942488456091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51518739581362589984608121 38639054686021942488456091)
  ·
    refine ⟨57958582029032913732684137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38639054686021942488456091 57958582029032913732684137)
    ·
      refine ⟨43468936521774685299513103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57958582029032913732684137 43468936521774685299513103)
      ·
        refine ⟨65203404782662027949269655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43468936521774685299513103 65203404782662027949269655)
        ·
          refine ⟨97805107173993041923904483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65203404782662027949269655 97805107173993041923904483)
          ·
            refine ⟨146707660760989562885856725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97805107173993041923904483 146707660760989562885856725)
            ·
              refine ⟨3438460799085692880137267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 146707660760989562885856725 3438460799085692880137267)
              ·
                refine ⟨5157691198628539320205901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3438460799085692880137267 5157691198628539320205901)
                ·
                  refine ⟨1934134199485702245077213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5157691198628539320205901 1934134199485702245077213)
                  ·
                    refine ⟨725300324807138341903955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1934134199485702245077213 725300324807138341903955)
                    ·
                      rfl

theorem cell22_2118776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7, 1, 3, 3].length) (baseStart_2118776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2118776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2118776 prefixEnd_2118776 := by exact prefixLift 2118776
  have htrace : WordTrace (prefixWord ++ tailWord_2118776) baseStart_2118776 baseEnd_2118776 := by
    simpa [prefixWord, tailWord_2118776, baseEnd_2118776] using wordTrace_append hprefix tailTrace_2118776
  have hstable : (prefixWord ++ tailWord_2118776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2118776).length < 2 ^ (prefixWord ++ tailWord_2118776).sum := by decide
  have hdescent : baseEnd_2118776 < baseStart_2118776 := by decide
  rcases family_descends (prefixWord ++ tailWord_2118776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2118823 : List Nat := [1, 1, 6, 2, 1, 2, 2, 2, 5]
def baseStart_2118823 : Nat := 118140960795 + 2118823 * 2 ^ 59
def prefixEnd_2118823 : Nat := 4983230072969 + 3 ^ 40 * 2118823 * 2
def baseEnd_2118823 : Nat := 241772137955881961992937

theorem tailTrace_2118823 : CollatzResearch.WordTrace tailWord_2118823 prefixEnd_2118823 241772137955881961992937 := by
  unfold tailWord_2118823
  simp only [CollatzResearch.WordTrace]
  refine ⟨77279823602873612003873123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51519882401915741335915415 77279823602873612003873123)
  ·
    refine ⟨115919735404310418005809685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77279823602873612003873123 115919735404310418005809685)
    ·
      refine ⟨5433737597077050844022329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 115919735404310418005809685 5433737597077050844022329)
      ·
        refine ⟨4075303197807788133016747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5433737597077050844022329 4075303197807788133016747)
        ·
          refine ⟨6112954796711682199525121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4075303197807788133016747 6112954796711682199525121)
          ·
            refine ⟨4584716097533761649643841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6112954796711682199525121 4584716097533761649643841)
            ·
              refine ⟨3438537073150321237232881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4584716097533761649643841 3438537073150321237232881)
              ·
                refine ⟨2578902804862740927924661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3438537073150321237232881 2578902804862740927924661)
                ·
                  refine ⟨241772137955881961992937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2578902804862740927924661 241772137955881961992937)
                  ·
                    rfl

theorem cell22_2118823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2, 2, 5].length) (baseStart_2118823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2118823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2118823 prefixEnd_2118823 := by exact prefixLift 2118823
  have htrace : WordTrace (prefixWord ++ tailWord_2118823) baseStart_2118823 baseEnd_2118823 := by
    simpa [prefixWord, tailWord_2118823, baseEnd_2118823] using wordTrace_append hprefix tailTrace_2118823
  have hstable : (prefixWord ++ tailWord_2118823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2118823).length < 2 ^ (prefixWord ++ tailWord_2118823).sum := by decide
  have hdescent : baseEnd_2118823 < baseStart_2118823 := by decide
  rcases family_descends (prefixWord ++ tailWord_2118823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2118866 : List Nat := [3, 2, 2, 2, 1, 1, 1, 4, 1, 5]
def baseStart_2118866 : Nat := 118140960795 + 2118866 * 2 ^ 59
def prefixEnd_2118866 : Nat := 4983230072969 + 3 ^ 40 * 2118866 * 2
def baseEnd_2118866 : Nat := 725331133646408107153679

theorem tailTrace_2118866 : CollatzResearch.WordTrace tailWord_2118866 prefixEnd_2118866 725331133646408107153679 := by
  unfold tailWord_2118866
  simp only [CollatzResearch.WordTrace]
  refine ⟨19320347985429457586922113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51520927961145220231792301 19320347985429457586922113)
  ·
    refine ⟨14490260989072093190191585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19320347985429457586922113 14490260989072093190191585)
    ·
      refine ⟨10867695741804069892643689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14490260989072093190191585 10867695741804069892643689)
      ·
        refine ⟨8150771806353052419482767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10867695741804069892643689 8150771806353052419482767)
        ·
          refine ⟨12226157709529578629224151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8150771806353052419482767 12226157709529578629224151)
          ·
            refine ⟨18339236564294367943836227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12226157709529578629224151 18339236564294367943836227)
            ·
              refine ⟨27508854846441551915754341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18339236564294367943836227 27508854846441551915754341)
              ·
                refine ⟨5157910283707790984203939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27508854846441551915754341 5157910283707790984203939)
                ·
                  refine ⟨7736865425561686476305909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5157910283707790984203939 7736865425561686476305909)
                  ·
                    refine ⟨725331133646408107153679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7736865425561686476305909 725331133646408107153679)
                    ·
                      rfl

theorem cell22_2118866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 4, 1, 5].length) (baseStart_2118866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2118866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2118866 prefixEnd_2118866 := by exact prefixLift 2118866
  have htrace : WordTrace (prefixWord ++ tailWord_2118866) baseStart_2118866 baseEnd_2118866 := by
    simpa [prefixWord, tailWord_2118866, baseEnd_2118866] using wordTrace_append hprefix tailTrace_2118866
  have hstable : (prefixWord ++ tailWord_2118866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2118866).length < 2 ^ (prefixWord ++ tailWord_2118866).sum := by decide
  have hdescent : baseEnd_2118866 < baseStart_2118866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2118866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2118913 : List Nat := [1, 2, 4, 1, 1, 5, 2, 6]
def baseStart_2118913 : Nat := 118140960795 + 2118913 * 2 ^ 59
def prefixEnd_2118913 : Nat := 4983230072969 + 3 ^ 40 * 2118913 * 2
def baseEnd_2118913 : Nat := 80594135856323961247615

theorem tailTrace_2118913 : CollatzResearch.WordTrace tailWord_2118913 prefixEnd_2118913 80594135856323961247615 := by
  unfold tailWord_2118913
  simp only [CollatzResearch.WordTrace]
  refine ⟨77283106172547557374649393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51522070781698371583099595 77283106172547557374649393)
  ·
    refine ⟨57962329629410668030987045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77283106172547557374649393 57962329629410668030987045)
    ·
      refine ⟨10867936805514500255810071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57962329629410668030987045 10867936805514500255810071)
      ·
        refine ⟨16301905208271750383715107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10867936805514500255810071 16301905208271750383715107)
        ·
          refine ⟨24452857812407625575572661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16301905208271750383715107 24452857812407625575572661)
          ·
            refine ⟨2292455419913214897709937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24452857812407625575572661 2292455419913214897709937)
            ·
              refine ⟨1719341564934911173282453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2292455419913214897709937 1719341564934911173282453)
              ·
                refine ⟨80594135856323961247615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1719341564934911173282453 80594135856323961247615)
                ·
                  rfl

theorem cell22_2118913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 2, 6].length) (baseStart_2118913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2118913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2118913 prefixEnd_2118913 := by exact prefixLift 2118913
  have htrace : WordTrace (prefixWord ++ tailWord_2118913) baseStart_2118913 baseEnd_2118913 := by
    simpa [prefixWord, tailWord_2118913, baseEnd_2118913] using wordTrace_append hprefix tailTrace_2118913
  have hstable : (prefixWord ++ tailWord_2118913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2118913).length < 2 ^ (prefixWord ++ tailWord_2118913).sum := by decide
  have hdescent : baseEnd_2118913 < baseStart_2118913 := by decide
  rcases family_descends (prefixWord ++ tailWord_2118913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2118930 : List Nat := [3, 2, 4, 2, 1, 2, 8]
def baseStart_2118930 : Nat := 118140960795 + 2118930 * 2 ^ 59
def prefixEnd_2118930 : Nat := 4983230072969 + 3 ^ 40 * 2118930 * 2
def baseEnd_2118930 : Nat := 26864927487197528650129

theorem tailTrace_2118930 : CollatzResearch.WordTrace tailWord_2118930 prefixEnd_2118930 26864927487197528650129 := by
  unfold tailWord_2118930
  simp only [CollatzResearch.WordTrace]
  refine ⟨19320931553371492319504561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51522484142323979518678829 19320931553371492319504561)
  ·
    refine ⟨14490698665028619239628421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19320931553371492319504561 14490698665028619239628421)
    ·
      refine ⟨2717005999692866107430329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14490698665028619239628421 2717005999692866107430329)
      ·
        refine ⟨2037754499769649580572747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2717005999692866107430329 2037754499769649580572747)
        ·
          refine ⟨3056631749654474370859121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2037754499769649580572747 3056631749654474370859121)
          ·
            refine ⟨2292473812240855778144341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3056631749654474370859121 2292473812240855778144341)
            ·
              refine ⟨26864927487197528650129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2292473812240855778144341 26864927487197528650129)
              ·
                rfl

theorem cell22_2118930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 8].length) (baseStart_2118930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2118930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2118930 prefixEnd_2118930 := by exact prefixLift 2118930
  have htrace : WordTrace (prefixWord ++ tailWord_2118930) baseStart_2118930 baseEnd_2118930 := by
    simpa [prefixWord, tailWord_2118930, baseEnd_2118930] using wordTrace_append hprefix tailTrace_2118930
  have hstable : (prefixWord ++ tailWord_2118930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2118930).length < 2 ^ (prefixWord ++ tailWord_2118930).sum := by decide
  have hdescent : baseEnd_2118930 < baseStart_2118930 := by decide
  rcases family_descends (prefixWord ++ tailWord_2118930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2119033 : List Nat := [1, 2, 1, 3, 2, 1, 5, 1, 2, 4]
def baseStart_2119033 : Nat := 118140960795 + 2119033 * 2 ^ 59
def prefixEnd_2119033 : Nat := 4983230072969 + 3 ^ 40 * 2119033 * 2
def baseEnd_2119033 : Nat := 725388301159275338228167

theorem tailTrace_2119033 : CollatzResearch.WordTrace tailWord_2119033 prefixEnd_2119033 725388301159275338228167 := by
  unfold tailWord_2119033
  simp only [CollatzResearch.WordTrace]
  refine ⟨77287482932112817869017753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51524988621408545246011835 77287482932112817869017753)
  ·
    refine ⟨57965612199084613401763315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77287482932112817869017753 57965612199084613401763315)
    ·
      refine ⟨86948418298626920102644973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57965612199084613401763315 86948418298626920102644973)
      ·
        refine ⟨32605656861985095038491865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86948418298626920102644973 32605656861985095038491865)
        ·
          refine ⟨24454242646488821278868899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32605656861985095038491865 24454242646488821278868899)
          ·
            refine ⟨36681363969733231918303349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24454242646488821278868899 36681363969733231918303349)
            ·
              refine ⟨3438877872162490492340939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36681363969733231918303349 3438877872162490492340939)
              ·
                refine ⟨5158316808243735738511409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3438877872162490492340939 5158316808243735738511409)
                ·
                  refine ⟨3868737606182801803883557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5158316808243735738511409 3868737606182801803883557)
                  ·
                    refine ⟨725388301159275338228167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3868737606182801803883557 725388301159275338228167)
                    ·
                      rfl

theorem cell22_2119033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5, 1, 2, 4].length) (baseStart_2119033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2119033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2119033 prefixEnd_2119033 := by exact prefixLift 2119033
  have htrace : WordTrace (prefixWord ++ tailWord_2119033) baseStart_2119033 baseEnd_2119033 := by
    simpa [prefixWord, tailWord_2119033, baseEnd_2119033] using wordTrace_append hprefix tailTrace_2119033
  have hstable : (prefixWord ++ tailWord_2119033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2119033).length < 2 ^ (prefixWord ++ tailWord_2119033).sum := by decide
  have hdescent : baseEnd_2119033 < baseStart_2119033 := by decide
  rcases family_descends (prefixWord ++ tailWord_2119033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2119061 : List Nat := [1, 3, 2, 1, 1, 2, 2, 1, 1, 8]
def baseStart_2119061 : Nat := 118140960795 + 2119061 * 2 ^ 59
def prefixEnd_2119061 : Nat := 4983230072969 + 3 ^ 40 * 2119061 * 2
def baseEnd_2119061 : Nat := 725397886131492598528081

theorem tailTrace_2119061 : CollatzResearch.WordTrace tailWord_2119061 prefixEnd_2119061 725397886131492598528081 := by
  unfold tailWord_2119061
  simp only [CollatzResearch.WordTrace]
  refine ⟨77288504176011378651037037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51525669450674252434024691 77288504176011378651037037)
  ·
    refine ⟨28983189066004266994138889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77288504176011378651037037 28983189066004266994138889)
    ·
      refine ⟨21737391799503200245604167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28983189066004266994138889 21737391799503200245604167)
      ·
        refine ⟨32606087699254800368406251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21737391799503200245604167 32606087699254800368406251)
        ·
          refine ⟨48909131548882200552609377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32606087699254800368406251 48909131548882200552609377)
          ·
            refine ⟨36681848661661650414457033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48909131548882200552609377 36681848661661650414457033)
            ·
              refine ⟨27511386496246237810842775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36681848661661650414457033 27511386496246237810842775)
              ·
                refine ⟨41267079744369356716264163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27511386496246237810842775 41267079744369356716264163)
                ·
                  refine ⟨61900619616554035074396245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41267079744369356716264163 61900619616554035074396245)
                  ·
                    refine ⟨725397886131492598528081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 61900619616554035074396245 725397886131492598528081)
                    ·
                      rfl

theorem cell22_2119061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 8].length) (baseStart_2119061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2119061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2119061 prefixEnd_2119061 := by exact prefixLift 2119061
  have htrace : WordTrace (prefixWord ++ tailWord_2119061) baseStart_2119061 baseEnd_2119061 := by
    simpa [prefixWord, tailWord_2119061, baseEnd_2119061] using wordTrace_append hprefix tailTrace_2119061
  have hstable : (prefixWord ++ tailWord_2119061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2119061).length < 2 ^ (prefixWord ++ tailWord_2119061).sum := by decide
  have hdescent : baseEnd_2119061 < baseStart_2119061 := by decide
  rcases family_descends (prefixWord ++ tailWord_2119061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2119091 : List Nat := [1, 1, 1, 2, 3, 1, 1, 4, 1, 7]
def baseStart_2119091 : Nat := 118140960795 + 2119091 * 2 ^ 59
def prefixEnd_2119091 : Nat := 4983230072969 + 3 ^ 40 * 2119091 * 2
def baseEnd_2119091 : Nat := 725408155744582520277989

theorem tailTrace_2119091 : CollatzResearch.WordTrace tailWord_2119091 prefixEnd_2119091 725408155744582520277989 := by
  unfold tailWord_2119091
  simp only [CollatzResearch.WordTrace]
  refine ⟨77289598365902693774629127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51526398910601795849752751 77289598365902693774629127)
  ·
    refine ⟨115934397548854040661943691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77289598365902693774629127 115934397548854040661943691)
    ·
      refine ⟨173901596323281060992915537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115934397548854040661943691 173901596323281060992915537)
      ·
        refine ⟨130426197242460795744686653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 173901596323281060992915537 130426197242460795744686653)
        ·
          refine ⟨48909823965922798404257495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 130426197242460795744686653 48909823965922798404257495)
          ·
            refine ⟨73364735948884197606386243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48909823965922798404257495 73364735948884197606386243)
            ·
              refine ⟨110047103923326296409579365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73364735948884197606386243 110047103923326296409579365)
              ·
                refine ⟨20633831985623680576796131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 110047103923326296409579365 20633831985623680576796131)
                ·
                  refine ⟨30950747978435520865194197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20633831985623680576796131 30950747978435520865194197)
                  ·
                    refine ⟨725408155744582520277989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30950747978435520865194197 725408155744582520277989)
                    ·
                      rfl

theorem cell22_2119091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 4, 1, 7].length) (baseStart_2119091 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2119091 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2119091 prefixEnd_2119091 := by exact prefixLift 2119091
  have htrace : WordTrace (prefixWord ++ tailWord_2119091) baseStart_2119091 baseEnd_2119091 := by
    simpa [prefixWord, tailWord_2119091, baseEnd_2119091] using wordTrace_append hprefix tailTrace_2119091
  have hstable : (prefixWord ++ tailWord_2119091).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2119091).length < 2 ^ (prefixWord ++ tailWord_2119091).sum := by decide
  have hdescent : baseEnd_2119091 < baseStart_2119091 := by decide
  rcases family_descends (prefixWord ++ tailWord_2119091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2119093 : List Nat := [1, 3, 3, 2, 2, 1, 1, 2, 7]
def baseStart_2119093 : Nat := 118140960795 + 2119093 * 2 ^ 59
def prefixEnd_2119093 : Nat := 4983230072969 + 3 ^ 40 * 2119093 * 2
def baseEnd_2119093 : Nat := 241802946795151727242661

theorem tailTrace_2119093 : CollatzResearch.WordTrace tailWord_2119093 prefixEnd_2119093 241802946795151727242661 := by
  unfold tailWord_2119093
  simp only [CollatzResearch.WordTrace]
  refine ⟨77289671311895448116201933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51526447541263632077467955 77289671311895448116201933)
  ·
    refine ⟨28983626741960793043575725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77289671311895448116201933 28983626741960793043575725)
    ·
      refine ⟨10868860028235297391340897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28983626741960793043575725 10868860028235297391340897)
      ·
        refine ⟨8151645021176473043505673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10868860028235297391340897 8151645021176473043505673)
        ·
          refine ⟨6113733765882354782629255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8151645021176473043505673 6113733765882354782629255)
          ·
            refine ⟨9170600648823532173943883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6113733765882354782629255 9170600648823532173943883)
            ·
              refine ⟨13755900973235298260915825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9170600648823532173943883 13755900973235298260915825)
              ·
                refine ⟨10316925729926473695686869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13755900973235298260915825 10316925729926473695686869)
                ·
                  refine ⟨241802946795151727242661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10316925729926473695686869 241802946795151727242661)
                  ·
                    rfl

theorem cell22_2119093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 2, 7].length) (baseStart_2119093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2119093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2119093 prefixEnd_2119093 := by exact prefixLift 2119093
  have htrace : WordTrace (prefixWord ++ tailWord_2119093) baseStart_2119093 baseEnd_2119093 := by
    simpa [prefixWord, tailWord_2119093, baseEnd_2119093] using wordTrace_append hprefix tailTrace_2119093
  have hstable : (prefixWord ++ tailWord_2119093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2119093).length < 2 ^ (prefixWord ++ tailWord_2119093).sum := by decide
  have hdescent : baseEnd_2119093 < baseStart_2119093 := by decide
  rcases family_descends (prefixWord ++ tailWord_2119093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2119114 : List Nat := [3, 1, 2, 1, 2, 4, 3, 2, 1, 3]
def baseStart_2119114 : Nat := 118140960795 + 2119114 * 2 ^ 59
def prefixEnd_2119114 : Nat := 4983230072969 + 3 ^ 40 * 2119114 * 2
def baseEnd_2119114 : Nat := 725416029114618126952919

theorem tailTrace_2119114 : CollatzResearch.WordTrace tailWord_2119114 prefixEnd_2119114 725416029114618126952919 := by
  unfold tailWord_2119114
  simp only [CollatzResearch.WordTrace]
  refine ⟨19322609311204842175679099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51526958163212912468477597 19322609311204842175679099)
  ·
    refine ⟨28983913966807263263518649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19322609311204842175679099 28983913966807263263518649)
    ·
      refine ⟨21737935475105447447638987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28983913966807263263518649 21737935475105447447638987)
      ·
        refine ⟨32606903212658171171458481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21737935475105447447638987 32606903212658171171458481)
        ·
          refine ⟨24455177409493628378593861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32606903212658171171458481 24455177409493628378593861)
          ·
            refine ⟨4585345764280055320986349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24455177409493628378593861 4585345764280055320986349)
            ·
              refine ⟨1719504661605020745369881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4585345764280055320986349 1719504661605020745369881)
              ·
                refine ⟨1289628496203765559027411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1719504661605020745369881 1289628496203765559027411)
                ·
                  refine ⟨1934442744305648338541117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1289628496203765559027411 1934442744305648338541117)
                  ·
                    refine ⟨725416029114618126952919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1934442744305648338541117 725416029114618126952919)
                    ·
                      rfl

theorem cell22_2119114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 3, 2, 1, 3].length) (baseStart_2119114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2119114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2119114 prefixEnd_2119114 := by exact prefixLift 2119114
  have htrace : WordTrace (prefixWord ++ tailWord_2119114) baseStart_2119114 baseEnd_2119114 := by
    simpa [prefixWord, tailWord_2119114, baseEnd_2119114] using wordTrace_append hprefix tailTrace_2119114
  have hstable : (prefixWord ++ tailWord_2119114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2119114).length < 2 ^ (prefixWord ++ tailWord_2119114).sum := by decide
  have hdescent : baseEnd_2119114 < baseStart_2119114 := by decide
  rcases family_descends (prefixWord ++ tailWord_2119114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2119153 : List Nat := [1, 2, 2, 2, 3, 2, 1, 1, 3, 5]
def baseStart_2119153 : Nat := 118140960795 + 2119153 * 2 ^ 59
def prefixEnd_2119153 : Nat := 4983230072969 + 3 ^ 40 * 2119153 * 2
def baseEnd_2119153 : Nat := 725429379611635025227799

theorem tailTrace_2119153 : CollatzResearch.WordTrace tailWord_2119153 prefixEnd_2119153 725429379611635025227799 := by
  unfold tailWord_2119153
  simp only [CollatzResearch.WordTrace]
  refine ⟨77291859691678078363386113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51527906461118718908924075 77291859691678078363386113)
  ·
    refine ⟨57968894768758558772539585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77291859691678078363386113 57968894768758558772539585)
    ·
      refine ⟨43476671076568919079404689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57968894768758558772539585 43476671076568919079404689)
      ·
        refine ⟨32607503307426689309553517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43476671076568919079404689 32607503307426689309553517)
        ·
          refine ⟨12227813740285008491082569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32607503307426689309553517 12227813740285008491082569)
          ·
            refine ⟨9170860305213756368311927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12227813740285008491082569 9170860305213756368311927)
            ·
              refine ⟨13756290457820634552467891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9170860305213756368311927 13756290457820634552467891)
              ·
                refine ⟨20634435686730951828701837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13756290457820634552467891 20634435686730951828701837)
                ·
                  refine ⟨7737913382524106935763189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20634435686730951828701837 7737913382524106935763189)
                  ·
                    refine ⟨725429379611635025227799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7737913382524106935763189 725429379611635025227799)
                    ·
                      rfl

theorem cell22_2119153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 1, 3, 5].length) (baseStart_2119153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2119153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2119153 prefixEnd_2119153 := by exact prefixLift 2119153
  have htrace : WordTrace (prefixWord ++ tailWord_2119153) baseStart_2119153 baseEnd_2119153 := by
    simpa [prefixWord, tailWord_2119153, baseEnd_2119153] using wordTrace_append hprefix tailTrace_2119153
  have hstable : (prefixWord ++ tailWord_2119153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2119153).length < 2 ^ (prefixWord ++ tailWord_2119153).sum := by decide
  have hdescent : baseEnd_2119153 < baseStart_2119153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2119153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2119238 : List Nat := [6, 1, 1, 1, 3, 1, 3, 1, 2, 3]
def baseStart_2119238 : Nat := 118140960795 + 2119238 * 2 ^ 59
def prefixEnd_2119238 : Nat := 4983230072969 + 3 ^ 40 * 2119238 * 2
def baseEnd_2119238 : Nat := 725458476848723136852539

theorem tailTrace_2119238 : CollatzResearch.WordTrace tailWord_2119238 prefixEnd_2119238 725458476848723136852539 := by
  unfold tailWord_2119238
  simp only [CollatzResearch.WordTrace]
  refine ⟨2415467496761566808757199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 51529973264246758586820245 2415467496761566808757199)
  ·
    refine ⟨3623201245142350213135799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2415467496761566808757199 3623201245142350213135799)
    ·
      refine ⟨5434801867713525319703699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3623201245142350213135799 5434801867713525319703699)
      ·
        refine ⟨8152202801570287979555549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5434801867713525319703699 8152202801570287979555549)
        ·
          refine ⟨3057076050588857992333331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8152202801570287979555549 3057076050588857992333331)
          ·
            refine ⟨4585614075883286988499997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3057076050588857992333331 4585614075883286988499997)
            ·
              refine ⟨1719605278456232620687499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4585614075883286988499997 1719605278456232620687499)
              ·
                refine ⟨2579407917684348931031249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1719605278456232620687499 2579407917684348931031249)
                ·
                  refine ⟨1934555938263261698273437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2579407917684348931031249 1934555938263261698273437)
                  ·
                    refine ⟨725458476848723136852539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1934555938263261698273437 725458476848723136852539)
                    ·
                      rfl

theorem cell22_2119238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 3, 1, 2, 3].length) (baseStart_2119238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2119238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2119238 prefixEnd_2119238 := by exact prefixLift 2119238
  have htrace : WordTrace (prefixWord ++ tailWord_2119238) baseStart_2119238 baseEnd_2119238 := by
    simpa [prefixWord, tailWord_2119238, baseEnd_2119238] using wordTrace_append hprefix tailTrace_2119238
  have hstable : (prefixWord ++ tailWord_2119238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2119238).length < 2 ^ (prefixWord ++ tailWord_2119238).sum := by decide
  have hdescent : baseEnd_2119238 < baseStart_2119238 := by decide
  rcases family_descends (prefixWord ++ tailWord_2119238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2119258 : List Nat := [3, 1, 1, 2, 1, 1, 1, 2, 2, 8]
def baseStart_2119258 : Nat := 118140960795 + 2119258 * 2 ^ 59
def prefixEnd_2119258 : Nat := 4983230072969 + 3 ^ 40 * 2119258 * 2
def baseEnd_2119258 : Nat := 725465323257449751352477

theorem tailTrace_2119258 : CollatzResearch.WordTrace tailWord_2119258 prefixEnd_2119258 725465323257449751352477 := by
  unfold tailWord_2119258
  simp only [CollatzResearch.WordTrace]
  refine ⟨19323922339074420323989607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51530459570865120863972285 19323922339074420323989607)
  ·
    refine ⟨28985883508611630485984411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19323922339074420323989607 28985883508611630485984411)
    ·
      refine ⟨43478825262917445728976617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28985883508611630485984411 43478825262917445728976617)
      ·
        refine ⟨32609118947188084296732463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43478825262917445728976617 32609118947188084296732463)
        ·
          refine ⟨48913678420782126445098695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32609118947188084296732463 48913678420782126445098695)
          ·
            refine ⟨73370517631173189667648043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48913678420782126445098695 73370517631173189667648043)
            ·
              refine ⟨110055776446759784501472065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73370517631173189667648043 110055776446759784501472065)
              ·
                refine ⟨82541832335069838376104049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 110055776446759784501472065 82541832335069838376104049)
                ·
                  refine ⟨61906374251302378782078037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 82541832335069838376104049 61906374251302378782078037)
                  ·
                    refine ⟨725465323257449751352477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 61906374251302378782078037 725465323257449751352477)
                    ·
                      rfl

theorem cell22_2119258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 2, 8].length) (baseStart_2119258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2119258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2119258 prefixEnd_2119258 := by exact prefixLift 2119258
  have htrace : WordTrace (prefixWord ++ tailWord_2119258) baseStart_2119258 baseEnd_2119258 := by
    simpa [prefixWord, tailWord_2119258, baseEnd_2119258] using wordTrace_append hprefix tailTrace_2119258
  have hstable : (prefixWord ++ tailWord_2119258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2119258).length < 2 ^ (prefixWord ++ tailWord_2119258).sum := by decide
  have hdescent : baseEnd_2119258 < baseStart_2119258 := by decide
  rcases family_descends (prefixWord ++ tailWord_2119258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2119273 : List Nat := [1, 2, 1, 1, 1, 4, 2, 2, 8]
def baseStart_2119273 : Nat := 118140960795 + 2119273 * 2 ^ 59
def prefixEnd_2119273 : Nat := 4983230072969 + 3 ^ 40 * 2119273 * 2
def baseEnd_2119273 : Nat := 241823486021331570742477

theorem tailTrace_2119273 : CollatzResearch.WordTrace tailWord_2119273 prefixEnd_2119273 241823486021331570742477 := by
  unfold tailWord_2119273
  simp only [CollatzResearch.WordTrace]
  refine ⟨77296236451243338857754473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51530824300828892571836315 77296236451243338857754473)
  ·
    refine ⟨57972177338432504143315855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77296236451243338857754473 57972177338432504143315855)
    ·
      refine ⟨86958266007648756214973783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57972177338432504143315855 86958266007648756214973783)
      ·
        refine ⟨130437399011473134322460675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86958266007648756214973783 130437399011473134322460675)
        ·
          refine ⟨195656098517209701483691013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130437399011473134322460675 195656098517209701483691013)
          ·
            refine ⟨36685518471976819028192065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 195656098517209701483691013 36685518471976819028192065)
            ·
              refine ⟨27514138853982614271144049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36685518471976819028192065 27514138853982614271144049)
              ·
                refine ⟨20635604140486960703358037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27514138853982614271144049 20635604140486960703358037)
                ·
                  refine ⟨241823486021331570742477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20635604140486960703358037 241823486021331570742477)
                  ·
                    rfl

theorem cell22_2119273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 2, 8].length) (baseStart_2119273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2119273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2119273 prefixEnd_2119273 := by exact prefixLift 2119273
  have htrace : WordTrace (prefixWord ++ tailWord_2119273) baseStart_2119273 baseEnd_2119273 := by
    simpa [prefixWord, tailWord_2119273, baseEnd_2119273] using wordTrace_append hprefix tailTrace_2119273
  have hstable : (prefixWord ++ tailWord_2119273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2119273).length < 2 ^ (prefixWord ++ tailWord_2119273).sum := by decide
  have hdescent : baseEnd_2119273 < baseStart_2119273 := by decide
  rcases family_descends (prefixWord ++ tailWord_2119273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2119288 : List Nat := [2, 1, 2, 1, 1, 1, 2, 1, 2, 9]
def baseStart_2119288 : Nat := 118140960795 + 2119288 * 2 ^ 59
def prefixEnd_2119288 : Nat := 4983230072969 + 3 ^ 40 * 2119288 * 2
def baseEnd_2119288 : Nat := 725475592870539673102385

theorem tailTrace_2119288 : CollatzResearch.WordTrace tailWord_2119288 prefixEnd_2119288 725475592870539673102385 := by
  unfold tailWord_2119288
  simp only [CollatzResearch.WordTrace]
  refine ⟨38648391773094498209775259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51531189030792664279700345 38648391773094498209775259)
  ·
    refine ⟨57972587659641747314662889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38648391773094498209775259 57972587659641747314662889)
    ·
      refine ⟨43479440744731310485997167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57972587659641747314662889 43479440744731310485997167)
      ·
        refine ⟨65219161117096965728995751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43479440744731310485997167 65219161117096965728995751)
        ·
          refine ⟨97828741675645448593493627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65219161117096965728995751 97828741675645448593493627)
          ·
            refine ⟨146743112513468172890240441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97828741675645448593493627 146743112513468172890240441)
            ·
              refine ⟨110057334385101129667680331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 146743112513468172890240441 110057334385101129667680331)
              ·
                refine ⟨165086001577651694501520497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 110057334385101129667680331 165086001577651694501520497)
                ·
                  refine ⟨123814501183238770876140373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 165086001577651694501520497 123814501183238770876140373)
                  ·
                    refine ⟨725475592870539673102385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 123814501183238770876140373 725475592870539673102385)
                    ·
                      rfl

theorem cell22_2119288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 2, 9].length) (baseStart_2119288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2119288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2119288 prefixEnd_2119288 := by exact prefixLift 2119288
  have htrace : WordTrace (prefixWord ++ tailWord_2119288) baseStart_2119288 baseEnd_2119288 := by
    simpa [prefixWord, tailWord_2119288, baseEnd_2119288] using wordTrace_append hprefix tailTrace_2119288
  have hstable : (prefixWord ++ tailWord_2119288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2119288).length < 2 ^ (prefixWord ++ tailWord_2119288).sum := by decide
  have hdescent : baseEnd_2119288 < baseStart_2119288 := by decide
  rcases family_descends (prefixWord ++ tailWord_2119288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2119326 : List Nat := [4, 3, 1, 1, 1, 3, 3, 1, 1, 4]
def baseStart_2119326 : Nat := 118140960795 + 2119326 * 2 ^ 59
def prefixEnd_2119326 : Nat := 4983230072969 + 3 ^ 40 * 2119326 * 2
def baseEnd_2119326 : Nat := 725488601047120240652269

theorem tailTrace_2119326 : CollatzResearch.WordTrace tailWord_2119326 prefixEnd_2119326 725488601047120240652269 := by
  unfold tailWord_2119326
  simp only [CollatzResearch.WordTrace]
  refine ⟨9662271190006416113679229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51532113013367552606289221 9662271190006416113679229)
  ·
    refine ⟨3623351696252406042629711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9662271190006416113679229 3623351696252406042629711)
    ·
      refine ⟨5435027544378609063944567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3623351696252406042629711 5435027544378609063944567)
      ·
        refine ⟨8152541316567913595916851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5435027544378609063944567 8152541316567913595916851)
        ·
          refine ⟨12228811974851870393875277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8152541316567913595916851 12228811974851870393875277)
          ·
            refine ⟨4585804490569451397703229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12228811974851870393875277 4585804490569451397703229)
            ·
              refine ⟨1719676683963544274138711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4585804490569451397703229 1719676683963544274138711)
              ·
                refine ⟨2579515025945316411208067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1719676683963544274138711 2579515025945316411208067)
                ·
                  refine ⟨3869272538917974616812101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2579515025945316411208067 3869272538917974616812101)
                  ·
                    refine ⟨725488601047120240652269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3869272538917974616812101 725488601047120240652269)
                    ·
                      rfl

theorem cell22_2119326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 3, 1, 1, 4].length) (baseStart_2119326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2119326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2119326 prefixEnd_2119326 := by exact prefixLift 2119326
  have htrace : WordTrace (prefixWord ++ tailWord_2119326) baseStart_2119326 baseEnd_2119326 := by
    simpa [prefixWord, tailWord_2119326, baseEnd_2119326] using wordTrace_append hprefix tailTrace_2119326
  have hstable : (prefixWord ++ tailWord_2119326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2119326).length < 2 ^ (prefixWord ++ tailWord_2119326).sum := by decide
  have hdescent : baseEnd_2119326 < baseStart_2119326 := by decide
  rcases family_descends (prefixWord ++ tailWord_2119326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2119367 : List Nat := [1, 1, 4, 1, 1, 1, 5, 2, 3, 3]
def baseStart_2119367 : Nat := 118140960795 + 2119367 * 2 ^ 59
def prefixEnd_2119367 : Nat := 4983230072969 + 3 ^ 40 * 2119367 * 2
def baseEnd_2119367 : Nat := 725502636185009800377143

theorem tailTrace_2119367 : CollatzResearch.WordTrace tailWord_2119367 prefixEnd_2119367 725502636185009800377143 := by
  unfold tailWord_2119367
  simp only [CollatzResearch.WordTrace]
  refine ⟨77299664912902792911676355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51533109941935195274450903 77299664912902792911676355)
  ·
    refine ⟨115949497369354189367514533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77299664912902792911676355 115949497369354189367514533)
    ·
      refine ⟨21740530756753910506408975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 115949497369354189367514533 21740530756753910506408975)
      ·
        refine ⟨32610796135130865759613463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21740530756753910506408975 32610796135130865759613463)
        ·
          refine ⟨48916194202696298639420195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32610796135130865759613463 48916194202696298639420195)
          ·
            refine ⟨73374291304044447959130293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48916194202696298639420195 73374291304044447959130293)
            ·
              refine ⟨6878839809754166996168465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 73374291304044447959130293 6878839809754166996168465)
              ·
                refine ⟨5159129857315625247126349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6878839809754166996168465 5159129857315625247126349)
                ·
                  refine ⟨1934673696493359467672381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5159129857315625247126349 1934673696493359467672381)
                  ·
                    refine ⟨725502636185009800377143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1934673696493359467672381 725502636185009800377143)
                    ·
                      rfl

theorem cell22_2119367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 2, 3, 3].length) (baseStart_2119367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2119367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2119367 prefixEnd_2119367 := by exact prefixLift 2119367
  have htrace : WordTrace (prefixWord ++ tailWord_2119367) baseStart_2119367 baseEnd_2119367 := by
    simpa [prefixWord, tailWord_2119367, baseEnd_2119367] using wordTrace_append hprefix tailTrace_2119367
  have hstable : (prefixWord ++ tailWord_2119367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2119367).length < 2 ^ (prefixWord ++ tailWord_2119367).sum := by decide
  have hdescent : baseEnd_2119367 < baseStart_2119367 := by decide
  rcases family_descends (prefixWord ++ tailWord_2119367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2119427 : List Nat := [1, 1, 1, 3, 2, 2, 3, 4, 1, 4]
def baseStart_2119427 : Nat := 118140960795 + 2119427 * 2 ^ 59
def prefixEnd_2119427 : Nat := 4983230072969 + 3 ^ 40 * 2119427 * 2
def baseEnd_2119427 : Nat := 725523175411189643876959

theorem tailTrace_2119427 : CollatzResearch.WordTrace tailWord_2119427 prefixEnd_2119427 725523175411189643876959 := by
  unfold tailWord_2119427
  simp only [CollatzResearch.WordTrace]
  refine ⟨77301853292685423158860535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51534568861790282105907023 77301853292685423158860535)
  ·
    refine ⟨115952779939028134738290803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77301853292685423158860535 115952779939028134738290803)
    ·
      refine ⟨173929169908542202107436205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115952779939028134738290803 173929169908542202107436205)
      ·
        refine ⟨65223438715703325790288577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 173929169908542202107436205 65223438715703325790288577)
        ·
          refine ⟨48917579036777494342716433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65223438715703325790288577 48917579036777494342716433)
          ·
            refine ⟨36688184277583120757037325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48917579036777494342716433 36688184277583120757037325)
            ·
              refine ⟨13758069104093670283888997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36688184277583120757037325 13758069104093670283888997)
              ·
                refine ⟨2579637957017563178229187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13758069104093670283888997 2579637957017563178229187)
                ·
                  refine ⟨3869456935526344767343781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2579637957017563178229187 3869456935526344767343781)
                  ·
                    refine ⟨725523175411189643876959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3869456935526344767343781 725523175411189643876959)
                    ·
                      rfl

theorem cell22_2119427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 4, 1, 4].length) (baseStart_2119427 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2119427 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2119427 prefixEnd_2119427 := by exact prefixLift 2119427
  have htrace : WordTrace (prefixWord ++ tailWord_2119427) baseStart_2119427 baseEnd_2119427 := by
    simpa [prefixWord, tailWord_2119427, baseEnd_2119427] using wordTrace_append hprefix tailTrace_2119427
  have hstable : (prefixWord ++ tailWord_2119427).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2119427).length < 2 ^ (prefixWord ++ tailWord_2119427).sum := by decide
  have hdescent : baseEnd_2119427 < baseStart_2119427 := by decide
  rcases family_descends (prefixWord ++ tailWord_2119427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2119478 : List Nat := [5, 1, 2, 2, 1, 3, 1, 2, 1, 4]
def baseStart_2119478 : Nat := 118140960795 + 2119478 * 2 ^ 59
def prefixEnd_2119478 : Nat := 4983230072969 + 3 ^ 40 * 2119478 * 2
def baseEnd_2119478 : Nat := 725540633753442510851803

theorem tailTrace_2119478 : CollatzResearch.WordTrace tailWord_2119478 prefixEnd_2119478 725540633753442510851803 := by
  unfold tailWord_2119478
  simp only [CollatzResearch.WordTrace]
  refine ⟨4831482088468791179310443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 51535808943667105912644725 4831482088468791179310443)
  ·
    refine ⟨7247223132703186768965665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4831482088468791179310443 7247223132703186768965665)
    ·
      refine ⟨5435417349527390076724249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7247223132703186768965665 5435417349527390076724249)
      ·
        refine ⟨4076563012145542557543187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5435417349527390076724249 4076563012145542557543187)
        ·
          refine ⟨6114844518218313836314781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4076563012145542557543187 6114844518218313836314781)
          ·
            refine ⟨2293066694331867688618043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6114844518218313836314781 2293066694331867688618043)
            ·
              refine ⟨3439600041497801532927065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2293066694331867688618043 3439600041497801532927065)
              ·
                refine ⟨2579700031123351149695299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3439600041497801532927065 2579700031123351149695299)
                ·
                  refine ⟨3869550046685026724542949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2579700031123351149695299 3869550046685026724542949)
                  ·
                    refine ⟨725540633753442510851803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3869550046685026724542949 725540633753442510851803)
                    ·
                      rfl

theorem cell22_2119478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 1, 2, 1, 4].length) (baseStart_2119478 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2119478 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2119478 prefixEnd_2119478 := by exact prefixLift 2119478
  have htrace : WordTrace (prefixWord ++ tailWord_2119478) baseStart_2119478 baseEnd_2119478 := by
    simpa [prefixWord, tailWord_2119478, baseEnd_2119478] using wordTrace_append hprefix tailTrace_2119478
  have hstable : (prefixWord ++ tailWord_2119478).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2119478).length < 2 ^ (prefixWord ++ tailWord_2119478).sum := by decide
  have hdescent : baseEnd_2119478 < baseStart_2119478 := by decide
  rcases family_descends (prefixWord ++ tailWord_2119478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2119566 : List Nat := [4, 1, 1, 5, 1, 1, 1, 1, 7]
def baseStart_2119566 : Nat := 118140960795 + 2119566 * 2 ^ 59
def prefixEnd_2119566 : Nat := 4983230072969 + 3 ^ 40 * 2119566 * 2
def baseEnd_2119566 : Nat := 241856919317279871550511

theorem tailTrace_2119566 : CollatzResearch.WordTrace tailWord_2119566 prefixEnd_2119566 241856919317279871550511 := by
  unfold tailWord_2119566
  simp only [CollatzResearch.WordTrace]
  refine ⟨9663365379897731237271319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51537948692787899932113701 9663365379897731237271319)
  ·
    refine ⟨14495048069846596855906979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9663365379897731237271319 14495048069846596855906979)
    ·
      refine ⟨21742572104769895283860469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14495048069846596855906979 21742572104769895283860469)
      ·
        refine ⟨2038366134822177682861919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21742572104769895283860469 2038366134822177682861919)
        ·
          refine ⟨3057549202233266524292879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2038366134822177682861919 3057549202233266524292879)
          ·
            refine ⟨4586323803349899786439319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3057549202233266524292879 4586323803349899786439319)
            ·
              refine ⟨6879485705024849679658979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4586323803349899786439319 6879485705024849679658979)
              ·
                refine ⟨10319228557537274519488469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6879485705024849679658979 10319228557537274519488469)
                ·
                  refine ⟨241856919317279871550511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10319228557537274519488469 241856919317279871550511)
                  ·
                    rfl

theorem cell22_2119566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 1, 7].length) (baseStart_2119566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2119566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2119566 prefixEnd_2119566 := by exact prefixLift 2119566
  have htrace : WordTrace (prefixWord ++ tailWord_2119566) baseStart_2119566 baseEnd_2119566 := by
    simpa [prefixWord, tailWord_2119566, baseEnd_2119566] using wordTrace_append hprefix tailTrace_2119566
  have hstable : (prefixWord ++ tailWord_2119566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2119566).length < 2 ^ (prefixWord ++ tailWord_2119566).sum := by decide
  have hdescent : baseEnd_2119566 < baseStart_2119566 := by decide
  rcases family_descends (prefixWord ++ tailWord_2119566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2119577 : List Nat := [1, 2, 1, 2, 1, 3, 3, 3, 6]
def baseStart_2119577 : Nat := 118140960795 + 2119577 * 2 ^ 59
def prefixEnd_2119577 : Nat := 4983230072969 + 3 ^ 40 * 2119577 * 2
def baseEnd_2119577 : Nat := 241858174492213084208833

theorem tailTrace_2119577 : CollatzResearch.WordTrace tailWord_2119577 prefixEnd_2119577 241858174492213084208833 := by
  unfold tailWord_2119577
  simp only [CollatzResearch.WordTrace]
  refine ⟨77307324242141998776820985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51538216161427999184547323 77307324242141998776820985)
  ·
    refine ⟨57980493181606499082615739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77307324242141998776820985 57980493181606499082615739)
    ·
      refine ⟨86970739772409748623923609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57980493181606499082615739 86970739772409748623923609)
      ·
        refine ⟨65228054829307311467942707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86970739772409748623923609 65228054829307311467942707)
        ·
          refine ⟨97842082243960967201914061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65228054829307311467942707 97842082243960967201914061)
          ·
            refine ⟨36690780841485362700717773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 97842082243960967201914061 36690780841485362700717773)
            ·
              refine ⟨13759042815557011012769165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36690780841485362700717773 13759042815557011012769165)
              ·
                refine ⟨5159641055833879129788437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13759042815557011012769165 5159641055833879129788437)
                ·
                  refine ⟨241858174492213084208833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5159641055833879129788437 241858174492213084208833)
                  ·
                    rfl

theorem cell22_2119577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 3, 6].length) (baseStart_2119577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2119577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2119577 prefixEnd_2119577 := by exact prefixLift 2119577
  have htrace : WordTrace (prefixWord ++ tailWord_2119577) baseStart_2119577 baseEnd_2119577 := by
    simpa [prefixWord, tailWord_2119577, baseEnd_2119577] using wordTrace_append hprefix tailTrace_2119577
  have hstable : (prefixWord ++ tailWord_2119577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2119577).length < 2 ^ (prefixWord ++ tailWord_2119577).sum := by decide
  have hdescent : baseEnd_2119577 < baseStart_2119577 := by decide
  rcases family_descends (prefixWord ++ tailWord_2119577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2119604 : List Nat := [2, 5, 2, 1, 3, 1, 1, 3, 1, 3]
def baseStart_2119604 : Nat := 118140960795 + 2119604 * 2 ^ 59
def prefixEnd_2119604 : Nat := 4983230072969 + 3 ^ 40 * 2119604 * 2
def baseEnd_2119604 : Nat := 725583766128420182201417

theorem tailTrace_2119604 : CollatzResearch.WordTrace tailWord_2119604 prefixEnd_2119604 725583766128420182201417 := by
  unfold tailWord_2119604
  simp only [CollatzResearch.WordTrace]
  refine ⟨38654154506522091194026933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51538872675362788258702577 38654154506522091194026933)
  ·
    refine ⟨3623826984986446049440025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38654154506522091194026933 3623826984986446049440025)
    ·
      refine ⟨2717870238739834537080019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3623826984986446049440025 2717870238739834537080019)
      ·
        refine ⟨4076805358109751805620029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2717870238739834537080019 4076805358109751805620029)
        ·
          refine ⟨1528802009291156927107511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4076805358109751805620029 1528802009291156927107511)
          ·
            refine ⟨2293203013936735390661267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1528802009291156927107511 2293203013936735390661267)
            ·
              refine ⟨3439804520905103085991901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2293203013936735390661267 3439804520905103085991901)
              ·
                refine ⟨1289926695339413657246963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3439804520905103085991901 1289926695339413657246963)
                ·
                  refine ⟨1934890043009120485870445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1289926695339413657246963 1934890043009120485870445)
                  ·
                    refine ⟨725583766128420182201417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1934890043009120485870445 725583766128420182201417)
                    ·
                      rfl

theorem cell22_2119604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_2119604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2119604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2119604 prefixEnd_2119604 := by exact prefixLift 2119604
  have htrace : WordTrace (prefixWord ++ tailWord_2119604) baseStart_2119604 baseEnd_2119604 := by
    simpa [prefixWord, tailWord_2119604, baseEnd_2119604] using wordTrace_append hprefix tailTrace_2119604
  have hstable : (prefixWord ++ tailWord_2119604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2119604).length < 2 ^ (prefixWord ++ tailWord_2119604).sum := by decide
  have hdescent : baseEnd_2119604 < baseStart_2119604 := by decide
  rcases family_descends (prefixWord ++ tailWord_2119604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2119609 : List Nat := [1, 2, 1, 4, 2, 1, 1, 1, 6, 3]
def baseStart_2119609 : Nat := 118140960795 + 2119609 * 2 ^ 59
def prefixEnd_2119609 : Nat := 4983230072969 + 3 ^ 40 * 2119609 * 2
def baseEnd_2119609 : Nat := 725585477730601835826401

theorem tailTrace_2119609 : CollatzResearch.WordTrace tailWord_2119609 prefixEnd_2119609 725585477730601835826401 := by
  unfold tailWord_2119609
  simp only [CollatzResearch.WordTrace]
  refine ⟨77308491378026068241985881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51538994252017378827990587 77308491378026068241985881)
  ·
    refine ⟨57981368533519551181489411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77308491378026068241985881 57981368533519551181489411)
    ·
      refine ⟨86972052800279326772234117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57981368533519551181489411 86972052800279326772234117)
      ·
        refine ⟨16307259900052373769793897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 86972052800279326772234117 16307259900052373769793897)
        ·
          refine ⟨12230444925039280327345423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16307259900052373769793897 12230444925039280327345423)
          ·
            refine ⟨18345667387558920491018135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12230444925039280327345423 18345667387558920491018135)
            ·
              refine ⟨27518501081338380736527203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18345667387558920491018135 27518501081338380736527203)
              ·
                refine ⟨41277751622007571104790805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27518501081338380736527203 41277751622007571104790805)
                ·
                  refine ⟨1934894607281604895537069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 41277751622007571104790805 1934894607281604895537069)
                  ·
                    refine ⟨725585477730601835826401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1934894607281604895537069 725585477730601835826401)
                    ·
                      rfl

theorem cell22_2119609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 6, 3].length) (baseStart_2119609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2119609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2119609 prefixEnd_2119609 := by exact prefixLift 2119609
  have htrace : WordTrace (prefixWord ++ tailWord_2119609) baseStart_2119609 baseEnd_2119609 := by
    simpa [prefixWord, tailWord_2119609, baseEnd_2119609] using wordTrace_append hprefix tailTrace_2119609
  have hstable : (prefixWord ++ tailWord_2119609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2119609).length < 2 ^ (prefixWord ++ tailWord_2119609).sum := by decide
  have hdescent : baseEnd_2119609 < baseStart_2119609 := by decide
  rcases family_descends (prefixWord ++ tailWord_2119609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2119624 : List Nat := [2, 1, 3, 1, 4, 1, 1, 1, 4, 4]
def baseStart_2119624 : Nat := 118140960795 + 2119624 * 2 ^ 59
def prefixEnd_2119624 : Nat := 4983230072969 + 3 ^ 40 * 2119624 * 2
def baseEnd_2119624 : Nat := 725590612537146796701355

theorem tailTrace_2119624 : CollatzResearch.WordTrace tailWord_2119624 prefixEnd_2119624 725590612537146796701355 := by
  unfold tailWord_2119624
  simp only [CollatzResearch.WordTrace]
  refine ⟨38654519236485862901890963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51539358981981150535854617 38654519236485862901890963)
  ·
    refine ⟨57981778854728794352836445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38654519236485862901890963 57981778854728794352836445)
    ·
      refine ⟨21743167070523297882313667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57981778854728794352836445 21743167070523297882313667)
      ·
        refine ⟨32614750605784946823470501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21743167070523297882313667 32614750605784946823470501)
        ·
          refine ⟨6115265738584677529400719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32614750605784946823470501 6115265738584677529400719)
          ·
            refine ⟨9172898607877016294101079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6115265738584677529400719 9172898607877016294101079)
            ·
              refine ⟨13759347911815524441151619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9172898607877016294101079 13759347911815524441151619)
              ·
                refine ⟨20639021867723286661727429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13759347911815524441151619 20639021867723286661727429)
                ·
                  refine ⟨3869816600198116249073893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20639021867723286661727429 3869816600198116249073893)
                  ·
                    refine ⟨725590612537146796701355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3869816600198116249073893 725590612537146796701355)
                    ·
                      rfl

theorem cell22_2119624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 1, 4, 4].length) (baseStart_2119624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2119624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2119624 prefixEnd_2119624 := by exact prefixLift 2119624
  have htrace : WordTrace (prefixWord ++ tailWord_2119624) baseStart_2119624 baseEnd_2119624 := by
    simpa [prefixWord, tailWord_2119624, baseEnd_2119624] using wordTrace_append hprefix tailTrace_2119624
  have hstable : (prefixWord ++ tailWord_2119624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2119624).length < 2 ^ (prefixWord ++ tailWord_2119624).sum := by decide
  have hdescent : baseEnd_2119624 < baseStart_2119624 := by decide
  rcases family_descends (prefixWord ++ tailWord_2119624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2119628 : List Nat := [2, 2, 1, 4, 1, 3, 3, 2, 4]
def baseStart_2119628 : Nat := 118140960795 + 2119628 * 2 ^ 59
def prefixEnd_2119628 : Nat := 4983230072969 + 3 ^ 40 * 2119628 * 2
def baseEnd_2119628 : Nat := 241863993939630706533781

theorem tailTrace_2119628 : CollatzResearch.WordTrace tailWord_2119628 prefixEnd_2119628 241863993939630706533781 := by
  unfold tailWord_2119628
  simp only [CollatzResearch.WordTrace]
  refine ⟨38654592182478617243463769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51539456243304822991285025 38654592182478617243463769)
  ·
    refine ⟨28990944136858962932597827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38654592182478617243463769 28990944136858962932597827)
    ·
      refine ⟨43486416205288444398896741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28990944136858962932597827 43486416205288444398896741)
      ·
        refine ⟨8153703038491583324793139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43486416205288444398896741 8153703038491583324793139)
        ·
          refine ⟨12230554557737374987189709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8153703038491583324793139 12230554557737374987189709)
          ·
            refine ⟨4586457959151515620196141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12230554557737374987189709 4586457959151515620196141)
            ·
              refine ⟨1719921734681818357573553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4586457959151515620196141 1719921734681818357573553)
              ·
                refine ⟨1289941301011363768180165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1719921734681818357573553 1289941301011363768180165)
                ·
                  refine ⟨241863993939630706533781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1289941301011363768180165 241863993939630706533781)
                  ·
                    rfl

theorem cell22_2119628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 3, 2, 4].length) (baseStart_2119628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2119628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2119628 prefixEnd_2119628 := by exact prefixLift 2119628
  have htrace : WordTrace (prefixWord ++ tailWord_2119628) baseStart_2119628 baseEnd_2119628 := by
    simpa [prefixWord, tailWord_2119628, baseEnd_2119628] using wordTrace_append hprefix tailTrace_2119628
  have hstable : (prefixWord ++ tailWord_2119628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2119628).length < 2 ^ (prefixWord ++ tailWord_2119628).sum := by decide
  have hdescent : baseEnd_2119628 < baseStart_2119628 := by decide
  rcases family_descends (prefixWord ++ tailWord_2119628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2119667 : List Nat := [1, 1, 1, 2, 2, 2, 1, 3, 9]
def baseStart_2119667 : Nat := 118140960795 + 2119667 * 2 ^ 59
def prefixEnd_2119667 : Nat := 4983230072969 + 3 ^ 40 * 2119667 * 2
def baseEnd_2119667 : Nat := 241868444105303005958741

theorem tailTrace_2119667 : CollatzResearch.WordTrace tailWord_2119667 prefixEnd_2119667 241868444105303005958741 := by
  unfold tailWord_2119667
  simp only [CollatzResearch.WordTrace]
  refine ⟨77310606811815944147597255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51540404541210629431731503 77310606811815944147597255)
  ·
    refine ⟨115965910217723916221395883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77310606811815944147597255 115965910217723916221395883)
    ·
      refine ⟨173948865326585874332093825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115965910217723916221395883 173948865326585874332093825)
      ·
        refine ⟨130461648994939405749070369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 173948865326585874332093825 130461648994939405749070369)
        ·
          refine ⟨97846236746204554311802777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130461648994939405749070369 97846236746204554311802777)
          ·
            refine ⟨73384677559653415733852083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97846236746204554311802777 73384677559653415733852083)
            ·
              refine ⟨110077016339480123600778125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73384677559653415733852083 110077016339480123600778125)
              ·
                refine ⟨41278881127305046350291797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 110077016339480123600778125 41278881127305046350291797)
                ·
                  refine ⟨241868444105303005958741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 41278881127305046350291797 241868444105303005958741)
                  ·
                    rfl

theorem cell22_2119667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 9].length) (baseStart_2119667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2119667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2119667 prefixEnd_2119667 := by exact prefixLift 2119667
  have htrace : WordTrace (prefixWord ++ tailWord_2119667) baseStart_2119667 baseEnd_2119667 := by
    simpa [prefixWord, tailWord_2119667, baseEnd_2119667] using wordTrace_append hprefix tailTrace_2119667
  have hstable : (prefixWord ++ tailWord_2119667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2119667).length < 2 ^ (prefixWord ++ tailWord_2119667).sum := by decide
  have hdescent : baseEnd_2119667 < baseStart_2119667 := by decide
  rcases family_descends (prefixWord ++ tailWord_2119667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2119688 : List Nat := [2, 1, 3, 2, 1, 2, 3, 4, 1, 3]
def baseStart_2119688 : Nat := 118140960795 + 2119688 * 2 ^ 59
def prefixEnd_2119688 : Nat := 4983230072969 + 3 ^ 40 * 2119688 * 2
def baseEnd_2119688 : Nat := 725612521045071963101159

theorem tailTrace_2119688 : CollatzResearch.WordTrace tailWord_2119688 prefixEnd_2119688 725612521045071963101159 := by
  unfold tailWord_2119688
  simp only [CollatzResearch.WordTrace]
  refine ⟨38655686372369932367055859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51540915163159909822741145 38655686372369932367055859)
  ·
    refine ⟨57983529558554898550583789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38655686372369932367055859 57983529558554898550583789)
    ·
      refine ⟨21743823584458086956468921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57983529558554898550583789 21743823584458086956468921)
      ·
        refine ⟨16307867688343565217351691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21743823584458086956468921 16307867688343565217351691)
        ·
          refine ⟨24461801532515347826027537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16307867688343565217351691 24461801532515347826027537)
          ·
            refine ⟨18346351149386510869520653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24461801532515347826027537 18346351149386510869520653)
            ·
              refine ⟨6879881681019941576070245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18346351149386510869520653 6879881681019941576070245)
              ·
                refine ⟨1289977815191239045513171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6879881681019941576070245 1289977815191239045513171)
                ·
                  refine ⟨1934966722786858568269757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1289977815191239045513171 1934966722786858568269757)
                  ·
                    refine ⟨725612521045071963101159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1934966722786858568269757 725612521045071963101159)
                    ·
                      rfl

theorem cell22_2119688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 4, 1, 3].length) (baseStart_2119688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2119688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2119688 prefixEnd_2119688 := by exact prefixLift 2119688
  have htrace : WordTrace (prefixWord ++ tailWord_2119688) baseStart_2119688 baseEnd_2119688 := by
    simpa [prefixWord, tailWord_2119688, baseEnd_2119688] using wordTrace_append hprefix tailTrace_2119688
  have hstable : (prefixWord ++ tailWord_2119688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2119688).length < 2 ^ (prefixWord ++ tailWord_2119688).sum := by decide
  have hdescent : baseEnd_2119688 < baseStart_2119688 := by decide
  rcases family_descends (prefixWord ++ tailWord_2119688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2119759 : List Nat := [1, 1, 2, 1, 1, 2, 2, 4, 4, 4]
def baseStart_2119759 : Nat := 118140960795 + 2119759 * 2 ^ 59
def prefixEnd_2119759 : Nat := 4983230072969 + 3 ^ 40 * 2119759 * 2
def baseEnd_2119759 : Nat := 725636825796051444575941

theorem tailTrace_2119759 : CollatzResearch.WordTrace tailWord_2119759 prefixEnd_2119759 725636825796051444575941 := by
  unfold tailWord_2119759
  simp only [CollatzResearch.WordTrace]
  refine ⟨77313962327482643859946331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51542641551655095906630887 77313962327482643859946331)
  ·
    refine ⟨115970943491223965789919497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77313962327482643859946331 115970943491223965789919497)
    ·
      refine ⟨86978207618417974342439623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115970943491223965789919497 86978207618417974342439623)
      ·
        refine ⟨130467311427626961513659435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86978207618417974342439623 130467311427626961513659435)
        ·
          refine ⟨195700967141440442270489153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130467311427626961513659435 195700967141440442270489153)
          ·
            refine ⟨146775725356080331702866865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 195700967141440442270489153 146775725356080331702866865)
            ·
              refine ⟨110081794017060248777150149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 146775725356080331702866865 110081794017060248777150149)
              ·
                refine ⟨20640336378198796645715653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 110081794017060248777150149 20640336378198796645715653)
                ·
                  refine ⟨3870063070912274371071685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20640336378198796645715653 3870063070912274371071685)
                  ·
                    refine ⟨725636825796051444575941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3870063070912274371071685 725636825796051444575941)
                    ·
                      rfl

theorem cell22_2119759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 4, 4, 4].length) (baseStart_2119759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2119759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2119759 prefixEnd_2119759 := by exact prefixLift 2119759
  have htrace : WordTrace (prefixWord ++ tailWord_2119759) baseStart_2119759 baseEnd_2119759 := by
    simpa [prefixWord, tailWord_2119759, baseEnd_2119759] using wordTrace_append hprefix tailTrace_2119759
  have hstable : (prefixWord ++ tailWord_2119759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2119759).length < 2 ^ (prefixWord ++ tailWord_2119759).sum := by decide
  have hdescent : baseEnd_2119759 < baseStart_2119759 := by decide
  rcases family_descends (prefixWord ++ tailWord_2119759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2119853 : List Nat := [1, 5, 2, 1, 2, 1, 1, 4, 5]
def baseStart_2119853 : Nat := 118140960795 + 2119853 * 2 ^ 59
def prefixEnd_2119853 : Nat := 4983230072969 + 3 ^ 40 * 2119853 * 2
def baseEnd_2119853 : Nat := 241889667972355510908551

theorem tailTrace_2119853 : CollatzResearch.WordTrace tailWord_2119853 prefixEnd_2119853 241889667972355510908551 := by
  unfold tailWord_2119853
  simp only [CollatzResearch.WordTrace]
  refine ⟨77317390789142097913868213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51544927192761398609245475 77317390789142097913868213)
  ·
    refine ⟨7248505386482071679425145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 77317390789142097913868213 7248505386482071679425145)
    ·
      refine ⟨5436379039861553759568859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7248505386482071679425145 5436379039861553759568859)
      ·
        refine ⟨8154568559792330639353289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5436379039861553759568859 8154568559792330639353289)
        ·
          refine ⟨6115926419844247979514967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8154568559792330639353289 6115926419844247979514967)
          ·
            refine ⟨9173889629766371969272451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6115926419844247979514967 9173889629766371969272451)
            ·
              refine ⟨13760834444649557953908677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9173889629766371969272451 13760834444649557953908677)
              ·
                refine ⟨2580156458371792116357877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13760834444649557953908677 2580156458371792116357877)
                ·
                  refine ⟨241889667972355510908551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2580156458371792116357877 241889667972355510908551)
                  ·
                    rfl

theorem cell22_2119853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 4, 5].length) (baseStart_2119853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2119853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2119853 prefixEnd_2119853 := by exact prefixLift 2119853
  have htrace : WordTrace (prefixWord ++ tailWord_2119853) baseStart_2119853 baseEnd_2119853 := by
    simpa [prefixWord, tailWord_2119853, baseEnd_2119853] using wordTrace_append hprefix tailTrace_2119853
  have hstable : (prefixWord ++ tailWord_2119853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2119853).length < 2 ^ (prefixWord ++ tailWord_2119853).sum := by decide
  have hdescent : baseEnd_2119853 < baseStart_2119853 := by decide
  rcases family_descends (prefixWord ++ tailWord_2119853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2119857 : List Nat := [1, 2, 2, 5, 2, 1, 1, 4, 1, 3]
def baseStart_2119857 : Nat := 118140960795 + 2119857 * 2 ^ 59
def prefixEnd_2119857 : Nat := 4983230072969 + 3 ^ 40 * 2119857 * 2
def baseEnd_2119857 : Nat := 725670373198811855625641

theorem tailTrace_2119857 : CollatzResearch.WordTrace tailWord_2119857 prefixEnd_2119857 725670373198811855625641 := by
  unfold tailWord_2119857
  simp only [CollatzResearch.WordTrace]
  refine ⟨77317536681127606597013825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51545024454085071064675883 77317536681127606597013825)
  ·
    refine ⟨57988152510845704947760369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77317536681127606597013825 57988152510845704947760369)
    ·
      refine ⟨43491114383134278710820277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57988152510845704947760369 43491114383134278710820277)
      ·
        refine ⟨4077291973418838629139401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 43491114383134278710820277 4077291973418838629139401)
        ·
          refine ⟨3057968980064128971854551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4077291973418838629139401 3057968980064128971854551)
          ·
            refine ⟨4586953470096193457781827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3057968980064128971854551 4586953470096193457781827)
            ·
              refine ⟨6880430205144290186672741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4586953470096193457781827 6880430205144290186672741)
              ·
                refine ⟨1290080663464554410001139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6880430205144290186672741 1290080663464554410001139)
                ·
                  refine ⟨1935120995196831615001709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1290080663464554410001139 1935120995196831615001709)
                  ·
                    refine ⟨725670373198811855625641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1935120995196831615001709 725670373198811855625641)
                    ·
                      rfl

theorem cell22_2119857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 4, 1, 3].length) (baseStart_2119857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2119857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2119857 prefixEnd_2119857 := by exact prefixLift 2119857
  have htrace : WordTrace (prefixWord ++ tailWord_2119857) baseStart_2119857 baseEnd_2119857 := by
    simpa [prefixWord, tailWord_2119857, baseEnd_2119857] using wordTrace_append hprefix tailTrace_2119857
  have hstable : (prefixWord ++ tailWord_2119857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2119857).length < 2 ^ (prefixWord ++ tailWord_2119857).sum := by decide
  have hdescent : baseEnd_2119857 < baseStart_2119857 := by decide
  rcases family_descends (prefixWord ++ tailWord_2119857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2119866 : List Nat := [3, 1, 1, 1, 2, 2, 3, 2, 3, 4]
def baseStart_2119866 : Nat := 118140960795 + 2119866 * 2 ^ 59
def prefixEnd_2119866 : Nat := 4983230072969 + 3 ^ 40 * 2119866 * 2
def baseEnd_2119866 : Nat := 725673454082738832150613

theorem tailTrace_2119866 : CollatzResearch.WordTrace tailWord_2119866 prefixEnd_2119866 725673454082738832150613 := by
  unfold tailWord_2119866
  simp only [CollatzResearch.WordTrace]
  refine ⟨19329466234523750283522863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51545243292063334089394301 19329466234523750283522863)
  ·
    refine ⟨28994199351785625425284295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19329466234523750283522863 28994199351785625425284295)
    ·
      refine ⟨43491299027678438137926443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28994199351785625425284295 43491299027678438137926443)
      ·
        refine ⟨65236948541517657206889665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43491299027678438137926443 65236948541517657206889665)
        ·
          refine ⟨48927711406138242905167249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65236948541517657206889665 48927711406138242905167249)
          ·
            refine ⟨36695783554603682178875437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48927711406138242905167249 36695783554603682178875437)
            ·
              refine ⟨13760918832976380817078289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36695783554603682178875437 13760918832976380817078289)
              ·
                refine ⟨10320689124732285612808717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13760918832976380817078289 10320689124732285612808717)
                ·
                  refine ⟨3870258421774607104803269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10320689124732285612808717 3870258421774607104803269)
                  ·
                    refine ⟨725673454082738832150613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3870258421774607104803269 725673454082738832150613)
                    ·
                      rfl

theorem cell22_2119866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 2, 3, 4].length) (baseStart_2119866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2119866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2119866 prefixEnd_2119866 := by exact prefixLift 2119866
  have htrace : WordTrace (prefixWord ++ tailWord_2119866) baseStart_2119866 baseEnd_2119866 := by
    simpa [prefixWord, tailWord_2119866, baseEnd_2119866] using wordTrace_append hprefix tailTrace_2119866
  have hstable : (prefixWord ++ tailWord_2119866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2119866).length < 2 ^ (prefixWord ++ tailWord_2119866).sum := by decide
  have hdescent : baseEnd_2119866 < baseStart_2119866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2119866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2119868 : List Nat := [2, 2, 2, 3, 3, 1, 1, 1, 2, 5]
def baseStart_2119868 : Nat := 118140960795 + 2119868 * 2 ^ 59
def prefixEnd_2119868 : Nat := 4983230072969 + 3 ^ 40 * 2119868 * 2
def baseEnd_2119868 : Nat := 725674138723611493600607

theorem tailTrace_2119868 : CollatzResearch.WordTrace tailWord_2119868 prefixEnd_2119868 725674138723611493600607 := by
  unfold tailWord_2119868
  simp only [CollatzResearch.WordTrace]
  refine ⟨38658968942043877737832129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51545291922725170317109505 38658968942043877737832129)
  ·
    refine ⟨28994226706532908303374097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38658968942043877737832129 28994226706532908303374097)
    ·
      refine ⟨21745670029899681227530573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28994226706532908303374097 21745670029899681227530573)
      ·
        refine ⟨8154626261212380460323965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21745670029899681227530573 8154626261212380460323965)
        ·
          refine ⟨3057984847954642672621487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8154626261212380460323965 3057984847954642672621487)
          ·
            refine ⟨4586977271931964008932231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3057984847954642672621487 4586977271931964008932231)
            ·
              refine ⟨6880465907897946013398347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4586977271931964008932231 6880465907897946013398347)
              ·
                refine ⟨10320698861846919020097521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6880465907897946013398347 10320698861846919020097521)
                ·
                  refine ⟨7740524146385189265073141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10320698861846919020097521 7740524146385189265073141)
                  ·
                    refine ⟨725674138723611493600607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7740524146385189265073141 725674138723611493600607)
                    ·
                      rfl

theorem cell22_2119868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 1, 2, 5].length) (baseStart_2119868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2119868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2119868 prefixEnd_2119868 := by exact prefixLift 2119868
  have htrace : WordTrace (prefixWord ++ tailWord_2119868) baseStart_2119868 baseEnd_2119868 := by
    simpa [prefixWord, tailWord_2119868, baseEnd_2119868] using wordTrace_append hprefix tailTrace_2119868
  have hstable : (prefixWord ++ tailWord_2119868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2119868).length < 2 ^ (prefixWord ++ tailWord_2119868).sum := by decide
  have hdescent : baseEnd_2119868 < baseStart_2119868 := by decide
  rcases family_descends (prefixWord ++ tailWord_2119868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2119898 : List Nat := [3, 1, 1, 2, 2, 1, 3, 5, 4]
def baseStart_2119898 : Nat := 118140960795 + 2119898 * 2 ^ 59
def prefixEnd_2119898 : Nat := 4983230072969 + 3 ^ 40 * 2119898 * 2
def baseEnd_2119898 : Nat := 241894802778900471783505

theorem tailTrace_2119898 : CollatzResearch.WordTrace tailWord_2119898 prefixEnd_2119898 241894802778900471783505 := by
  unfold tailWord_2119898
  simp only [CollatzResearch.WordTrace]
  refine ⟨19329758018494767649814087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51546021382652713732837565 19329758018494767649814087)
  ·
    refine ⟨28994637027742151474721131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19329758018494767649814087 28994637027742151474721131)
    ·
      refine ⟨43491955541613227212081697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28994637027742151474721131 43491955541613227212081697)
      ·
        refine ⟨32618966656209920409061273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43491955541613227212081697 32618966656209920409061273)
        ·
          refine ⟨24464224992157440306795955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32618966656209920409061273 24464224992157440306795955)
          ·
            refine ⟨36696337488236160460193933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24464224992157440306795955 36696337488236160460193933)
            ·
              refine ⟨13761126558088560172572725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36696337488236160460193933 13761126558088560172572725)
              ·
                refine ⟨1290105614820802516178693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13761126558088560172572725 1290105614820802516178693)
                ·
                  refine ⟨241894802778900471783505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1290105614820802516178693 241894802778900471783505)
                  ·
                    rfl

theorem cell22_2119898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 5, 4].length) (baseStart_2119898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2119898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2119898 prefixEnd_2119898 := by exact prefixLift 2119898
  have htrace : WordTrace (prefixWord ++ tailWord_2119898) baseStart_2119898 baseEnd_2119898 := by
    simpa [prefixWord, tailWord_2119898, baseEnd_2119898] using wordTrace_append hprefix tailTrace_2119898
  have hstable : (prefixWord ++ tailWord_2119898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2119898).length < 2 ^ (prefixWord ++ tailWord_2119898).sum := by decide
  have hdescent : baseEnd_2119898 < baseStart_2119898 := by decide
  rcases family_descends (prefixWord ++ tailWord_2119898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2119971 : List Nat := [1, 1, 1, 4, 2, 2, 1, 3, 7]
def baseStart_2119971 : Nat := 118140960795 + 2119971 * 2 ^ 59
def prefixEnd_2119971 : Nat := 4983230072969 + 3 ^ 40 * 2119971 * 2
def baseEnd_2119971 : Nat := 241903132576184519425097

theorem tailTrace_2119971 : CollatzResearch.WordTrace tailWord_2119971 prefixEnd_2119971 241903132576184519425097 := by
  unfold tailWord_2119971
  simp only [CollatzResearch.WordTrace]
  refine ⟨77321694602714604066663767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51547796401809736044442511 77321694602714604066663767)
  ·
    refine ⟨115982541904071906099995651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77321694602714604066663767 115982541904071906099995651)
    ·
      refine ⟨173973812856107859149993477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115982541904071906099995651 173973812856107859149993477)
      ·
        refine ⟨32620089910520223590623777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 173973812856107859149993477 32620089910520223590623777)
        ·
          refine ⟨24465067432890167692967833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32620089910520223590623777 24465067432890167692967833)
          ·
            refine ⟨18348800574667625769725875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24465067432890167692967833 18348800574667625769725875)
            ·
              refine ⟨27523200862001438654588813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18348800574667625769725875 27523200862001438654588813)
              ·
                refine ⟨10321200323250539495470805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27523200862001438654588813 10321200323250539495470805)
                ·
                  refine ⟨241903132576184519425097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10321200323250539495470805 241903132576184519425097)
                  ·
                    rfl

theorem cell22_2119971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 3, 7].length) (baseStart_2119971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2119971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2119971 prefixEnd_2119971 := by exact prefixLift 2119971
  have htrace : WordTrace (prefixWord ++ tailWord_2119971) baseStart_2119971 baseEnd_2119971 := by
    simpa [prefixWord, tailWord_2119971, baseEnd_2119971] using wordTrace_append hprefix tailTrace_2119971
  have hstable : (prefixWord ++ tailWord_2119971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2119971).length < 2 ^ (prefixWord ++ tailWord_2119971).sum := by decide
  have hdescent : baseEnd_2119971 < baseStart_2119971 := by decide
  rcases family_descends (prefixWord ++ tailWord_2119971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2119981 : List Nat := [1, 5, 3, 1, 2, 2, 2, 1, 2, 3]
def baseStart_2119981 : Nat := 118140960795 + 2119981 * 2 ^ 59
def prefixEnd_2119981 : Nat := 4983230072969 + 3 ^ 40 * 2119981 * 2
def baseEnd_2119981 : Nat := 725712820932916865525261

theorem tailTrace_2119981 : CollatzResearch.WordTrace tailWord_2119981 prefixEnd_2119981 725712820932916865525261 := by
  unfold tailWord_2119981
  simp only [CollatzResearch.WordTrace]
  refine ⟨77322059332678375774527797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51548039555118917183018531 77322059332678375774527797)
  ·
    refine ⟨7248943062438597728861981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 77322059332678375774527797 7248943062438597728861981)
    ·
      refine ⟨2718353648414474148323243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7248943062438597728861981 2718353648414474148323243)
      ·
        refine ⟨4077530472621711222484865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2718353648414474148323243 4077530472621711222484865)
        ·
          refine ⟨3058147854466283416863649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4077530472621711222484865 3058147854466283416863649)
          ·
            refine ⟨2293610890849712562647737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3058147854466283416863649 2293610890849712562647737)
            ·
              refine ⟨1720208168137284421985803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2293610890849712562647737 1720208168137284421985803)
              ·
                refine ⟨2580312252205926632978705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1720208168137284421985803 2580312252205926632978705)
                ·
                  refine ⟨1935234189154444974734029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2580312252205926632978705 1935234189154444974734029)
                  ·
                    refine ⟨725712820932916865525261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1935234189154444974734029 725712820932916865525261)
                    ·
                      rfl

theorem cell22_2119981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_2119981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2119981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2119981 prefixEnd_2119981 := by exact prefixLift 2119981
  have htrace : WordTrace (prefixWord ++ tailWord_2119981) baseStart_2119981 baseEnd_2119981 := by
    simpa [prefixWord, tailWord_2119981, baseEnd_2119981] using wordTrace_append hprefix tailTrace_2119981
  have hstable : (prefixWord ++ tailWord_2119981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2119981).length < 2 ^ (prefixWord ++ tailWord_2119981).sum := by decide
  have hdescent : baseEnd_2119981 < baseStart_2119981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2119981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2120048 : List Nat := [2, 1, 1, 1, 4, 3, 1, 3, 1, 5]
def baseStart_2120048 : Nat := 118140960795 + 2120048 * 2 ^ 59
def prefixEnd_2120048 : Nat := 4983230072969 + 3 ^ 40 * 2120048 * 2
def baseEnd_2120048 : Nat := 725735756402151024100055

theorem tailTrace_2120048 : CollatzResearch.WordTrace tailWord_2120048 prefixEnd_2120048 725735756402151024100055 := by
  unfold tailWord_2120048
  simp only [CollatzResearch.WordTrace]
  refine ⟨38662251511717823108608399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51549668682290430811477865 38662251511717823108608399)
  ·
    refine ⟨57993377267576734662912599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38662251511717823108608399 57993377267576734662912599)
    ·
      refine ⟨86990065901365101994368899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57993377267576734662912599 86990065901365101994368899)
      ·
        refine ⟨130485098852047652991553349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86990065901365101994368899 130485098852047652991553349)
        ·
          refine ⟨24465956034758934935916253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 130485098852047652991553349 24465956034758934935916253)
          ·
            refine ⟨9174733513034600600968595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24465956034758934935916253 9174733513034600600968595)
            ·
              refine ⟨13762100269551900901452893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9174733513034600600968595 13762100269551900901452893)
              ·
                refine ⟨5160787601081962838044835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13762100269551900901452893 5160787601081962838044835)
                ·
                  refine ⟨7741181401622944257067253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5160787601081962838044835 7741181401622944257067253)
                  ·
                    refine ⟨725735756402151024100055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7741181401622944257067253 725735756402151024100055)
                    ·
                      rfl

theorem cell22_2120048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 3, 1, 5].length) (baseStart_2120048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2120048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2120048 prefixEnd_2120048 := by exact prefixLift 2120048
  have htrace : WordTrace (prefixWord ++ tailWord_2120048) baseStart_2120048 baseEnd_2120048 := by
    simpa [prefixWord, tailWord_2120048, baseEnd_2120048] using wordTrace_append hprefix tailTrace_2120048
  have hstable : (prefixWord ++ tailWord_2120048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2120048).length < 2 ^ (prefixWord ++ tailWord_2120048).sum := by decide
  have hdescent : baseEnd_2120048 < baseStart_2120048 := by decide
  rcases family_descends (prefixWord ++ tailWord_2120048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2120065 : List Nat := [1, 2, 4, 3, 1, 1, 2, 2, 1, 5]
def baseStart_2120065 : Nat := 118140960795 + 2120065 * 2 ^ 59
def prefixEnd_2120065 : Nat := 4983230072969 + 3 ^ 40 * 2120065 * 2
def baseEnd_2120065 : Nat := 725741575849568646425003

theorem tailTrace_2120065 : CollatzResearch.WordTrace tailWord_2120065 prefixEnd_2120065 725741575849568646425003 := by
  unfold tailWord_2120065
  simp only [CollatzResearch.WordTrace]
  refine ⟨77325123064374058120585649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51550082042916038747057099 77325123064374058120585649)
  ·
    refine ⟨57993842298280543590439237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77325123064374058120585649 57993842298280543590439237)
    ·
      refine ⟨10873845430927601923207357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57993842298280543590439237 10873845430927601923207357)
      ·
        refine ⟨4077692036597850721202759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10873845430927601923207357 4077692036597850721202759)
        ·
          refine ⟨6116538054896776081804139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4077692036597850721202759 6116538054896776081804139)
          ·
            refine ⟨9174807082345164122706209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6116538054896776081804139 9174807082345164122706209)
            ·
              refine ⟨6881105311758873092029657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9174807082345164122706209 6881105311758873092029657)
              ·
                refine ⟨5160828983819154819022243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6881105311758873092029657 5160828983819154819022243)
                ·
                  refine ⟨7741243475728732228533365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5160828983819154819022243 7741243475728732228533365)
                  ·
                    refine ⟨725741575849568646425003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7741243475728732228533365 725741575849568646425003)
                    ·
                      rfl

theorem cell22_2120065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 5].length) (baseStart_2120065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2120065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2120065 prefixEnd_2120065 := by exact prefixLift 2120065
  have htrace : WordTrace (prefixWord ++ tailWord_2120065) baseStart_2120065 baseEnd_2120065 := by
    simpa [prefixWord, tailWord_2120065, baseEnd_2120065] using wordTrace_append hprefix tailTrace_2120065
  have hstable : (prefixWord ++ tailWord_2120065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2120065).length < 2 ^ (prefixWord ++ tailWord_2120065).sum := by decide
  have hdescent : baseEnd_2120065 < baseStart_2120065 := by decide
  rcases family_descends (prefixWord ++ tailWord_2120065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2120067 : List Nat := [1, 1, 1, 3, 6, 1, 2, 3, 4]
def baseStart_2120067 : Nat := 118140960795 + 2120067 * 2 ^ 59
def prefixEnd_2120067 : Nat := 4983230072969 + 3 ^ 40 * 2120067 * 2
def baseEnd_2120067 : Nat := 241914086830147102624999

theorem tailTrace_2120067 : CollatzResearch.WordTrace tailWord_2120067 prefixEnd_2120067 241914086830147102624999 := by
  unfold tailWord_2120067
  simp only [CollatzResearch.WordTrace]
  refine ⟨77325196010366812462158455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51550130673577874974772303 77325196010366812462158455)
  ·
    refine ⟨115987794015550218693237683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77325196010366812462158455 115987794015550218693237683)
    ·
      refine ⟨173981691023325328039856525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115987794015550218693237683 173981691023325328039856525)
      ·
        refine ⟨65243134133746998014946197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 173981691023325328039856525 65243134133746998014946197)
        ·
          refine ⟨3058271912519390531950603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 65243134133746998014946197 3058271912519390531950603)
          ·
            refine ⟨4587407868779085797925905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3058271912519390531950603 4587407868779085797925905)
            ·
              refine ⟨3440555901584314348444429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4587407868779085797925905 3440555901584314348444429)
              ·
                refine ⟨1290208463094117880666661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3440555901584314348444429 1290208463094117880666661)
                ·
                  refine ⟨241914086830147102624999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1290208463094117880666661 241914086830147102624999)
                  ·
                    rfl

theorem cell22_2120067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 2, 3, 4].length) (baseStart_2120067 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2120067 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2120067 prefixEnd_2120067 := by exact prefixLift 2120067
  have htrace : WordTrace (prefixWord ++ tailWord_2120067) baseStart_2120067 baseEnd_2120067 := by
    simpa [prefixWord, tailWord_2120067, baseEnd_2120067] using wordTrace_append hprefix tailTrace_2120067
  have hstable : (prefixWord ++ tailWord_2120067).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2120067).length < 2 ^ (prefixWord ++ tailWord_2120067).sum := by decide
  have hdescent : baseEnd_2120067 < baseStart_2120067 := by decide
  rcases family_descends (prefixWord ++ tailWord_2120067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2120129 : List Nat := [1, 2, 7, 1, 1, 2, 8]
def baseStart_2120129 : Nat := 118140960795 + 2120129 * 2 ^ 59
def prefixEnd_2120129 : Nat := 4983230072969 + 3 ^ 40 * 2120129 * 2
def baseEnd_2120129 : Nat := 26880129050277548623141

theorem tailTrace_2120129 : CollatzResearch.WordTrace tailWord_2120129 prefixEnd_2120129 26880129050277548623141 := by
  unfold tailWord_2120129
  simp only [CollatzResearch.WordTrace]
  refine ⟨77327457336142197050915441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51551638224094798033943627 77327457336142197050915441)
  ·
    refine ⟨57995593002106647788186581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77327457336142197050915441 57995593002106647788186581)
    ·
      refine ⟨1359271710986874557535623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 57995593002106647788186581 1359271710986874557535623)
      ·
        refine ⟨2038907566480311836303435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1359271710986874557535623 2038907566480311836303435)
        ·
          refine ⟨3058361349720467754455153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2038907566480311836303435 3058361349720467754455153)
          ·
            refine ⟨2293771012290350815841365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3058361349720467754455153 2293771012290350815841365)
            ·
              refine ⟨26880129050277548623141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2293771012290350815841365 26880129050277548623141)
              ·
                rfl

theorem cell22_2120129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 8].length) (baseStart_2120129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2120129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2120129 prefixEnd_2120129 := by exact prefixLift 2120129
  have htrace : WordTrace (prefixWord ++ tailWord_2120129) baseStart_2120129 baseEnd_2120129 := by
    simpa [prefixWord, tailWord_2120129, baseEnd_2120129] using wordTrace_append hprefix tailTrace_2120129
  have hstable : (prefixWord ++ tailWord_2120129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2120129).length < 2 ^ (prefixWord ++ tailWord_2120129).sum := by decide
  have hdescent : baseEnd_2120129 < baseStart_2120129 := by decide
  rcases family_descends (prefixWord ++ tailWord_2120129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2120202 : List Nat := [3, 1, 2, 2, 2, 1, 3, 4, 4]
def baseStart_2120202 : Nat := 118140960795 + 2120202 * 2 ^ 59
def prefixEnd_2120202 : Nat := 4983230072969 + 3 ^ 40 * 2120202 * 2
def baseEnd_2120202 : Nat := 241929491249781985249861

theorem tailTrace_2120202 : CollatzResearch.WordTrace tailWord_2120202 prefixEnd_2120202 241929491249781985249861 := by
  unfold tailWord_2120202
  simp only [CollatzResearch.WordTrace]
  refine ⟨19332529966219432629580715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51553413243251820345548573 19332529966219432629580715)
  ·
    refine ⟨28998794949329148944371073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19332529966219432629580715 28998794949329148944371073)
    ·
      refine ⟨21749096211996861708278305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28998794949329148944371073 21749096211996861708278305)
      ·
        refine ⟨16311822158997646281208729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21749096211996861708278305 16311822158997646281208729)
        ·
          refine ⟨12233866619248234710906547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16311822158997646281208729 12233866619248234710906547)
          ·
            refine ⟨18350799928872352066359821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12233866619248234710906547 18350799928872352066359821)
            ·
              refine ⟨6881549973327132024884933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18350799928872352066359821 6881549973327132024884933)
              ·
                refine ⟨1290290619998837254665925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6881549973327132024884933 1290290619998837254665925)
                ·
                  refine ⟨241929491249781985249861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1290290619998837254665925 241929491249781985249861)
                  ·
                    rfl

theorem cell22_2120202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 4, 4].length) (baseStart_2120202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2120202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2120202 prefixEnd_2120202 := by exact prefixLift 2120202
  have htrace : WordTrace (prefixWord ++ tailWord_2120202) baseStart_2120202 baseEnd_2120202 := by
    simpa [prefixWord, tailWord_2120202, baseEnd_2120202] using wordTrace_append hprefix tailTrace_2120202
  have hstable : (prefixWord ++ tailWord_2120202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2120202).length < 2 ^ (prefixWord ++ tailWord_2120202).sum := by decide
  have hdescent : baseEnd_2120202 < baseStart_2120202 := by decide
  rcases family_descends (prefixWord ++ tailWord_2120202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2120232 : List Nat := [2, 1, 5, 2, 1, 2, 1, 1, 1, 6]
def baseStart_2120232 : Nat := 118140960795 + 2120232 * 2 ^ 59
def prefixEnd_2120232 : Nat := 4983230072969 + 3 ^ 40 * 2120232 * 2
def baseEnd_2120232 : Nat := 725798743362435877499491

theorem tailTrace_2120232 : CollatzResearch.WordTrace tailWord_2120232 prefixEnd_2120232 725798743362435877499491 := by
  unfold tailWord_2120232
  simp only [CollatzResearch.WordTrace]
  refine ⟨38665607027384522820957475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51554142703179363761276633 38665607027384522820957475)
  ·
    refine ⟨57998410541076784231436213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38665607027384522820957475 57998410541076784231436213)
    ·
      refine ⟨5437350988225948521697145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 57998410541076784231436213 5437350988225948521697145)
      ·
        refine ⟨4078013241169461391272859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5437350988225948521697145 4078013241169461391272859)
        ·
          refine ⟨6117019861754192086909289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4078013241169461391272859 6117019861754192086909289)
          ·
            refine ⟨4587764896315644065181967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6117019861754192086909289 4587764896315644065181967)
            ·
              refine ⟨6881647344473466097772951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4587764896315644065181967 6881647344473466097772951)
              ·
                refine ⟨10322471016710199146659427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6881647344473466097772951 10322471016710199146659427)
                ·
                  refine ⟨15483706525065298719989141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10322471016710199146659427 15483706525065298719989141)
                  ·
                    refine ⟨725798743362435877499491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15483706525065298719989141 725798743362435877499491)
                    ·
                      rfl

theorem cell22_2120232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_2120232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2120232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2120232 prefixEnd_2120232 := by exact prefixLift 2120232
  have htrace : WordTrace (prefixWord ++ tailWord_2120232) baseStart_2120232 baseEnd_2120232 := by
    simpa [prefixWord, tailWord_2120232, baseEnd_2120232] using wordTrace_append hprefix tailTrace_2120232
  have hstable : (prefixWord ++ tailWord_2120232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2120232).length < 2 ^ (prefixWord ++ tailWord_2120232).sum := by decide
  have hdescent : baseEnd_2120232 < baseStart_2120232 := by decide
  rcases family_descends (prefixWord ++ tailWord_2120232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2120238 : List Nat := [4, 1, 3, 1, 4, 1, 2, 1, 1, 4]
def baseStart_2120238 : Nat := 118140960795 + 2120238 * 2 ^ 59
def prefixEnd_2120238 : Nat := 4983230072969 + 3 ^ 40 * 2120238 * 2
def baseEnd_2120238 : Nat := 725800797285053861849473

theorem tailTrace_2120238 : CollatzResearch.WordTrace tailWord_2120238 prefixEnd_2120238 725800797285053861849473 := by
  unfold tailWord_2120238
  simp only [CollatzResearch.WordTrace]
  refine ⟨9666429111593413583329171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51554288595164872444422245 9666429111593413583329171)
  ·
    refine ⟨14499643667390120374993757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9666429111593413583329171 14499643667390120374993757)
    ·
      refine ⟨5437366375271295140622659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14499643667390120374993757 5437366375271295140622659)
      ·
        refine ⟨8156049562906942710933989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5437366375271295140622659 8156049562906942710933989)
        ·
          refine ⟨1529259293045051758300123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8156049562906942710933989 1529259293045051758300123)
          ·
            refine ⟨2293888939567577637450185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1529259293045051758300123 2293888939567577637450185)
            ·
              refine ⟨1720416704675683228087639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2293888939567577637450185 1720416704675683228087639)
              ·
                refine ⟨2580625057013524842131459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1720416704675683228087639 2580625057013524842131459)
                ·
                  refine ⟨3870937585520287263197189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2580625057013524842131459 3870937585520287263197189)
                  ·
                    refine ⟨725800797285053861849473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3870937585520287263197189 725800797285053861849473)
                    ·
                      rfl

theorem cell22_2120238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 2, 1, 1, 4].length) (baseStart_2120238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2120238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2120238 prefixEnd_2120238 := by exact prefixLift 2120238
  have htrace : WordTrace (prefixWord ++ tailWord_2120238) baseStart_2120238 baseEnd_2120238 := by
    simpa [prefixWord, tailWord_2120238, baseEnd_2120238] using wordTrace_append hprefix tailTrace_2120238
  have hstable : (prefixWord ++ tailWord_2120238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2120238).length < 2 ^ (prefixWord ++ tailWord_2120238).sum := by decide
  have hdescent : baseEnd_2120238 < baseStart_2120238 := by decide
  rcases family_descends (prefixWord ++ tailWord_2120238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2120305 : List Nat := [1, 2, 2, 2, 1, 1, 1, 1, 7, 4]
def baseStart_2120305 : Nat := 118140960795 + 2120305 * 2 ^ 59
def prefixEnd_2120305 : Nat := 4983230072969 + 3 ^ 40 * 2120305 * 2
def baseEnd_2120305 : Nat := 725823732754288020424267

theorem tailTrace_2120305 : CollatzResearch.WordTrace tailWord_2120305 prefixEnd_2120305 725823732754288020424267 := by
  unfold tailWord_2120305
  simp only [CollatzResearch.WordTrace]
  refine ⟨77333876583504579109322369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51555917722336386072881579 77333876583504579109322369)
  ·
    refine ⟨58000407437628434331991777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77333876583504579109322369 58000407437628434331991777)
    ·
      refine ⟨43500305578221325748993833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58000407437628434331991777 43500305578221325748993833)
      ·
        refine ⟨32625229183665994311745375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43500305578221325748993833 32625229183665994311745375)
        ·
          refine ⟨48937843775498991467618063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32625229183665994311745375 48937843775498991467618063)
          ·
            refine ⟨73406765663248487201427095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48937843775498991467618063 73406765663248487201427095)
            ·
              refine ⟨110110148494872730802140643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73406765663248487201427095 110110148494872730802140643)
              ·
                refine ⟨165165222742309096203210965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 110110148494872730802140643 165165222742309096203210965)
                ·
                  refine ⟨3871059908022869442262757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 165165222742309096203210965 3871059908022869442262757)
                  ·
                    refine ⟨725823732754288020424267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3871059908022869442262757 725823732754288020424267)
                    ·
                      rfl

theorem cell22_2120305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 7, 4].length) (baseStart_2120305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2120305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2120305 prefixEnd_2120305 := by exact prefixLift 2120305
  have htrace : WordTrace (prefixWord ++ tailWord_2120305) baseStart_2120305 baseEnd_2120305 := by
    simpa [prefixWord, tailWord_2120305, baseEnd_2120305] using wordTrace_append hprefix tailTrace_2120305
  have hstable : (prefixWord ++ tailWord_2120305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2120305).length < 2 ^ (prefixWord ++ tailWord_2120305).sum := by decide
  have hdescent : baseEnd_2120305 < baseStart_2120305 := by decide
  rcases family_descends (prefixWord ++ tailWord_2120305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2120367 : List Nat := [1, 1, 2, 1, 2, 5, 2, 2, 2, 4]
def baseStart_2120367 : Nat := 118140960795 + 2120367 * 2 ^ 59
def prefixEnd_2120367 : Nat := 4983230072969 + 3 ^ 40 * 2120367 * 2
def baseEnd_2120367 : Nat := 725844956621340525374077

theorem tailTrace_2120367 : CollatzResearch.WordTrace tailWord_2120367 prefixEnd_2120367 725844956621340525374077 := by
  unfold tailWord_2120367
  simp only [CollatzResearch.WordTrace]
  refine ⟨77336137909279963698079355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51557425272853309132052903 77336137909279963698079355)
  ·
    refine ⟨116004206863919945547119033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77336137909279963698079355 116004206863919945547119033)
    ·
      refine ⟨87003155147939959160339275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116004206863919945547119033 87003155147939959160339275)
      ·
        refine ⟨130504732721909938740508913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87003155147939959160339275 130504732721909938740508913)
        ·
          refine ⟨97878549541432454055381685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130504732721909938740508913 97878549541432454055381685)
          ·
            refine ⟨9176114019509292567692033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 97878549541432454055381685 9176114019509292567692033)
            ·
              refine ⟨6882085514631969425769025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9176114019509292567692033 6882085514631969425769025)
              ·
                refine ⟨5161564135973977069326769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6882085514631969425769025 5161564135973977069326769)
                ·
                  refine ⟨3871173101980482801995077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5161564135973977069326769 3871173101980482801995077)
                  ·
                    refine ⟨725844956621340525374077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3871173101980482801995077 725844956621340525374077)
                    ·
                      rfl

theorem cell22_2120367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 2, 2, 4].length) (baseStart_2120367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2120367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2120367 prefixEnd_2120367 := by exact prefixLift 2120367
  have htrace : WordTrace (prefixWord ++ tailWord_2120367) baseStart_2120367 baseEnd_2120367 := by
    simpa [prefixWord, tailWord_2120367, baseEnd_2120367] using wordTrace_append hprefix tailTrace_2120367
  have hstable : (prefixWord ++ tailWord_2120367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2120367).length < 2 ^ (prefixWord ++ tailWord_2120367).sum := by decide
  have hdescent : baseEnd_2120367 < baseStart_2120367 := by decide
  rcases family_descends (prefixWord ++ tailWord_2120367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2120371 : List Nat := [1, 1, 1, 2, 3, 6, 2, 2, 4]
def baseStart_2120371 : Nat := 118140960795 + 2120371 * 2 ^ 59
def prefixEnd_2120371 : Nat := 4983230072969 + 3 ^ 40 * 2120371 * 2
def baseEnd_2120371 : Nat := 241948775301028616091355

theorem tailTrace_2120371 : CollatzResearch.WordTrace tailWord_2120371 prefixEnd_2120371 241948775301028616091355 := by
  unfold tailWord_2120371
  simp only [CollatzResearch.WordTrace]
  refine ⟨77336283801265472381224967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51557522534176981587483311 77336283801265472381224967)
  ·
    refine ⟨116004425701898208571837451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77336283801265472381224967 116004425701898208571837451)
    ·
      refine ⟨174006638552847312857756177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116004425701898208571837451 174006638552847312857756177)
      ·
        refine ⟨130504978914635484643317133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 174006638552847312857756177 130504978914635484643317133)
        ·
          refine ⟨48939367092988306741243925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 130504978914635484643317133 48939367092988306741243925)
          ·
            refine ⟨2294032832483826878495809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 48939367092988306741243925 2294032832483826878495809)
            ·
              refine ⟨1720524624362870158871857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2294032832483826878495809 1720524624362870158871857)
              ·
                refine ⟨1290393468272152619153893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1720524624362870158871857 1290393468272152619153893)
                ·
                  refine ⟨241948775301028616091355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1290393468272152619153893 241948775301028616091355)
                  ·
                    rfl

theorem cell22_2120371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 2, 2, 4].length) (baseStart_2120371 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2120371 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2120371 prefixEnd_2120371 := by exact prefixLift 2120371
  have htrace : WordTrace (prefixWord ++ tailWord_2120371) baseStart_2120371 baseEnd_2120371 := by
    simpa [prefixWord, tailWord_2120371, baseEnd_2120371] using wordTrace_append hprefix tailTrace_2120371
  have hstable : (prefixWord ++ tailWord_2120371).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2120371).length < 2 ^ (prefixWord ++ tailWord_2120371).sum := by decide
  have hdescent : baseEnd_2120371 < baseStart_2120371 := by decide
  rcases family_descends (prefixWord ++ tailWord_2120371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2120431 : List Nat := [1, 1, 2, 1, 5, 2, 2, 4, 1, 3]
def baseStart_2120431 : Nat := 118140960795 + 2120431 * 2 ^ 59
def prefixEnd_2120431 : Nat := 4983230072969 + 3 ^ 40 * 2120431 * 2
def baseEnd_2120431 : Nat := 725866865129265691773881

theorem tailTrace_2120431 : CollatzResearch.WordTrace tailWord_2120431 prefixEnd_2120431 725866865129265691773881 := by
  unfold tailWord_2120431
  simp only [CollatzResearch.WordTrace]
  refine ⟨77338472181048102628409147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51558981454032068418939431 77338472181048102628409147)
  ·
    refine ⟨116007708271572153942613721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77338472181048102628409147 116007708271572153942613721)
    ·
      refine ⟨87005781203679115456960291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116007708271572153942613721 87005781203679115456960291)
      ·
        refine ⟨130508671805518673185440437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87005781203679115456960291 130508671805518673185440437)
        ·
          refine ⟨12235187981767375611135041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 130508671805518673185440437 12235187981767375611135041)
          ·
            refine ⟨9176390986325531708351281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12235187981767375611135041 9176390986325531708351281)
            ·
              refine ⟨6882293239744148781263461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9176390986325531708351281 6882293239744148781263461)
              ·
                refine ⟨1290429982452027896486899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6882293239744148781263461 1290429982452027896486899)
                ·
                  refine ⟨1935644973678041844730349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1290429982452027896486899 1935644973678041844730349)
                  ·
                    refine ⟨725866865129265691773881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1935644973678041844730349 725866865129265691773881)
                    ·
                      rfl

theorem cell22_2120431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 4, 1, 3].length) (baseStart_2120431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2120431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2120431 prefixEnd_2120431 := by exact prefixLift 2120431
  have htrace : WordTrace (prefixWord ++ tailWord_2120431) baseStart_2120431 baseEnd_2120431 := by
    simpa [prefixWord, tailWord_2120431, baseEnd_2120431] using wordTrace_append hprefix tailTrace_2120431
  have hstable : (prefixWord ++ tailWord_2120431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2120431).length < 2 ^ (prefixWord ++ tailWord_2120431).sum := by decide
  have hdescent : baseEnd_2120431 < baseStart_2120431 := by decide
  rcases family_descends (prefixWord ++ tailWord_2120431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2120437 : List Nat := [1, 3, 6, 1, 1, 1, 3, 1, 2, 3]
def baseStart_2120437 : Nat := 118140960795 + 2120437 * 2 ^ 59
def prefixEnd_2120437 : Nat := 4983230072969 + 3 ^ 40 * 2120437 * 2
def baseEnd_2120437 : Nat := 725868919051883676123863

theorem tailTrace_2120437 : CollatzResearch.WordTrace tailWord_2120437 prefixEnd_2120437 725868919051883676123863 := by
  unfold tailWord_2120437
  simp only [CollatzResearch.WordTrace]
  refine ⟨77338691019026365653127565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51559127346017577102085043 77338691019026365653127565)
  ·
    refine ⟨29002009132134887119922837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77338691019026365653127565 29002009132134887119922837)
    ·
      refine ⟨1359469178068822833746383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 29002009132134887119922837 1359469178068822833746383)
      ·
        refine ⟨2039203767103234250619575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1359469178068822833746383 2039203767103234250619575)
        ·
          refine ⟨3058805650654851375929363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2039203767103234250619575 3058805650654851375929363)
          ·
            refine ⟨4588208475982277063894045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3058805650654851375929363 4588208475982277063894045)
            ·
              refine ⟨1720578178493353898960267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4588208475982277063894045 1720578178493353898960267)
              ·
                refine ⟨2580867267740030848440401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1720578178493353898960267 2580867267740030848440401)
                ·
                  refine ⟨1935650450805023136330301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2580867267740030848440401 1935650450805023136330301)
                  ·
                    refine ⟨725868919051883676123863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1935650450805023136330301 725868919051883676123863)
                    ·
                      rfl

theorem cell22_2120437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_2120437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2120437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2120437 prefixEnd_2120437 := by exact prefixLift 2120437
  have htrace : WordTrace (prefixWord ++ tailWord_2120437) baseStart_2120437 baseEnd_2120437 := by
    simpa [prefixWord, tailWord_2120437, baseEnd_2120437] using wordTrace_append hprefix tailTrace_2120437
  have hstable : (prefixWord ++ tailWord_2120437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2120437).length < 2 ^ (prefixWord ++ tailWord_2120437).sum := by decide
  have hdescent : baseEnd_2120437 < baseStart_2120437 := by decide
  rcases family_descends (prefixWord ++ tailWord_2120437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2120442 : List Nat := [3, 1, 1, 1, 1, 3, 4, 1, 2, 5]
def baseStart_2120442 : Nat := 118140960795 + 2120442 * 2 ^ 59
def prefixEnd_2120442 : Nat := 4983230072969 + 3 ^ 40 * 2120442 * 2
def baseEnd_2120442 : Nat := 725870630654065329748847

theorem tailTrace_2120442 : CollatzResearch.WordTrace tailWord_2120442 prefixEnd_2120442 725870630654065329748847 := by
  unfold tailWord_2120442
  simp only [CollatzResearch.WordTrace]
  refine ⟨19334718346002062876764895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51559248922672167671373053 19334718346002062876764895)
  ·
    refine ⟨29002077519003094315147343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19334718346002062876764895 29002077519003094315147343)
    ·
      refine ⟨43503116278504641472721015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29002077519003094315147343 43503116278504641472721015)
      ·
        refine ⟨65254674417756962209081523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43503116278504641472721015 65254674417756962209081523)
        ·
          refine ⟨97882011626635443313622285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65254674417756962209081523 97882011626635443313622285)
          ·
            refine ⟨36705754359988291242608357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 97882011626635443313622285 36705754359988291242608357)
            ·
              refine ⟨6882328942497804607989067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36705754359988291242608357 6882328942497804607989067)
              ·
                refine ⟨10323493413746706911983601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6882328942497804607989067 10323493413746706911983601)
                ·
                  refine ⟨7742620060310030183987701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10323493413746706911983601 7742620060310030183987701)
                  ·
                    refine ⟨725870630654065329748847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7742620060310030183987701 725870630654065329748847)
                    ·
                      rfl

theorem cell22_2120442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 1, 2, 5].length) (baseStart_2120442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2120442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2120442 prefixEnd_2120442 := by exact prefixLift 2120442
  have htrace : WordTrace (prefixWord ++ tailWord_2120442) baseStart_2120442 baseEnd_2120442 := by
    simpa [prefixWord, tailWord_2120442, baseEnd_2120442] using wordTrace_append hprefix tailTrace_2120442
  have hstable : (prefixWord ++ tailWord_2120442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2120442).length < 2 ^ (prefixWord ++ tailWord_2120442).sum := by decide
  have hdescent : baseEnd_2120442 < baseStart_2120442 := by decide
  rcases family_descends (prefixWord ++ tailWord_2120442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2120457 : List Nat := [1, 2, 1, 1, 3, 2, 2, 3, 3, 4]
def baseStart_2120457 : Nat := 118140960795 + 2120457 * 2 ^ 59
def prefixEnd_2120457 : Nat := 4983230072969 + 3 ^ 40 * 2120457 * 2
def baseEnd_2120457 : Nat := 725875765460610290623801

theorem tailTrace_2120457 : CollatzResearch.WordTrace tailWord_2120457 prefixEnd_2120457 725875765460610290623801 := by
  unfold tailWord_2120457
  simp only [CollatzResearch.WordTrace]
  refine ⟨77339420478953909068855625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51559613652635939379237083 77339420478953909068855625)
  ·
    refine ⟨58004565359215431801641719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77339420478953909068855625 58004565359215431801641719)
    ·
      refine ⟨87006848038823147702462579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58004565359215431801641719 87006848038823147702462579)
      ·
        refine ⟨130510272058234721553693869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87006848038823147702462579 130510272058234721553693869)
        ·
          refine ⟨48941352021838020582635201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 130510272058234721553693869 48941352021838020582635201)
          ·
            refine ⟨36706014016378515436976401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48941352021838020582635201 36706014016378515436976401)
            ·
              refine ⟨27529510512283886577732301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36706014016378515436976401 27529510512283886577732301)
              ·
                refine ⟨10323566442106457466649613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27529510512283886577732301 10323566442106457466649613)
                ·
                  refine ⟨3871337415789921549993605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10323566442106457466649613 3871337415789921549993605)
                  ·
                    refine ⟨725875765460610290623801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3871337415789921549993605 725875765460610290623801)
                    ·
                      rfl

theorem cell22_2120457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 3, 3, 4].length) (baseStart_2120457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2120457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2120457 prefixEnd_2120457 := by exact prefixLift 2120457
  have htrace : WordTrace (prefixWord ++ tailWord_2120457) baseStart_2120457 baseEnd_2120457 := by
    simpa [prefixWord, tailWord_2120457, baseEnd_2120457] using wordTrace_append hprefix tailTrace_2120457
  have hstable : (prefixWord ++ tailWord_2120457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2120457).length < 2 ^ (prefixWord ++ tailWord_2120457).sum := by decide
  have hdescent : baseEnd_2120457 < baseStart_2120457 := by decide
  rcases family_descends (prefixWord ++ tailWord_2120457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2120474 : List Nat := [3, 1, 1, 3, 2, 1, 1, 5, 1, 4]
def baseStart_2120474 : Nat := 118140960795 + 2120474 * 2 ^ 59
def prefixEnd_2120474 : Nat := 4983230072969 + 3 ^ 40 * 2120474 * 2
def baseEnd_2120474 : Nat := 725881584908027912948749

theorem tailTrace_2120474 : CollatzResearch.WordTrace tailWord_2120474 prefixEnd_2120474 725881584908027912948749 := by
  unfold tailWord_2120474
  simp only [CollatzResearch.WordTrace]
  refine ⟨19335010129973080243056119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51560027013261547314816317 19335010129973080243056119)
  ·
    refine ⟨29002515194959620364584179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19335010129973080243056119 29002515194959620364584179)
    ·
      refine ⟨43503772792439430546876269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29002515194959620364584179 43503772792439430546876269)
      ·
        refine ⟨16313914797164786455078601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43503772792439430546876269 16313914797164786455078601)
        ·
          refine ⟨12235436097873589841308951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16313914797164786455078601 12235436097873589841308951)
          ·
            refine ⟨18353154146810384761963427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12235436097873589841308951 18353154146810384761963427)
            ·
              refine ⟨27529731220215577142945141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18353154146810384761963427 27529731220215577142945141)
              ·
                refine ⟨2580912301895210357151107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27529731220215577142945141 2580912301895210357151107)
                ·
                  refine ⟨3871368452842815535726661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2580912301895210357151107 3871368452842815535726661)
                  ·
                    refine ⟨725881584908027912948749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3871368452842815535726661 725881584908027912948749)
                    ·
                      rfl

theorem cell22_2120474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 5, 1, 4].length) (baseStart_2120474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2120474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2120474 prefixEnd_2120474 := by exact prefixLift 2120474
  have htrace : WordTrace (prefixWord ++ tailWord_2120474) baseStart_2120474 baseEnd_2120474 := by
    simpa [prefixWord, tailWord_2120474, baseEnd_2120474] using wordTrace_append hprefix tailTrace_2120474
  have hstable : (prefixWord ++ tailWord_2120474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2120474).length < 2 ^ (prefixWord ++ tailWord_2120474).sum := by decide
  have hdescent : baseEnd_2120474 < baseStart_2120474 := by decide
  rcases family_descends (prefixWord ++ tailWord_2120474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2120525 : List Nat := [1, 6, 1, 2, 2, 1, 3, 1, 1, 4]
def baseStart_2120525 : Nat := 118140960795 + 2120525 * 2 ^ 59
def prefixEnd_2120525 : Nat := 4983230072969 + 3 ^ 40 * 2120525 * 2
def baseEnd_2120525 : Nat := 725899043250280779923593

theorem tailTrace_2120525 : CollatzResearch.WordTrace tailWord_2120525 prefixEnd_2120525 725899043250280779923593 := by
  unfold tailWord_2120525
  simp only [CollatzResearch.WordTrace]
  refine ⟨77341900642707556682331029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51561267095138371121554019 77341900642707556682331029)
  ·
    refine ⟨3625401592626916719484267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 77341900642707556682331029 3625401592626916719484267)
    ·
      refine ⟨5438102388940375079226401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3625401592626916719484267 5438102388940375079226401)
      ·
        refine ⟨4078576791705281309419801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5438102388940375079226401 4078576791705281309419801)
        ·
          refine ⟨3058932593778960982064851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4078576791705281309419801 3058932593778960982064851)
          ·
            refine ⟨4588398890668441473097277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3058932593778960982064851 4588398890668441473097277)
            ·
              refine ⟨1720649584000665552411479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4588398890668441473097277 1720649584000665552411479)
              ·
                refine ⟨2580974376000998328617219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1720649584000665552411479 2580974376000998328617219)
                ·
                  refine ⟨3871461564001497492925829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2580974376000998328617219 3871461564001497492925829)
                  ·
                    refine ⟨725899043250280779923593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3871461564001497492925829 725899043250280779923593)
                    ·
                      rfl

theorem cell22_2120525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 3, 1, 1, 4].length) (baseStart_2120525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2120525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2120525 prefixEnd_2120525 := by exact prefixLift 2120525
  have htrace : WordTrace (prefixWord ++ tailWord_2120525) baseStart_2120525 baseEnd_2120525 := by
    simpa [prefixWord, tailWord_2120525, baseEnd_2120525] using wordTrace_append hprefix tailTrace_2120525
  have hstable : (prefixWord ++ tailWord_2120525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2120525).length < 2 ^ (prefixWord ++ tailWord_2120525).sum := by decide
  have hdescent : baseEnd_2120525 < baseStart_2120525 := by decide
  rcases family_descends (prefixWord ++ tailWord_2120525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2120540 : List Nat := [2, 2, 4, 2, 1, 3, 2, 2, 4]
def baseStart_2120540 : Nat := 118140960795 + 2120540 * 2 ^ 59
def prefixEnd_2120540 : Nat := 4983230072969 + 3 ^ 40 * 2120540 * 2
def baseEnd_2120540 : Nat := 241968059352275246932849

theorem tailTrace_2120540 : CollatzResearch.WordTrace tailWord_2120540 prefixEnd_2120540 241968059352275246932849 := by
  unfold tailWord_2120540
  simp only [CollatzResearch.WordTrace]
  refine ⟨38671223868826607122063537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51561631825102142829418049 38671223868826607122063537)
  ·
    refine ⟨29003417901619955341547653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38671223868826607122063537 29003417901619955341547653)
    ·
      refine ⟨5438140856553741626540185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29003417901619955341547653 5438140856553741626540185)
      ·
        refine ⟨4078605642415306219905139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5438140856553741626540185 4078605642415306219905139)
        ·
          refine ⟨6117908463622959329857709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4078605642415306219905139 6117908463622959329857709)
          ·
            refine ⟨2294215673858609748696641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6117908463622959329857709 2294215673858609748696641)
            ·
              refine ⟨1720661755393957311522481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2294215673858609748696641 1720661755393957311522481)
              ·
                refine ⟨1290496316545467983641861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1720661755393957311522481 1290496316545467983641861)
                ·
                  refine ⟨241968059352275246932849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1290496316545467983641861 241968059352275246932849)
                  ·
                    rfl

theorem cell22_2120540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 2, 2, 4].length) (baseStart_2120540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2120540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2120540 prefixEnd_2120540 := by exact prefixLift 2120540
  have htrace : WordTrace (prefixWord ++ tailWord_2120540) baseStart_2120540 baseEnd_2120540 := by
    simpa [prefixWord, tailWord_2120540, baseEnd_2120540] using wordTrace_append hprefix tailTrace_2120540
  have hstable : (prefixWord ++ tailWord_2120540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2120540).length < 2 ^ (prefixWord ++ tailWord_2120540).sum := by decide
  have hdescent : baseEnd_2120540 < baseStart_2120540 := by decide
  rcases family_descends (prefixWord ++ tailWord_2120540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2120583 : List Nat := [1, 1, 4, 2, 3, 1, 1, 5, 1, 3]
def baseStart_2120583 : Nat := 118140960795 + 2120583 * 2 ^ 59
def prefixEnd_2120583 : Nat := 4983230072969 + 3 ^ 40 * 2120583 * 2
def baseEnd_2120583 : Nat := 725918897835587961973415

theorem tailTrace_2120583 : CollatzResearch.WordTrace tailWord_2120583 prefixEnd_2120583 725918897835587961973415 := by
  unfold tailWord_2120583
  simp only [CollatzResearch.WordTrace]
  refine ⟨77344016076497432587942403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51562677384331621725294935 77344016076497432587942403)
  ·
    refine ⟨116016024114746148881913605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77344016076497432587942403 116016024114746148881913605)
    ·
      refine ⟨21753004521514902915358801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 116016024114746148881913605 21753004521514902915358801)
      ·
        refine ⟨16314753391136177186519101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21753004521514902915358801 16314753391136177186519101)
        ·
          refine ⟨6118032521676066444944663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16314753391136177186519101 6118032521676066444944663)
          ·
            refine ⟨9177048782514099667416995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6118032521676066444944663 9177048782514099667416995)
            ·
              refine ⟨13765573173771149501125493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9177048782514099667416995 13765573173771149501125493)
              ·
                refine ⟨1290522485041045265730515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13765573173771149501125493 1290522485041045265730515)
                ·
                  refine ⟨1935783727561567898595773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1290522485041045265730515 1935783727561567898595773)
                  ·
                    refine ⟨725918897835587961973415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1935783727561567898595773 725918897835587961973415)
                    ·
                      rfl

theorem cell22_2120583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 5, 1, 3].length) (baseStart_2120583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2120583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2120583 prefixEnd_2120583 := by exact prefixLift 2120583
  have htrace : WordTrace (prefixWord ++ tailWord_2120583) baseStart_2120583 baseEnd_2120583 := by
    simpa [prefixWord, tailWord_2120583, baseEnd_2120583] using wordTrace_append hprefix tailTrace_2120583
  have hstable : (prefixWord ++ tailWord_2120583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2120583).length < 2 ^ (prefixWord ++ tailWord_2120583).sum := by decide
  have hdescent : baseEnd_2120583 < baseStart_2120583 := by decide
  rcases family_descends (prefixWord ++ tailWord_2120583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2120592 : List Nat := [2, 1, 1, 1, 1, 1, 2, 2, 1, 10]
def baseStart_2120592 : Nat := 118140960795 + 2120592 * 2 ^ 59
def prefixEnd_2120592 : Nat := 4983230072969 + 3 ^ 40 * 2120592 * 2
def baseEnd_2120592 : Nat := 725921978719514938498387

theorem tailTrace_2120592 : CollatzResearch.WordTrace tailWord_2120592 prefixEnd_2120592 725921978719514938498387 := by
  unfold tailWord_2120592
  simp only [CollatzResearch.WordTrace]
  refine ⟨38672172166732413562510015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51562896222309884750013353 38672172166732413562510015)
  ·
    refine ⟨58008258250098620343765023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38672172166732413562510015 58008258250098620343765023)
    ·
      refine ⟨87012387375147930515647535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58008258250098620343765023 87012387375147930515647535)
      ·
        refine ⟨130518581062721895773471303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87012387375147930515647535 130518581062721895773471303)
        ·
          refine ⟨195777871594082843660206955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130518581062721895773471303 195777871594082843660206955)
          ·
            refine ⟨293666807391124265490310433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 195777871594082843660206955 293666807391124265490310433)
            ·
              refine ⟨220250105543343199117732825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 293666807391124265490310433 220250105543343199117732825)
              ·
                refine ⟨165187579157507399338299619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 220250105543343199117732825 165187579157507399338299619)
                ·
                  refine ⟨247781368736261099007449429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 165187579157507399338299619 247781368736261099007449429)
                  ·
                    refine ⟨725921978719514938498387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 247781368736261099007449429 725921978719514938498387)
                    ·
                      rfl

theorem cell22_2120592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 1, 10].length) (baseStart_2120592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2120592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2120592 prefixEnd_2120592 := by exact prefixLift 2120592
  have htrace : WordTrace (prefixWord ++ tailWord_2120592) baseStart_2120592 baseEnd_2120592 := by
    simpa [prefixWord, tailWord_2120592, baseEnd_2120592] using wordTrace_append hprefix tailTrace_2120592
  have hstable : (prefixWord ++ tailWord_2120592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2120592).length < 2 ^ (prefixWord ++ tailWord_2120592).sum := by decide
  have hdescent : baseEnd_2120592 < baseStart_2120592 := by decide
  rcases family_descends (prefixWord ++ tailWord_2120592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2120656 : List Nat := [2, 1, 1, 1, 1, 2, 3, 6, 2, 3]
def baseStart_2120656 : Nat := 118140960795 + 2120656 * 2 ^ 59
def prefixEnd_2120656 : Nat := 4983230072969 + 3 ^ 40 * 2120656 * 2
def baseEnd_2120656 : Nat := 725943887227440104898191

theorem tailTrace_2120656 : CollatzResearch.WordTrace tailWord_2120656 prefixEnd_2120656 725943887227440104898191 := by
  unfold tailWord_2120656
  simp only [CollatzResearch.WordTrace]
  refine ⟨38673339302616483027674911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51564452403488644036899881 38673339302616483027674911)
  ·
    refine ⟨58010008953924724541512367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38673339302616483027674911 58010008953924724541512367)
    ·
      refine ⟨87015013430887086812268551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58010008953924724541512367 87015013430887086812268551)
      ·
        refine ⟨130522520146330630218402827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87015013430887086812268551 130522520146330630218402827)
        ·
          refine ⟨195783780219495945327604241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130522520146330630218402827 195783780219495945327604241)
          ·
            refine ⟨146837835164621958995703181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 195783780219495945327604241 146837835164621958995703181)
            ·
              refine ⟨55064188186733234623388693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 146837835164621958995703181 55064188186733234623388693)
              ·
                refine ⟨2581133821253120372971345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 55064188186733234623388693 2581133821253120372971345)
                ·
                  refine ⟨1935850365939840279728509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2581133821253120372971345 1935850365939840279728509)
                  ·
                    refine ⟨725943887227440104898191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1935850365939840279728509 725943887227440104898191)
                    ·
                      rfl

theorem cell22_2120656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 6, 2, 3].length) (baseStart_2120656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2120656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2120656 prefixEnd_2120656 := by exact prefixLift 2120656
  have htrace : WordTrace (prefixWord ++ tailWord_2120656) baseStart_2120656 baseEnd_2120656 := by
    simpa [prefixWord, tailWord_2120656, baseEnd_2120656] using wordTrace_append hprefix tailTrace_2120656
  have hstable : (prefixWord ++ tailWord_2120656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2120656).length < 2 ^ (prefixWord ++ tailWord_2120656).sum := by decide
  have hdescent : baseEnd_2120656 < baseStart_2120656 := by decide
  rcases family_descends (prefixWord ++ tailWord_2120656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2120658 : List Nat := [3, 2, 2, 3, 1, 3, 1, 1, 6]
def baseStart_2120658 : Nat := 118140960795 + 2120658 * 2 ^ 59
def prefixEnd_2120658 : Nat := 4983230072969 + 3 ^ 40 * 2120658 * 2
def baseEnd_2120658 : Nat := 241981523956104255449395

theorem tailTrace_2120658 : CollatzResearch.WordTrace tailWord_2120658 prefixEnd_2120658 241981523956104255449395 := by
  unfold tailWord_2120658
  simp only [CollatzResearch.WordTrace]
  refine ⟨19336687887806430099230657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51564501034150480264615085 19336687887806430099230657)
  ·
    refine ⟨14502515915854822574422993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19336687887806430099230657 14502515915854822574422993)
    ·
      refine ⟨10876886936891116930817245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14502515915854822574422993 10876886936891116930817245)
      ·
        refine ⟨4078832601334168849056467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10876886936891116930817245 4078832601334168849056467)
        ·
          refine ⟨6118248902001253273584701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4078832601334168849056467 6118248902001253273584701)
          ·
            refine ⟨2294343338250469977594263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6118248902001253273584701 2294343338250469977594263)
            ·
              refine ⟨3441515007375704966391395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2294343338250469977594263 3441515007375704966391395)
              ·
                refine ⟨5162272511063557449587093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3441515007375704966391395 5162272511063557449587093)
                ·
                  refine ⟨241981523956104255449395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5162272511063557449587093 241981523956104255449395)
                  ·
                    rfl

theorem cell22_2120658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 1, 1, 6].length) (baseStart_2120658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2120658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2120658 prefixEnd_2120658 := by exact prefixLift 2120658
  have htrace : WordTrace (prefixWord ++ tailWord_2120658) baseStart_2120658 baseEnd_2120658 := by
    simpa [prefixWord, tailWord_2120658, baseEnd_2120658] using wordTrace_append hprefix tailTrace_2120658
  have hstable : (prefixWord ++ tailWord_2120658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2120658).length < 2 ^ (prefixWord ++ tailWord_2120658).sum := by decide
  have hdescent : baseEnd_2120658 < baseStart_2120658 := by decide
  rcases family_descends (prefixWord ++ tailWord_2120658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2120677 : List Nat := [1, 3, 1, 6, 2, 1, 1, 2, 1, 4]
def baseStart_2120677 : Nat := 118140960795 + 2120677 * 2 ^ 59
def prefixEnd_2120677 : Nat := 4983230072969 + 3 ^ 40 * 2120677 * 2
def baseEnd_2120677 : Nat := 725951075956603050123127

theorem tailTrace_2120677 : CollatzResearch.WordTrace tailWord_2120677 prefixEnd_2120677 725951075956603050123127 := by
  unfold tailWord_2120677
  simp only [CollatzResearch.WordTrace]
  refine ⟨77347444538156886641864285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51564963025437924427909523 77347444538156886641864285)
  ·
    refine ⟨29005291701808832490699107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77347444538156886641864285 29005291701808832490699107)
    ·
      refine ⟨43507937552713248736048661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29005291701808832490699107 43507937552713248736048661)
      ·
        refine ⟨2039434572783433534502281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 43507937552713248736048661 2039434572783433534502281)
        ·
          refine ⟨1529575929587575150876711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2039434572783433534502281 1529575929587575150876711)
          ·
            refine ⟨2294363894381362726315067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1529575929587575150876711 2294363894381362726315067)
            ·
              refine ⟨3441545841572044089472601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2294363894381362726315067 3441545841572044089472601)
              ·
                refine ⟨2581159381179033067104451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3441545841572044089472601 2581159381179033067104451)
                ·
                  refine ⟨3871739071768549600656677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2581159381179033067104451 3871739071768549600656677)
                  ·
                    refine ⟨725951075956603050123127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3871739071768549600656677 725951075956603050123127)
                    ·
                      rfl

theorem cell22_2120677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 1, 2, 1, 4].length) (baseStart_2120677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2120677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2120677 prefixEnd_2120677 := by exact prefixLift 2120677
  have htrace : WordTrace (prefixWord ++ tailWord_2120677) baseStart_2120677 baseEnd_2120677 := by
    simpa [prefixWord, tailWord_2120677, baseEnd_2120677] using wordTrace_append hprefix tailTrace_2120677
  have hstable : (prefixWord ++ tailWord_2120677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2120677).length < 2 ^ (prefixWord ++ tailWord_2120677).sum := by decide
  have hdescent : baseEnd_2120677 < baseStart_2120677 := by decide
  rcases family_descends (prefixWord ++ tailWord_2120677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2120729 : List Nat := [1, 2, 1, 2, 1, 1, 5, 1, 1, 7]
def baseStart_2120729 : Nat := 118140960795 + 2120729 * 2 ^ 59
def prefixEnd_2120729 : Nat := 4983230072969 + 3 ^ 40 * 2120729 * 2
def baseEnd_2120729 : Nat := 725968876619292247822967

theorem tailTrace_2120729 : CollatzResearch.WordTrace tailWord_2120729 prefixEnd_2120729 725968876619292247822967 := by
  unfold tailWord_2120729
  simp only [CollatzResearch.WordTrace]
  refine ⟨77349341133968499522757241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51566227422645666348504827 77349341133968499522757241)
  ·
    refine ⟨58012005850476374642067931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77349341133968499522757241 58012005850476374642067931)
    ·
      refine ⟨87018008775714561963101897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58012005850476374642067931 87018008775714561963101897)
      ·
        refine ⟨65263506581785921472326423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87018008775714561963101897 65263506581785921472326423)
        ·
          refine ⟨97895259872678882208489635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65263506581785921472326423 97895259872678882208489635)
          ·
            refine ⟨146842889809018323312734453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97895259872678882208489635 146842889809018323312734453)
            ·
              refine ⟨13766520919595467810568855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 146842889809018323312734453 13766520919595467810568855)
              ·
                refine ⟨20649781379393201715853283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13766520919595467810568855 20649781379393201715853283)
                ·
                  refine ⟨30974672069089802573779925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20649781379393201715853283 30974672069089802573779925)
                  ·
                    refine ⟨725968876619292247822967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30974672069089802573779925 725968876619292247822967)
                    ·
                      rfl

theorem cell22_2120729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 1, 1, 7].length) (baseStart_2120729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2120729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2120729 prefixEnd_2120729 := by exact prefixLift 2120729
  have htrace : WordTrace (prefixWord ++ tailWord_2120729) baseStart_2120729 baseEnd_2120729 := by
    simpa [prefixWord, tailWord_2120729, baseEnd_2120729] using wordTrace_append hprefix tailTrace_2120729
  have hstable : (prefixWord ++ tailWord_2120729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2120729).length < 2 ^ (prefixWord ++ tailWord_2120729).sum := by decide
  have hdescent : baseEnd_2120729 < baseStart_2120729 := by decide
  rcases family_descends (prefixWord ++ tailWord_2120729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2120759 : List Nat := [1, 1, 3, 1, 2, 2, 1, 1, 10]
def baseStart_2120759 : Nat := 118140960795 + 2120759 * 2 ^ 59
def prefixEnd_2120759 : Nat := 4983230072969 + 3 ^ 40 * 2120759 * 2
def baseEnd_2120759 : Nat := 241993048744127389857625

theorem tailTrace_2120759 : CollatzResearch.WordTrace tailWord_2120759 prefixEnd_2120759 241993048744127389857625 := by
  unfold tailWord_2120759
  simp only [CollatzResearch.WordTrace]
  refine ⟨77350435323859814646349331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51566956882573209764232887 77350435323859814646349331)
  ·
    refine ⟨116025652985789721969523997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77350435323859814646349331 116025652985789721969523997)
    ·
      refine ⟨43509619869671145738571499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116025652985789721969523997 43509619869671145738571499)
      ·
        refine ⟨65264429804506718607857249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43509619869671145738571499 65264429804506718607857249)
        ·
          refine ⟨48948322353380038955892937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65264429804506718607857249 48948322353380038955892937)
          ·
            refine ⟨36711241765035029216919703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48948322353380038955892937 36711241765035029216919703)
            ·
              refine ⟨55066862647552543825379555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36711241765035029216919703 55066862647552543825379555)
              ·
                refine ⟨82600293971328815738069333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55066862647552543825379555 82600293971328815738069333)
                ·
                  refine ⟨241993048744127389857625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 82600293971328815738069333 241993048744127389857625)
                  ·
                    rfl

theorem cell22_2120759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 10].length) (baseStart_2120759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2120759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2120759 prefixEnd_2120759 := by exact prefixLift 2120759
  have htrace : WordTrace (prefixWord ++ tailWord_2120759) baseStart_2120759 baseEnd_2120759 := by
    simpa [prefixWord, tailWord_2120759, baseEnd_2120759] using wordTrace_append hprefix tailTrace_2120759
  have hstable : (prefixWord ++ tailWord_2120759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2120759).length < 2 ^ (prefixWord ++ tailWord_2120759).sum := by decide
  have hdescent : baseEnd_2120759 < baseStart_2120759 := by decide
  rcases family_descends (prefixWord ++ tailWord_2120759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2120776 : List Nat := [2, 1, 3, 1, 1, 1, 6, 1, 6]
def baseStart_2120776 : Nat := 118140960795 + 2120776 * 2 ^ 59
def prefixEnd_2120776 : Nat := 4983230072969 + 3 ^ 40 * 2120776 * 2
def baseEnd_2120776 : Nat := 241994988559933263965941

theorem tailTrace_2120776 : CollatzResearch.WordTrace tailWord_2120776 prefixEnd_2120776 241994988559933263965941 := by
  unfold tailWord_2120776
  simp only [CollatzResearch.WordTrace]
  refine ⟨38675527682399113274859091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51567370243198817699812121 38675527682399113274859091)
  ·
    refine ⟨58013291523598669912288637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38675527682399113274859091 58013291523598669912288637)
    ·
      refine ⟨21754984321349501217108239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58013291523598669912288637 21754984321349501217108239)
      ·
        refine ⟨32632476482024251825662359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21754984321349501217108239 32632476482024251825662359)
        ·
          refine ⟨48948714723036377738493539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32632476482024251825662359 48948714723036377738493539)
          ·
            refine ⟨73423072084554566607740309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48948714723036377738493539 73423072084554566607740309)
            ·
              refine ⟨3441706503963495309737827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 73423072084554566607740309 3441706503963495309737827)
              ·
                refine ⟨5162559755945242964606741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3441706503963495309737827 5162559755945242964606741)
                ·
                  refine ⟨241994988559933263965941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5162559755945242964606741 241994988559933263965941)
                  ·
                    rfl

theorem cell22_2120776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6, 1, 6].length) (baseStart_2120776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2120776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2120776 prefixEnd_2120776 := by exact prefixLift 2120776
  have htrace : WordTrace (prefixWord ++ tailWord_2120776) baseStart_2120776 baseEnd_2120776 := by
    simpa [prefixWord, tailWord_2120776, baseEnd_2120776] using wordTrace_append hprefix tailTrace_2120776
  have hstable : (prefixWord ++ tailWord_2120776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2120776).length < 2 ^ (prefixWord ++ tailWord_2120776).sum := by decide
  have hdescent : baseEnd_2120776 < baseStart_2120776 := by decide
  rcases family_descends (prefixWord ++ tailWord_2120776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2120810 : List Nat := [3, 1, 3, 2, 2, 1, 3, 3, 4]
def baseStart_2120810 : Nat := 118140960795 + 2120810 * 2 ^ 59
def prefixEnd_2120810 : Nat := 4983230072969 + 3 ^ 40 * 2120810 * 2
def baseEnd_2120810 : Nat := 241998868191545012182573

theorem tailTrace_2120810 : CollatzResearch.WordTrace tailWord_2120810 prefixEnd_2120810 241998868191545012182573 := by
  unfold tailWord_2120810
  simp only [CollatzResearch.WordTrace]
  refine ⟨19338073861668762589113971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51568196964450033570970589 19338073861668762589113971)
  ·
    refine ⟨29007110792503143883670957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19338073861668762589113971 29007110792503143883670957)
    ·
      refine ⟨10877666547188678956376609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29007110792503143883670957 10877666547188678956376609)
      ·
        refine ⟨8158249910391509217282457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10877666547188678956376609 8158249910391509217282457)
        ·
          refine ⟨6118687432793631912961843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8158249910391509217282457 6118687432793631912961843)
          ·
            refine ⟨9178031149190447869442765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6118687432793631912961843 9178031149190447869442765)
            ·
              refine ⟨3441761680946417951041037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9178031149190447869442765 3441761680946417951041037)
              ·
                refine ⟨1290660630354906731640389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3441761680946417951041037 1290660630354906731640389)
                ·
                  refine ⟨241998868191545012182573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1290660630354906731640389 241998868191545012182573)
                  ·
                    rfl

theorem cell22_2120810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3, 3, 4].length) (baseStart_2120810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2120810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2120810 prefixEnd_2120810 := by exact prefixLift 2120810
  have htrace : WordTrace (prefixWord ++ tailWord_2120810) baseStart_2120810 baseEnd_2120810 := by
    simpa [prefixWord, tailWord_2120810, baseEnd_2120810] using wordTrace_append hprefix tailTrace_2120810
  have hstable : (prefixWord ++ tailWord_2120810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2120810).length < 2 ^ (prefixWord ++ tailWord_2120810).sum := by decide
  have hdescent : baseEnd_2120810 < baseStart_2120810 := by decide
  rcases family_descends (prefixWord ++ tailWord_2120810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2120913 : List Nat := [1, 2, 2, 1, 2, 2, 1, 6, 1, 4]
def baseStart_2120913 : Nat := 118140960795 + 2120913 * 2 ^ 59
def prefixEnd_2120913 : Nat := 4983230072969 + 3 ^ 40 * 2120913 * 2
def baseEnd_2120913 : Nat := 726031863579577101222403

theorem tailTrace_2120913 : CollatzResearch.WordTrace tailWord_2120913 prefixEnd_2120913 726031863579577101222403 := by
  unfold tailWord_2120913
  simp only [CollatzResearch.WordTrace]
  refine ⟨77356052165301898947455393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51570701443534599298303595 77356052165301898947455393)
  ·
    refine ⟨58017039123976424210591545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77356052165301898947455393 58017039123976424210591545)
    ·
      refine ⟨43512779342982318157943659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58017039123976424210591545 43512779342982318157943659)
      ·
        refine ⟨65269169014473477236915489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43512779342982318157943659 65269169014473477236915489)
        ·
          refine ⟨48951876760855107927686617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65269169014473477236915489 48951876760855107927686617)
          ·
            refine ⟨36713907570641330945764963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48951876760855107927686617 36713907570641330945764963)
            ·
              refine ⟨55070861355961996418647445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36713907570641330945764963 55070861355961996418647445)
              ·
                refine ⟨2581446626060718582124099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 55070861355961996418647445 2581446626060718582124099)
                ·
                  refine ⟨3872169939091077873186149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2581446626060718582124099 3872169939091077873186149)
                  ·
                    refine ⟨726031863579577101222403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3872169939091077873186149 726031863579577101222403)
                    ·
                      rfl

theorem cell22_2120913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 6, 1, 4].length) (baseStart_2120913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2120913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2120913 prefixEnd_2120913 := by exact prefixLift 2120913
  have htrace : WordTrace (prefixWord ++ tailWord_2120913) baseStart_2120913 baseEnd_2120913 := by
    simpa [prefixWord, tailWord_2120913, baseEnd_2120913] using wordTrace_append hprefix tailTrace_2120913
  have hstable : (prefixWord ++ tailWord_2120913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2120913).length < 2 ^ (prefixWord ++ tailWord_2120913).sum := by decide
  have hdescent : baseEnd_2120913 < baseStart_2120913 := by decide
  rcases family_descends (prefixWord ++ tailWord_2120913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2121056 : List Nat := [2, 1, 1, 3, 4, 3, 2, 2, 1, 3]
def baseStart_2121056 : Nat := 118140960795 + 2121056 * 2 ^ 59
def prefixEnd_2121056 : Nat := 4983230072969 + 3 ^ 40 * 2121056 * 2
def baseEnd_2121056 : Nat := 726080815401972394896965

theorem tailTrace_2121056 : CollatzResearch.WordTrace tailWord_2121056 prefixEnd_2121056 726080815401972394896965 := by
  unfold tailWord_2121056
  simp only [CollatzResearch.WordTrace]
  refine ⟨38680633901891917184955511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51574178535855889579940681 38680633901891917184955511)
  ·
    refine ⟨58020950852837875777433267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38680633901891917184955511 58020950852837875777433267)
    ·
      refine ⟨87031426279256813666149901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58020950852837875777433267 87031426279256813666149901)
      ·
        refine ⟨32636784854721305124806213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87031426279256813666149901 32636784854721305124806213)
        ·
          refine ⟨6119397160260244710901165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32636784854721305124806213 6119397160260244710901165)
          ·
            refine ⟨2294773935097591766587937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6119397160260244710901165 2294773935097591766587937)
            ·
              refine ⟨1721080451323193824940953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2294773935097591766587937 1721080451323193824940953)
              ·
                refine ⟨1290810338492395368705715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1721080451323193824940953 1290810338492395368705715)
                ·
                  refine ⟨1936215507738593053058573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1290810338492395368705715 1936215507738593053058573)
                  ·
                    refine ⟨726080815401972394896965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1936215507738593053058573 726080815401972394896965)
                    ·
                      rfl

theorem cell22_2121056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 2, 2, 1, 3].length) (baseStart_2121056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2121056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2121056 prefixEnd_2121056 := by exact prefixLift 2121056
  have htrace : WordTrace (prefixWord ++ tailWord_2121056) baseStart_2121056 baseEnd_2121056 := by
    simpa [prefixWord, tailWord_2121056, baseEnd_2121056] using wordTrace_append hprefix tailTrace_2121056
  have hstable : (prefixWord ++ tailWord_2121056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2121056).length < 2 ^ (prefixWord ++ tailWord_2121056).sum := by decide
  have hdescent : baseEnd_2121056 < baseStart_2121056 := by decide
  rcases family_descends (prefixWord ++ tailWord_2121056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2121095 : List Nat := [1, 1, 4, 2, 2, 2, 2, 2, 1, 5]
def baseStart_2121095 : Nat := 118140960795 + 2121095 * 2 ^ 59
def prefixEnd_2121095 : Nat := 4983230072969 + 3 ^ 40 * 2121095 * 2
def baseEnd_2121095 : Nat := 726094165898989293171845

theorem tailTrace_2121095 : CollatzResearch.WordTrace tailWord_2121095 prefixEnd_2121095 726094165898989293171845 := by
  unfold tailWord_2121095
  simp only [CollatzResearch.WordTrace]
  refine ⟨77362690250642544030580739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51575126833761696020387159 77362690250642544030580739)
  ·
    refine ⟨116044035375963816045871109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77362690250642544030580739 116044035375963816045871109)
    ·
      refine ⟨21758256632993215508600833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 116044035375963816045871109 21758256632993215508600833)
      ·
        refine ⟨16318692474744911631450625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21758256632993215508600833 16318692474744911631450625)
        ·
          refine ⟨12239019356058683723587969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16318692474744911631450625 12239019356058683723587969)
          ·
            refine ⟨9179264517044012792690977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12239019356058683723587969 9179264517044012792690977)
            ·
              refine ⟨6884448387783009594518233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9179264517044012792690977 6884448387783009594518233)
              ·
                refine ⟨5163336290837257195888675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6884448387783009594518233 5163336290837257195888675)
                ·
                  refine ⟨7745004436255885793833013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5163336290837257195888675 7745004436255885793833013)
                  ·
                    refine ⟨726094165898989293171845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7745004436255885793833013 726094165898989293171845)
                    ·
                      rfl

theorem cell22_2121095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 2, 1, 5].length) (baseStart_2121095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2121095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2121095 prefixEnd_2121095 := by exact prefixLift 2121095
  have htrace : WordTrace (prefixWord ++ tailWord_2121095) baseStart_2121095 baseEnd_2121095 := by
    simpa [prefixWord, tailWord_2121095, baseEnd_2121095] using wordTrace_append hprefix tailTrace_2121095
  have hstable : (prefixWord ++ tailWord_2121095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2121095).length < 2 ^ (prefixWord ++ tailWord_2121095).sum := by decide
  have hdescent : baseEnd_2121095 < baseStart_2121095 := by decide
  rcases family_descends (prefixWord ++ tailWord_2121095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2121187 : List Nat := [1, 1, 1, 6, 2, 2, 1, 3, 5]
def baseStart_2121187 : Nat := 118140960795 + 2121187 * 2 ^ 59
def prefixEnd_2121187 : Nat := 4983230072969 + 3 ^ 40 * 2121187 * 2
def baseEnd_2121187 : Nat := 242041886459710573290521

theorem tailTrace_2121187 : CollatzResearch.WordTrace tailWord_2121187 prefixEnd_2121187 242041886459710573290521 := by
  unfold tailWord_2121187
  simp only [CollatzResearch.WordTrace]
  refine ⟨77366045766309243742929815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51577363844206162495286543 77366045766309243742929815)
  ·
    refine ⟨116049068649463865614394723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77366045766309243742929815 116049068649463865614394723)
    ·
      refine ⟨174073602974195798421592085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116049068649463865614394723 174073602974195798421592085)
      ·
        refine ⟨8159700139415428051012129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 174073602974195798421592085 8159700139415428051012129)
        ·
          refine ⟨6119775104561571038259097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8159700139415428051012129 6119775104561571038259097)
          ·
            refine ⟨4589831328421178278694323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6119775104561571038259097 4589831328421178278694323)
            ·
              refine ⟨6884746992631767418041485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4589831328421178278694323 6884746992631767418041485)
              ·
                refine ⟨2581780122236912781765557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6884746992631767418041485 2581780122236912781765557)
                ·
                  refine ⟨242041886459710573290521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2581780122236912781765557 242041886459710573290521)
                  ·
                    rfl

theorem cell22_2121187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 3, 5].length) (baseStart_2121187 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2121187 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2121187 prefixEnd_2121187 := by exact prefixLift 2121187
  have htrace : WordTrace (prefixWord ++ tailWord_2121187) baseStart_2121187 baseEnd_2121187 := by
    simpa [prefixWord, tailWord_2121187, baseEnd_2121187] using wordTrace_append hprefix tailTrace_2121187
  have hstable : (prefixWord ++ tailWord_2121187).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2121187).length < 2 ^ (prefixWord ++ tailWord_2121187).sum := by decide
  have hdescent : baseEnd_2121187 < baseStart_2121187 := by decide
  rcases family_descends (prefixWord ++ tailWord_2121187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2121277 : List Nat := [1, 4, 1, 3, 3, 1, 9]
def baseStart_2121277 : Nat := 118140960795 + 2121277 * 2 ^ 59
def prefixEnd_2121277 : Nat := 4983230072969 + 3 ^ 40 * 2121277 * 2
def baseEnd_2121277 : Nat := 26894684008088943893381

theorem tailTrace_2121277 : CollatzResearch.WordTrace tailWord_2121277 prefixEnd_2121277 26894684008088943893381 := by
  unfold tailWord_2121277
  simp only [CollatzResearch.WordTrace]
  refine ⟨77369328335983189113706085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51579552223988792742470723 77369328335983189113706085)
  ·
    refine ⟨14506749062996847958819891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77369328335983189113706085 14506749062996847958819891)
    ·
      refine ⟨21760123594495271938229837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14506749062996847958819891 21760123594495271938229837)
      ·
        refine ⟨8160046347935726976836189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21760123594495271938229837 8160046347935726976836189)
        ·
          refine ⟨3060017380475897616313571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8160046347935726976836189 3060017380475897616313571)
          ·
            refine ⟨4590026070713846424470357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3060017380475897616313571 4590026070713846424470357)
            ·
              refine ⟨26894684008088943893381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4590026070713846424470357 26894684008088943893381)
              ·
                rfl

theorem cell22_2121277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 9].length) (baseStart_2121277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2121277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2121277 prefixEnd_2121277 := by exact prefixLift 2121277
  have htrace : WordTrace (prefixWord ++ tailWord_2121277) baseStart_2121277 baseEnd_2121277 := by
    simpa [prefixWord, tailWord_2121277, baseEnd_2121277] using wordTrace_append hprefix tailTrace_2121277
  have hstable : (prefixWord ++ tailWord_2121277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2121277).length < 2 ^ (prefixWord ++ tailWord_2121277).sum := by decide
  have hdescent : baseEnd_2121277 < baseStart_2121277 := by decide
  rcases family_descends (prefixWord ++ tailWord_2121277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2121322 : List Nat := [3, 1, 3, 2, 1, 2, 1, 2, 7]
def baseStart_2121322 : Nat := 118140960795 + 2121322 * 2 ^ 59
def prefixEnd_2121322 : Nat := 4983230072969 + 3 ^ 40 * 2121322 * 2
def baseEnd_2121322 : Nat := 242057290879345455915383

theorem tailTrace_2121322 : CollatzResearch.WordTrace tailWord_2121322 prefixEnd_2121322 242057290879345455915383 := by
  unfold tailWord_2121322
  simp only [CollatzResearch.WordTrace]
  refine ⟨19342742405205040449773555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51580646413880107866062813 19342742405205040449773555)
  ·
    refine ⟨29014113607807560674660333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19342742405205040449773555 29014113607807560674660333)
    ·
      refine ⟨10880292602927835252997625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29014113607807560674660333 10880292602927835252997625)
      ·
        refine ⟨8160219452195876439748219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10880292602927835252997625 8160219452195876439748219)
        ·
          refine ⟨12240329178293814659622329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8160219452195876439748219 12240329178293814659622329)
          ·
            refine ⟨9180246883720360994716747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12240329178293814659622329 9180246883720360994716747)
            ·
              refine ⟨13770370325580541492075121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9180246883720360994716747 13770370325580541492075121)
              ·
                refine ⟨10327777744185406119056341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13770370325580541492075121 10327777744185406119056341)
                ·
                  refine ⟨242057290879345455915383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10327777744185406119056341 242057290879345455915383)
                  ·
                    rfl

theorem cell22_2121322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 2, 7].length) (baseStart_2121322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2121322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2121322 prefixEnd_2121322 := by exact prefixLift 2121322
  have htrace : WordTrace (prefixWord ++ tailWord_2121322) baseStart_2121322 baseEnd_2121322 := by
    simpa [prefixWord, tailWord_2121322, baseEnd_2121322] using wordTrace_append hprefix tailTrace_2121322
  have hstable : (prefixWord ++ tailWord_2121322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2121322).length < 2 ^ (prefixWord ++ tailWord_2121322).sum := by decide
  have hdescent : baseEnd_2121322 < baseStart_2121322 := by decide
  rcases family_descends (prefixWord ++ tailWord_2121322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2121401 : List Nat := [1, 2, 1, 4, 1, 1, 6, 2, 4]
def baseStart_2121401 : Nat := 118140960795 + 2121401 * 2 ^ 59
def prefixEnd_2121401 : Nat := 4983230072969 + 3 ^ 40 * 2121401 * 2
def baseEnd_2121401 : Nat := 242066305317502165006969

theorem tailTrace_2121401 : CollatzResearch.WordTrace tailWord_2121401 prefixEnd_2121401 242066305317502165006969 := by
  unfold tailWord_2121401
  simp only [CollatzResearch.WordTrace]
  refine ⟨77373850987533958291220057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51582567325022638860813371 77373850987533958291220057)
  ·
    refine ⟨58030388240650468718415043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77373850987533958291220057 58030388240650468718415043)
    ·
      refine ⟨87045582360975703077622565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58030388240650468718415043 87045582360975703077622565)
      ·
        refine ⟨16321046692682944327054231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 87045582360975703077622565 16321046692682944327054231)
        ·
          refine ⟨24481570039024416490581347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16321046692682944327054231 24481570039024416490581347)
          ·
            refine ⟨36722355058536624735872021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24481570039024416490581347 36722355058536624735872021)
            ·
              refine ⟨1721360393368904284494001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 36722355058536624735872021 1721360393368904284494001)
              ·
                refine ⟨1291020295026678213370501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1721360393368904284494001 1291020295026678213370501)
                ·
                  refine ⟨242066305317502165006969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1291020295026678213370501 242066305317502165006969)
                  ·
                    rfl

theorem cell22_2121401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 6, 2, 4].length) (baseStart_2121401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2121401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2121401 prefixEnd_2121401 := by exact prefixLift 2121401
  have htrace : WordTrace (prefixWord ++ tailWord_2121401) baseStart_2121401 baseEnd_2121401 := by
    simpa [prefixWord, tailWord_2121401, baseEnd_2121401] using wordTrace_append hprefix tailTrace_2121401
  have hstable : (prefixWord ++ tailWord_2121401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2121401).length < 2 ^ (prefixWord ++ tailWord_2121401).sum := by decide
  have hdescent : baseEnd_2121401 < baseStart_2121401 := by decide
  rcases family_descends (prefixWord ++ tailWord_2121401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2121437 : List Nat := [1, 4, 3, 3, 2, 1, 2, 1, 1, 4]
def baseStart_2121437 : Nat := 118140960795 + 2121437 * 2 ^ 59
def prefixEnd_2121437 : Nat := 4983230072969 + 3 ^ 40 * 2121437 * 2
def baseEnd_2121437 : Nat := 726211239488214401120797

theorem tailTrace_2121437 : CollatzResearch.WordTrace tailWord_2121437 prefixEnd_2121437 726211239488214401120797 := by
  unfold tailWord_2121437
  simp only [CollatzResearch.WordTrace]
  refine ⟨77375164015403536439530565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51583442676935690959687043 77375164015403536439530565)
  ·
    refine ⟨14507843252888163082411981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77375164015403536439530565 14507843252888163082411981)
    ·
      refine ⟨5440441219833061155904493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14507843252888163082411981 5440441219833061155904493)
      ·
        refine ⟨2040165457437397933464185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5440441219833061155904493 2040165457437397933464185)
        ·
          refine ⟨1530124093078048450098139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2040165457437397933464185 1530124093078048450098139)
          ·
            refine ⟨2295186139617072675147209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1530124093078048450098139 2295186139617072675147209)
            ·
              refine ⟨1721389604712804506360407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2295186139617072675147209 1721389604712804506360407)
              ·
                refine ⟨2582084407069206759540611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1721389604712804506360407 2582084407069206759540611)
                ·
                  refine ⟨3873126610603810139310917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2582084407069206759540611 3873126610603810139310917)
                  ·
                    refine ⟨726211239488214401120797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3873126610603810139310917 726211239488214401120797)
                    ·
                      rfl

theorem cell22_2121437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 2, 1, 1, 4].length) (baseStart_2121437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2121437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2121437 prefixEnd_2121437 := by exact prefixLift 2121437
  have htrace : WordTrace (prefixWord ++ tailWord_2121437) baseStart_2121437 baseEnd_2121437 := by
    simpa [prefixWord, tailWord_2121437, baseEnd_2121437] using wordTrace_append hprefix tailTrace_2121437
  have hstable : (prefixWord ++ tailWord_2121437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2121437).length < 2 ^ (prefixWord ++ tailWord_2121437).sum := by decide
  have hdescent : baseEnd_2121437 < baseStart_2121437 := by decide
  rcases family_descends (prefixWord ++ tailWord_2121437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2121444 : List Nat := [2, 3, 1, 1, 1, 3, 1, 2, 5, 3]
def baseStart_2121444 : Nat := 118140960795 + 2121444 * 2 ^ 59
def prefixEnd_2121444 : Nat := 4983230072969 + 3 ^ 40 * 2121444 * 2
def baseEnd_2121444 : Nat := 726213635731268716195775

theorem tailTrace_2121444 : CollatzResearch.WordTrace tailWord_2121444 prefixEnd_2121444 726213635731268716195775 := by
  unfold tailWord_2121444
  simp only [CollatzResearch.WordTrace]
  refine ⟨38687709663189088317517693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51583612884252117756690257 38687709663189088317517693)
  ·
    refine ⟨14507891123695908119069135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38687709663189088317517693 14507891123695908119069135)
    ·
      refine ⟨21761836685543862178603703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14507891123695908119069135 21761836685543862178603703)
      ·
        refine ⟨32642755028315793267905555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21761836685543862178603703 32642755028315793267905555)
        ·
          refine ⟨48964132542473689901858333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32642755028315793267905555 48964132542473689901858333)
          ·
            refine ⟨18361549703427633713196875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48964132542473689901858333 18361549703427633713196875)
            ·
              refine ⟨27542324555141450569795313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18361549703427633713196875 27542324555141450569795313)
              ·
                refine ⟨20656743416356087927346485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27542324555141450569795313 20656743416356087927346485)
                ·
                  refine ⟨1936569695283383243188733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20656743416356087927346485 1936569695283383243188733)
                  ·
                    refine ⟨726213635731268716195775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1936569695283383243188733 726213635731268716195775)
                    ·
                      rfl

theorem cell22_2121444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 2, 5, 3].length) (baseStart_2121444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2121444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2121444 prefixEnd_2121444 := by exact prefixLift 2121444
  have htrace : WordTrace (prefixWord ++ tailWord_2121444) baseStart_2121444 baseEnd_2121444 := by
    simpa [prefixWord, tailWord_2121444, baseEnd_2121444] using wordTrace_append hprefix tailTrace_2121444
  have hstable : (prefixWord ++ tailWord_2121444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2121444).length < 2 ^ (prefixWord ++ tailWord_2121444).sum := by decide
  have hdescent : baseEnd_2121444 < baseStart_2121444 := by decide
  rcases family_descends (prefixWord ++ tailWord_2121444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2121495 : List Nat := [1, 1, 3, 4, 2, 3, 1, 3, 1, 3]
def baseStart_2121495 : Nat := 118140960795 + 2121495 * 2 ^ 59
def prefixEnd_2121495 : Nat := 4983230072969 + 3 ^ 40 * 2121495 * 2
def baseEnd_2121495 : Nat := 726231094073521583170619

theorem tailTrace_2121495 : CollatzResearch.WordTrace tailWord_2121495 prefixEnd_2121495 726231094073521583170619 := by
  unfold tailWord_2121495
  simp only [CollatzResearch.WordTrace]
  refine ⟨77377279449193412345141939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51584852966128941563427959 77377279449193412345141939)
  ·
    refine ⟨116065919173790118517712909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77377279449193412345141939 116065919173790118517712909)
    ·
      refine ⟨43524719690171294444142341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116065919173790118517712909 43524719690171294444142341)
      ·
        refine ⟨8160884941907117708276689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43524719690171294444142341 8160884941907117708276689)
        ·
          refine ⟨6120663706430338281207517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8160884941907117708276689 6120663706430338281207517)
          ·
            refine ⟨2295248889911376855452819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6120663706430338281207517 2295248889911376855452819)
            ·
              refine ⟨3442873334867065283179229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2295248889911376855452819 3442873334867065283179229)
              ·
                refine ⟨1291077500575149481192211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3442873334867065283179229 1291077500575149481192211)
                ·
                  refine ⟨1936616250862724221788317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1291077500575149481192211 1936616250862724221788317)
                  ·
                    refine ⟨726231094073521583170619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1936616250862724221788317 726231094073521583170619)
                    ·
                      rfl

theorem cell22_2121495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 1, 3, 1, 3].length) (baseStart_2121495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2121495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2121495 prefixEnd_2121495 := by exact prefixLift 2121495
  have htrace : WordTrace (prefixWord ++ tailWord_2121495) baseStart_2121495 baseEnd_2121495 := by
    simpa [prefixWord, tailWord_2121495, baseEnd_2121495] using wordTrace_append hprefix tailTrace_2121495
  have hstable : (prefixWord ++ tailWord_2121495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2121495).length < 2 ^ (prefixWord ++ tailWord_2121495).sum := by decide
  have hdescent : baseEnd_2121495 < baseStart_2121495 := by decide
  rcases family_descends (prefixWord ++ tailWord_2121495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2121525 : List Nat := [1, 3, 3, 1, 5, 1, 2, 1, 5]
def baseStart_2121525 : Nat := 118140960795 + 2121525 * 2 ^ 59
def prefixEnd_2121525 : Nat := 4983230072969 + 3 ^ 40 * 2121525 * 2
def baseEnd_2121525 : Nat := 242080454562203834973509

theorem tailTrace_2121525 : CollatzResearch.WordTrace tailWord_2121525 prefixEnd_2121525 242080454562203834973509 := by
  unfold tailWord_2121525
  simp only [CollatzResearch.WordTrace]
  refine ⟨77378373639084727468734029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51585582426056484979156019 77378373639084727468734029)
  ·
    refine ⟨29016890114656772800775261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77378373639084727468734029 29016890114656772800775261)
    ·
      refine ⟨10881333792996289800290723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29016890114656772800775261 10881333792996289800290723)
      ·
        refine ⟨16322000689494434700436085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10881333792996289800290723 16322000689494434700436085)
        ·
          refine ⟨1530187564640103253165883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16322000689494434700436085 1530187564640103253165883)
          ·
            refine ⟨2295281346960154879748825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1530187564640103253165883 2295281346960154879748825)
            ·
              refine ⟨1721461010220116159811619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2295281346960154879748825 1721461010220116159811619)
              ·
                refine ⟨2582191515330174239717429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1721461010220116159811619 2582191515330174239717429)
                ·
                  refine ⟨242080454562203834973509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2582191515330174239717429 242080454562203834973509)
                  ·
                    rfl

theorem cell22_2121525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 2, 1, 5].length) (baseStart_2121525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2121525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2121525 prefixEnd_2121525 := by exact prefixLift 2121525
  have htrace : WordTrace (prefixWord ++ tailWord_2121525) baseStart_2121525 baseEnd_2121525 := by
    simpa [prefixWord, tailWord_2121525, baseEnd_2121525] using wordTrace_append hprefix tailTrace_2121525
  have hstable : (prefixWord ++ tailWord_2121525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2121525).length < 2 ^ (prefixWord ++ tailWord_2121525).sum := by decide
  have hdescent : baseEnd_2121525 < baseStart_2121525 := by decide
  rcases family_descends (prefixWord ++ tailWord_2121525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2121564 : List Nat := [2, 2, 4, 2, 12]
def baseStart_2121564 : Nat := 118140960795 + 2121564 * 2 ^ 59
def prefixEnd_2121564 : Nat := 4983230072969 + 3 ^ 40 * 2121564 * 2
def baseEnd_2121564 : Nat := 2988702527504643634549

theorem tailTrace_2121564 : CollatzResearch.WordTrace tailWord_2121564 prefixEnd_2121564 2988702527504643634549 := by
  unfold tailWord_2121564
  simp only [CollatzResearch.WordTrace]
  refine ⟨38689898042971718564701873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51586530723962291419602497 38689898042971718564701873)
  ·
    refine ⟨29017423532228788923526405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38689898042971718564701873 29017423532228788923526405)
    ·
      refine ⟨5440766912292897923161201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29017423532228788923526405 5440766912292897923161201)
      ·
        refine ⟨4080575184219673442370901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5440766912292897923161201 4080575184219673442370901)
        ·
          refine ⟨2988702527504643634549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 4080575184219673442370901 2988702527504643634549)
          ·
            rfl

theorem cell22_2121564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 12].length) (baseStart_2121564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2121564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2121564 prefixEnd_2121564 := by exact prefixLift 2121564
  have htrace : WordTrace (prefixWord ++ tailWord_2121564) baseStart_2121564 baseEnd_2121564 := by
    simpa [prefixWord, tailWord_2121564, baseEnd_2121564] using wordTrace_append hprefix tailTrace_2121564
  have hstable : (prefixWord ++ tailWord_2121564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2121564).length < 2 ^ (prefixWord ++ tailWord_2121564).sum := by decide
  have hdescent : baseEnd_2121564 < baseStart_2121564 := by decide
  rcases family_descends (prefixWord ++ tailWord_2121564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2121568 : List Nat := [2, 1, 1, 3, 3, 3, 2, 2, 2, 3]
def baseStart_2121568 : Nat := 118140960795 + 2121568 * 2 ^ 59
def prefixEnd_2121568 : Nat := 4983230072969 + 3 ^ 40 * 2121568 * 2
def baseEnd_2121568 : Nat := 726256083465373726095395

theorem tailTrace_2121568 : CollatzResearch.WordTrace tailWord_2121568 prefixEnd_2121568 726256083465373726095395 := by
  unfold tailWord_2121568
  simp only [CollatzResearch.WordTrace]
  refine ⟨38689970988964472906274679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51586627985285963875032905 38689970988964472906274679)
  ·
    refine ⟨58034956483446709359412019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38689970988964472906274679 58034956483446709359412019)
    ·
      refine ⟨87052434725170064039118029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58034956483446709359412019 87052434725170064039118029)
      ·
        refine ⟨32644663021938774014669261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87052434725170064039118029 32644663021938774014669261)
        ·
          refine ⟨12241748633227040255500973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32644663021938774014669261 12241748633227040255500973)
          ·
            refine ⟨4590655737460140095812865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12241748633227040255500973 4590655737460140095812865)
            ·
              refine ⟨3442991803095105071859649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4590655737460140095812865 3442991803095105071859649)
              ·
                refine ⟨2582243852321328803894737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3442991803095105071859649 2582243852321328803894737)
                ·
                  refine ⟨1936682889240996602921053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2582243852321328803894737 1936682889240996602921053)
                  ·
                    refine ⟨726256083465373726095395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1936682889240996602921053 726256083465373726095395)
                    ·
                      rfl

theorem cell22_2121568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2, 2, 2, 3].length) (baseStart_2121568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2121568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2121568 prefixEnd_2121568 := by exact prefixLift 2121568
  have htrace : WordTrace (prefixWord ++ tailWord_2121568) baseStart_2121568 baseEnd_2121568 := by
    simpa [prefixWord, tailWord_2121568, baseEnd_2121568] using wordTrace_append hprefix tailTrace_2121568
  have hstable : (prefixWord ++ tailWord_2121568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2121568).length < 2 ^ (prefixWord ++ tailWord_2121568).sum := by decide
  have hdescent : baseEnd_2121568 < baseStart_2121568 := by decide
  rcases family_descends (prefixWord ++ tailWord_2121568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2121570 : List Nat := [3, 3, 2, 1, 2, 1, 4, 2, 4]
def baseStart_2121570 : Nat := 118140960795 + 2121570 * 2 ^ 59
def prefixEnd_2121570 : Nat := 4983230072969 + 3 ^ 40 * 2121570 * 2
def baseEnd_2121570 : Nat := 242085589368748795848463

theorem tailTrace_2121570 : CollatzResearch.WordTrace tailWord_2121570 prefixEnd_2121570 242085589368748795848463 := by
  unfold tailWord_2121570
  simp only [CollatzResearch.WordTrace]
  refine ⟨19345003730980425038530541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51586676615947800102748109 19345003730980425038530541)
  ·
    refine ⟨7254376399117659389448953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19345003730980425038530541 7254376399117659389448953)
    ·
      refine ⟨5440782299338244542086715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7254376399117659389448953 5440782299338244542086715)
      ·
        refine ⟨8161173449007366813130073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5440782299338244542086715 8161173449007366813130073)
        ·
          refine ⟨6120880086755525109847555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8161173449007366813130073 6120880086755525109847555)
          ·
            refine ⟨9181320130133287664771333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6120880086755525109847555 9181320130133287664771333)
            ·
              refine ⟨1721497524399991437144625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9181320130133287664771333 1721497524399991437144625)
              ·
                refine ⟨1291123143299993577858469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1721497524399991437144625 1291123143299993577858469)
                ·
                  refine ⟨242085589368748795848463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1291123143299993577858469 242085589368748795848463)
                  ·
                    rfl

theorem cell22_2121570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 4, 2, 4].length) (baseStart_2121570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2121570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2121570 prefixEnd_2121570 := by exact prefixLift 2121570
  have htrace : WordTrace (prefixWord ++ tailWord_2121570) baseStart_2121570 baseEnd_2121570 := by
    simpa [prefixWord, tailWord_2121570, baseEnd_2121570] using wordTrace_append hprefix tailTrace_2121570
  have hstable : (prefixWord ++ tailWord_2121570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2121570).length < 2 ^ (prefixWord ++ tailWord_2121570).sum := by decide
  have hdescent : baseEnd_2121570 < baseStart_2121570 := by decide
  rcases family_descends (prefixWord ++ tailWord_2121570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2121609 : List Nat := [1, 2, 1, 1, 5, 1, 2, 2, 7]
def baseStart_2121609 : Nat := 118140960795 + 2121609 * 2 ^ 59
def prefixEnd_2121609 : Nat := 4983230072969 + 3 ^ 40 * 2121609 * 2
def baseEnd_2121609 : Nat := 242090039534421095273423

theorem tailTrace_2121609 : CollatzResearch.WordTrace tailWord_2121609 prefixEnd_2121609 242090039534421095273423 := by
  unfold tailWord_2121609
  simp only [CollatzResearch.WordTrace]
  refine ⟨77381437370780409814791881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51587624913853606543194587 77381437370780409814791881)
  ·
    refine ⟨58036078028085307361093911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77381437370780409814791881 58036078028085307361093911)
    ·
      refine ⟨87054117042127961041640867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58036078028085307361093911 87054117042127961041640867)
      ·
        refine ⟨130581175563191941562461301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87054117042127961041640867 130581175563191941562461301)
        ·
          refine ⟨12241985209049244521480747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 130581175563191941562461301 12241985209049244521480747)
          ·
            refine ⟨18362977813573866782221121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12241985209049244521480747 18362977813573866782221121)
            ·
              refine ⟨13772233360180400086665841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18362977813573866782221121 13772233360180400086665841)
              ·
                refine ⟨10329175020135300064999381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13772233360180400086665841 10329175020135300064999381)
                ·
                  refine ⟨242090039534421095273423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10329175020135300064999381 242090039534421095273423)
                  ·
                    rfl

theorem cell22_2121609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 2, 7].length) (baseStart_2121609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2121609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2121609 prefixEnd_2121609 := by exact prefixLift 2121609
  have htrace : WordTrace (prefixWord ++ tailWord_2121609) baseStart_2121609 baseEnd_2121609 := by
    simpa [prefixWord, tailWord_2121609, baseEnd_2121609] using wordTrace_append hprefix tailTrace_2121609
  have hstable : (prefixWord ++ tailWord_2121609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2121609).length < 2 ^ (prefixWord ++ tailWord_2121609).sum := by decide
  have hdescent : baseEnd_2121609 < baseStart_2121609 := by decide
  rcases family_descends (prefixWord ++ tailWord_2121609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2121626 : List Nat := [3, 1, 1, 4, 2, 2, 1, 1, 7]
def baseStart_2121626 : Nat := 118140960795 + 2121626 * 2 ^ 59
def prefixEnd_2121626 : Nat := 4983230072969 + 3 ^ 40 * 2121626 * 2
def baseEnd_2121626 : Nat := 242091979350226969381739

theorem tailTrace_2121626 : CollatzResearch.WordTrace tailWord_2121626 prefixEnd_2121626 242091979350226969381739 := by
  unfold tailWord_2121626
  simp only [CollatzResearch.WordTrace]
  refine ⟨19345514352929705429540183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51588038274479214478773821 19345514352929705429540183)
  ·
    refine ⟨29018271529394558144310275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19345514352929705429540183 29018271529394558144310275)
    ·
      refine ⟨43527407294091837216465413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29018271529394558144310275 43527407294091837216465413)
      ·
        refine ⟨8161388867642219478087265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43527407294091837216465413 8161388867642219478087265)
        ·
          refine ⟨6121041650731664608565449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8161388867642219478087265 6121041650731664608565449)
          ·
            refine ⟨4590781238048748456424087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6121041650731664608565449 4590781238048748456424087)
            ·
              refine ⟨6886171857073122684636131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4590781238048748456424087 6886171857073122684636131)
              ·
                refine ⟨10329257785609684026954197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6886171857073122684636131 10329257785609684026954197)
                ·
                  refine ⟨242091979350226969381739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10329257785609684026954197 242091979350226969381739)
                  ·
                    rfl

theorem cell22_2121626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 1, 7].length) (baseStart_2121626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2121626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2121626 prefixEnd_2121626 := by exact prefixLift 2121626
  have htrace : WordTrace (prefixWord ++ tailWord_2121626) baseStart_2121626 baseEnd_2121626 := by
    simpa [prefixWord, tailWord_2121626, baseEnd_2121626] using wordTrace_append hprefix tailTrace_2121626
  have hstable : (prefixWord ++ tailWord_2121626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2121626).length < 2 ^ (prefixWord ++ tailWord_2121626).sum := by decide
  have hdescent : baseEnd_2121626 < baseStart_2121626 := by decide
  rcases family_descends (prefixWord ++ tailWord_2121626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2121793 : List Nat := [1, 2, 5, 1, 2, 1, 1, 2, 2, 5]
def baseStart_2121793 : Nat := 118140960795 + 2121793 * 2 ^ 59
def prefixEnd_2121793 : Nat := 4983230072969 + 3 ^ 40 * 2121793 * 2
def baseEnd_2121793 : Nat := 726333105563548139219705

theorem tailTrace_2121793 : CollatzResearch.WordTrace tailWord_2121793 prefixEnd_2121793 726333105563548139219705 := by
  unfold tailWord_2121793
  simp only [CollatzResearch.WordTrace]
  refine ⟨77388148402113809239490033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51592098934742539492993355 77388148402113809239490033)
  ·
    refine ⟨58041111301585356929617525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77388148402113809239490033 58041111301585356929617525)
    ·
      refine ⟨5441354184523627212151643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 58041111301585356929617525 5441354184523627212151643)
      ·
        refine ⟨8162031276785440818227465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5441354184523627212151643 8162031276785440818227465)
        ·
          refine ⟨6121523457589080613670599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8162031276785440818227465 6121523457589080613670599)
          ·
            refine ⟨9182285186383620920505899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6121523457589080613670599 9182285186383620920505899)
            ·
              refine ⟨13773427779575431380758849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9182285186383620920505899 13773427779575431380758849)
              ·
                refine ⟨10330070834681573535569137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13773427779575431380758849 10330070834681573535569137)
                ·
                  refine ⟨7747553126011180151676853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10330070834681573535569137 7747553126011180151676853)
                  ·
                    refine ⟨726333105563548139219705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7747553126011180151676853 726333105563548139219705)
                    ·
                      rfl

theorem cell22_2121793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_2121793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2121793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2121793 prefixEnd_2121793 := by exact prefixLift 2121793
  have htrace : WordTrace (prefixWord ++ tailWord_2121793) baseStart_2121793 baseEnd_2121793 := by
    simpa [prefixWord, tailWord_2121793, baseEnd_2121793] using wordTrace_append hprefix tailTrace_2121793
  have hstable : (prefixWord ++ tailWord_2121793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2121793).length < 2 ^ (prefixWord ++ tailWord_2121793).sum := by decide
  have hdescent : baseEnd_2121793 < baseStart_2121793 := by decide
  rcases family_descends (prefixWord ++ tailWord_2121793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2121838 : List Nat := [4, 1, 2, 2, 1, 1, 2, 1, 3, 5]
def baseStart_2121838 : Nat := 118140960795 + 2121838 * 2 ^ 59
def prefixEnd_2121838 : Nat := 4983230072969 + 3 ^ 40 * 2121838 * 2
def baseEnd_2121838 : Nat := 726348509983183021844567

theorem tailTrace_2121838 : CollatzResearch.WordTrace tailWord_2121838 prefixEnd_2121838 726348509983183021844567 := by
  unfold tailWord_2121838
  simp only [CollatzResearch.WordTrace]
  refine ⟨9673723710868847740609771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51593193124633854616585445 9673723710868847740609771)
  ·
    refine ⟨14510585566303271610914657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9673723710868847740609771 14510585566303271610914657)
    ·
      refine ⟨10882939174727453708185993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14510585566303271610914657 10882939174727453708185993)
      ·
        refine ⟨8162204381045590281139495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10882939174727453708185993 8162204381045590281139495)
        ·
          refine ⟨12243306571568385421709243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8162204381045590281139495 12243306571568385421709243)
          ·
            refine ⟨18364959857352578132563865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12243306571568385421709243 18364959857352578132563865)
            ·
              refine ⟨13773719893014433599422899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18364959857352578132563865 13773719893014433599422899)
              ·
                refine ⟨20660579839521650399134349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13773719893014433599422899 20660579839521650399134349)
                ·
                  refine ⟨7747717439820618899675381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20660579839521650399134349 7747717439820618899675381)
                  ·
                    refine ⟨726348509983183021844567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7747717439820618899675381 726348509983183021844567)
                    ·
                      rfl

theorem cell22_2121838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_2121838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2121838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2121838 prefixEnd_2121838 := by exact prefixLift 2121838
  have htrace : WordTrace (prefixWord ++ tailWord_2121838) baseStart_2121838 baseEnd_2121838 := by
    simpa [prefixWord, tailWord_2121838, baseEnd_2121838] using wordTrace_append hprefix tailTrace_2121838
  have hstable : (prefixWord ++ tailWord_2121838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2121838).length < 2 ^ (prefixWord ++ tailWord_2121838).sum := by decide
  have hdescent : baseEnd_2121838 < baseStart_2121838 := by decide
  rcases family_descends (prefixWord ++ tailWord_2121838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2121840 : List Nat := [2, 1, 1, 1, 5, 2, 3, 3, 4]
def baseStart_2121840 : Nat := 118140960795 + 2121840 * 2 ^ 59
def prefixEnd_2121840 : Nat := 4983230072969 + 3 ^ 40 * 2121840 * 2
def baseEnd_2121840 : Nat := 242116398208018561098187

theorem tailTrace_2121840 : CollatzResearch.WordTrace tailWord_2121840 prefixEnd_2121840 242116398208018561098187 := by
  unfold tailWord_2121840
  simp only [CollatzResearch.WordTrace]
  refine ⟨38694931316471768133225487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51593241755295690844300649 38694931316471768133225487)
  ·
    refine ⟨58042396974707652199838231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38694931316471768133225487 58042396974707652199838231)
    ·
      refine ⟨87063595462061478299757347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58042396974707652199838231 87063595462061478299757347)
      ·
        refine ⟨130595393193092217449636021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87063595462061478299757347 130595393193092217449636021)
        ·
          refine ⟨12243318111852395385903377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 130595393193092217449636021 12243318111852395385903377)
          ·
            refine ⟨9182488583889296539427533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12243318111852395385903377 9182488583889296539427533)
            ·
              refine ⟨3443433218958486202285325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9182488583889296539427533 3443433218958486202285325)
              ·
                refine ⟨1291287457109432325856997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3443433218958486202285325 1291287457109432325856997)
                ·
                  refine ⟨242116398208018561098187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1291287457109432325856997 242116398208018561098187)
                  ·
                    rfl

theorem cell22_2121840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3, 3, 4].length) (baseStart_2121840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2121840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2121840 prefixEnd_2121840 := by exact prefixLift 2121840
  have htrace : WordTrace (prefixWord ++ tailWord_2121840) baseStart_2121840 baseEnd_2121840 := by
    simpa [prefixWord, tailWord_2121840, baseEnd_2121840] using wordTrace_append hprefix tailTrace_2121840
  have hstable : (prefixWord ++ tailWord_2121840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2121840).length < 2 ^ (prefixWord ++ tailWord_2121840).sum := by decide
  have hdescent : baseEnd_2121840 < baseStart_2121840 := by decide
  rcases family_descends (prefixWord ++ tailWord_2121840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2121853 : List Nat := [1, 4, 1, 1, 3, 2, 1, 1, 4, 4]
def baseStart_2121853 : Nat := 118140960795 + 2121853 * 2 ^ 59
def prefixEnd_2121853 : Nat := 4983230072969 + 3 ^ 40 * 2121853 * 2
def baseEnd_2121853 : Nat := 726353644789727982719521

theorem tailTrace_2121853 : CollatzResearch.WordTrace tailWord_2121853 prefixEnd_2121853 726353644789727982719521 := by
  unfold tailWord_2121853
  simp only [CollatzResearch.WordTrace]
  refine ⟨77390336781896439486674213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51593557854597626324449475 77390336781896439486674213)
  ·
    refine ⟨14510688146605582403751415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77390336781896439486674213 14510688146605582403751415)
    ·
      refine ⟨21766032219908373605627123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14510688146605582403751415 21766032219908373605627123)
      ·
        refine ⟨32649048329862560408440685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21766032219908373605627123 32649048329862560408440685)
        ·
          refine ⟨12243393123698460153165257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32649048329862560408440685 12243393123698460153165257)
          ·
            refine ⟨9182544842773845114873943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12243393123698460153165257 9182544842773845114873943)
            ·
              refine ⟨13773817264160767672310915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9182544842773845114873943 13773817264160767672310915)
              ·
                refine ⟨20660725896241151508466373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13773817264160767672310915 20660725896241151508466373)
                ·
                  refine ⟨3873886105545215907837445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20660725896241151508466373 3873886105545215907837445)
                  ·
                    refine ⟨726353644789727982719521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3873886105545215907837445 726353644789727982719521)
                    ·
                      rfl

theorem cell22_2121853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 1, 4, 4].length) (baseStart_2121853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2121853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2121853 prefixEnd_2121853 := by exact prefixLift 2121853
  have htrace : WordTrace (prefixWord ++ tailWord_2121853) baseStart_2121853 baseEnd_2121853 := by
    simpa [prefixWord, tailWord_2121853, baseEnd_2121853] using wordTrace_append hprefix tailTrace_2121853
  have hstable : (prefixWord ++ tailWord_2121853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2121853).length < 2 ^ (prefixWord ++ tailWord_2121853).sum := by decide
  have hdescent : baseEnd_2121853 < baseStart_2121853 := by decide
  rcases family_descends (prefixWord ++ tailWord_2121853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2121857 : List Nat := [1, 2, 4, 2, 4, 1, 1, 1, 6]
def baseStart_2121857 : Nat := 118140960795 + 2121857 * 2 ^ 59
def prefixEnd_2121857 : Nat := 4983230072969 + 3 ^ 40 * 2121857 * 2
def baseEnd_2121857 : Nat := 242118338023824435206503

theorem tailTrace_2121857 : CollatzResearch.WordTrace tailWord_2121857 prefixEnd_2121857 242118338023824435206503 := by
  unfold tailWord_2121857
  simp only [CollatzResearch.WordTrace]
  refine ⟨77390482673881948169819825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51593655115921298779879883 77390482673881948169819825)
  ·
    refine ⟨58042862005411461127364869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77390482673881948169819825 58042862005411461127364869)
    ·
      refine ⟨10883036626014648961380913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58042862005411461127364869 10883036626014648961380913)
      ·
        refine ⟨8162277469510986721035685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10883036626014648961380913 8162277469510986721035685)
        ·
          refine ⟨1530427025533310010194191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8162277469510986721035685 1530427025533310010194191)
          ·
            refine ⟨2295640538299965015291287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1530427025533310010194191 2295640538299965015291287)
            ·
              refine ⟨3443460807449947522936931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2295640538299965015291287 3443460807449947522936931)
              ·
                refine ⟨5165191211174921284405397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3443460807449947522936931 5165191211174921284405397)
                ·
                  refine ⟨242118338023824435206503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5165191211174921284405397 242118338023824435206503)
                  ·
                    rfl

theorem cell22_2121857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 1, 1, 6].length) (baseStart_2121857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2121857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2121857 prefixEnd_2121857 := by exact prefixLift 2121857
  have htrace : WordTrace (prefixWord ++ tailWord_2121857) baseStart_2121857 baseEnd_2121857 := by
    simpa [prefixWord, tailWord_2121857, baseEnd_2121857] using wordTrace_append hprefix tailTrace_2121857
  have hstable : (prefixWord ++ tailWord_2121857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2121857).length < 2 ^ (prefixWord ++ tailWord_2121857).sum := by decide
  have hdescent : baseEnd_2121857 < baseStart_2121857 := by decide
  rcases family_descends (prefixWord ++ tailWord_2121857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2121876 : List Nat := [2, 4, 2, 3, 2, 1, 1, 2, 1, 4]
def baseStart_2121876 : Nat := 118140960795 + 2121876 * 2 ^ 59
def prefixEnd_2121876 : Nat := 4983230072969 + 3 ^ 40 * 2121876 * 2
def baseEnd_2121876 : Nat := 726361518159763589394451

theorem tailTrace_2121876 : CollatzResearch.WordTrace tailWord_2121876 prefixEnd_2121876 726361518159763589394451 := by
  unfold tailWord_2121876
  simp only [CollatzResearch.WordTrace]
  refine ⟨38695587830406557207380741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51594117107208742943174321 38695587830406557207380741)
  ·
    refine ⟨7255422718201229476383889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38695587830406557207380741 7255422718201229476383889)
    ·
      refine ⟨5441567038650922107287917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7255422718201229476383889 5441567038650922107287917)
      ·
        refine ⟨2040587639494095790232969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5441567038650922107287917 2040587639494095790232969)
        ·
          refine ⟨1530440729620571842674727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2040587639494095790232969 1530440729620571842674727)
          ·
            refine ⟨2295661094430857764012091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1530440729620571842674727 2295661094430857764012091)
            ·
              refine ⟨3443491641646286646018137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2295661094430857764012091 3443491641646286646018137)
              ·
                refine ⟨2582618731234714984513603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3443491641646286646018137 2582618731234714984513603)
                ·
                  refine ⟨3873928096852072476770405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2582618731234714984513603 3873928096852072476770405)
                  ·
                    refine ⟨726361518159763589394451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3873928096852072476770405 726361518159763589394451)
                    ·
                      rfl

theorem cell22_2121876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 1, 2, 1, 4].length) (baseStart_2121876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2121876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2121876 prefixEnd_2121876 := by exact prefixLift 2121876
  have htrace : WordTrace (prefixWord ++ tailWord_2121876) baseStart_2121876 baseEnd_2121876 := by
    simpa [prefixWord, tailWord_2121876, baseEnd_2121876] using wordTrace_append hprefix tailTrace_2121876
  have hstable : (prefixWord ++ tailWord_2121876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2121876).length < 2 ^ (prefixWord ++ tailWord_2121876).sum := by decide
  have hdescent : baseEnd_2121876 < baseStart_2121876 := by decide
  rcases family_descends (prefixWord ++ tailWord_2121876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2121902 : List Nat := [4, 1, 4, 2, 2, 9]
def baseStart_2121902 : Nat := 118140960795 + 2121902 * 2 ^ 59
def prefixEnd_2121902 : Nat := 4983230072969 + 3 ^ 40 * 2121902 * 2
def baseEnd_2121902 : Nat := 8967536030754422077091

theorem tailTrace_2121902 : CollatzResearch.WordTrace tailWord_2121902 prefixEnd_2121902 8967536030754422077091 := by
  unfold tailWord_2121902
  simp only [CollatzResearch.WordTrace]
  refine ⟨9674015494839865106900995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51594749305812613903471973 9674015494839865106900995)
  ·
    refine ⟨14511023242259797660351493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9674015494839865106900995 14511023242259797660351493)
    ·
      refine ⟨2720816857923712061315905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14511023242259797660351493 2720816857923712061315905)
      ·
        refine ⟨2040612643442784045986929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2720816857923712061315905 2040612643442784045986929)
        ·
          refine ⟨1530459482582088034490197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2040612643442784045986929 1530459482582088034490197)
          ·
            refine ⟨8967536030754422077091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1530459482582088034490197 8967536030754422077091)
            ·
              rfl

theorem cell22_2121902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 9].length) (baseStart_2121902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2121902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2121902 prefixEnd_2121902 := by exact prefixLift 2121902
  have htrace : WordTrace (prefixWord ++ tailWord_2121902) baseStart_2121902 baseEnd_2121902 := by
    simpa [prefixWord, tailWord_2121902, baseEnd_2121902] using wordTrace_append hprefix tailTrace_2121902
  have hstable : (prefixWord ++ tailWord_2121902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2121902).length < 2 ^ (prefixWord ++ tailWord_2121902).sum := by decide
  have hdescent : baseEnd_2121902 < baseStart_2121902 := by decide
  rcases family_descends (prefixWord ++ tailWord_2121902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2122020 : List Nat := [2, 3, 1, 3, 1, 4, 8]
def baseStart_2122020 : Nat := 118140960795 + 2122020 * 2 ^ 59
def prefixEnd_2122020 : Nat := 4983230072969 + 3 ^ 40 * 2122020 * 2
def baseEnd_2122020 : Nat := 26904104159355378288667

theorem tailTrace_2122020 : CollatzResearch.WordTrace tailWord_2122020 prefixEnd_2122020 26904104159355378288667 := by
  unfold tailWord_2122020
  simp only [CollatzResearch.WordTrace]
  refine ⟨38698213886145713504001757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51597618514860951338669009 38698213886145713504001757)
  ·
    refine ⟨14511830207304642564000659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38698213886145713504001757 14511830207304642564000659)
    ·
      refine ⟨21767745310956963846000989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14511830207304642564000659 21767745310956963846000989)
      ·
        refine ⟨8162904491608861442250371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21767745310956963846000989 8162904491608861442250371)
        ·
          refine ⟨12244356737413292163375557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8162904491608861442250371 12244356737413292163375557)
          ·
            refine ⟨2295816888264992280632917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12244356737413292163375557 2295816888264992280632917)
            ·
              refine ⟨26904104159355378288667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2295816888264992280632917 26904104159355378288667)
              ·
                rfl

theorem cell22_2122020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 8].length) (baseStart_2122020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2122020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2122020 prefixEnd_2122020 := by exact prefixLift 2122020
  have htrace : WordTrace (prefixWord ++ tailWord_2122020) baseStart_2122020 baseEnd_2122020 := by
    simpa [prefixWord, tailWord_2122020, baseEnd_2122020] using wordTrace_append hprefix tailTrace_2122020
  have hstable : (prefixWord ++ tailWord_2122020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2122020).length < 2 ^ (prefixWord ++ tailWord_2122020).sum := by decide
  have hdescent : baseEnd_2122020 < baseStart_2122020 := by decide
  rcases family_descends (prefixWord ++ tailWord_2122020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2122026 : List Nat := [3, 1, 4, 2, 2, 1, 3, 2, 4]
def baseStart_2122026 : Nat := 118140960795 + 2122026 * 2 ^ 59
def prefixEnd_2122026 : Nat := 4983230072969 + 3 ^ 40 * 2122026 * 2
def baseEnd_2122026 : Nat := 242137622075071066047997

theorem tailTrace_2122026 : CollatzResearch.WordTrace tailWord_2122026 prefixEnd_2122026 242137622075071066047997 := by
  unfold tailWord_2122026
  simp only [CollatzResearch.WordTrace]
  refine ⟨19349161652567422508180483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51597764406846460021814621 19349161652567422508180483)
  ·
    refine ⟨29023742478851133762270725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19349161652567422508180483 29023742478851133762270725)
    ·
      refine ⟨5441951714784587580425761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29023742478851133762270725 5441951714784587580425761)
      ·
        refine ⟨4081463786088440685319321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5441951714784587580425761 4081463786088440685319321)
        ·
          refine ⟨3061097839566330513989491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4081463786088440685319321 3061097839566330513989491)
          ·
            refine ⟨4591646759349495770984237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3061097839566330513989491 4591646759349495770984237)
            ·
              refine ⟨1721867534756060914119089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4591646759349495770984237 1721867534756060914119089)
              ·
                refine ⟨1291400651067045685589317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1721867534756060914119089 1291400651067045685589317)
                ·
                  refine ⟨242137622075071066047997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1291400651067045685589317 242137622075071066047997)
                  ·
                    rfl

theorem cell22_2122026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 3, 2, 4].length) (baseStart_2122026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2122026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2122026 prefixEnd_2122026 := by exact prefixLift 2122026
  have htrace : WordTrace (prefixWord ++ tailWord_2122026) baseStart_2122026 baseEnd_2122026 := by
    simpa [prefixWord, tailWord_2122026, baseEnd_2122026] using wordTrace_append hprefix tailTrace_2122026
  have hstable : (prefixWord ++ tailWord_2122026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2122026).length < 2 ^ (prefixWord ++ tailWord_2122026).sum := by decide
  have hdescent : baseEnd_2122026 < baseStart_2122026 := by decide
  rcases family_descends (prefixWord ++ tailWord_2122026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2122041 : List Nat := [1, 2, 1, 6, 1, 3, 2, 1, 2, 3]
def baseStart_2122041 : Nat := 118140960795 + 2122041 * 2 ^ 59
def prefixEnd_2122041 : Nat := 4983230072969 + 3 ^ 40 * 2122041 * 2
def baseEnd_2122041 : Nat := 726418001031758159018945

theorem tailTrace_2122041 : CollatzResearch.WordTrace tailWord_2122041 prefixEnd_2122041 726418001031758159018945 := by
  unfold tailWord_2122041
  simp only [CollatzResearch.WordTrace]
  refine ⟨77397193705215347594517977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51598129136810231729678651 77397193705215347594517977)
  ·
    refine ⟨58047895278911510695888483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77397193705215347594517977 58047895278911510695888483)
    ·
      refine ⟨87071842918367266043832725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58047895278911510695888483 87071842918367266043832725)
      ·
        refine ⟨4081492636798465595804659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 87071842918367266043832725 4081492636798465595804659)
        ·
          refine ⟨6122238955197698393706989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4081492636798465595804659 6122238955197698393706989)
          ·
            refine ⟨2295839608199136897640121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6122238955197698393706989 2295839608199136897640121)
            ·
              refine ⟨1721879706149352673230091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2295839608199136897640121 1721879706149352673230091)
              ·
                refine ⟨2582819559224029009845137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1721879706149352673230091 2582819559224029009845137)
                ·
                  refine ⟨1937114669418021757383853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2582819559224029009845137 1937114669418021757383853)
                  ·
                    refine ⟨726418001031758159018945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1937114669418021757383853 726418001031758159018945)
                    ·
                      rfl

theorem cell22_2122041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 2, 1, 2, 3].length) (baseStart_2122041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2122041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2122041 prefixEnd_2122041 := by exact prefixLift 2122041
  have htrace : WordTrace (prefixWord ++ tailWord_2122041) baseStart_2122041 baseEnd_2122041 := by
    simpa [prefixWord, tailWord_2122041, baseEnd_2122041] using wordTrace_append hprefix tailTrace_2122041
  have hstable : (prefixWord ++ tailWord_2122041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2122041).length < 2 ^ (prefixWord ++ tailWord_2122041).sum := by decide
  have hdescent : baseEnd_2122041 < baseStart_2122041 := by decide
  rcases family_descends (prefixWord ++ tailWord_2122041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2122048 : List Nat := [2, 1, 1, 2, 2, 1, 2, 2, 9]
def baseStart_2122048 : Nat := 118140960795 + 2122048 * 2 ^ 59
def prefixEnd_2122048 : Nat := 4983230072969 + 3 ^ 40 * 2122048 * 2
def baseEnd_2122048 : Nat := 242140132424937491364641

theorem tailTrace_2122048 : CollatzResearch.WordTrace tailWord_2122048 prefixEnd_2122048 242140132424937491364641 := by
  unfold tailWord_2122048
  simp only [CollatzResearch.WordTrace]
  refine ⟨38698724508094993895011399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51598299344126658526681865 38698724508094993895011399)
  ·
    refine ⟨58048086762142490842517099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38698724508094993895011399 58048086762142490842517099)
    ·
      refine ⟨87072130143213736263775649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58048086762142490842517099 87072130143213736263775649)
      ·
        refine ⟨65304097607410302197831737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87072130143213736263775649 65304097607410302197831737)
        ·
          refine ⟨48978073205557726648373803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65304097607410302197831737 48978073205557726648373803)
          ·
            refine ⟨73467109808336589972560705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48978073205557726648373803 73467109808336589972560705)
            ·
              refine ⟨55100332356252442479420529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73467109808336589972560705 55100332356252442479420529)
              ·
                refine ⟨41325249267189331859565397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55100332356252442479420529 41325249267189331859565397)
                ·
                  refine ⟨242140132424937491364641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 41325249267189331859565397 242140132424937491364641)
                  ·
                    rfl

theorem cell22_2122048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 9].length) (baseStart_2122048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2122048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2122048 prefixEnd_2122048 := by exact prefixLift 2122048
  have htrace : WordTrace (prefixWord ++ tailWord_2122048) baseStart_2122048 baseEnd_2122048 := by
    simpa [prefixWord, tailWord_2122048, baseEnd_2122048] using wordTrace_append hprefix tailTrace_2122048
  have hstable : (prefixWord ++ tailWord_2122048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2122048).length < 2 ^ (prefixWord ++ tailWord_2122048).sum := by decide
  have hdescent : baseEnd_2122048 < baseStart_2122048 := by decide
  rcases family_descends (prefixWord ++ tailWord_2122048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2122063 : List Nat := [1, 1, 2, 1, 1, 2, 1, 3, 3, 7]
def baseStart_2122063 : Nat := 118140960795 + 2122063 * 2 ^ 59
def prefixEnd_2122063 : Nat := 4983230072969 + 3 ^ 40 * 2122063 * 2
def baseEnd_2122063 : Nat := 726425532081357434968877

theorem tailTrace_2122063 : CollatzResearch.WordTrace tailWord_2122063 prefixEnd_2122063 726425532081357434968877 := by
  unfold tailWord_2122063
  simp only [CollatzResearch.WordTrace]
  refine ⟨77397996111135645351818843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51598664074090430234545895 77397996111135645351818843)
  ·
    refine ⟨116096994166703468027728265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77397996111135645351818843 116096994166703468027728265)
    ·
      refine ⟨87072745625027601020796199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116096994166703468027728265 87072745625027601020796199)
      ·
        refine ⟨130609118437541401531194299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87072745625027601020796199 130609118437541401531194299)
        ·
          refine ⟨195913677656312102296791449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130609118437541401531194299 195913677656312102296791449)
          ·
            refine ⟨146935258242234076722593587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 195913677656312102296791449 146935258242234076722593587)
            ·
              refine ⟨220402887363351115083890381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 146935258242234076722593587 220402887363351115083890381)
              ·
                refine ⟨82651082761256668156458893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 220402887363351115083890381 82651082761256668156458893)
                ·
                  refine ⟨30994156035471250558672085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 82651082761256668156458893 30994156035471250558672085)
                  ·
                    refine ⟨726425532081357434968877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30994156035471250558672085 726425532081357434968877)
                    ·
                      rfl

theorem cell22_2122063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 3, 7].length) (baseStart_2122063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2122063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2122063 prefixEnd_2122063 := by exact prefixLift 2122063
  have htrace : WordTrace (prefixWord ++ tailWord_2122063) baseStart_2122063 baseEnd_2122063 := by
    simpa [prefixWord, tailWord_2122063, baseEnd_2122063] using wordTrace_append hprefix tailTrace_2122063
  have hstable : (prefixWord ++ tailWord_2122063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2122063).length < 2 ^ (prefixWord ++ tailWord_2122063).sum := by decide
  have hdescent : baseEnd_2122063 < baseStart_2122063 := by decide
  rcases family_descends (prefixWord ++ tailWord_2122063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2122082 : List Nat := [3, 3, 2, 1, 1, 2, 1, 4, 5]
def baseStart_2122082 : Nat := 118140960795 + 2122082 * 2 ^ 59
def prefixEnd_2122082 : Nat := 4983230072969 + 3 ^ 40 * 2122082 * 2
def baseEnd_2122082 : Nat := 242144012056549239581273

theorem tailTrace_2122082 : CollatzResearch.WordTrace tailWord_2122082 prefixEnd_2122082 242144012056549239581273 := by
  unfold tailWord_2122082
  simp only [CollatzResearch.WordTrace]
  refine ⟨19349672274516702899190125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51599126065377874397840333 19349672274516702899190125)
  ·
    refine ⟨7256127102943763587196297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19349672274516702899190125 7256127102943763587196297)
    ·
      refine ⟨5442095327207822690397223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7256127102943763587196297 5442095327207822690397223)
      ·
        refine ⟨8163142990811734035595835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5442095327207822690397223 8163142990811734035595835)
        ·
          refine ⟨12244714486217601053393753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8163142990811734035595835 12244714486217601053393753)
          ·
            refine ⟨9183535864663200790045315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12244714486217601053393753 9183535864663200790045315)
            ·
              refine ⟨13775303796994801185067973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9183535864663200790045315 13775303796994801185067973)
              ·
                refine ⟨2582869461936525222200245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13775303796994801185067973 2582869461936525222200245)
                ·
                  refine ⟨242144012056549239581273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2582869461936525222200245 242144012056549239581273)
                  ·
                    rfl

theorem cell22_2122082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 4, 5].length) (baseStart_2122082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2122082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2122082 prefixEnd_2122082 := by exact prefixLift 2122082
  have htrace : WordTrace (prefixWord ++ tailWord_2122082) baseStart_2122082 baseEnd_2122082 := by
    simpa [prefixWord, tailWord_2122082, baseEnd_2122082] using wordTrace_append hprefix tailTrace_2122082
  have hstable : (prefixWord ++ tailWord_2122082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2122082).length < 2 ^ (prefixWord ++ tailWord_2122082).sum := by decide
  have hdescent : baseEnd_2122082 < baseStart_2122082 := by decide
  rcases family_descends (prefixWord ++ tailWord_2122082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2122172 : List Nat := [2, 2, 2, 4, 1, 2, 1, 8]
def baseStart_2122172 : Nat := 118140960795 + 2122172 * 2 ^ 59
def prefixEnd_2122172 : Nat := 4983230072969 + 3 ^ 40 * 2122172 * 2
def baseEnd_2122172 : Nat := 80718093889879720443727

theorem tailTrace_2122172 : CollatzResearch.WordTrace tailWord_2122172 prefixEnd_2122172 80718093889879720443727 := by
  unfold tailWord_2122172
  simp only [CollatzResearch.WordTrace]
  refine ⟨38700985833870378483768385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51601314445160504645024513 38700985833870378483768385)
  ·
    refine ⟨29025739375402783862826289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38700985833870378483768385 29025739375402783862826289)
    ·
      refine ⟨21769304531552087897119717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29025739375402783862826289 21769304531552087897119717)
      ·
        refine ⟨4081744599666016480709947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21769304531552087897119717 4081744599666016480709947)
        ·
          refine ⟨6122616899499024721064921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4081744599666016480709947 6122616899499024721064921)
          ·
            refine ⟨4591962674624268540798691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6122616899499024721064921 4591962674624268540798691)
            ·
              refine ⟨6887944011936402811198037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4591962674624268540798691 6887944011936402811198037)
              ·
                refine ⟨80718093889879720443727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6887944011936402811198037 80718093889879720443727)
                ·
                  rfl

theorem cell22_2122172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 8].length) (baseStart_2122172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2122172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2122172 prefixEnd_2122172 := by exact prefixLift 2122172
  have htrace : WordTrace (prefixWord ++ tailWord_2122172) baseStart_2122172 baseEnd_2122172 := by
    simpa [prefixWord, tailWord_2122172, baseEnd_2122172] using wordTrace_append hprefix tailTrace_2122172
  have hstable : (prefixWord ++ tailWord_2122172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2122172).length < 2 ^ (prefixWord ++ tailWord_2122172).sum := by decide
  have hdescent : baseEnd_2122172 < baseStart_2122172 := by decide
  rcases family_descends (prefixWord ++ tailWord_2122172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2122277 : List Nat := [1, 3, 1, 2, 2, 1, 3, 3, 1, 5]
def baseStart_2122277 : Nat := 118140960795 + 2122277 * 2 ^ 59
def prefixEnd_2122277 : Nat := 4983230072969 + 3 ^ 40 * 2122277 * 2
def baseEnd_2122277 : Nat := 726498788654732210118221

theorem tailTrace_2122277 : CollatzResearch.WordTrace tailWord_2122277 prefixEnd_2122277 726498788654732210118221 := by
  unfold tailWord_2122277
  simp only [CollatzResearch.WordTrace]
  refine ⟨77405801332360359900109085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51603867554906906600072723 77405801332360359900109085)
  ·
    refine ⟨29027175499635134962540907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77405801332360359900109085 29027175499635134962540907)
    ·
      refine ⟨43540763249452702443811361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29027175499635134962540907 43540763249452702443811361)
      ·
        refine ⟨32655572437089526832858521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43540763249452702443811361 32655572437089526832858521)
        ·
          refine ⟨24491679327817145124643891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32655572437089526832858521 24491679327817145124643891)
          ·
            refine ⟨36737518991725717686965837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24491679327817145124643891 36737518991725717686965837)
            ·
              refine ⟨13776569621897144132612189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36737518991725717686965837 13776569621897144132612189)
              ·
                refine ⟨5166213608211429049729571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13776569621897144132612189 5166213608211429049729571)
                ·
                  refine ⟨7749320412317143574594357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5166213608211429049729571 7749320412317143574594357)
                  ·
                    refine ⟨726498788654732210118221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7749320412317143574594357 726498788654732210118221)
                    ·
                      rfl

theorem cell22_2122277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 3, 1, 5].length) (baseStart_2122277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2122277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2122277 prefixEnd_2122277 := by exact prefixLift 2122277
  have htrace : WordTrace (prefixWord ++ tailWord_2122277) baseStart_2122277 baseEnd_2122277 := by
    simpa [prefixWord, tailWord_2122277, baseEnd_2122277] using wordTrace_append hprefix tailTrace_2122277
  have hstable : (prefixWord ++ tailWord_2122277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2122277).length < 2 ^ (prefixWord ++ tailWord_2122277).sum := by decide
  have hdescent : baseEnd_2122277 < baseStart_2122277 := by decide
  rcases family_descends (prefixWord ++ tailWord_2122277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2122311 : List Nat := [1, 1, 4, 1, 4, 1, 3, 2, 2, 3]
def baseStart_2122311 : Nat := 118140960795 + 2122311 * 2 ^ 59
def prefixEnd_2122311 : Nat := 4983230072969 + 3 ^ 40 * 2122311 * 2
def baseEnd_2122311 : Nat := 726510427549567454768117

theorem tailTrace_2122311 : CollatzResearch.WordTrace tailWord_2122311 prefixEnd_2122311 726510427549567454768117 := by
  unfold tailWord_2122311
  simp only [CollatzResearch.WordTrace]
  refine ⟨77407041414237183706846787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51604694276158122471231191 77407041414237183706846787)
  ·
    refine ⟨116110562121355775560270181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77407041414237183706846787 116110562121355775560270181)
    ·
      refine ⟨21770730397754207917550659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 116110562121355775560270181 21770730397754207917550659)
      ·
        refine ⟨32656095596631311876325989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21770730397754207917550659 32656095596631311876325989)
        ·
          refine ⟨6123017924368370976811123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32656095596631311876325989 6123017924368370976811123)
          ·
            refine ⟨9184526886552556465216685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6123017924368370976811123 9184526886552556465216685)
            ·
              refine ⟨3444197582457208674456257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9184526886552556465216685 3444197582457208674456257)
              ·
                refine ⟨2583148186842906505842193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3444197582457208674456257 2583148186842906505842193)
                ·
                  refine ⟨1937361140132179879381645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2583148186842906505842193 1937361140132179879381645)
                  ·
                    refine ⟨726510427549567454768117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1937361140132179879381645 726510427549567454768117)
                    ·
                      rfl

theorem cell22_2122311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3, 2, 2, 3].length) (baseStart_2122311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2122311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2122311 prefixEnd_2122311 := by exact prefixLift 2122311
  have htrace : WordTrace (prefixWord ++ tailWord_2122311) baseStart_2122311 baseEnd_2122311 := by
    simpa [prefixWord, tailWord_2122311, baseEnd_2122311] using wordTrace_append hprefix tailTrace_2122311
  have hstable : (prefixWord ++ tailWord_2122311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2122311).length < 2 ^ (prefixWord ++ tailWord_2122311).sum := by decide
  have hdescent : baseEnd_2122311 < baseStart_2122311 := by decide
  rcases family_descends (prefixWord ++ tailWord_2122311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2122339 : List Nat := [1, 1, 1, 5, 1, 2, 1, 4, 3, 3]
def baseStart_2122339 : Nat := 118140960795 + 2122339 * 2 ^ 59
def prefixEnd_2122339 : Nat := 4983230072969 + 3 ^ 40 * 2122339 * 2
def baseEnd_2122339 : Nat := 726520012521784715068031

theorem tailTrace_2122339 : CollatzResearch.WordTrace tailWord_2122339 prefixEnd_2122339 726520012521784715068031 := by
  unfold tailWord_2122339
  simp only [CollatzResearch.WordTrace]
  refine ⟨77408062658135744488866071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51605375105423829659244047 77408062658135744488866071)
  ·
    refine ⟨116112093987203616733299107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77408062658135744488866071 116112093987203616733299107)
    ·
      refine ⟨174168140980805425099948661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116112093987203616733299107 174168140980805425099948661)
      ·
        refine ⟨16328263216950508603120187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 174168140980805425099948661 16328263216950508603120187)
        ·
          refine ⟨24492394825425762904680281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16328263216950508603120187 24492394825425762904680281)
          ·
            refine ⟨18369296119069322178510211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24492394825425762904680281 18369296119069322178510211)
            ·
              refine ⟨27553944178603983267765317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18369296119069322178510211 27553944178603983267765317)
              ·
                refine ⟨5166364533488246862705997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27553944178603983267765317 5166364533488246862705997)
                ·
                  refine ⟨1937386700058092573514749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5166364533488246862705997 1937386700058092573514749)
                  ·
                    refine ⟨726520012521784715068031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1937386700058092573514749 726520012521784715068031)
                    ·
                      rfl

theorem cell22_2122339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 4, 3, 3].length) (baseStart_2122339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2122339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2122339 prefixEnd_2122339 := by exact prefixLift 2122339
  have htrace : WordTrace (prefixWord ++ tailWord_2122339) baseStart_2122339 baseEnd_2122339 := by
    simpa [prefixWord, tailWord_2122339, baseEnd_2122339] using wordTrace_append hprefix tailTrace_2122339
  have hstable : (prefixWord ++ tailWord_2122339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2122339).length < 2 ^ (prefixWord ++ tailWord_2122339).sum := by decide
  have hdescent : baseEnd_2122339 < baseStart_2122339 := by decide
  rcases family_descends (prefixWord ++ tailWord_2122339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2122341 : List Nat := [1, 3, 1, 3, 4, 2, 2, 6]
def baseStart_2122341 : Nat := 118140960795 + 2122341 * 2 ^ 59
def prefixEnd_2122341 : Nat := 4983230072969 + 3 ^ 40 * 2122341 * 2
def baseEnd_2122341 : Nat := 80724521906961930724225

theorem tailTrace_2122341 : CollatzResearch.WordTrace tailWord_2122341 prefixEnd_2122341 80724521906961930724225 := by
  unfold tailWord_2122341
  simp only [CollatzResearch.WordTrace]
  refine ⟨77408135604128498830438877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51605423736085665886959251 77408135604128498830438877)
  ·
    refine ⟨29028050851548187061414579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77408135604128498830438877 29028050851548187061414579)
    ·
      refine ⟨43542076277322280592121869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29028050851548187061414579 43542076277322280592121869)
      ·
        refine ⟨16328278603995855222045701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43542076277322280592121869 16328278603995855222045701)
        ·
          refine ⟨3061552238249222854133569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16328278603995855222045701 3061552238249222854133569)
          ·
            refine ⟨2296164178686917140600177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3061552238249222854133569 2296164178686917140600177)
            ·
              refine ⟨1722123134015187855450133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2296164178686917140600177 1722123134015187855450133)
              ·
                refine ⟨80724521906961930724225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1722123134015187855450133 80724521906961930724225)
                ·
                  rfl

theorem cell22_2122341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 2, 6].length) (baseStart_2122341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2122341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2122341 prefixEnd_2122341 := by exact prefixLift 2122341
  have htrace : WordTrace (prefixWord ++ tailWord_2122341) baseStart_2122341 baseEnd_2122341 := by
    simpa [prefixWord, tailWord_2122341, baseEnd_2122341] using wordTrace_append hprefix tailTrace_2122341
  have hstable : (prefixWord ++ tailWord_2122341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2122341).length < 2 ^ (prefixWord ++ tailWord_2122341).sum := by decide
  have hdescent : baseEnd_2122341 < baseStart_2122341 := by decide
  rcases family_descends (prefixWord ++ tailWord_2122341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2122367 : List Nat := [1, 1, 2, 2, 1, 1, 1, 6, 2, 5]
def baseStart_2122367 : Nat := 118140960795 + 2122367 * 2 ^ 59
def prefixEnd_2122367 : Nat := 4983230072969 + 3 ^ 40 * 2122367 * 2
def baseEnd_2122367 : Nat := 726529597494001975367945

theorem tailTrace_2122367 : CollatzResearch.WordTrace tailWord_2122367 prefixEnd_2122367 726529597494001975367945 := by
  unfold tailWord_2122367
  simp only [CollatzResearch.WordTrace]
  refine ⟨77409083902034305270885355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51606055934689536847256903 77409083902034305270885355)
  ·
    refine ⟨116113625853051457906328033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77409083902034305270885355 116113625853051457906328033)
    ·
      refine ⟨87085219389788593429746025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116113625853051457906328033 87085219389788593429746025)
      ·
        refine ⟨65313914542341445072309519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87085219389788593429746025 65313914542341445072309519)
        ·
          refine ⟨97970871813512167608464279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65313914542341445072309519 97970871813512167608464279)
          ·
            refine ⟨146956307720268251412696419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97970871813512167608464279 146956307720268251412696419)
            ·
              refine ⟨220434461580402377119044629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 146956307720268251412696419 220434461580402377119044629)
              ·
                refine ⟨10332865386581361427455217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 220434461580402377119044629 10332865386581361427455217)
                ·
                  refine ⟨7749649039936021070591413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10332865386581361427455217 7749649039936021070591413)
                  ·
                    refine ⟨726529597494001975367945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7749649039936021070591413 726529597494001975367945)
                    ·
                      rfl

theorem cell22_2122367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 6, 2, 5].length) (baseStart_2122367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2122367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2122367 prefixEnd_2122367 := by exact prefixLift 2122367
  have htrace : WordTrace (prefixWord ++ tailWord_2122367) baseStart_2122367 baseEnd_2122367 := by
    simpa [prefixWord, tailWord_2122367, baseEnd_2122367] using wordTrace_append hprefix tailTrace_2122367
  have hstable : (prefixWord ++ tailWord_2122367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2122367).length < 2 ^ (prefixWord ++ tailWord_2122367).sum := by decide
  have hdescent : baseEnd_2122367 < baseStart_2122367 := by decide
  rcases family_descends (prefixWord ++ tailWord_2122367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2122369 : List Nat := [1, 2, 4, 2, 1, 1, 2, 4, 5]
def baseStart_2122369 : Nat := 118140960795 + 2122369 * 2 ^ 59
def prefixEnd_2122369 : Nat := 4983230072969 + 3 ^ 40 * 2122369 * 2
def baseEnd_2122369 : Nat := 242176760711624878939313

theorem tailTrace_2122369 : CollatzResearch.WordTrace tailWord_2122369 prefixEnd_2122369 242176760711624878939313 := by
  unfold tailWord_2122369
  simp only [CollatzResearch.WordTrace]
  refine ⟨77409156848027059612458161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51606104565351373074972107 77409156848027059612458161)
  ·
    refine ⟨58056867636020294709343621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77409156848027059612458161 58056867636020294709343621)
    ·
      refine ⟨10885662681753805258001929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58056867636020294709343621 10885662681753805258001929)
      ·
        refine ⟨8164247011315353943501447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10885662681753805258001929 8164247011315353943501447)
        ·
          refine ⟨12246370516973030915252171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8164247011315353943501447 12246370516973030915252171)
          ·
            refine ⟨18369555775459546372878257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12246370516973030915252171 18369555775459546372878257)
            ·
              refine ⟨13777166831594659779658693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18369555775459546372878257 13777166831594659779658693)
              ·
                refine ⟨2583218780923998708686005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13777166831594659779658693 2583218780923998708686005)
                ·
                  refine ⟨242176760711624878939313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2583218780923998708686005 242176760711624878939313)
                  ·
                    rfl

theorem cell22_2122369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 4, 5].length) (baseStart_2122369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2122369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2122369 prefixEnd_2122369 := by exact prefixLift 2122369
  have htrace : WordTrace (prefixWord ++ tailWord_2122369) baseStart_2122369 baseEnd_2122369 := by
    simpa [prefixWord, tailWord_2122369, baseEnd_2122369] using wordTrace_append hprefix tailTrace_2122369
  have hstable : (prefixWord ++ tailWord_2122369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2122369).length < 2 ^ (prefixWord ++ tailWord_2122369).sum := by decide
  have hdescent : baseEnd_2122369 < baseStart_2122369 := by decide
  rcases family_descends (prefixWord ++ tailWord_2122369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2122386 : List Nat := [3, 2, 3, 1, 2, 2, 1, 3, 5]
def baseStart_2122386 : Nat := 118140960795 + 2122386 * 2 ^ 59
def prefixEnd_2122386 : Nat := 4983230072969 + 3 ^ 40 * 2122386 * 2
def baseEnd_2122386 : Nat := 242178700527430753047629

theorem tailTrace_2122386 : CollatzResearch.WordTrace tailWord_2122386 prefixEnd_2122386 242178700527430753047629 := by
  unfold tailWord_2122386
  simp only [CollatzResearch.WordTrace]
  refine ⟨19352444222241367878956753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51606517925976981010551341 19352444222241367878956753)
  ·
    refine ⟨14514333166681025909217565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19352444222241367878956753 14514333166681025909217565)
    ·
      refine ⟨5442874937505384715956587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14514333166681025909217565 5442874937505384715956587)
      ·
        refine ⟨8164312406258077073934881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5442874937505384715956587 8164312406258077073934881)
        ·
          refine ⟨6123234304693557805451161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8164312406258077073934881 6123234304693557805451161)
          ·
            refine ⟨4592425728520168354088371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6123234304693557805451161 4592425728520168354088371)
            ·
              refine ⟨6888638592780252531132557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4592425728520168354088371 6888638592780252531132557)
              ·
                refine ⟨2583239472292594699174709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6888638592780252531132557 2583239472292594699174709)
                ·
                  refine ⟨242178700527430753047629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2583239472292594699174709 242178700527430753047629)
                  ·
                    rfl

theorem cell22_2122386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 3, 5].length) (baseStart_2122386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2122386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2122386 prefixEnd_2122386 := by exact prefixLift 2122386
  have htrace : WordTrace (prefixWord ++ tailWord_2122386) baseStart_2122386 baseEnd_2122386 := by
    simpa [prefixWord, tailWord_2122386, baseEnd_2122386] using wordTrace_append hprefix tailTrace_2122386
  have hstable : (prefixWord ++ tailWord_2122386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2122386).length < 2 ^ (prefixWord ++ tailWord_2122386).sum := by decide
  have hdescent : baseEnd_2122386 < baseStart_2122386 := by decide
  rcases family_descends (prefixWord ++ tailWord_2122386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2122427 : List Nat := [1, 1, 1, 1, 1, 2, 3, 1, 5, 6]
def baseStart_2122427 : Nat := 118140960795 + 2122427 * 2 ^ 59
def prefixEnd_2122427 : Nat := 4983230072969 + 3 ^ 40 * 2122427 * 2
def baseEnd_2122427 : Nat := 726550136720181818867761

theorem tailTrace_2122427 : CollatzResearch.WordTrace tailWord_2122427 prefixEnd_2122427 726550136720181818867761 := by
  unfold tailWord_2122427
  simp only [CollatzResearch.WordTrace]
  refine ⟨77411272281816935518069535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51607514854544623678713023 77411272281816935518069535)
  ·
    refine ⟨116116908422725403277104303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77411272281816935518069535 116116908422725403277104303)
    ·
      refine ⟨174175362634088104915656455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116116908422725403277104303 174175362634088104915656455)
      ·
        refine ⟨261263043951132157373484683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174175362634088104915656455 261263043951132157373484683)
        ·
          refine ⟨391894565926698236060227025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 261263043951132157373484683 391894565926698236060227025)
          ·
            refine ⟨293920924445023677045170269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 391894565926698236060227025 293920924445023677045170269)
            ·
              refine ⟨110220346666883878891938851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 293920924445023677045170269 110220346666883878891938851)
              ·
                refine ⟨165330520000325818337908277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 110220346666883878891938851 165330520000325818337908277)
                ·
                  refine ⟨15499736250030545469178901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 165330520000325818337908277 15499736250030545469178901)
                  ·
                    refine ⟨726550136720181818867761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15499736250030545469178901 726550136720181818867761)
                    ·
                      rfl

theorem cell22_2122427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 5, 6].length) (baseStart_2122427 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2122427 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2122427 prefixEnd_2122427 := by exact prefixLift 2122427
  have htrace : WordTrace (prefixWord ++ tailWord_2122427) baseStart_2122427 baseEnd_2122427 := by
    simpa [prefixWord, tailWord_2122427, baseEnd_2122427] using wordTrace_append hprefix tailTrace_2122427
  have hstable : (prefixWord ++ tailWord_2122427).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2122427).length < 2 ^ (prefixWord ++ tailWord_2122427).sum := by decide
  have hdescent : baseEnd_2122427 < baseStart_2122427 := by decide
  rcases family_descends (prefixWord ++ tailWord_2122427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
